{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
module Icicle.Test.Avalanche.Flatten where

import           Icicle.Test.Gen.Core.Value
import           Icicle.Test.Gen.Core.Type
import           Icicle.Test.Gen.Core.Program
import           Icicle.Test.Arbitrary.Data
import           Icicle.Test.Arbitrary.Core (testFresh, testFreshT)

import           Hedgehog hiding (Var, eval)

import qualified Icicle.Core.Eval.Exp       as XV

import qualified Icicle.Core.Program.Check as Core
import qualified Icicle.Avalanche.Check     as Check
import qualified Icicle.Avalanche.Program   as AP
import qualified Icicle.Avalanche.FromCore  as AC
import qualified Icicle.Avalanche.Eval      as AE
import qualified Icicle.Avalanche.Prim.Eval as AE
import qualified Icicle.Avalanche.Prim.Flat as AF
import qualified Icicle.Avalanche.Statement.Flatten   as AF
import qualified Icicle.Avalanche.Statement.Flatten.Type as AF
import qualified Icicle.Avalanche.Simp                    as Avalanche

import           Icicle.Internal.Pretty (pretty)

import qualified Icicle.Compiler as P


import           P

import           System.IO


-- We need a way to differentiate stream variables from scalars
namer = AC.namerText (flip Var 0)


-- TODO: add async lifted timeout, fail when >10s or so
prop_flatten_commutes_check = property $ do
 t      <- forAll genInputType
 o      <- forAll genOutputType
 evalIO $ putStrLn " - - - G E N E R A T E - - -"
 core   <- forAll (programForStreamType t o)
 evalIO $ putStrLn "========================================================"
 evalIO $ putStrLn (show $ pretty core)
 evalIO $ putStrLn "========================================================"

 evalIO $ putStrLn " - - - C O R E C H E C K - - -"
 _      <- evalEither $ Core.checkProgram core

 evalIO $ putStrLn " - - - A V A L A N C H E - - -"
 let aval = P.coreAvalanche core
 evalIO $ putStrLn (show $ pretty aval)

 evalIO $ putStrLn " - - - F L A T T E N - - -"
 flat <- evalEither $ P.flattenAvalanche aval
 evalIO $ putStrLn (show $ pretty flat)

 evalIO $ putStrLn " - - - S I M P - - -"
 simp <- evalEither $ P.simpFlattened Avalanche.defaultSimpOpts flat

 evalIO $ putStrLn " - - - S I M P C H E C K - - -"
 _ <- evalEither $ Check.checkProgram AF.flatFragment simp
 return ()


-- Flattening - removing all folds keeps value same
prop_flatten_commutes_value = property $ do
 t      <- forAll genInputType
 o      <- forAll genOutputType
 p      <- forAll (programForStreamType t o)
 (vs,d) <- forAll (inputsForType t)

 let p' = testFresh "fromCore" $ AC.programFromCore namer p
 let eval xp = AE.evalProgram xp d vs
 let simp = testFreshT "anf" (AF.flatten () $ AP.statements p')

 case simp of
  Left e -> do
   annotate (show e)
   annotate (show $ pretty p')
   failure
  Right s' -> do
   annotate ("Avalanche:\n" <> show (pretty p'))
   annotate ("Flat:\n" <> show (pretty s'))
   let xv' = flatOuts (eval XV.evalPrim p')
   let fv' = eval AE.evalPrim p' { AP.statements = s'}
   first show xv' === first show fv'
 where
  -- We might need to fix up some outputs after the flattening.
  -- Flattening changes buffers to pairs of buffers (for fact identifiers),
  -- so any buffers in the output will have changed values.
  -- However, this will not occur in a "real program" as they cannot return buffers,
  -- only arrays that are read from buffers.
  -- That means it is fine to do the transform afterwards, here.
  flatOuts (Right (outs,bgs))
   = Right (fmap (second AF.flatV) outs, bgs)

  flatOuts other = other



prop_flatten_simp_commutes_value = property $ do
 t <- forAll genInputType
 o <- forAll genOutputType
 p <- forAll (programForStreamType t o)
 x <- forAll (inputsForType t)
 flatten_simp_commutes_value p x

flatten_simp_commutes_value p (vs, d) = do
  let aval = P.coreAvalanche p
  let flat = P.coreFlatten p
  case flat of
   Left e -> do
    annotate (show e)
    annotate (show $ pretty aval)
    failure
   Right flat' -> do
    annotate (show $ pretty aval)
    annotate (show $ pretty flat')
    eval XV.evalPrim aval `compareEvalResult` eval AE.evalPrim flat'
 where
  eval xp  = AE.evalProgram xp d vs
  compareEvalResult xv yv = do
    let xv' = second snd (first show xv)
    let yv' = second snd (first show yv)
    xv' === yv'

return []
tests :: IO Bool
tests = checkParallel $$(discover)

