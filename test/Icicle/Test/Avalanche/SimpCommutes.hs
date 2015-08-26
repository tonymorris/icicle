{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
module Icicle.Test.Avalanche.SimpCommutes where

import           Icicle.Test.Core.Arbitrary
import           Icicle.Core.Program.Check
import qualified Icicle.Core.Eval.Exp       as XV

import qualified Icicle.Avalanche.FromCore  as AC
import qualified Icicle.Avalanche.Eval      as AE
import qualified Icicle.Avalanche.Simp      as AS

import           Icicle.Common.Base
import qualified Icicle.Common.Fresh                as Fresh

import           Icicle.Internal.Pretty

import           P

import           System.IO

import           Test.QuickCheck

-- We need a way to differentiate stream variables from scalars
namer = AC.namerText (flip Var 0)


-- Simplifying the Avalanche doesn't affect the value
prop_simp_commutes_value t =
 forAll (programForStreamType t)
 $ \p ->
 forAll (inputsForType t)
 $ \(vs,d) ->
    isRight     (checkProgram p) ==>
     let p' = AC.programFromCore namer p

         simp = snd
              $ Fresh.runFresh
                        (AS.simpAvalanche () p')
                        (Fresh.counterNameState (Name . Var "anf") 0)
         eval = AE.evalProgram XV.evalPrim d vs
     in counterexample (show $ pretty p')
      $ counterexample (show $ pretty simp)
       ((snd <$> eval p') === (snd <$> eval simp))


return []
tests :: IO Bool
tests = $quickCheckAll
-- tests = $forAllProperties $ quickCheckWithResult (stdArgs {maxSuccess = 10000})

