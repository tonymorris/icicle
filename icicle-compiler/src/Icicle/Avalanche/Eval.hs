-- | Evaluate Avalanche programs
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PatternGuards     #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DoAndIfThenElse   #-}
module Icicle.Avalanche.Eval (
    evalProgram
  , evalStmt
  , RuntimeError
  ) where

import              Icicle.Avalanche.Statement.Statement
import              Icicle.Avalanche.Statement.Simp.Melt
import              Icicle.Avalanche.Program

import              Icicle.Common.Base
import              Icicle.Common.Eval
import              Icicle.Common.NanEq
import              Icicle.Common.Type
import              Icicle.Common.Value
import qualified    Icicle.Common.Exp as XV

import              Icicle.Data         (AsAt(..))
import              Icicle.Data.Name

import              GHC.Generics (Generic)

import              P

import              Data.List   (zip)
import qualified    Data.Map    as Map
import              Data.Hashable (Hashable)


import              Icicle.Internal.Pretty

-- | Store history information about the accumulators
type AccumulatorHeap n
 = Map.Map (Name n) BaseValue


-- | What can go wrong evaluating an Avalanche
data RuntimeError a n p
 = RuntimeErrorNoAccumulator (Name n)
 | RuntimeErrorAccumulator   (XV.RuntimeError a n p)
 | RuntimeErrorLoop          (XV.RuntimeError a n p)
 | RuntimeErrorLoopAccumulatorBad (Name n)
 | RuntimeErrorIfNotBool     BaseValue
 | RuntimeErrorForeachNotInt BaseValue BaseValue
 | RuntimeErrorForeachTypeMismatch [(Name n, ValType)] ValType BaseValue
 | RuntimeErrorOutputTypeMismatch  OutputId ValType [BaseValue]
 | RuntimeErrorNotBaseValue  (Value a n p)
 | RuntimeErrorAccumulatorLatestNotInt  BaseValue
 | RuntimeErrorOutOfScope (Name n)
 deriving (Eq, Show, Generic, NanEq)

instance (Pretty n, Pretty p) => Pretty (RuntimeError a n p) where
 pretty (RuntimeErrorNoAccumulator n)
  = "No accumulator:" <+> pretty n
 pretty (RuntimeErrorAccumulator p)
  = pretty p
 pretty (RuntimeErrorLoop p)
  = pretty p
 pretty (RuntimeErrorLoopAccumulatorBad n)
  = "Bad loop accumulator:" <+> pretty n
 pretty (RuntimeErrorIfNotBool p)
  = "Value should be a bool but isn't" <+> (pretty p)
 pretty (RuntimeErrorForeachNotInt p p')
  = "Foreach not ints:" <+> pretty p <+> pretty p'
 pretty (RuntimeErrorForeachTypeMismatch ns ty v)
  = "Foreach type error: bindings = " <+> align (vsep (fmap pretty ns)) <> line <>
    "                    type     = " <+> pretty ty <> line <>
    "                    value    = " <+> pretty v
 pretty (RuntimeErrorOutputTypeMismatch n ty vs)
  = "Output type error: name   = " <+> pretty n  <> line <>
    "                   type   = " <+> pretty ty <> line <>
    "                   values = " <+> align (vsep (fmap pretty vs))
 pretty (RuntimeErrorNotBaseValue p)
  = "Value isn't a base value:" <+> (pretty p)
 pretty (RuntimeErrorAccumulatorLatestNotInt p)
  = "Accumulator Latest needs an integer, got" <+> pretty p
 pretty (RuntimeErrorOutOfScope n)
  = "Name went out of scope unexpectedly:" <+> pretty n


-- | Extract base value; return an error if it's a closure
baseValue :: Value a n p -> Either (RuntimeError a n p) BaseValue
baseValue v
 = getBaseValue (RuntimeErrorNotBaseValue v) v


-- | Evaluate an entire program
-- with given primitive evaluator and values
evalProgram
        :: (Hashable n, Eq n, Show n, Show p, Show a)
        => XV.EvalPrim a n p
        -> EvalContext
        -> [AsAt BaseValue]
        -> Program a n p
        -> Either (RuntimeError a n p) [(OutputId, BaseValue)]

evalProgram evalPrim ctx values p
 = do   -- Precomputations are just expressions

        -- Keep evaluating the same loop for every value
        -- with accumulator and scalar heaps threaded through
        let stmts = statements p
        let xh    = Map.fromList
                  [ (bindtime   p, VBase $ VTime $ evalSnapshotTime ctx)
                  , (maxMapSize p, VBase $ VInt  $ evalMaxMapSize   ctx) ]
        let ah    = Map.empty
        snd <$> evalStmt evalPrim xh values ah stmts


-- | Evaluate a single statement for a single value
evalStmt
        :: (Hashable n, Eq n, Show n, Show p, Show a)
        => XV.EvalPrim a n p
        -> Heap a n p
        -> [AsAt BaseValue]
        -> AccumulatorHeap n
        -> Statement a n p
        -> Either (RuntimeError a n p) (AccumulatorHeap n, [(OutputId, BaseValue)])

evalStmt evalPrim xh values ah stmt
 = case stmt of
    If x stmts elses
     -> do  v   <- eval x >>= baseValue
            case v of
             -- Run "then" or "else"?
             VBool True
              -> go' stmts
             VBool False
              -> go' elses
             _-> Left (RuntimeErrorIfNotBool v)

    -- Evaluate and insert the value into the heap.
    Let n x stmts
     -> do  v <- eval x
            go (Map.insert n v xh) ah stmts

    While t acc _ to stmts
     -> do  tov <- eval to >>= baseValue
            let check WhileEq = (==)
                check WhileNe = (/=)
            let evalLoop curr@(ah',out) end
                 = do accv <- maybeToRight (RuntimeErrorLoopAccumulatorBad acc)
                            $ Map.lookup acc ah'
                      if check t accv end
                      then do next <-  appendOutputs out
                                   <$> go xh ah' stmts
                              evalLoop next end
                      else return curr
            evalLoop (ah, mempty) tov

    ForeachInts t n from to stmts
     -> do  fromv <- eval from >>= baseValue
            tov   <- eval to   >>= baseValue
            let evalLoop (ah',out) index
                 = appendOutputs out
                 <$> go (Map.insert n (VBase $ VInt index) xh) ah' stmts

            case (fromv, tov) of
             (VInt fromi, VInt toi)
              -> -- Open-closed interval [from,to)
                 -- ie "foreach i in 0 to 0" does not run
                 foldM evalLoop
                       (ah, mempty)
                       (case t of
                          ForeachStepUp   -> [fromi, fromi + 1 .. toi-1]
                          ForeachStepDown -> [fromi, fromi - 1 .. toi+1])
             _
              -> Left $ RuntimeErrorForeachNotInt fromv tov

    -- Allow unmelted foreach
    -- (i.e. where ty == ty' and we only have a singleton list of bindings)
    ForeachFacts (FactBinds ntime [(n, ty)]) ty' stmts
     | ty == ty'
     -> do  let evalInput (ah',out) inp = do
                  let v0     = atFact inp
                      v1     = VTime (atTime inp)
                      vv     = VPair v0 v1
                      input' = Map.insert n     (VBase vv)
                             $ Map.insert ntime (VBase v1) xh

                  appendOutputs out <$> evalStmt evalPrim input' [] ah' stmts

            foldM evalInput (ah,mempty) values

    ForeachFacts (FactBinds ntime ns) ty stmts
     -> do  let evalInput (ah',out) inp = do
                  let v0  = atFact inp
                      v1  = VTime (atTime inp)
                      vv  = VPair v0 v1
                      mvs = meltValue vv ty
                      input1 = Map.insert ntime (VBase v1) xh

                  case mvs of
                    Nothing
                     -> Left (RuntimeErrorForeachTypeMismatch ns ty vv)

                    Just vs
                     | length vs /= length ns
                     -> Left (RuntimeErrorForeachTypeMismatch ns ty vv)

                     | otherwise
                     , nvs    <- zip (fmap fst ns) vs
                     , input' <- foldr (\(n, v) -> Map.insert n (VBase v)) input1 nvs
                     -> appendOutputs out <$> evalStmt evalPrim input' [] ah' stmts

            foldM evalInput (ah,mempty) values

    Block []
     -> returnHeap ah
    Block [s]
     -> go' s
    Block (s:ss)
     -> do (ah',out) <- go xh ah s
           appendOutputs out <$> go xh ah' (Block ss)

    InitAccumulator (Accumulator n _ x) stmts
     -> do v <- eval x >>= baseValue
           let ah' = Map.insert n v ah
           go xh ah' stmts

    -- Read from an accumulator
    Read n acc _ stmts
     -> do  -- Get the current value and apply the function
            v   <- case Map.lookup acc ah of
                    Just vacc
                     -> return $ VBase vacc
                    _
                     -> Left (RuntimeErrorLoopAccumulatorBad acc)
            go (Map.insert n v xh) ah stmts

    -- Update accumulator
    Write n x
     -> do  v   <- eval x >>= baseValue
            returnHeap (Map.insert n v ah)

    Output n t xts
     -> do  vs  <- traverse ((baseValue =<<) . eval . fst) xts
            case (vs, unmeltValue vs t) of
              --
              -- If this Avalanche program has been through the melting
              -- transform and everything worked properly then `unmeltValue`
              -- will return `Just v`, otherwise it will return `Nothing`.
              --
              -- `Nothing` could mean that we have an invalid Avalanche program
              -- or a bug in `unmeltValue`, but if `vs` only contains a single
              -- value, then it probably means that it was a value that didn't
              -- need unmelting because the program has not been through the
              -- melting transform yet.
              --
              (_,    Just v)  -> return (ah, [(n, v)])
              (v:[], Nothing) -> return (ah, [(n, v)])
              (_,    Nothing) -> Left (RuntimeErrorOutputTypeMismatch n t vs)

 where
  -- Go through all the substatements
  go xh' = evalStmt evalPrim xh' values
  go' = go xh ah

  appendOutputs out (ah', out')
   = (ah', out <> out')
  returnHeap ah'
   = return (ah', mempty)

  -- Raise Exp error to Avalanche
  eval = first RuntimeErrorLoop
       . XV.eval evalPrim xh

