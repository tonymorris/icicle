-- | Query expressions, like aggregates and operators and stuff
-- Expressions can have nested queries, but putting queries and expressions
-- in the same file just gets too confusing.
-- To break the cycle, we make Exp' take a recursive parameter for the query,
-- and "tie the knot" in Query.
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TupleSections #-}
module Icicle.Source.Query.Exp (
    Exp'      (..)
  , Prim      (..)
  , Lit       (..)
  , Op        (..)
  , Fun
  , BuiltinFun   (..)
  , BuiltinMath  (..)
  , BuiltinText  (..)
  , BuiltinTime  (..)
  , BuiltinData  (..)
  , BuiltinArray (..)
  , BuiltinMap   (..)
  , BuiltinRegex (..)

  , TraverseAnnot (..)
  , reannot

  , takeApps
  , makeApp
  , takePrimApps
  , takeLams
  , makeLams
  , annotOfExp
  , annotOfExpL
  , mkApp
  , precedenceOfX
  , listOfIntroducedFuns
  , listOfWiredFuns
  ) where

import           Control.Lens.Setter (over)
import           Control.Lens(Plated(plate), Lens', view, _2)
import qualified Data.Text as Text

import           GHC.Generics (Generic)

import           Icicle.Data.Time
import           Icicle.Source.Query.Builtin
import           Icicle.Source.Query.Constructor
import           Icicle.Source.Query.Operators
import           Icicle.Source.Type (Annot (..))
import           Icicle.Internal.Pretty
import           Icicle.Common.Base

import           P

-- | Icicle Source Language Constructs.
data Exp' q a n

  -- | Bound variable
  = Var a (Name n)

  -- | Function abstraction.
  | Lam a (Name n) (Exp' q a n)

  -- | Nested query
  | Nested a (q a n)

  -- | Function application.
  | App  a (Exp' q a n) (Exp' q a n)

  -- | Source Primitive
  | Prim a Prim

  -- | If then else block
  | If a (Exp' q a n) (Exp' q a n) (Exp' q a n)

  -- | Case matching with patterns
  | Case a (Exp' q a n) [(Pattern n, Exp' q a n)]

  -- | Struct field access
  | Access a (Exp' q a n) StructField

  deriving (Show, Eq, Ord, Generic)

instance (NFData (q a n), NFData a, NFData n) => NFData (Exp' q a n)

instance Plated (Exp' q a n) where
  plate _ (Var a n) =
    pure (Var a n)
  plate f (Lam a n q) =
    Lam a n <$> f q
  plate _ (Nested a q) =
    pure (Nested a q)
  plate f (App a x y) =
    App a <$> f x <*> f y
  plate _ (Prim a p) =
    pure (Prim a p)
  plate f (If a pred true false) =
    If a <$> f pred <*> f true <*> f false
  plate f (Case a scrut pats) =
    Case a <$> f scrut <*> (traverse . _2) f pats
  plate f (Access a x n) =
    Access a <$> f x <*> pure n

-- | Icicle Source Language Primitives
data Prim

  -- | Operators
  = Op Op

  -- | Literals, such as Int and String
  | Lit Lit

  -- | Primitive functions
  | Fun BuiltinFun

  -- | Type constructors
  | PrimCon Constructor

  deriving (Show, Eq, Ord, Generic)

instance NFData Prim

-- | Built-in Source functions
type Fun = BuiltinFun


class TraverseAnnot q where
  traverseAnnot :: Applicative f => (a -> f a') -> q a n -> f (q a' n)


reannot :: TraverseAnnot q => (a -> a') -> q a n -> q a' n
reannot = over traverseAnnot


instance TraverseAnnot Annot where
  traverseAnnot f xx =
    case xx of
      Annot a r cs ->
        Annot <$> f a <*> pure r <*> traverse (\(p, x) -> (,x) <$> f p) cs


instance TraverseAnnot q => TraverseAnnot (Exp' q) where
  traverseAnnot f xx =
    case xx of
      Var a n ->
        Var <$> f a <*> pure n
      Lam a n q ->
        Lam <$> f a <*> pure n <*> traverseAnnot f q
      Nested a q ->
        Nested <$> f a <*> traverseAnnot f q
      App a x y ->
        App <$> f a <*> traverseAnnot f x <*> traverseAnnot f y
      Prim a p ->
        Prim <$> f a <*> pure p
      If a pred true false ->
        If
          <$> f a
          <*> traverseAnnot f pred
          <*> traverseAnnot f true
          <*> traverseAnnot f false
      Case a scrut pats ->
        Case
          <$> f a
          <*> traverseAnnot f scrut
          <*> traverse (\(p, x) -> (p,) <$> traverseAnnot f x) pats
      Access a x n ->
        Access <$> f a <*> traverseAnnot f x <*> pure n

takeLams :: Exp' q a n -> ([(a, Name n)], Exp' q a n)
takeLams (Lam a n x) =
  let
    (bs, ret) = takeLams x
    binds = (a, n) : bs
  in
    (binds, ret)
takeLams x = ([], x)

makeLams :: [(a, Name n)] -> Exp' q a n -> Exp' q a n
makeLams ls x = foldr (uncurry Lam) x ls

takeApps :: Exp' q a n -> (Exp' q a n, [Exp' q a n])
takeApps xx
 = case xx of
    App _ f x
     -> let (f', xs) = takeApps f
        in  (f', xs <> [x])
    _
     -> (xx, [])

makeApp :: a ->  [Exp' q a n] -> Exp' q a n -> Exp' q a n
makeApp a ls x = foldr (App a) x ls

takePrimApps :: Exp' q a n -> Maybe (Prim, a, [Exp' q a n])
takePrimApps x
 | (Prim a p, xs) <- takeApps x
 = Just (p, a, xs)
 | otherwise
 = Nothing

annotOfExp :: Exp' q a n -> a
annotOfExp = view annotOfExpL

annotOfExpL :: Lens' (Exp' q a n) a
annotOfExpL f (Var a n)=
  fmap (\a' -> Var a' n) (f a)
annotOfExpL f (Lam a n q)=
  fmap (\a' -> Lam a' n q) (f a)
annotOfExpL f (Nested a q)=
  fmap (\a' -> Nested a' q) (f a)
annotOfExpL f (App a x y)=
  fmap (\a' -> App a' x y) (f a)
annotOfExpL f (Prim a p)=
  fmap (\a' -> Prim a' p) (f a)
annotOfExpL f (If a pred true false)=
  fmap (\a' -> If a' pred true false) (f a)
annotOfExpL f (Case a scrut pats)=
  fmap (\a' -> Case a' scrut pats) (f a)
annotOfExpL f (Access a x n)=
  fmap (\a' -> Access a' x n) (f a)

mkApp :: Exp' q a n -> Exp' q a n -> Exp' q a n
mkApp x y
 = App (annotOfExp x) x y

instance (Pretty n, Pretty (q a n)) => Pretty (Exp' q a n) where
  prettyPrec outer_prec xx =
    wrap $
      case xx of
        Var _ n ->
          annotate AnnVariable (pretty n)

        Nested _ q ->
          pretty q

        App{}
           -- Operators
           | Just (Op o, _, [x]) <- takePrimApps xx
           , FPrefix <- fixity o
           -> pretty o <+> prettyPrec inner_prec x
           | Just (Op o, _, [x,y]) <- takePrimApps xx
           , FInfix _ <- fixity o
           ->  prettyPrec inner_prec_1 x
           <+> pretty o
           <+> prettyPrec inner_prec_2 y

        App _ x y ->
          prettyPrec inner_prec_1 x <+> prettyPrec inner_prec_2 y

        Prim _ (Lit (LitTime t)) ->
          annotate AnnPrimitive (text $ Text.unpack $ renderTime t)

        Prim _ p ->
          annotate AnnPrimitive (pretty p)

        Lam _ n x ->
          prettyPunctuation "(" <>
          prettyPunctuation "\\" <> pretty n <+> prettyPunctuation "->" <+> prettyPrec appPrec1 x <>
          prettyPunctuation ")"

        Case _ scrut pats ->
          vsep [
              prettyKeyword "case" <+> pretty scrut <+> prettyKeyword "of"
            , prettyPunctuation "{"
            , vcat . with pats $ \(p, x) ->
                vsep [
                    indent 2 $ pretty p <+> prettyPunctuation "then"
                  , indent 4 $ pretty x
                  ] <+> prettyPunctuation ";"
            , prettyPunctuation "}"
            ]

        If _ scrut true false ->
          vsep [
              prettyKeyword "if" <+> pretty scrut <+> prettyKeyword "then"
            , indent 4 $ pretty true
            , prettyKeyword "else"
            , indent 4 $ pretty false
            ]

        Access _ expression field ->
          pretty expression <> "." <> pretty field

   where
    (inner_prec, assoc) = precedenceOfX xx

    -- Precedence of first operator argument
    inner_prec_1
     | AssocLeft <- assoc
     = inner_prec
     | otherwise
     = inner_prec + 1

    -- Precedence of second operator argument
    inner_prec_2
     | AssocRight <- assoc
     = inner_prec
     | otherwise
     = inner_prec + 1

    -- Suppose we have
    --
    --   7   6   7   (precedences)
    -- a * b + c * d
    --
    --        +        6
    --      /   \
    --     *     *     7
    --    / \   / \
    --   a   b c   d
    --
    -- So when pretty printing, the precedence is allowed to increase
    -- without requiring parentheses, but decreasing needs them.
    --
    wrap =
      parensWhen (inner_prec < outer_prec)

-- | Find the pretty-printing precedence of an expression.
precedenceOfX :: Exp' q a n -> (Int, Assoc)
precedenceOfX xx
 -- Note: this is assuming that operators will only be applied to one or two arguments,
 -- and that the expression has the right number of arguments.
 | Just (Op o, _, as) <- takePrimApps xx
 = case fixity o of
    FInfix (Infix a p)
     | length as == 2
     -> (p, a)
    FPrefix
     | length as == 1
     -> precedencePrefix

    _
     -> precedenceApplication
 | otherwise
 = case xx of
    Var{}
     -> precedenceNeverParens
    Lam{}
     -> precedenceApplication
    Nested{}
     -> precedenceAlwaysParens
    App{}
     -> precedenceApplication
    Prim _ (Op _)
     -> precedenceAlwaysParens
    Prim{}
     -> precedenceNeverParens
    If{}
     -> precedenceApplication
    Case{}
     -> precedenceApplication
    Access{}
     -> precedenceNeverParens

instance Pretty Prim where
  pretty = \case
    Op o ->
      pretty o
    Lit l ->
      pretty l
    Fun f ->
      pretty f
    PrimCon c ->
      pretty c
