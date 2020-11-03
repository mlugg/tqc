{-# LANGUAGE Safe, LambdaCase, OverloadedStrings #-}

module QntSyn where

import Data.Char
import Data.Text (Text)
import qualified Data.Text as T
import Numeric.Natural
import Data.Set (Set)
import qualified Data.Set as S

-- Expressions {{{

data Expr
  = EName Text
  | ENatLit Natural
  | EAppl Expr Expr
  | ELambda Text Expr
  | ELet [Binding] Expr
  | ECase Expr [(Pattern, Expr)]
  deriving (Show)

data Binding
  = BindingImpl Text Expr
  | BindingExpl Text Expr TypeScheme
  deriving (Show)

data Pattern
  = PName Text
  | PNatLit Natural
  | PConstr Text [Text] -- TODO: eventually, allow nesting
  deriving (Show)

-- }}}

-- Datatype declarations {{{

data DataDecl = DataDecl Text [TyParam] [DataConstr]
  deriving (Show)

data TyParam = TyParam Text Kind
  deriving (Show)

data DataConstr = DataConstr Text [Type]
  deriving (Show)

-- }}}

-- Types {{{

data Type
  = TName Text
  | TVar Text
  | TUnif Integer
  | TApp Type Type
  deriving (Show, Eq)

tArrow :: Type -> Type -> Type
tArrow t0 t1 = TApp (TApp (TName "->") t0) t1

data TypeScheme = TypeScheme (Set Text) Type
  deriving (Show, Eq)

-- }}}

-- Kinds {{{

data Kind
  = KStar
  | KArrow Kind Kind
  deriving (Show)

-- }}}

data QntProg
  = QntProg [DataDecl] [Binding]
  deriving (Show)

pPrintTypeScheme :: TypeScheme -> Text
pPrintTypeScheme (TypeScheme univs t) =
  if null univs
  then pPrintType t
  else "∀" <> T.intercalate " " (S.elems univs) <> " . " <> pPrintType t

pPrintType :: Type -> Text
pPrintType = \case
  TApp (TApp (TName "->") x) y -> "(" <> pPrintType x <> " -> " <> pPrintType y <> ")"

  TName x ->
    if isSymbolic x
    then "(" <> x <> ")"
    else x

  TVar x -> x

  TUnif x -> "α" <> T.pack (show x)

  TApp x y -> "(" <> pPrintType x <> " " <> pPrintType y <> ")"

  where isSymbolic = not . isAlpha . T.head
