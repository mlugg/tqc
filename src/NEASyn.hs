{-# LANGUAGE Safe, LambdaCase, OverloadedStrings #-}

module NEASyn where

import Data.Char
import Data.Text (Text)
import qualified Data.Text as T
import Numeric.Natural

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
  | TAppl Type Type
  deriving (Show)

data TypeScheme = TypeScheme [Text] Type
  deriving (Show)

-- }}}

-- Kinds {{{

data Kind
  = KStar
  | KArrow Kind Kind
  deriving (Show)

-- }}}

data NEAProg
  = NEAProg [DataDecl] [Binding]
  deriving (Show)

pPrintTypeScheme :: TypeScheme -> Text
pPrintTypeScheme (TypeScheme univs t) =
  if null univs
  then pPrintType t
  else "∀" <> T.intercalate " " univs <> ". " <> pPrintType t

pPrintType :: Type -> Text
pPrintType = \case
  TAppl (TAppl (TName "->") x) y -> "(" <> pPrintType x <> " -> " <> pPrintType y <> ")"

  TName x ->
    if isSymbolic x
    then "(" <> x <> ")"
    else x

  TVar x -> x

  TAppl x y -> "(" <> pPrintType x <> " " <> pPrintType y <> ")"

  where isSymbolic = not . isAlpha . T.head
