{-# LANGUAGE Safe                #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module QntSyn where

import Tqc
import Data.Char
import Data.Text (Text)
import qualified Data.Text as T
import Numeric.Natural
import Data.Set (Set)
import qualified Data.Set as S
import Data.Proxy

type family Id p where
  Id 'Parsed = Text
  Id 'Renamed = RName
  Id 'Typechecked = RName

data RName
  = QualName Module Text
  | LoclName Text
  | GenName Text

data Located a = L SrcSpan a
  deriving (Functor, Foldable, Traversable)

type LExpr p = Located (Expr p)
type LAlt p = Located (Alt p)
type LScheme = Located Scheme

-- Expressions {{{

data Expr p
  = EName (Id p)
  | ENatLit Natural
  | EAppl (LExpr p) (LExpr p)
  | ELambda Text (LExpr p)
  | ELet [Binding p] (LExpr p)
  | ECase (LExpr p) [LAlt p]

data Binding p
  = BindingImpl Text (LExpr p)
  | BindingExpl Text (LExpr p) LScheme

data Pattern
  = PName Text
  | PNatLit Natural
  | PConstr Text [Pattern]

data Alt p = Alt Pattern (LExpr p)

bindName :: Binding p -> Text
bindName = \case
  BindingImpl n _   -> n
  BindingExpl n _ _ -> n

-- }}}

-- Datatype declarations {{{

data DataDecl p = DataDecl Text [TyParam] [DataConstr p]

data TyParam = TyParam Text Kind

data DataConstr p = DataConstr Text [Type]

-- }}}

-- Types {{{

data Type
  = TName Text
  | TVar Text
  | TUnif Integer
  | TApp Type Type

tArrow :: Type -> Type -> Type
tArrow t0 t1 = (TApp (TName "->") t0) `TApp` t1

data Scheme = Scheme (Set Text) Type

-- }}}

-- Kinds {{{

data Kind
  = KStar
  | KArrow Kind Kind

-- }}}

data QntProg p
  = QntProg [DataDecl p] [Binding p]

pPrintScheme :: Scheme -> Text
pPrintScheme (Scheme univs t) =
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

pPrintPat :: Pattern -> Text
pPrintPat = \case
  PName x -> x
  PNatLit x -> T.pack $ show x
  PConstr c ps -> "(" <> c <> " " <> T.intercalate " " (pPrintPat <$> ps) <> ")"

-- Expression pretty-printing {{{

class PrettyExpr p where
  pPrintId :: Proxy p -> Id p -> Text

pPrintExpr :: forall p. (PrettyExpr p) => Expr p -> Text
pPrintExpr = \case
  EName x ->
    let x' = pPrintId (Proxy :: Proxy p) x
    in if isSymbolic x' then "(" <> x' <> ")" else x'
  ENatLit x -> T.pack $ show x
  EAppl (L _ e0) (L _ e1) -> "(" <> go e0 <> " " <> go e1 <> ")"
  ELambda x (L _ e) -> "(λ " <> x <> " -> " <> go e <> ")"
  ELet bs (L _ e) -> "let {" <> inter pPrintBinding bs <> "} in " <> go e
  ECase (L _ e) as -> "case " <> go e <> " of {" <> inter pPrintAlt as <> "}"
  where isSymbolic = not . isAlpha . T.head
        inter f xs = T.intercalate "; " (f <$> xs)
        go = pPrintExpr

instance PrettyExpr 'Parsed where
  pPrintId _ x = x

instance PrettyExpr 'Renamed where
  pPrintId _ = \case
    QualName (Module ms) x -> T.intercalate "." ms <> "." <> x
    LoclName x -> x
    GenName x -> "%" <> x


pPrintAlt :: (PrettyExpr p) => LAlt p -> Text
pPrintAlt (L _ (Alt pat (L _ e))) = pPrintPat pat <> " -> " <> pPrintExpr e

pPrintBinding :: (PrettyExpr p) => Binding p -> Text
pPrintBinding = \case
  BindingImpl x (L _ e) -> x <> " = " <> pPrintExpr e
  BindingExpl x (L _ e) (L _ t) -> x <> " :: " <> pPrintScheme t <> "; " <> x <> " = " <> pPrintExpr e

-- }}}
