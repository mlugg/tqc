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
import Data.Text (Text)
import qualified Data.Text as T
import Numeric.Natural
import Data.Set (Set)
import Data.Proxy
import Text.Megaparsec.Pos (SourcePos)

type family Id p where
  Id 'Parsed = Text
  Id 'Renamed = RName
  Id 'Typechecked = RName

type family Binder p where
  Binder 'Parsed = Text
  Binder 'Renamed = Text
  Binder 'Typechecked = TcBinder

data TcBinder = TcBinder Text Type

type LQntExpr p = Located (QntExpr p)
type LQntAlt p = Located (QntAlt p)
type LScheme = Located Scheme

-- Expressions {{{

data QntExpr p
  = QntVar (Id p)
  | QntNatLit Natural
  | QntApp (LQntExpr p) (LQntExpr p)
  | QntLam (Binder p) (LQntExpr p)
  | QntLet [QntBind p] (LQntExpr p)
  | QntCase (LQntExpr p) [LQntAlt p]

data QntBind p
  = QntImpl (Binder p) (LQntExpr p)
  | QntExpl (Binder p) (LQntExpr p) LScheme

data QntPat
  = QntNamePat Text
  | QntNatLitPat Natural
  | QntConstrPat Text [QntPat]

data QntAlt p = QntAlt QntPat (LQntExpr p)

bindingName :: forall p. (IsPass p) => QntBind p -> Text
bindingName = \case
  QntImpl n _   -> psBinderName pr n
  QntExpl n _ _ -> psBinderName pr n
  where pr :: Proxy p
        pr = Proxy

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
  = QntProg [DataDecl p] [QntBind p]

-- IsPass {{{

-- There are some utility functions that we want to work for all passes
-- of the AST. Because the type families involved aren't injective, this
-- is a bit fiddly; we define this typeclass which uses Proxy to
-- restrict which instances are used. All functions in this class should
-- be prefixed 'ps' for 'pass'.
class IsPass p where
  psPrintId    :: Proxy p -> Id p     -> Text
  psBinderName :: Proxy p -> Binder p -> Text
  psBinderType :: Proxy p -> Binder p -> Maybe Type

instance IsPass 'Parsed where
  psPrintId    _ x = x
  psBinderName _ x = x
  psBinderType _ _ = Nothing

instance IsPass 'Renamed where
  psPrintId _ = \case
    QualName (Qual (Module ms) x) -> T.intercalate "." ms <> "." <> x
    LoclName x -> x
    GenName x -> "%" <> x

  psBinderName _ x = x
  psBinderType _ _ = Nothing

instance IsPass 'Typechecked where
  psPrintId _ = psPrintId (Proxy :: Proxy 'Renamed)
  psBinderName _ (TcBinder x _) = x
  psBinderType _ (TcBinder _ t) = Just t

-- }}}

data SrcSpan = SrcSpan SourcePos SourcePos
  deriving (Show, Eq)

instance Semigroup SrcSpan where
  SrcSpan s0 e0 <> SrcSpan s1 e1 = SrcSpan (min s0 s1) (max e0 e1)

data Located a = L (Maybe SrcSpan) a
  deriving (Functor, Foldable, Traversable)

unLoc :: Located a -> a
unLoc (L _ x) = x

instance Applicative Located where
  pure = L mempty
  L s0 f <*> L s1 x = L (s0 <> s1) (f x)
