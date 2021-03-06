{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module QntSyn where

import Common
import Data.Text (Text)
import qualified Data.Text as T
import Numeric.Natural
import Data.Set (Set)
import Data.Proxy
import Text.Megaparsec.Pos (SourcePos)

-- An identifer for the given pass; used in QntVar. The renamer resolvesd
-- var references into an RName. However, note that we never actually
-- use GenName until conversion to Nucleus.
type family Id p where
  Id 'Parsed = Text
  Id 'Renamed = RName
  Id 'Typechecked = RName

-- Similar to Id, but for type names.
type family TyId p where
  TyId 'Parsed = Text
  TyId 'Renamed = Qual
  TyId 'Typechecked = Qual

-- A constructor reference for the given pass; used in QntConstrPat. The
-- renamer resolves the constructors and qualifies them with the module
-- they originate from.
type family Constr p where
  Constr 'Parsed = Text
  Constr 'Renamed = Qual
  Constr 'Typechecked = Qual

-- The type of binders. The typechecker annotates these with the type
-- being bound, primarily for debugging purposes.
type family Binder p where
  Binder 'Parsed = Text
  Binder 'Renamed = Text
  Binder 'Typechecked = TcBinder

data TcBinder = TcBinder Text (Type Qual)

-- Aliases for located forms of various syntactic constructs
type LQntExpr p = Located (QntExpr p)
type LQntAlt p = Located (QntAlt p)
type LScheme id = Located (Scheme id)

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
  | QntExpl (Binder p) (LQntExpr p) (LScheme (TyId p))

data QntPat p
  = QntNamePat (NamePat p)
  | QntNatLitPat NatLitPat
  | QntConstrPat (ConstrPat p)

newtype NamePat p = NamePat (Binder p)
newtype NatLitPat = NatLitPat Natural
  deriving (Eq, Ord)
data ConstrPat p = ConstrPat (Constr p) [QntPat p]

data QntAlt p = QntAlt (QntPat p) (LQntExpr p)

bindName :: forall p. (IsPass p) => QntBind p -> Text
bindName = \case
  QntImpl n _   -> psBinderName pr n
  QntExpl n _ _ -> psBinderName pr n
  where pr :: Proxy p
        pr = Proxy

bindExpr :: QntBind p -> LQntExpr p
bindExpr = \case
  QntImpl _ e   -> e
  QntExpl _ e _ -> e

-- }}}

-- Datatype declarations {{{

data DataDecl p = DataDecl Text [TyParam] [DataConstr p]

data TyParam = TyParam Text Kind

data DataConstr p = DataConstr Text [Type (TyId p)]

-- }}}

-- Types {{{

data Type id
  = TName id
  | TVar TyVar
  | TApp (Type id) (Type id)
  deriving (Eq, Show)

newtype TyVar = TyVar Integer
  deriving (Ord, Eq, Show)

infixr 5 `tArrow`

tArrow :: Type Qual -> Type Qual -> Type Qual
tArrow t0 t1 = (TApp (TName (Qual (Module []) "->")) t0) `TApp` t1

data Scheme id = Scheme (Set Text) (Type id)
  deriving (Show)

-- }}}

-- Kinds {{{

infixr 5 `KArrow`

data Kind
  = KStar
  | KArrow Kind Kind
  deriving (Eq, Show)

-- }}}

data QntProg
  = QntProg [DataDecl 'Parsed] [QntBind 'Parsed]

-- IsPass {{{

-- There are some utility functions that we want to work for all passes
-- of the AST. Because the type families involved aren't injective, this
-- is a bit fiddly; we define this typeclass which uses Proxy to
-- restrict which instances are used. All functions in this class should
-- be prefixed 'ps' for 'pass'.
class IsPass p where
  psPrintId    :: Proxy p -> Id p     -> Text
  psPrintTyId  :: Proxy p -> TyId p   -> Text
  psBinderName :: Proxy p -> Binder p -> Text
  psBinderType :: Proxy p -> Binder p -> Maybe (Type (TyId p))
  psConstrName :: Proxy p -> Constr p -> Text

  psDetectFunTy :: Proxy p -> Type (TyId p) -> Maybe (Type (TyId p), Type (TyId p))

instance IsPass 'Parsed where
  psPrintId    _ x = x
  psPrintTyId  _ x = x
  psBinderName _ x = x
  psBinderType _ _ = Nothing
  psConstrName _ x = x

  psDetectFunTy _ = \case
    TApp (TApp (TName "->") t0) t1 -> Just (t0,t1)
    _ -> Nothing
  

instance IsPass 'Renamed where
  psPrintId _ = \case
    QualName (Qual (Module ms) x) -> T.intercalate "." ms <> "." <> x
    LoclName (SrcName x) -> x
    LoclName (GenName x) -> "%" <> x

  psPrintTyId _ (Qual (Module ms) x) = T.intercalate "." ms <> "." <> x

  psBinderName _ x = x
  psBinderType _ _ = Nothing

  psConstrName _ (Qual (Module ms) x) = T.intercalate "." ms <> "." <> x

  psDetectFunTy _ = \case
    TApp (TApp (TName (Qual (Module []) "->")) t0) t1 -> Just (t0,t1)
    _ -> Nothing

instance IsPass 'Typechecked where
  psPrintId _ = psPrintId (Proxy :: Proxy 'Renamed)
  psPrintTyId _ = psPrintTyId (Proxy :: Proxy 'Renamed)
  psBinderName _ (TcBinder x _) = x
  psBinderType _ (TcBinder _ t) = Just t
  psConstrName _ = psConstrName (Proxy :: Proxy 'Renamed)

  psDetectFunTy _ = \case
    TApp (TApp (TName (Qual (Module []) "->")) t0) t1 -> Just (t0,t1)
    _ -> Nothing

-- }}}

data SrcSpan = SrcSpan SourcePos SourcePos
  deriving (Show, Eq)

instance Semigroup SrcSpan where
  SrcSpan s0 e0 <> SrcSpan s1 e1 = SrcSpan (min s0 s1) (max e0 e1)

data Located a = L SrcSpan a
  deriving (Functor, Foldable, Traversable, Show)

unLoc :: Located a -> a
unLoc (L _ x) = x
