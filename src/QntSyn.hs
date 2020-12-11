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

-- An identifer for the given pass; used in QntVar. The renamer resolvesd
-- var references into an RName. However, note that we never actually
-- use GenName until conversion to Nucleus.
type family Id p where
  Id 'Parsed = Text
  Id 'Renamed = RName
  Id 'Typechecked = RName

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

data TcBinder = TcBinder Text (Type RName)

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
  | QntExpl (Binder p) (LQntExpr p) (LScheme (Id p))

data QntPat p
  = QntNamePat (Binder p)
  | QntNatLitPat Natural
  | QntConstrPat (Constr p) [QntPat p]

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

data DataConstr p = DataConstr Text [Type (Id p)]

-- }}}

-- Types {{{

data Type id
  = TName id
  | TVar TyVar
  | TApp (Type id) (Type id)
  deriving (Eq)

data TyVar = TvName Text
           | TvUnif Integer
           deriving (Ord, Eq)

tArrow :: Type RName -> Type RName -> Type RName
tArrow t0 t1 = (TApp (TName (QualName (Qual (Module []) "->"))) t0) `TApp` t1

data Scheme id = Scheme (Set Text) (Type id)

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
  psBinderType :: Proxy p -> Binder p -> Maybe (Type (Id p))
  psConstrName :: Proxy p -> Constr p -> Text

  psDetectFunTy :: Proxy p -> Type (Id p) -> Maybe (Type (Id p), Type (Id p))

instance IsPass 'Parsed where
  psPrintId    _ x = x
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

  psBinderName _ x = x
  psBinderType _ _ = Nothing

  psConstrName _ (Qual (Module ms) x) = T.intercalate "." ms <> "." <> x

  psDetectFunTy _ = \case
    TApp (TApp (TName (QualName (Qual (Module []) "->"))) t0) t1 -> Just (t0,t1)
    _ -> Nothing

instance IsPass 'Typechecked where
  psPrintId _ = psPrintId (Proxy :: Proxy 'Renamed)
  psBinderName _ (TcBinder x _) = x
  psBinderType _ (TcBinder _ t) = Just t
  psConstrName _ = psConstrName (Proxy :: Proxy 'Renamed)

  psDetectFunTy _ = \case
    TApp (TApp (TName (QualName (Qual (Module []) "->"))) t0) t1 -> Just (t0,t1)
    _ -> Nothing

-- }}}

data SrcSpan = SrcSpan SourcePos SourcePos
  deriving (Show, Eq)

instance Semigroup SrcSpan where
  SrcSpan s0 e0 <> SrcSpan s1 e1 = SrcSpan (min s0 s1) (max e0 e1)

data Located a = L SrcSpan a
  deriving (Functor, Foldable, Traversable)

unLoc :: Located a -> a
unLoc (L _ x) = x
