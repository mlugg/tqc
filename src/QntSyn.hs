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

type family Id p where
  Id 'Parsed = Text
  Id 'Renamed = RName
  Id 'Typechecked = RName

type family Bind p where
  Bind 'Parsed = Text
  Bind 'Renamed = Text
  Bind 'Typechecked = TcBind

data TcBind = TcBind Text Type

data Located a = L SrcSpan a
  deriving (Functor, Foldable, Traversable)

unLoc :: Located a -> a
unLoc (L _ x) = x

type LExpr p = Located (Expr p)
type LAlt p = Located (Alt p)
type LScheme = Located Scheme

-- Expressions {{{

data Expr p
  = EName (Id p)
  | ENatLit Natural
  | EAppl (LExpr p) (LExpr p)
  | ELambda (Bind p) (LExpr p)
  | ELet [Binding p] (LExpr p)
  | ECase (LExpr p) [LAlt p]

data Binding p
  = BindingImpl (Bind p) (LExpr p)
  | BindingExpl (Bind p) (LExpr p) LScheme

data Pattern
  = PName Text
  | PNatLit Natural
  | PConstr Text [Pattern]

data Alt p = Alt Pattern (LExpr p)

bindingName :: forall p. (IsPass p) => Binding p -> Text
bindingName = \case
  BindingImpl n _   -> psBindName pr n
  BindingExpl n _ _ -> psBindName pr n
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
  = QntProg [DataDecl p] [Binding p]

-- IsPass {{{

-- There are some utility functions that we want to work for all passes
-- of the AST. Because the type families involved aren't injective, this
-- is a bit fiddly; we define this typeclass which uses Proxy to
-- restrict which instances are used. All functions in this class should
-- be prefixed 'ps' for 'pass'.
class IsPass p where
  psPrintId  :: Proxy p -> Id p   -> Text
  psBindName :: Proxy p -> Bind p -> Text
  psBindType :: Proxy p -> Bind p -> Maybe Type

instance IsPass 'Parsed where
  psPrintId  _ x = x
  psBindName _ x = x
  psBindType _ _ = Nothing

instance IsPass 'Renamed where
  psPrintId _ = \case
    QualName (Qual (Module ms) x) -> T.intercalate "." ms <> "." <> x
    LoclName x -> x
    GenName x -> "%" <> x

  psBindName _ x = x
  psBindType _ _ = Nothing

instance IsPass 'Typechecked where
  psPrintId  _ = psPrintId (Proxy :: Proxy 'Renamed)
  psBindName _ (TcBind x _) = x
  psBindType _ (TcBind _ t) = Just t

-- }}}
