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

-- Pretty-printing {{{

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

pPrintExpr :: forall p. (IsPass p) => Expr p -> Text
pPrintExpr = \case
  EName x ->
    let n = psPPrintId pr x
    in if isSymbolic n
       then "(" <> n <> ")"
       else n

  ENatLit x -> T.pack $ show x

  EAppl (L _ e0) (L _ e1) -> mconcat
    [ "("
    , pPrintExpr e0
    , " "
    , pPrintExpr e1
    , ")"
    ]

  ELambda x (L _ e) -> mconcat
    [ "(λ "
    , psPPrintBind pr x
    , " -> "
    , pPrintExpr e
    , ")"
    ]

  ELet bs (L _ e) -> mconcat
    [ "let { "
    , inter pPrintBinding bs
    , " } in "
    , pPrintExpr e
    ]

  ECase (L _ e) as -> mconcat
    [ "case "
    , pPrintExpr e
    , " of { "
    , inter (pPrintAlt . unLoc) as
    , " }"
    ]
  where pr :: Proxy p
        pr = Proxy
        isSymbolic = not . isAlpha . T.head
        inter f xs = T.intercalate "; " (f <$> xs)

pPrintAlt :: (IsPass p) => Alt p -> Text
pPrintAlt (Alt pat (L _ e)) = mconcat
  [ pPrintPat pat
  , " -> "
  , pPrintExpr e
  ]

pPrintBinding :: forall p. (IsPass p) => Binding p -> Text
pPrintBinding = \case
  BindingImpl x (L _ e) -> mconcat
    [ psPPrintBind pr x
    , " = "
    , pPrintExpr e
    ]

  BindingExpl x (L _ e) (L _ t) -> mconcat
    [ psPPrintBind pr x
    , " :: "
    , pPrintScheme t
    , "; "
    , psPPrintBind pr x
    , " = "
    , pPrintExpr e
    ]
  where pr :: Proxy p
        pr = Proxy

-- }}}

-- IsPass {{{

-- There are some utility functions that we want to work for all passes
-- of the AST. Because the type families involved aren't injective, this
-- is a bit fiddly; we define this typeclass which uses Proxy to
-- restrict which instances are used. All functions in this class should
-- be prefixed 'ps' for 'pass'.
class IsPass p where
  psPPrintId   :: Proxy p -> Id p   -> Text
  psPPrintBind :: Proxy p -> Bind p -> Text
  psBindName   :: Proxy p -> Bind p -> Text

instance IsPass 'Parsed where
  psPPrintId   _ x = x
  psPPrintBind _ x = x
  psBindName   _ x = x

instance IsPass 'Renamed where
  psPPrintId _ = \case
    QualName (Qual (Module ms) x) -> T.intercalate "." ms <> "." <> x
    LoclName x -> x
    GenName x -> "%" <> x

  psPPrintBind _ x = x

  psBindName _ x = x

instance IsPass 'Typechecked where
  psPPrintId _ = psPPrintId (Proxy :: Proxy 'Renamed)
  psPPrintBind _ (TcBind x ty) = mconcat
    [ "("
    , x
    , " :: "
    , pPrintType ty
    , ")"
    ]

  psBindName _ (TcBind x _) = x

-- }}}
