{-# LANGUAGE Safe, LambdaCase, ScopedTypeVariables, OverloadedStrings #-}

module QntSyn.Pretty where

import Data.Char
import QntSyn
import Data.Text (Text)
import Data.Proxy
import qualified Data.Text as T
import qualified Data.Set as S

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
    let n = psPrintId pr x
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
    , pPrintBind pr x
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
    [ pPrintBind pr x
    , " = "
    , pPrintExpr e
    ]

  BindingExpl x (L _ e) (L _ t) -> mconcat
    [ pPrintBind pr x
    , " :: "
    , pPrintScheme t
    , "; "
    , pPrintBind pr x
    , " = "
    , pPrintExpr e
    ]
  where pr :: Proxy p
        pr = Proxy

pPrintBind :: (IsPass p) => Proxy p -> Bind p -> Text
pPrintBind pr b = case psBindType pr b of
  Nothing -> psBindName pr b
  Just t  -> mconcat
    [ "("
    , psBindName pr b
    , " :: "
    , pPrintType t
    , ")"
    ]
