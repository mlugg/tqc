{-# LANGUAGE Safe, LambdaCase, ScopedTypeVariables, OverloadedStrings, ViewPatterns #-}

module QntSyn.Pretty where

import Data.Char
import QntSyn
import Data.Text (Text)
import Data.Proxy
import qualified Data.Text as T
import qualified Data.Set as S

pPrintScheme :: (IsPass p) => Scheme p -> Text
pPrintScheme (Scheme univs t) =
  if null univs
  then pPrintType t
  else "∀" <> T.intercalate " " (S.elems univs) <> " . " <> pPrintType t

pPrintType :: forall p. (IsPass p) => Type p -> Text
pPrintType = \case
  (psDetectFunTy pr -> Just (t0, t1)) -> "(" <> pPrintType t0 <> " -> " <> pPrintType t1 <> ")"

  TName n ->
    let n' = psPrintId pr n
    in if isSymbolic n'
       then "(" <> n' <> ")"
       else n'

  TVar (TvName x) -> x

  TVar (TvUnif x) -> "α" <> T.pack (show x)

  TApp x y -> "(" <> pPrintType x <> " " <> pPrintType y <> ")"

  where isSymbolic = not . isAlpha . T.head
        pr :: Proxy p
        pr = Proxy

pPrintPat :: forall p. (IsPass p) => QntPat p -> Text
pPrintPat = \case
  QntNamePat x -> pPrintBinder pr x
  QntNatLitPat x -> T.pack $ show x
  QntConstrPat c ps -> "(" <> psConstrName pr c <> " " <> T.intercalate " " (pPrintPat <$> ps) <> ")"
  where pr :: Proxy p
        pr = Proxy

pPrintExpr :: forall p. (IsPass p) => QntExpr p -> Text
pPrintExpr = \case
  QntVar x ->
    let n = psPrintId pr x
    in if isSymbolic n
       then "(" <> n <> ")"
       else n

  QntNatLit x -> T.pack $ show x

  QntApp (L _ e0) (L _ e1) -> mconcat
    [ "("
    , pPrintExpr e0
    , " "
    , pPrintExpr e1
    , ")"
    ]

  QntLam x (L _ e) -> mconcat
    [ "(λ "
    , pPrintBinder pr x
    , " -> "
    , pPrintExpr e
    , ")"
    ]

  QntLet bs (L _ e) -> mconcat
    [ "let { "
    , inter pPrintBind bs
    , " } in "
    , pPrintExpr e
    ]

  QntCase (L _ e) as -> mconcat
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

pPrintAlt :: (IsPass p) => QntAlt p -> Text
pPrintAlt (QntAlt pat (L _ e)) = mconcat
  [ pPrintPat pat
  , " -> "
  , pPrintExpr e
  ]

pPrintBind :: forall p. (IsPass p) => QntBind p -> Text
pPrintBind = \case
  QntImpl x (L _ e) -> mconcat
    [ pPrintBinder pr x
    , " = "
    , pPrintExpr e
    ]

  QntExpl x (L _ e) (L _ t) -> mconcat
    [ pPrintBinder pr x
    , " :: "
    , pPrintScheme t
    , "; "
    , pPrintBinder pr x
    , " = "
    , pPrintExpr e
    ]
  where pr :: Proxy p
        pr = Proxy

pPrintBinder :: (IsPass p) => Proxy p -> Binder p -> Text
pPrintBinder pr b = case psBinderType pr b of
  Nothing -> psBinderName pr b
  Just t  -> mconcat
    [ "("
    , psBinderName pr b
    , " :: "
    , pPrintType t
    , ")"
    ]
