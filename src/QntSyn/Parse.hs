{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}

module QntSyn.Parse where

import QntSyn
import Common
import Data.Void
import Control.Monad
import Numeric.Natural

import Data.Text (Text)
import qualified Data.Text as T

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Control.Monad.Combinators.Expr

import qualified Data.Set as S

import Data.Either

type Parser = Parsec Void Text

located :: Parser a -> Parser (Located a)
located m = do
  start <- getSourcePos
  x <- m
  end <- getSourcePos
  pure $ L (SrcSpan start end) x

-- Utility parsers {{{

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockCommentNested "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

decimal :: Parser Natural
decimal = lexeme L.decimal

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")
braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

reservedWords :: [Text]
reservedWords = [ "let", "in", "case", "of", "data", "STAR", "forall" ]
reservedOps :: [Text]
reservedOps = [ "\\", "->", "::", "=", "|", "." ]

identChar :: Parser Char
identChar = oneOf $ ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ ['_','\'']
opChar :: Parser Char
opChar = oneOf (".,:!<>[]+-=|\\/" :: [Char])

identifier :: Parser Char -> Parser Text
identifier identStart = try $ do
  x <- identStart
  xs <- many identChar
  sc
  let name = T.pack $ x:xs
  guard (not $ name `elem` reservedWords)
  pure name

operator :: Parser Text
operator = try $ do
  xs <- some opChar
  sc
  let name = T.pack xs
  guard (not $ name `elem` reservedOps)
  pure name

identLower :: Parser Text
identLower = identifier $ oneOf $ '_' : ['a'..'z']
identUpperOp :: Parser Text
identUpperOp = identifier (oneOf ['A'..'Z']) <|> parens operator
identAnyOp :: Parser Text
identAnyOp = identifier (oneOf $ '_' : ['a'..'z'] ++ ['A'..'Z']) <|> parens operator

reserved :: Text -> Parser Text
reserved x = lexeme $ string x <* notFollowedBy identChar
reservedOp :: Text -> Parser Text
reservedOp x = lexeme $ string x <* notFollowedBy opChar

semi :: Parser Text
semi = symbol ";"

semiTerm :: Parser a -> Parser a
semiTerm p = p <* semi

-- }}}

file :: Parser QntProg
file = sc *> (mkProg <$> tl `endBy` semi) <* eof
  where tl = Left  <$> dataDecl
         <|> Right <$> binding
        mkProg tls =
          let (dataDecls, bindings) = partitionEithers tls
          in QntProg dataDecls bindings

-- Top-level parsers {{{

-- Data declarations have the form `data Type a b = Foo a (List b)`
dataDecl :: Parser (DataDecl 'Parsed)
dataDecl = DataDecl
  <$> (reserved "data" *> identUpperOp)
  <*> many typeParam
  <*> (reservedOp "=" *> dataConstr `sepBy` reservedOp "|")

-- dataDecl helpers {{{

-- Type parameters have an optional kind annotation; if not given, the
-- kind is assumed to be STAR
typeParam :: Parser TyParam
typeParam = flip TyParam KStar <$> identLower
        <|> parens (TyParam <$> (identLower <* reservedOp "::") <*> kind)

-- A data constructor is just the constructor name followed by the types
-- of its parameters
dataConstr :: Parser (DataConstr 'Parsed)
dataConstr = DataConstr <$> identUpperOp <*> many typeTerm

-- }}}

-- If a binding has a type signature, it must immediately precede the
-- binding
binding :: Parser (QntBind 'Parsed)
binding = do
  sig <- optional $ semiTerm typeSig
  (x, e) <- definition

  case sig of
    Just (y, t) ->
      if x == y
      then pure $ QntExpl x e t
      else fail "Type signature is not followed by an accompanying binding"

    Nothing -> pure $ QntImpl x e

-- binding helpers {{{

typeSig :: Parser (Text, LScheme Text)
typeSig = label "type signature" $ (,)
  <$> try (identLower <* reservedOp "::")
  <*> typeScheme

definition :: Parser (Text, LQntExpr 'Parsed)
definition = label "definition" $ (,)
  <$> try (identLower <* reservedOp "=")
  <*> expr

-- }}}

-- }}}

-- Kinds {{{

kind :: Parser Kind
kind = try (KArrow <$> (kTerm <* reservedOp "->") <*> kind)
   <|> kTerm
   where kTerm = KStar <$ reserved "STAR" <|> parens kind

-- }}}

-- Types {{{

type_ :: Parser (Type Text)
type_ = makeExprParser typeTerm
  [ [ InfixL $ pure TApp ]
  , [ InfixR $ (\x y -> TApp (TApp (TName "->") x) y) <$ reservedOp "->" ]
  ]

typeTerm :: Parser (Type Text)
typeTerm = parens type_
  <|> TName <$> identAnyOp

typeScheme :: Parser (LScheme Text)
typeScheme = located $ polyType <|> (Scheme S.empty <$> type_)
  where
    polyType = Scheme
      <$> (reserved "forall" *> (S.fromList <$> some identLower))
      <*> (reservedOp "." *> type_)

-- }}}

-- Expressions {{{

expr :: Parser (LQntExpr 'Parsed)
expr = makeExprParser exprTerm
  [ [ InfixL $ pure $ \ f@(L fs _) x@(L xs _) -> L (fs <> xs) (QntApp f x) ]
  ]

exprTerm :: Parser (LQntExpr 'Parsed)
exprTerm = try (parens expr)
  <|> located (QntVar <$> identAnyOp)
  <|> located (QntNatLit <$> decimal)
  <|> located (QntLam <$> (reservedOp "\\" *> identLower) <*> (reservedOp "->" *> expr))
  <|> let_
  <|> case_

let_ :: Parser (LQntExpr 'Parsed)
let_ = located $ QntLet <$> (reserved "let" *> braces (binding `sepEndBy` semi)) <*> (reserved "in" *> expr)

case_ :: Parser (LQntExpr 'Parsed)
case_ = located $ QntCase <$> (reserved "case" *> expr) <*> (reserved "of" *> braces (branch `sepEndBy` semi))
  where branch = located $ QntAlt <$> pattern <*> (reserved "->" *> expr)

-- }}}

-- Patterns {{{

pattern :: Parser (QntPat 'Parsed)
pattern = parens pattern
  <|> QntNamePat . NamePat <$> identLower
  <|> QntNatLitPat . NatLitPat <$> decimal
  <|> QntConstrPat <$> (ConstrPat <$> identUpperOp <*> many pattern)

-- }}}
