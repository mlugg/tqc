{-# LANGUAGE OverloadedStrings, DataKinds, Safe #-}

module QntSyn.Parse where

import QntSyn
import Tqc
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

type Parser = Parsec Void Text

locate :: Parser a -> Parser (Located a)
locate m = do
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
semiTerm x = x <* semi

-- }}}

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
dataConstr = DataConstr <$> identUpperOp <*> many type_

-- }}}

-- If a binding has a type signature, it must immediately precede the
-- binding
binding :: Parser (Binding 'Parsed)
binding = do
  sig <- optional $ semiTerm typeSig
  (x, e) <- definition

  case sig of
    Just (y, t) ->
      if x == y
      then pure $ BindingExpl x e t
      else fail "Type signature is not followed by an accompanying binding"

    Nothing -> pure $ BindingImpl x e

-- binding helpers {{{

typeSig :: Parser (Text, LScheme)
typeSig = label "type signature" $ (,)
  <$> try (identLower <* reservedOp "::")
  <*> typeScheme

definition :: Parser (Text, LExpr 'Parsed)
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

type_ :: Parser Type
type_ = makeExprParser typeTerm
  [ [ InfixL $ pure TApp ]
  , [ InfixR $ (\x y -> TApp (TApp (TName "->") x) y) <$ reservedOp "->" ]
  ]

typeTerm :: Parser Type
typeTerm = parens type_
  <|> TName <$> identUpperOp
  <|> TVar  <$> identLower

typeScheme :: Parser LScheme
typeScheme = locate $ polyType <|> (Scheme S.empty <$> type_)
  where
    polyType = Scheme
      <$> (reserved "forall" *> (S.fromList <$> some identLower))
      <*> (reservedOp "." *> type_)

-- }}}

-- Expressions {{{

expr :: Parser (LExpr 'Parsed)
expr = makeExprParser exprTerm
  [ [ InfixL $ pure $ \ f@(L fSpan _) x@(L xSpan _) -> L (fSpan <> xSpan) (EAppl f x) ]
  ]

exprTerm :: Parser (LExpr 'Parsed)
exprTerm = try (parens expr)
  <|> locate (EName <$> identAnyOp)
  <|> locate (ENatLit <$> decimal)
  <|> locate (ELambda <$> (reservedOp "\\" *> identLower) <*> (reservedOp "->" *> expr))
  <|> let_
  <|> case_

let_ :: Parser (LExpr 'Parsed)
let_ = locate $ ELet <$> (reserved "let" *> braces (binding `sepEndBy` semi)) <*> (reserved "in" *> expr)

case_ :: Parser (LExpr 'Parsed)
case_ = locate $ ECase <$> (reserved "case" *> expr) <*> (reserved "of" *> braces (branch `sepEndBy` semi))
  where branch = locate $ Alt <$> pattern <*> (reserved "->" *> expr)

-- }}}

-- Patterns {{{

pattern :: Parser Pattern
pattern = parens pattern
  <|> PName <$> identLower
  <|> PNatLit <$> decimal
  <|> PConstr <$> identUpperOp <*> many pattern

-- }}}
