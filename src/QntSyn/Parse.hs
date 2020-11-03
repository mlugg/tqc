{-# LANGUAGE OverloadedStrings #-}
-- TODO: trustworthy?

module QntSyn.Parse where

import QntSyn

import Data.Void
import Control.Monad

import Data.Text (Text)
import qualified Data.Text as T

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Control.Monad.Combinators.Expr

import qualified Data.Set as S

type Parser = Parsec Void Text

-- Utility parsers {{{

sc = L.space space1 (L.skipLineComment "--") (L.skipBlockCommentNested "{-" "-}")
lexeme = L.lexeme sc
symbol = L.symbol sc

decimal = lexeme L.decimal

parens = between (symbol "(") (symbol ")")
braces = between (symbol "{") (symbol "}")

reservedWords = [ "let", "in", "case", "of", "data", "STAR", "forall" ]
reservedOps = [ "\\", "->", "::", "=", "|", "." ]

identChar = oneOf $ ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ ['_','\'']
opChar = oneOf (".,:!<>[]+-=|\\/" :: [Char])

identifier identStart = try $ do
  x <- identStart
  xs <- many identChar
  sc
  let name = T.pack $ x:xs
  guard (not $ name `elem` reservedWords)
  pure name

operator = try $ do
  xs <- some opChar
  sc
  let name = T.pack xs
  guard (not $ name `elem` reservedOps)
  pure name

identLower = identifier $ oneOf $ '_' : ['a'..'z']
identUpperOp = identifier (oneOf ['A'..'Z']) <|> parens operator
identAnyOp = identifier (oneOf $ '_' : ['a'..'z'] ++ ['A'..'Z']) <|> parens operator

reserved x = lexeme $ string x <* notFollowedBy identChar
reservedOp x = lexeme $ string x <* notFollowedBy opChar

semi = symbol ";"

semiTerm x = x <* semi

-- }}}

-- Top-level parsers {{{

-- Data declarations have the form `data Type a b = Foo a (List b)`
dataDecl :: Parser DataDecl
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
dataConstr :: Parser DataConstr
dataConstr = DataConstr <$> identUpperOp <*> many type_

-- }}}

-- If a binding has a type signature, it must immediately precede the
-- binding
binding :: Parser Binding
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

typeSig :: Parser (Text, TypeScheme)
typeSig = label "type signature" $ (,)
  <$> try (identLower <* reservedOp "::")
  <*> typeScheme

definition :: Parser (Text, Expr)
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

typeScheme :: Parser TypeScheme
typeScheme = polyType <|> (TypeScheme S.empty <$> type_)
  where
    polyType = TypeScheme
      <$> (reserved "forall" *> (S.fromList <$> some identLower))
      <*> (reservedOp "." *> type_)

-- }}}

-- Expressions {{{

expr :: Parser Expr
expr = makeExprParser exprTerm
  [ [ InfixL $ pure EAppl ]
  ]

exprTerm :: Parser Expr
exprTerm
    = try (parens expr)
  <|> EName <$> identAnyOp
  <|> ENatLit <$> decimal
  <|> ELambda <$> (reservedOp "\\" *> identLower) <*> (reservedOp "->" *> expr)
  <|> let_
  <|> case_

let_ :: Parser Expr
let_ = ELet <$> (reserved "let" *> braces (binding `sepEndBy` semi)) <*> (reserved "in" *> expr)

case_ :: Parser Expr
case_ = ECase <$> (reserved "case" *> expr) <*> (reserved "of" *> braces (branch `sepEndBy` semi))
  where branch = (,) <$> pattern <*> (reserved "->" *> expr)

-- }}}

-- Patterns {{{

pattern :: Parser Pattern
pattern = PName <$> identLower
  <|> PNatLit <$> decimal
  <|> PConstr <$> identUpperOp <*> many identLower

-- }}}
