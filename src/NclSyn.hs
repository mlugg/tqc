{-# LANGUAGE Safe #-}

module NclSyn where

import Data.Text (Text)
import Numeric.Natural

{-
 - There are three main differences between QntSyn and NclSyn.
 -
 - 1) NclSyn is not typed. Type checking occurs on the QntSyn source
 -    language, and only incredibly primitive type information (i.e.
 -    whether something is a function or not) is required during code
 -    generation. As code that reaches this stage of compilation is
 -    definitely well-typed, we can remove the type information,
 -    simplifying the IR.
 -
 - 2) Pattern matches in NclSyn are more primitive than in QntSyn.
 -    NclSyn case expressions can only match a single constructor,
 -    putting all its arguments into named variables. Each expression
 -    also has a default case; during IR creation, if this is not
 -    present, one that throws an error is generated.
 -
 - 3) Lambda abstractions have extra information associated with them: a
 -    list of free variables referenced within the lambda. This
 -    information must be found before code generation.
 -}

data Expr
  = EName Text
  | ENatLit Natural
  | EAppl Expr Expr
  | ELambda Text [Text] Expr  -- ELambda arg frees body
  | ELet [(Text, Expr)] Expr
  | ECase Expr [(Pattern, Expr)] (Text, Expr)  -- ECase scrutinee cases default
  deriving (Show)

data Pattern
  = PConstr Text [Text]
  | PNatLit Natural
  deriving (Show)

-- Like Expr, DataDecl is untyped
data DataDecl = DataDecl Text [DataConstr] -- DataDecl name constrs
  deriving (Show)
data DataConstr = DataConstr Text Natural  -- DataConstr name nargs
  deriving (Show)

data NclProg = NclProg [DataDecl] [(Text, Expr)]
  deriving (Show)
