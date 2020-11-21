{-# LANGUAGE Safe #-}

module NclSyn where

import Data.Text (Text)
import Numeric.Natural
import Tqc

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
  = EName RName
  | ENatLit Natural
  | EAppl Expr Expr
  | ELambda Text [Text] Expr  -- ELambda arg frees body
  | ELet [Binding] Expr
  | ECase Expr Text [Alt] Expr -- ECase scrutinee name alts def

data Binding = Binding Text Expr

data Pattern
  = PConstr Qual [Text]
  | PNatLit Natural

data Alt = Alt Pattern Expr

-- Like Expr, DataDecl is untyped
data DataDecl = DataDecl Text [DataConstr]

data DataConstr = DataConstr Text Natural  -- DataConstr name nargs

data NclProg = NclProg [DataDecl] [Binding]
