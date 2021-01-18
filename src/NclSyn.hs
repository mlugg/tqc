{-# LANGUAGE Safe #-}

module NclSyn where

import Data.Text (Text)
import Numeric.Natural
import Common

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
 - 2a) Case expression scrutinees can only be variables (i.e. 'RName's)
 -     for simplicity
 -
 - 3) Lambda abstractions have extra information associated with them: a
 -    list of free variables referenced within the lambda. This
 -    information must be found before code generation.
 -}

data NclBinder
  = NclBinder LName
  deriving (Ord, Eq)

data NclExpr
  = NclVar RName
  | NclNatLit Natural
  | NclApp NclExpr NclExpr
  | NclLam NclBinder [NclBinder] NclExpr  -- ELambda arg frees body
  | NclLet [NclBind] NclExpr
  | NclCase RName [NclAlt] NclExpr -- ECase scrutinee alts def

data NclBind = NclBind NclBinder [NclBinder] NclExpr

nclBinder :: NclBind -> NclBinder
nclBinder (NclBind b _ _) = b

data NclPat
  = NclConstrPat Qual [NclBinder]
  | NclNatLitPat Natural

data NclAlt = NclAlt NclPat NclExpr

-- Like NclExpr, DataDecl is untyped
data DataDecl = DataDecl Text [DataConstr]

data DataConstr = DataConstr Text Natural  -- DataConstr name nargs

data NclProg = NclProg [DataDecl] [NclBind]
