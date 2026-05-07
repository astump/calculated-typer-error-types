module Syntax where

open import lib

data Value : Set where
 I : ℤ → Value
 B : 𝔹 → Value
 Fail : Value
 Loop : Value

data Op : Set where
 Add : Op
 Mult : Op

data Expr : Set where
 Var : Expr
 Val : Value → Expr
 Arith : Op → Expr → Expr → Expr
 If : Expr → Expr → Expr → Expr
 Search : Expr → Expr
