module Syntax where

open import lib hiding (_>>=_ ; return)
open import Monad

data Val : Set where
 I : ℤ → Val
 B : 𝔹 → Val

data Expr : Set where
 Var : Expr
 Value : Val → Expr
 Add : Expr → Expr → Expr
 IsZero : Expr → Expr
 Cond : Expr → Expr → Expr → Expr
 Search : Expr → Expr

data Result (V : Set) : Set where
 Value : V → Result V
 Fail : Result V
 Unfinished : Result V

infixr 8 _>>=r_

_>>=r_ : ∀{A B : Set} → Result A → (A → Result B) → Result B
Value x >>=r r = r x 
Fail >>=r r' = Fail
Unfinished >>=r r' = Unfinished

returnr : ∀{A : Set} → A → Result A
returnr = Value

instance
  ResultMonad : Monad Result 
  ResultMonad = record { return = returnr ; _>>=_ = _>>=r_ }
 
