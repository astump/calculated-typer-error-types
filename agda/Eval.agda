module Eval where

open import lib
open import Syntax

arith : Op → Value → Value → Value
arith _ (B b) _ = Fail
arith _ Loop _ = Loop
arith _ Fail _ = Fail
arith _ _ Loop = Loop
arith Add (I x) (I y) = I (x +ℤ y)
arith Mult (I x) (I y) = I (x *ℤ y)
arith _ _ _ = Fail

cond : Value → Value → Value → Value
cond (B x) y z = if x then y else z
cond Loop _ _ = Loop
cond _ _ _ = Fail

search : ℕ → (ℕ → Value) → Value
search g vv with vv g
search g vv | I k with k =ℤ 0ℤ 
search g vv | I k | tt = I (toℤ g)
search (suc g) vv | I k | ff = vv g
search 0 vv | I k | ff = Loop
search g vv | B x = Fail
search g vv | Fail = Fail
search g vv | Loop = Loop

-- g bounds searches, v is the value of the variable
eval : ℕ → Expr → ℕ → Value
eval g Var v = I (toℤ v)
eval g (Val x) v = x
eval g (Arith op e1 e2) v = arith op (eval g e1 v) (eval g e2 v)
eval g (If e1 e2 e3) v = cond (eval g e1 v) (eval g e2 v) (eval g e3 v)
eval g (Search e) _ = search g (eval g e)

