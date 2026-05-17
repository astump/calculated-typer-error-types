module Eval where

open import lib hiding (_>>=_ ; return)
open import Monad
open import Syntax

add : Val → Val → Result Val
add (I x) (I y) = return (I (x +ℤ y))
add _ _ = Fail

cond : Val → Result Val → Result Val → Result Val
cond (B x) y z = if x then y else z
cond _ _ _ = Fail

mutual 
 search : ℕ → (ℕ → Result Val) → Result Val
 search g vv =
  do
   d ← vv g
   searchh g vv d 
 searchh : ℕ → (ℕ → Result Val) → Val → Result Val
 searchh g vv (B x) = Fail
 searchh g vv (I x) with x =ℤ 0ℤ
 searchh g vv (I x) | tt = return (I (toℤ g))
 searchh zero vv (I x) | ff = Unfinished
 searchh (suc g) vv (I x) | ff = search g vv

isZero : Val → Result Val
isZero (I x) = return (B (x =ℤ 0ℤ))
isZero _ = Fail

-- g bounds searches, v is the value of the variable
eval : ℕ → Expr → ℕ → Result Val
eval g Var v = return (I (toℤ v))
eval g (Value x) v = return x
eval g (Add e1 e2) v =
  do
    r1 ← eval g e1 v
    r2 ← eval g e2 v
    add r1 r2
eval g (IsZero e) v =
  do
    r ← eval g e v
    isZero r
eval g (Cond e1 e2 e3) v =
  do
    b ← eval g e1 v
    cond b (eval g e2 v) (eval g e3 v)
eval g (Search e) _ = search g (eval g e)

