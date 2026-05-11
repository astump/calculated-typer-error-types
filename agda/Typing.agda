module Typing where

open import lib hiding (_>>=_ ; return)
open import Sign
open import Syntax
open import Monad

data Data : Set where
  INT : Data
  BOOL : Data

_=c_ : Data → Data → 𝔹
INT =c INT = tt
BOOL =c BOOL = tt
_ =c _ = ff

=c≡ : ∀{d d' : Data} → d =c d' ≡ tt → d ≡ d'
=c≡ {INT} {INT} e = refl
=c≡ {BOOL} {BOOL} e = refl

data RType : Set where
  DATA : (c : Data) → RType
  UNFINISHED : RType
  FAIL : RType

data EType (X : Set) : Set where
  DATA : (b : 𝔹)(c : X) → EType X -- if the 𝔹 is tt, it means the expression could diverge; otherwise not
  FAIL : 𝔹 → EType X
  UNKNOWN : EType X
  LOOP : EType X

infix 8 _⊓_

_⊓_ : EType Data → EType Data → EType Data
DATA b c ⊓ DATA b₁ c₁ = if c =c c₁ then DATA (b || b₁) c else UNKNOWN
DATA b c ⊓ FAIL x = UNKNOWN
DATA b c ⊓ UNKNOWN = UNKNOWN
DATA b c ⊓ LOOP = DATA tt c
FAIL b ⊓ DATA b₁ c = UNKNOWN
FAIL b ⊓ FAIL b' = FAIL (b || b')
FAIL b ⊓ UNKNOWN = UNKNOWN
FAIL b ⊓ LOOP = FAIL tt 
UNKNOWN ⊓ e2 = UNKNOWN
LOOP ⊓ DATA b c = DATA tt c
LOOP ⊓ FAIL b = FAIL tt
LOOP ⊓ UNKNOWN = UNKNOWN
LOOP ⊓ LOOP = LOOP

infix 8 _⇓_ 

-- b ⇓ t  means t in a context which is possibly diverging iff b is tt 
_⇓_ : ∀{A : Set} → 𝔹 → EType A → EType A
b ⇓ DATA b' t = DATA (b || b') t
b ⇓ t = t

infix 8 _>>=e_

_>>=e_ : ∀{A B : Set} → EType A → (A → EType B) → EType B
DATA b t >>=e f = b ⇓ f t
FAIL b >>=e f = FAIL b
UNKNOWN >>=e f = UNKNOWN
LOOP >>=e f = LOOP

returne : ∀{A : Set} → A → EType A
returne x = DATA ff x

instance
  ETypeMonad : Monad EType
  ETypeMonad = record { return = returne ; _>>=_ = _>>=e_ }
 
tval : Val → Data
tval (I _) = INT
tval (B _) = BOOL

tresult : Result Val → RType
tresult (Value v) = DATA (tval v)
tresult Fail = FAIL 
tresult Unfinished = UNFINISHED

add' : Data → Data → EType Data
add' INT INT = DATA ff INT
add' _ _ = FAIL ff

isZero' : Data → EType Data
isZero' INT = DATA ff BOOL
isZero' _ = FAIL ff

cond' : Data → EType Data → EType Data → EType Data
cond' BOOL t1 t2 = t1 ⊓ t2 
cond' _ _ _ = FAIL ff

search' : Data → Sign 𝔹 → EType Data
search' INT (Known tt) = LOOP
search' INT _ = DATA tt INT
search' _ _ = FAIL tt

texp : Expr → EType Data
texp Var = DATA ff INT
texp (Value v) = DATA ff (tval v)
texp (Add e1 e2) = 
 do
   t1 ← texp e1
   t2 ← texp e2
   add' t1 t2
texp (IsZero e) =
 do
   t ← texp e
   isZero' t
texp (Cond e1 e2 e3) =
 do
   t1 ← texp e1
   cond' t1 (texp e2) (texp e3)
texp (Search e) =
 do
   t ← texp e
   search' t (sexp e)

