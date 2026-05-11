module Sign where

open import lib hiding (_>>=_ ; return)
open import Syntax
open import Monad

data Sign (A : Set) : Set where
  Known : A → Sign A
  Unknown : Sign A

returns : ∀{A : Set} → A → Sign A
returns = Known

infixr 8 _>>=s_

_>>=s_ : ∀{A B : Set} → Sign A → (A → Sign B) → Sign B
Known x >>=s f = f x
Unknown >>=s f = Unknown

instance
  SignMonad : Monad Sign 
  SignMonad = record { return = returns ; _>>=_ = _>>=s_ }
 


Pos : Sign 𝔹
Pos = Known tt

Nonneg : Sign 𝔹
Nonneg = Known ff

sval : Val → Sign 𝔹
sval (I (mkℤ zero triv)) = Nonneg
sval (I (mkℤ (suc n) tt)) = Pos
sval (I (mkℤ (suc n) ff)) = Unknown
sval (B x) = Unknown

sresult : Result Val → Sign 𝔹
sresult (Value v) = sval v
sresult Fail = Unknown
sresult Loop = Unknown

sexp : Expr → Sign 𝔹
sexp Var = Nonneg
sexp (Value x) = sval x
sexp (Add e e') =
  do
    s ← sexp e
    s' ← sexp e'
    return (s || s')
sexp _ = Unknown

infix 6 _≪sign_ 

data _≪sign_ : Sign 𝔹 → Sign 𝔹 → Set where
  ≪Unknown : ∀ {s} → Unknown ≪sign s
  ≪Refl : ∀{s} → s ≪sign s
  ≪Nonneg : Nonneg ≪sign Pos

