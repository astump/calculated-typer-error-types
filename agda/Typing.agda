module Typing where

open import lib
open import Sign
open import Syntax

data Type : Set where
  INT : 𝔹 → Type     -- tt means might diverge
  BOOL : 𝔹 → Type
  FAIL : Type
  UNKNOWN : Type
  LOOP : Type

tval : Value → Type
tval (I _) = INT ff
tval (B _) = BOOL ff
tval Fail = FAIL
tval Loop = LOOP

infix 7 _⊓_ 

_⊓_ : Type → Type → Type
(INT b1) ⊓ (INT b2) = INT (b1 || b2)
(BOOL b1) ⊓ (BOOL b2) = BOOL (b1 || b2)
FAIL ⊓ FAIL = FAIL
LOOP ⊓ LOOP = LOOP
LOOP ⊓ (INT _) = INT tt
(INT _) ⊓ LOOP = INT tt
LOOP ⊓ (BOOL _) = BOOL tt
(BOOL _) ⊓ LOOP = BOOL tt
_ ⊓ _ = UNKNOWN

-- b ↑ T  means T in a context which is possibly diverging iff b is tt 
_↑_ : 𝔹 → Type → Type
b ↑ (INT b') = INT (b || b')
b ↑ (BOOL b') = BOOL (b || b')
tt ↑ FAIL = UNKNOWN
ff ↑ FAIL = FAIL
b ↑ UNKNOWN = UNKNOWN
_ ↑ LOOP = LOOP


arith' : Type → Type → Type
arith' t1 t2 with t1 ⊓ t2
arith' t1 t2 | BOOL tt = UNKNOWN
arith' t1 t2 | BOOL ff = FAIL
arith' t1 t2 | v = v

-- maybe need to use a ⊓ operator to handle cases like
-- 
--    cond' (BOOL tt) (INT tt) (INT tt) ≪ cond' (BOOL tt) (INT tt) LOOP

cond' : Type → Type → Type → Type
cond' (BOOL b1) t1 t2 = b1 ↑ (t1 ⊓ t2)
cond' FAIL _ _ = FAIL
cond' LOOP _ _ = LOOP
cond' (INT tt) _ _ = UNKNOWN
cond' (INT ff) _ _ = FAIL
cond' UNKNOWN _ _ = UNKNOWN

search' : Type → Sign → Type
search' (INT _) Pos = LOOP
search' (INT _) _ = INT tt
search' (BOOL ff) _ = FAIL
search' (BOOL tt) _ = UNKNOWN -- we should really generalize so we can have FAIL tt here
search' UNKNOWN _ = UNKNOWN
search' LOOP _ = LOOP
search' FAIL _ = FAIL


texp : Expr → Type
texp (Val v) = tval v
texp (Arith _ e1 e2) = arith' (texp e1) (texp e2) 
texp (If e1 e2 e3) = cond' (texp e1) (texp e2) (texp e3)
texp Var = INT ff
texp (Search e) = search' (texp e) (sign e)

infix 6 _≪_ 

data _≪_ : Type → Type → Set where
  ≪Unknown : ∀ {T : Type} → UNKNOWN ≪ T
  ≪Refl : ∀{T : Type} → T ≪ T
  ≪Int : INT tt ≪ INT ff
  ≪Bool : BOOL tt ≪ BOOL ff
  ≪IntLoop : INT tt ≪ LOOP
  ≪BoolLoop : BOOL tt ≪ LOOP

≪-trans : ∀{t1 t2 t3 : Type} →
            t1 ≪ t2 →
            t2 ≪ t3 →
            t1 ≪ t3
≪-trans ≪Unknown ≪Unknown = ≪Unknown
≪-trans ≪Unknown ≪Refl = ≪Unknown
≪-trans ≪Refl ≪Unknown = ≪Unknown
≪-trans ≪Refl ≪Refl = ≪Refl
≪-trans ≪Unknown d' = ≪Unknown
≪-trans ≪Refl d' = d'
≪-trans ≪Int ≪Refl = ≪Int 
≪-trans ≪Bool ≪Refl = ≪Bool
≪-trans ≪IntLoop ≪Refl = ≪IntLoop
≪-trans ≪BoolLoop ≪Refl = ≪BoolLoop

{-search'-INT-ff : ∀{s : Sign} → search' (INT ff) s ≪ INT ff
search'-INT-ff {Pos} = {!!}
search'-INT-ff {Nonneg} = ≪Int
search'-INT-ff {Unknown} = ≪Int-}