module SoundnessSign where

open import lib
open import Sign
open import Syntax
open import Eval

infix 6 _≪sign_ 

data _≪sign_ : Sign 𝔹 → Sign 𝔹 → Set where
  ≪Unknown : ∀ {s} → Unknown ≪sign s
  ≪Refl : ∀{s} → s ≪sign s
  ≪Nonneg : Nonneg ≪sign Pos

return≪sign : ∀{v : Val} → 
              (sval v) ≪sign sresult (returnr v)
return≪sign {I (mkℤ zero triv)} = ≪Refl
return≪sign {I (mkℤ (suc n) tt)} = ≪Refl
return≪sign {I (mkℤ (suc n) ff)} = ≪Refl
return≪sign {B x} = ≪Refl

infixr 8 _>>=≪sign_

_>>=≪sign_ : ∀{a : Sign 𝔹}{a' : Result Val} →
        {f : 𝔹 → Sign 𝔹}{f' : Val → Result Val} → 
         a ≪sign sresult a' →
         (∀{b : 𝔹}{v : Val}{q : a ≡ Known b}{q' : a' ≡ Value v} →
           Known b ≪sign sval v → 
           f b ≪sign sresult (f' v)) → 
        (a >>=s f) ≪sign sresult (a' >>=r f')
_>>=≪sign_ {Known b} {Value (I (mkℤ zero triv))} {f} {f'} ≪Refl d2 = d2{q = refl}{q' = refl} ≪Refl
_>>=≪sign_ {Known b} {Value (I (mkℤ (suc n) tt))} {f} {f'} ≪Refl d2 = d2{q = refl}{q' = refl} ≪Refl
_>>=≪sign_ {Known b} {Value (I (mkℤ (suc n) tt))} {f} {f'} ≪Nonneg d2 = d2{q = refl}{q' = refl} ≪Nonneg
_>>=≪sign_ {Unknown} {Value x} {f} {f'} d1 d2 = ≪Unknown
_>>=≪sign_ {Unknown} {Fail} {f} {f'} d1 d2 = ≪Unknown
_>>=≪sign_ {Unknown} {Unfinished} {f} {f'} d1 d2 = ≪Unknown

sign-add : ∀{b b' : 𝔹}{u u' : Val} →
           Known b ≪sign sval u →
           Known b' ≪sign sval u' →
           Known (b || b') ≪sign sresult (add u u')
sign-add {b} {b'} {I (mkℤ zero triv)} {I (mkℤ zero triv)} ≪Refl ≪Refl = ≪Refl
sign-add {b} {b'} {I (mkℤ zero triv)} {I (mkℤ (suc n₁) tt)} ≪Refl ≪Refl = ≪Refl
sign-add {b} {b'} {I (mkℤ zero triv)} {I (mkℤ (suc n₁) tt)} ≪Refl ≪Nonneg = ≪Nonneg
sign-add {b} {b'} {I (mkℤ (suc n) tt)} {I (mkℤ zero triv)} ≪Refl ≪Refl = ≪Refl
sign-add {b} {b'} {I (mkℤ (suc n) tt)} {I (mkℤ zero triv)} ≪Nonneg ≪Refl = ≪Nonneg
sign-add {b} {b'} {I (mkℤ (suc n) tt)} {I (mkℤ (suc n₁) tt)} ≪Refl ≪Refl = ≪Refl
sign-add {b} {b'} {I (mkℤ (suc n) tt)} {I (mkℤ (suc n₁) tt)} ≪Refl ≪Nonneg = ≪Refl
sign-add {b} {b'} {I (mkℤ (suc n) tt)} {I (mkℤ (suc n₁) tt)} ≪Nonneg ≪Refl = ≪Refl
sign-add {b} {b'} {I (mkℤ (suc n) tt)} {I (mkℤ (suc n₁) tt)} ≪Nonneg ≪Nonneg = ≪Nonneg

sexp-soundness : ∀{e : Expr}{g v : ℕ} →
                 sexp e ≪sign sresult (eval g e v)
sexp-soundness {Var} {g} {zero} = ≪Refl
sexp-soundness {Var} {g} {suc v} = ≪Nonneg
sexp-soundness {Value x} {g} {v} = ≪Refl
sexp-soundness {Add e1 e2} {g} {v} =
  _>>=≪sign_{sexp e1}{eval g e1 v} (sexp-soundness{e1}{g}{v})
  (λ{b}{u} q →
  _>>=≪sign_ {sexp e2} {eval g e2 v} (sexp-soundness {e2} {g} {v})
  (λ{b'}{u'} q' → sign-add q q'))

sexp-soundness {IsZero e} {g} {v} = ≪Unknown
sexp-soundness {Cond e e₁ e₂} {g} {v} = ≪Unknown
sexp-soundness {Search e} {g} {v} = ≪Unknown

