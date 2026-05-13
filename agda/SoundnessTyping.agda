{- Extending the ideas from

   The Calculated Typer (Functional Pearl) by Garby, Bahr, and Hutton
   Haskell Symposium 2025.

   by distinguishing between unknown and certainly erroneous, and using monads throughout.
-}
module SoundnessTyping where

open import lib
open import Sign
open import Syntax
open import Eval
open import Typing
open import SoundnessSign


infix 6 _≪_ 

data _≪_ : EType Data → RType → Set where
  ≪Unknown : ∀ {T} → UNKNOWN ≪ T
  ≪Data : ∀{T}{b} → DATA b T ≪ DATA T
  ≪Fail : ∀{b} → FAIL b ≪ FAIL
  ≪Unfinished : ∀{T} → T ≪ UNFINISHED

⇓mono : ∀{e : EType Data}{r : RType}{b : 𝔹} →
        e ≪ r →
        (b ⇓ e) ≪ r
⇓mono {e} {r} {b} ≪Unknown = ≪Unknown
⇓mono {e} {r} {b} ≪Data = ≪Data
⇓mono {e} {r} {b} ≪Unfinished = ≪Unfinished
⇓mono {e} {r} {b} ≪Fail = ≪Fail

return≪ : ∀{v : Val} →
          returne (tval v) ≪ tresult (returnr v)
return≪{v} = ≪Data

infixr 8 _>>=≪_

_>>=≪_ : ∀{a : EType Data}{a' : Result Val} →
        {f : Data → EType Data}{f' : Val → Result Val} → 
         a ≪ tresult a' →
         (∀{v : Val}{b : 𝔹}
           {q : a ≡ DATA b (tval v)}
           {q' : a' ≡ Value v}
           {q'' : DATA b (tval v) ≪ DATA (tval v)} → 
           f (tval v) ≪ tresult (f' v)) → 
        (a >>=e f) ≪ tresult (a' >>=r f')
_>>=≪_ {DATA b c} {Value x} {f} {f'} ≪Data d2 = ⇓mono (d2{x}{b}{refl}{refl}{≪Data})
_>>=≪_ {DATA b c} {Unfinished} {f} {f'} ≪Unfinished d2 = ≪Unfinished
_>>=≪_ {FAIL b} {Fail} {f} {f'} d1 d2 = ≪Fail
_>>=≪_ {FAIL b} {Unfinished} {f} {f'} d1 d2 = ≪Unfinished
_>>=≪_ {UNKNOWN} {Value x} {f} {f'} d1 d2 = ≪Unknown
_>>=≪_ {UNKNOWN} {Fail} {f} {f'} d1 d2 = ≪Unknown
_>>=≪_ {UNKNOWN} {Unfinished} {f} {f'} d1 d2 = ≪Unknown
_>>=≪_ {LOOP} {Unfinished} {f} {f'} d1 d2 = ≪Unfinished

⊓lb1 : ∀{a b : EType Data}{a' b' : RType} →
      a ≪ a' →
      b ≪ b' →
      a ⊓ b ≪ a'
⊓lb1 {a} {b} {a'} {b'} ≪Unknown d2 = ≪Unknown
⊓lb1 {a} {DATA b T} {a'} {b'} (≪Data{T'}) d2 with T' =c T 
⊓lb1 {a} {DATA b T} {a'} {b'} (≪Data{T'}) d2 | tt = ≪Data
⊓lb1 {a} {DATA b T} {a'} {b'} (≪Data{T'}) d2 | ff = ≪Unknown
⊓lb1 {a} {FAIL x} {a'} {b'} ≪Data d2 = ≪Unknown
⊓lb1 {a} {UNKNOWN} {a'} {b'} ≪Data d2 = ≪Unknown
⊓lb1 {a} {LOOP} {a'} {b'} ≪Data d2 = ≪Data
⊓lb1 {a} {DATA b c} {a'} {b'} ≪Fail d2 = ≪Unknown
⊓lb1 {a} {FAIL x} {a'} {b'} ≪Fail d2 = ≪Fail
⊓lb1 {a} {UNKNOWN} {a'} {b'} ≪Fail d2 = ≪Unknown
⊓lb1 {a} {LOOP} {a'} {b'} ≪Fail d2 = ≪Fail
⊓lb1 {a} {b} {a'} {b'} ≪Unfinished d2 = ≪Unfinished

⊓lb2 : ∀{a b : EType Data}{a' b' : RType} →
      a ≪ a' →
      b ≪ b' →
      a ⊓ b ≪ b'
⊓lb2 {DATA b₁ c} {b} {a'} {b'} d1 ≪Unknown = ≪Unknown
⊓lb2 {FAIL x} {b} {a'} {b'} d1 ≪Unknown = ≪Unknown
⊓lb2 {UNKNOWN} {b} {a'} {b'} d1 ≪Unknown = ≪Unknown
⊓lb2 {LOOP} {b} {a'} {b'} d1 ≪Unknown = ≪Unknown
⊓lb2 {DATA b₁ T} {b} {a'} {b'} d1 (≪Data{T'}) with keep (T =c T')
⊓lb2 {DATA b₁ T} {b} {a'} {b'} d1 (≪Data{T'}) | tt , p rewrite p | =c≡ p = ≪Data
⊓lb2 {DATA b₁ T} {b} {a'} {b'} d1 (≪Data{T'}) | ff , p rewrite p = ≪Unknown
⊓lb2 {FAIL x} {b} {a'} {b'} d1 ≪Data = ≪Unknown
⊓lb2 {UNKNOWN} {b} {a'} {b'} d1 ≪Data = ≪Unknown
⊓lb2 {LOOP} {b} {a'} {b'} d1 ≪Data = ≪Data
⊓lb2 {DATA b₁ c} {b} {a'} {b'} d1 ≪Fail = ≪Unknown
⊓lb2 {FAIL x} {b} {a'} {b'} d1 ≪Fail = ≪Fail
⊓lb2 {UNKNOWN} {b} {a'} {b'} d1 ≪Fail = ≪Unknown
⊓lb2 {LOOP} {b} {a'} {b'} d1 ≪Fail = ≪Fail
⊓lb2 {a} {b} {a'} {b'} d1 ≪Unfinished = ≪Unfinished

case-isZero : ∀{v : Val} →
              isZero' (tval v) ≪ tresult (isZero v)
case-isZero {I x} = ≪Data
case-isZero {B x} = ≪Fail

case-add : ∀{v1 v2 : Val} →
           add' (tval v1) (tval v2) ≪ tresult (add v1 v2)
case-add {I x} {I x₁} = ≪Data
case-add {I x} {B x₁} = ≪Fail
case-add {B x} {I x₁} = ≪Fail
case-add {B x} {B x₁} = ≪Fail

case-cond : ∀{v1 : Val}{r2 r3 : Result Val}{t2 t3 : EType Data} →
            t2 ≪ tresult r2 →
            t3 ≪ tresult r3 →             
            cond' (tval v1) t2 t3 ≪ tresult (cond v1 r2 r3)
case-cond {I x} {r2} {r3} {t2} {t3} d1 d2 = ≪Fail
case-cond {B tt} {r2} {r3} {t2} {t3} d1 d2 = ⊓lb1 d1 d2
case-cond {B ff} {r2} {r3} {t2} {t3} d1 d2 = ⊓lb2 d1 d2

⇓search'INT : ∀{s : Sign 𝔹} → tt ⇓ search' INT s ≡ search' INT s
⇓search'INT {Known tt} = refl
⇓search'INT {Known ff} = refl
⇓search'INT {Unknown} = refl

weaken-DATA≪ : ∀{b : 𝔹}{T : Data}{R : RType} →
                DATA b T ≪ R → 
                DATA tt T ≪ R 
weaken-DATA≪ ≪Data = ≪Data
weaken-DATA≪ ≪Unfinished = ≪Unfinished

mutual 
 case-searchh : ∀ {u : Val}{s : Sign 𝔹}{vv : ℕ → Result Val}{g : ℕ}{b : 𝔹} →
               (∀{n : ℕ} → DATA b (tval u) ≪ tresult (vv n)) → 
               (∀{n : ℕ} → s ≪sign sresult (vv n)) →
               s ≪sign sval u → 
               search' (tval u) s ≪ tresult (searchh g vv u)
 case-searchh {B x} {s} {vv} {g} dd d d' = ≪Fail
 case-searchh {I x} {s} {vv} {g} dd d d' with keep (x =ℤ 0ℤ)
 case-searchh {I x} {s} {vv} {g} dd d d' | tt , p rewrite p | =ℤ-to-≡{x}{0ℤ} p with d' 
 case-searchh {I x} {s} {vv} {g} dd d _ | tt , p | ≪Unknown = ≪Data
 case-searchh {I x} {s} {vv} {g} dd d _ | tt , p | ≪Refl = ≪Data
 case-searchh {I x} {s} {vv} {suc g} dd d d' | ff , p rewrite p = case-search{vv = vv} (λ{n} → weaken-DATA≪ (dd{n})) d
 case-searchh {I x} {s} {vv} {zero} dd d d' | ff , p rewrite p = ≪Unfinished

 case-search : ∀ {s : Sign 𝔹}{vv : ℕ → Result Val}{g : ℕ} →
               (∀{n : ℕ} → DATA tt INT ≪ tresult (vv n)) → 
               (∀{n : ℕ} → s ≪sign sresult (vv n)) →
               search' INT s ≪ tresult (search g vv)
 case-search{s}{vv}{g} dd d' rewrite sym (⇓search'INT{s}) = d''
   where inj2-DATA : ∀{b b' : 𝔹}{t t' : Data} → DATA b t ≡ DATA b' t' → t ≡ t'
         inj2-DATA refl = refl
         dv : ∀{v : Val}{n : ℕ}{b : 𝔹} →
              DATA tt INT ≡ DATA b (tval v) → 
              DATA tt (tval v) ≪ tresult (vv n)
         dv{v}{n} e rewrite sym (inj2-DATA e) = dd


         h : ∀{v : Val}{r : Result Val} →
             s ≪sign sresult r →
             r ≡ Value v →
             s ≪sign sval v
         h d1 refl = d1
         d'' = _>>=≪_{DATA tt INT}{vv g}{λ v → search' v s} (dd{g})
               (λ{v}{b}{q'}{q}{q''} → case-searchh{v}{s}{vv}{g}{tt} (dv q') d' (h (d'{g}) q)) 

texp-soundness : ∀{e : Expr}{g v : ℕ} →
                 texp e ≪ tresult (eval g e v)
texp-soundness {Var} {g} {v} = ≪Data
texp-soundness {Value x} {g} {v} = return≪
texp-soundness {Add e1 e2} {g} {v} = 
  (texp-soundness{e1}{g}{v}) >>=≪
  λ{v1} →
   texp-soundness{e2}{g}{v} >>=≪
   λ{v2} → case-add
texp-soundness {IsZero e} {g} {v} = 
  (texp-soundness{e}{g}{v}) >>=≪
  case-isZero 
texp-soundness {Cond e1 e2 e3} {g} {v} = 
  (texp-soundness{e1}{g}{v}) >>=≪ λ{v1} → 
  case-cond{v1} (texp-soundness{e2}{g}{v}) (texp-soundness{e3}{g}{v})
texp-soundness {Search e} {g} {v} = 
  (texp-soundness{e}{g}{g}) >>=≪
  λ{u}{b}{q}{q'} →
     case-searchh{u}{b = b} (λ{n} → h {u} q) (sign-soundness{e}) (h' q')

  where h : ∀{u : Val}{b : 𝔹}{n : ℕ} →
            texp e ≡ DATA b (tval u) →
            DATA b (tval u) ≪ tresult (eval g e n)
        h{n = n} r with texp-soundness{e}{g}{n} 
        h r | d rewrite r = d
        h' : ∀{u : Val} →
             eval g e g ≡ Value u →
             sexp e ≪sign sval u
        h' r with sign-soundness{e}{g}{g}
        h' r | sd rewrite r = sd