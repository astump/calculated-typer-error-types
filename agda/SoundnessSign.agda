{- Extending the ideas from

   The Calculated Typer (Functional Pearl) by Garby, Bahr, and Hutton
   Haskell Symposium 2025.

   by distinguishing between unknown and certainly erroneous.
-}
module SoundnessSign where

open import lib
open import Sign
open import Syntax
open import Eval

tsign-add-II : ∀{z1 z2 : ℤ} →
               addSign (tsign (I z1)) (tsign (I z2)) ≪sign tsign (I (z1 +ℤ z2))
tsign-add-II {mkℤ zero triv} {mkℤ zero triv} = ≪Refl
tsign-add-II {mkℤ zero triv} {mkℤ (suc n₁) tt} = ≪Refl
tsign-add-II {mkℤ zero triv} {mkℤ (suc n₁) ff} = ≪Unknown
tsign-add-II {mkℤ (suc n) tt} {mkℤ zero triv} = ≪Refl
tsign-add-II {mkℤ (suc n) tt} {mkℤ (suc n₁) tt} = ≪Refl
tsign-add-II {mkℤ (suc n) tt} {mkℤ (suc n₁) ff} = ≪Unknown
tsign-add-II {mkℤ (suc n) ff} {mkℤ zero triv} = ≪Unknown
tsign-add-II {mkℤ (suc n) ff} {mkℤ (suc n₁) tt} = ≪Unknown
tsign-add-II {mkℤ (suc n) ff} {mkℤ (suc n₁) ff} = ≪Unknown

tsign-mult-II : ∀{z1 z2 : ℤ} →
               multSign (tsign (I z1)) (tsign (I z2)) ≪sign tsign (I (z1 *ℤ z2))
tsign-mult-II {mkℤ zero triv} {mkℤ zero triv} = ≪Refl
tsign-mult-II {mkℤ zero triv} {mkℤ (suc n₁) tt} = ≪Refl
tsign-mult-II {mkℤ zero triv} {mkℤ (suc n₁) ff} = ≪Unknown
tsign-mult-II {mkℤ (suc n) tt} {mkℤ zero triv} = ≪Refl
tsign-mult-II {mkℤ (suc n) tt} {mkℤ (suc n₁) tt} = ≪Refl
tsign-mult-II {mkℤ (suc n) tt} {mkℤ (suc n₁) ff} = ≪Unknown
tsign-mult-II {mkℤ (suc n) ff} {mkℤ zero triv} = ≪Unknown
tsign-mult-II {mkℤ (suc n) ff} {mkℤ (suc n₁) tt} = ≪Unknown
tsign-mult-II {mkℤ (suc n) ff} {mkℤ (suc n₁) ff} = ≪Unknown

tsign-arith : ∀{v1 v2 : Value}{op : Op}{g v : ℕ} →
              arithSign op (tsign v1) (tsign v2) ≪sign tsign (arith op v1 v2)
tsign-arith {I x} {I y} {Add} = tsign-add-II
tsign-arith {I x} {I y} {Mult} = tsign-mult-II
tsign-arith {I x} {B y} {Add} = ≪Unknown
tsign-arith {I x} {B y} {Mult} = ≪Unknown
tsign-arith {I x} {Fail} {Add} = ≪Unknown
tsign-arith {I x} {Fail} {Mult} = ≪Unknown
tsign-arith {I x} {Loop} {Add} = ≪Unknown
tsign-arith {I x} {Loop} {Mult} = ≪Unknown
tsign-arith {B x} {I y} {Add} rewrite addSign-Unknown{tsign (I y)} = ≪Unknown
tsign-arith {B x} {I y} {Mult} rewrite multSign-Unknown{tsign (I y)} = ≪Unknown
tsign-arith {B x} {B y} {Add} = ≪Unknown
tsign-arith {B x} {B y} {Mult} = ≪Unknown
tsign-arith {B x} {Fail} {Add} = ≪Unknown
tsign-arith {B x} {Fail} {Mult} = ≪Unknown
tsign-arith {B x} {Loop} {Add} = ≪Unknown
tsign-arith {B x} {Loop} {Mult} = ≪Unknown
tsign-arith {Fail} {I x} {Add} rewrite addSign-Unknown{tsign (I x)} = ≪Unknown
tsign-arith {Fail} {I x} {Mult} rewrite multSign-Unknown{tsign (I x)} = ≪Unknown
tsign-arith {Fail} {B x} {Add} = ≪Unknown
tsign-arith {Fail} {B x} {Mult} = ≪Unknown
tsign-arith {Fail} {Fail} {Add} = ≪Unknown
tsign-arith {Fail} {Fail} {Mult} = ≪Unknown
tsign-arith {Fail} {Loop} {Add} = ≪Unknown
tsign-arith {Fail} {Loop} {Mult} = ≪Unknown
tsign-arith {Loop} {I x} {Add} rewrite addSign-Unknown{tsign (I x)} = ≪Unknown
tsign-arith {Loop} {I x} {Mult} rewrite multSign-Unknown{tsign (I x)} = ≪Unknown
tsign-arith {Loop} {B x} {Add} = ≪Unknown
tsign-arith {Loop} {B x} {Mult} = ≪Unknown
tsign-arith {Loop} {Fail} {Add} = ≪Unknown
tsign-arith {Loop} {Fail} {Mult} = ≪Unknown
tsign-arith {Loop} {Loop} {Add} = ≪Unknown
tsign-arith {Loop} {Loop} {Mult} = ≪Unknown

sign-soundness : ∀{e : Expr}{g v : ℕ} →
                 sign e ≪sign tsign (eval g e v)
sign-soundness {Val x} = ≪Refl
sign-soundness {Arith op e1 e2}{g}{v} = ≪sign-trans (arithSign-mono{op = op} (sign-soundness {e1}{g}{v}) (sign-soundness {e2}{g}{v}))
                                               (tsign-arith{eval g e1 v}{eval g e2 v}{op}{g}{v})
sign-soundness {If e1 e2 e3}{g}{v} = ≪Unknown
sign-soundness {Var} {g} {zero} = ≪Refl
sign-soundness {Var} {g} {suc v} = ≪Nonneg
sign-soundness {Search e}{g}{v} = ≪Unknown

