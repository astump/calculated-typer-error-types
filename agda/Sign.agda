module Sign where

open import lib
open import Syntax

data Sign : Set where
  Pos : Sign
  Nonneg : Sign
  Unknown : Sign

addSign : Sign → Sign → Sign
addSign _ Unknown = Unknown
addSign Unknown _ = Unknown
addSign Pos Pos = Pos
addSign Pos Nonneg = Pos
addSign Nonneg Pos = Pos
addSign Nonneg Nonneg = Nonneg

multSign : Sign → Sign → Sign
multSign _ Unknown = Unknown
multSign Unknown _ = Unknown
multSign Pos Pos = Pos
multSign Pos Nonneg = Nonneg
multSign Nonneg Pos = Nonneg
multSign Nonneg Nonneg = Nonneg

arithSign : Op → Sign → Sign → Sign
arithSign Add = addSign
arithSign Mult = multSign

tsign : Value → Sign
tsign (I (mkℤ zero triv)) = Nonneg
tsign (I (mkℤ (suc n) tt)) = Pos
tsign (I (mkℤ (suc n) ff)) = Unknown
tsign (B x) = Unknown
tsign Fail = Unknown
tsign Loop = Unknown


sign : Expr → Sign
sign Var = Nonneg
sign (Val x) = tsign x
sign (Arith op e e') = arithSign op (sign e) (sign e')
sign (If i e e') = Unknown -- we don't have enough info to know if i will evaluate to a bool
sign (Search e) = Unknown

infix 6 _≪sign_ 

data _≪sign_ : Sign → Sign → Set where
  ≪Unknown : ∀ {s : Sign} → Unknown ≪sign s
  ≪Refl : ∀{s : Sign} → s ≪sign s
  ≪Nonneg : Nonneg ≪sign Pos

≪sign-trans : ∀{s1 s2 s3 : Sign} →
              s1 ≪sign s2 →
              s2 ≪sign s3 →               
              s1 ≪sign s3
≪sign-trans ≪Unknown ≪Unknown = ≪Unknown
≪sign-trans ≪Unknown ≪Refl = ≪Unknown
≪sign-trans ≪Unknown ≪Nonneg = ≪Unknown
≪sign-trans ≪Refl ≪Unknown = ≪Unknown
≪sign-trans ≪Refl ≪Refl = ≪Refl
≪sign-trans ≪Refl ≪Nonneg = ≪Nonneg
≪sign-trans ≪Nonneg ≪Refl = ≪Nonneg

arithSign-mono : ∀{s1 s1' s2 s2' : Sign}{op : Op} →
                 s1 ≪sign s1' →
                 s2 ≪sign s2' →                  
                 arithSign op s1 s2 ≪sign arithSign op s1' s2'
arithSign-mono {op = Add} ≪Unknown ≪Unknown = ≪Unknown
arithSign-mono {s2 = Pos} {op = Add} ≪Unknown ≪Refl = ≪Unknown
arithSign-mono {s2 = Nonneg} {op = Add} ≪Unknown ≪Refl = ≪Unknown
arithSign-mono {s2 = Unknown} {op = Add} ≪Unknown ≪Refl = ≪Unknown
arithSign-mono {op = Add} ≪Unknown ≪Nonneg = ≪Unknown
arithSign-mono {s1 = Pos} {op = Add} ≪Refl ≪Unknown = ≪Unknown
arithSign-mono {s1 = Nonneg} {op = Add} ≪Refl ≪Unknown = ≪Unknown
arithSign-mono {s1 = Unknown} {op = Add} ≪Refl ≪Unknown = ≪Unknown
arithSign-mono {op = Add} ≪Refl ≪Refl = ≪Refl
arithSign-mono {s1 = Pos} {op = Add} ≪Refl ≪Nonneg = ≪Refl
arithSign-mono {s1 = Nonneg} {op = Add} ≪Refl ≪Nonneg = ≪Nonneg
arithSign-mono {s1 = Unknown} {op = Add} ≪Refl ≪Nonneg = ≪Unknown
arithSign-mono {op = Add} ≪Nonneg ≪Unknown = ≪Unknown
arithSign-mono {s2 = Pos} {op = Add} ≪Nonneg ≪Refl = ≪Refl
arithSign-mono {s2 = Nonneg} {op = Add} ≪Nonneg ≪Refl = ≪Nonneg
arithSign-mono {s2 = Unknown} {op = Add} ≪Nonneg ≪Refl = ≪Unknown
arithSign-mono {op = Add} ≪Nonneg ≪Nonneg = ≪Nonneg
arithSign-mono {op = Mult} ≪Unknown ≪Unknown = ≪Unknown
arithSign-mono {s2 = Pos} {op = Mult} ≪Unknown ≪Refl = ≪Unknown
arithSign-mono {s2 = Nonneg} {op = Mult} ≪Unknown ≪Refl = ≪Unknown
arithSign-mono {s2 = Unknown} {op = Mult} ≪Unknown ≪Refl = ≪Unknown
arithSign-mono {op = Mult} ≪Unknown ≪Nonneg = ≪Unknown
arithSign-mono {s1 = Pos} {op = Mult} ≪Refl ≪Unknown = ≪Unknown
arithSign-mono {s1 = Nonneg} {op = Mult} ≪Refl ≪Unknown = ≪Unknown
arithSign-mono {s1 = Unknown} {op = Mult} ≪Refl ≪Unknown = ≪Unknown
arithSign-mono {op = Mult} ≪Refl ≪Refl = ≪Refl
arithSign-mono {s1 = Pos} {op = Mult} ≪Refl ≪Nonneg = ≪Nonneg
arithSign-mono {s1 = Nonneg} {op = Mult} ≪Refl ≪Nonneg = ≪Refl
arithSign-mono {s1 = Unknown} {op = Mult} ≪Refl ≪Nonneg = ≪Unknown
arithSign-mono {op = Mult} ≪Nonneg ≪Unknown = ≪Unknown
arithSign-mono {s2 = Pos} {op = Mult} ≪Nonneg ≪Refl = ≪Nonneg
arithSign-mono {s2 = Nonneg} {op = Mult} ≪Nonneg ≪Refl = ≪Refl
arithSign-mono {s2 = Unknown} {op = Mult} ≪Nonneg ≪Refl = ≪Unknown
arithSign-mono {op = Mult} ≪Nonneg ≪Nonneg = ≪Nonneg

addSign-Unknown : ∀{s : Sign} →
                  addSign Unknown s ≡ Unknown
addSign-Unknown {Pos} = refl
addSign-Unknown {Nonneg} = refl
addSign-Unknown {Unknown} = refl

multSign-Unknown : ∀{s : Sign} →
                  multSign Unknown s ≡ Unknown
multSign-Unknown {Pos} = refl
multSign-Unknown {Nonneg} = refl
multSign-Unknown {Unknown} = refl