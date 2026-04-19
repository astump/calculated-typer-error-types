{- modified version of code presented in

   The Calculated Typer (Functional Pearl) by Garby, Bahr, and Hutton
   Haskell Symposium 2025.

   Here I distinguish between unknown and certainly erroneous.
-}
module CalculatedTyperPlus where

open import lib

data Value : Set where
 I : ℕ → Value
 B : 𝔹 → Value
 Error : Value

data Expr : Set where
 Val : Value → Expr
 Add : Expr → Expr → Expr
 If : Expr → Expr → Expr → Expr

-- if False then True + 3 else False
example : Expr
example = If (Val (B ff)) (Add (Val (B tt)) (Val (I 3))) (Val (B ff))

-- if False then 3 else False

add : Value → Value → Value
add (I x) (I y) = I (x + y)
add _ _ = Error

cond : Value → Value → Value → Value
cond (B x) y z = if x then y else z
cond _ _ _ = Error

eval : Expr → Value
eval (Val x) = x
eval (Add e1 e2) = add (eval e1) (eval e2)
eval (If e1 e2 e3) = cond (eval e1) (eval e2) (eval e3)

----------------------------------------------------------------------

data Type : Set where
  INT : Type
  BOOL : Type
  ERROR : Type
  UNKNOWN : Type

tval : Value → Type
tval (I _) = INT
tval (B _) = BOOL
tval Error = ERROR

add' : Type → Type → Type
add' INT INT = INT
add' ERROR UNKNOWN  = ERROR
add' ERROR INT  = ERROR
add' ERROR BOOL  = ERROR
add' ERROR ERROR  = ERROR
add' UNKNOWN ERROR  = ERROR
add' INT ERROR  = ERROR
add' BOOL ERROR  = ERROR
add' UNKNOWN INT = UNKNOWN
add' UNKNOWN BOOL = ERROR
add' UNKNOWN UNKNOWN = UNKNOWN
add' INT UNKNOWN = UNKNOWN
add' BOOL UNKNOWN = ERROR
add' BOOL INT = ERROR
add' INT BOOL = ERROR
add' BOOL BOOL = ERROR

cond' : Type → Type → Type → Type
cond' BOOL INT INT = INT
cond' BOOL BOOL BOOL = BOOL
cond' BOOL ERROR ERROR = ERROR
cond' BOOL _ _ = UNKNOWN
cond' UNKNOWN ERROR ERROR = ERROR
cond' UNKNOWN _ _ = UNKNOWN
cond' ERROR _ _ = ERROR
cond' INT _ _ = ERROR

texp : Expr → Type
texp (Val x) = tval x
texp (Add e1 e2) = add' (texp e1) (texp e2) 
texp (If e1 e2 e3) = cond' (texp e1) (texp e2) (texp e3)

data _≪_ : Type → Type → Set where
  ≪UNKNOWN : ∀ {T : Type} → UNKNOWN ≪ T
  ≪Refl : ∀{T : Type} → T ≪ T

≪-trans : ∀{t1 t2 t3 : Type} →
            t1 ≪ t2 →
            t2 ≪ t3 →
            t1 ≪ t3
≪-trans ≪UNKNOWN ≪UNKNOWN = ≪UNKNOWN
≪-trans ≪UNKNOWN ≪Refl = ≪UNKNOWN
≪-trans ≪Refl ≪UNKNOWN = ≪UNKNOWN
≪-trans ≪Refl ≪Refl = ≪Refl
 
tval-add : ∀{v1 v2 : Value} →
            add' (tval v1) (tval v2) ≪ tval (add v1 v2) 
tval-add {I x} {I x₁} = ≪Refl
tval-add {I x} {B x₁} = ≪Refl
tval-add {I x} {Error} = ≪Refl
tval-add {B x} {I x₁} = ≪Refl
tval-add {B x} {B x₁} = ≪Refl
tval-add {B x} {Error} = ≪Refl
tval-add {Error} {I x} = ≪Refl
tval-add {Error} {B x} = ≪Refl
tval-add {Error} {Error} = ≪Refl

add'-mono : ∀{t1 t2 t1' t2' : Type} →
            t1 ≪ t1' →
            t2 ≪ t2' →
            add' t1 t2 ≪ add' t1' t2'
add'-mono ≪UNKNOWN ≪UNKNOWN = ≪UNKNOWN
add'-mono {t2 = INT} ≪UNKNOWN ≪Refl = ≪UNKNOWN
add'-mono {t2 = BOOL} {INT} ≪UNKNOWN ≪Refl = ≪Refl
add'-mono {t2 = BOOL} {BOOL} ≪UNKNOWN ≪Refl = ≪Refl
add'-mono {t2 = BOOL} {ERROR} ≪UNKNOWN ≪Refl = ≪Refl
add'-mono {t2 = BOOL} {UNKNOWN} ≪UNKNOWN ≪Refl = ≪Refl
add'-mono {t2 = ERROR} {INT} ≪UNKNOWN ≪Refl = ≪Refl
add'-mono {t2 = ERROR} {BOOL} ≪UNKNOWN ≪Refl = ≪Refl
add'-mono {t2 = ERROR} {ERROR} ≪UNKNOWN ≪Refl = ≪Refl
add'-mono {t2 = ERROR} {UNKNOWN} ≪UNKNOWN ≪Refl = ≪Refl
add'-mono {t2 = UNKNOWN} ≪UNKNOWN ≪Refl = ≪UNKNOWN
add'-mono {INT} ≪Refl ≪UNKNOWN = ≪UNKNOWN
add'-mono {BOOL} {t2' = INT} ≪Refl ≪UNKNOWN = ≪Refl
add'-mono {BOOL} {t2' = BOOL} ≪Refl ≪UNKNOWN = ≪Refl
add'-mono {BOOL} {t2' = ERROR} ≪Refl ≪UNKNOWN = ≪Refl
add'-mono {BOOL} {t2' = UNKNOWN} ≪Refl ≪UNKNOWN = ≪Refl
add'-mono {ERROR} {t2' = INT} ≪Refl ≪UNKNOWN = ≪Refl
add'-mono {ERROR} {t2' = BOOL} ≪Refl ≪UNKNOWN = ≪Refl
add'-mono {ERROR} {t2' = ERROR} ≪Refl ≪UNKNOWN = ≪Refl
add'-mono {ERROR} {t2' = UNKNOWN} ≪Refl ≪UNKNOWN = ≪Refl
add'-mono {UNKNOWN} ≪Refl ≪UNKNOWN = ≪UNKNOWN
add'-mono {INT} {INT} ≪Refl ≪Refl = ≪Refl
add'-mono {INT} {BOOL} ≪Refl ≪Refl = ≪Refl 
add'-mono {INT} {ERROR} ≪Refl ≪Refl = ≪Refl 
add'-mono {INT} {UNKNOWN} ≪Refl ≪Refl = ≪Refl 
add'-mono {BOOL} {INT} ≪Refl ≪Refl = ≪Refl 
add'-mono {BOOL} {BOOL} ≪Refl ≪Refl = ≪Refl 
add'-mono {BOOL} {ERROR} ≪Refl ≪Refl = ≪Refl 
add'-mono {BOOL} {UNKNOWN} ≪Refl ≪Refl = ≪Refl 
add'-mono {ERROR} {INT} ≪Refl ≪Refl = ≪Refl 
add'-mono {ERROR} {BOOL} ≪Refl ≪Refl = ≪Refl 
add'-mono {ERROR} {ERROR} ≪Refl ≪Refl = ≪Refl 
add'-mono {ERROR} {UNKNOWN} ≪Refl ≪Refl = ≪Refl 
add'-mono {UNKNOWN} {INT} ≪Refl ≪Refl = ≪Refl
add'-mono {UNKNOWN} {BOOL} ≪Refl ≪Refl = ≪Refl 
add'-mono {UNKNOWN} {ERROR} ≪Refl ≪Refl = ≪Refl 
add'-mono {UNKNOWN} {UNKNOWN} ≪Refl ≪Refl = ≪Refl

add'-soundness : ∀{v1 v2 : Value} →
                 add' (tval v1) (tval v2) ≪ tval (add v1 v2)
add'-soundness {I x} {I y} = ≪Refl
add'-soundness {I x} {B y} = ≪Refl
add'-soundness {I x} {Error} = ≪Refl
add'-soundness {B x} {I y} = ≪Refl
add'-soundness {B x} {B y} = ≪Refl
add'-soundness {B x} {Error} = ≪Refl
add'-soundness {Error} {I x} = ≪Refl
add'-soundness {Error} {B x} = ≪Refl
add'-soundness {Error} {Error} = ≪Refl

cond'-mono : ∀{t1 t2 t3 t1' t2' t3' : Type} →
            t1 ≪ t1' →
            t2 ≪ t2' →
            t3 ≪ t3' →            
            cond' t1 t2 t3 ≪ cond' t1' t2' t3'
cond'-mono {INT} {INT} {t3} {INT} {INT} {t3'} d1 d2 d3 = ≪Refl
cond'-mono {INT} {BOOL} {t3} {INT} {BOOL} {t3'} d1 d2 d3 = ≪Refl
cond'-mono {INT} {ERROR} {t3} {INT} {ERROR} {t3'} d1 d2 d3 = ≪Refl
cond'-mono {INT} {UNKNOWN} {t3} {INT} {INT} {t3'} d1 d2 d3 = ≪Refl
cond'-mono {INT} {UNKNOWN} {t3} {INT} {BOOL} {t3'} d1 d2 d3 = ≪Refl
cond'-mono {INT} {UNKNOWN} {t3} {INT} {ERROR} {t3'} d1 d2 d3 = ≪Refl
cond'-mono {INT} {UNKNOWN} {t3} {INT} {UNKNOWN} {t3'} d1 d2 d3 = ≪Refl
cond'-mono {BOOL} {t2} {t3} {BOOL} {t2'} {t3'} d1 ≪UNKNOWN ≪UNKNOWN = ≪UNKNOWN
cond'-mono {BOOL} {t2} {t3} {BOOL} {t2'} {t3'} d1 ≪UNKNOWN ≪Refl = ≪UNKNOWN
cond'-mono {BOOL} {INT} {t3} {BOOL} d1 ≪Refl ≪UNKNOWN = ≪UNKNOWN
cond'-mono {BOOL} {BOOL} {t3} {BOOL} d1 ≪Refl ≪UNKNOWN = ≪UNKNOWN
cond'-mono {BOOL} {ERROR} {t3} {BOOL} d1 ≪Refl ≪UNKNOWN = ≪UNKNOWN
cond'-mono {BOOL} {UNKNOWN} {t3} {BOOL} d1 ≪Refl ≪UNKNOWN = ≪UNKNOWN
cond'-mono {BOOL} {INT} {INT} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪Refl
cond'-mono {BOOL} {INT} {BOOL} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪Refl
cond'-mono {BOOL} {INT} {ERROR} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪Refl
cond'-mono {BOOL} {INT} {UNKNOWN} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪Refl
cond'-mono {BOOL} {BOOL} {INT} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪Refl
cond'-mono {BOOL} {BOOL} {BOOL} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪Refl
cond'-mono {BOOL} {BOOL} {ERROR} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪Refl
cond'-mono {BOOL} {BOOL} {UNKNOWN} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪Refl
cond'-mono {BOOL} {ERROR} {INT} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪Refl
cond'-mono {BOOL} {ERROR} {BOOL} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪Refl
cond'-mono {BOOL} {ERROR} {ERROR} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪Refl
cond'-mono {BOOL} {ERROR} {UNKNOWN} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪Refl
cond'-mono {BOOL} {UNKNOWN} {INT} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪Refl
cond'-mono {BOOL} {UNKNOWN} {BOOL} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪Refl
cond'-mono {BOOL} {UNKNOWN} {ERROR} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪Refl
cond'-mono {BOOL} {UNKNOWN} {UNKNOWN} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪Refl
cond'-mono {ERROR} {t2} {t3} {ERROR} {t2'} {t3'} d1 d2 d3 = ≪Refl
cond'-mono {UNKNOWN} {INT} {INT} {INT} {t2'} {t3'} d1 d2 d3 = ≪UNKNOWN
cond'-mono {UNKNOWN} {INT} {BOOL} {INT} {t2'} {t3'} d1 d2 d3 = ≪UNKNOWN
cond'-mono {UNKNOWN} {INT} {ERROR} {INT} {t2'} {t3'} d1 d2 d3 = ≪UNKNOWN
cond'-mono {UNKNOWN} {INT} {UNKNOWN} {INT} {t2'} {t3'} d1 d2 d3 = ≪UNKNOWN
cond'-mono {UNKNOWN} {BOOL} {INT} {INT} {t2'} {t3'} d1 d2 d3 = ≪UNKNOWN
cond'-mono {UNKNOWN} {BOOL} {BOOL} {INT} {t2'} {t3'} d1 d2 d3 = ≪UNKNOWN
cond'-mono {UNKNOWN} {BOOL} {ERROR} {INT} {t2'} {t3'} d1 d2 d3 = ≪UNKNOWN
cond'-mono {UNKNOWN} {BOOL} {UNKNOWN} {INT} {t2'} {t3'} d1 d2 d3 = ≪UNKNOWN
cond'-mono {UNKNOWN} {ERROR} {INT} {INT} {t2'} {t3'} d1 d2 d3 = ≪UNKNOWN
cond'-mono {UNKNOWN} {ERROR} {BOOL} {INT} {t2'} {t3'} d1 d2 d3 = ≪UNKNOWN
cond'-mono {UNKNOWN} {ERROR} {ERROR} {INT} {t2'} {t3'} d1 d2 d3 = ≪Refl
cond'-mono {UNKNOWN} {ERROR} {UNKNOWN} {INT} {t2'} {t3'} d1 d2 d3 = ≪UNKNOWN
cond'-mono {UNKNOWN} {UNKNOWN} {INT} {INT} {t2'} {t3'} d1 d2 d3 = ≪UNKNOWN
cond'-mono {UNKNOWN} {UNKNOWN} {BOOL} {INT} {t2'} {t3'} d1 d2 d3 = ≪UNKNOWN
cond'-mono {UNKNOWN} {UNKNOWN} {ERROR} {INT} {t2'} {t3'} d1 d2 d3 = ≪UNKNOWN
cond'-mono {UNKNOWN} {UNKNOWN} {UNKNOWN} {INT} {t2'} {t3'} d1 d2 d3 = ≪UNKNOWN
cond'-mono {UNKNOWN} {t2} {t3} {BOOL} {t2'} {t3'} d1 ≪UNKNOWN d3 = ≪UNKNOWN
cond'-mono {UNKNOWN} {INT} {t3} {BOOL} {t2'} {t3'} d1 ≪Refl ≪UNKNOWN = ≪UNKNOWN
cond'-mono {UNKNOWN} {BOOL} {t3} {BOOL} {t2'} {t3'} d1 ≪Refl ≪UNKNOWN = ≪UNKNOWN
cond'-mono {UNKNOWN} {ERROR} {t3} {BOOL} {t2'} {t3'} d1 ≪Refl ≪UNKNOWN = ≪UNKNOWN
cond'-mono {UNKNOWN} {UNKNOWN} {t3} {BOOL} {t2'} {t3'} d1 ≪Refl ≪UNKNOWN = ≪UNKNOWN
cond'-mono {UNKNOWN} {INT} {INT} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {INT} {BOOL} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {INT} {ERROR} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {INT} {UNKNOWN} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {BOOL} {INT} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {BOOL} {BOOL} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {BOOL} {ERROR} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {BOOL} {UNKNOWN} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {ERROR} {INT} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {ERROR} {BOOL} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {ERROR} {ERROR} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪Refl
cond'-mono {UNKNOWN} {ERROR} {UNKNOWN} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {UNKNOWN} {INT} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {UNKNOWN} {BOOL} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {UNKNOWN} {ERROR} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {UNKNOWN} {UNKNOWN} {BOOL} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {t2} {t3} {ERROR} {t2'} {t3'} d1 ≪UNKNOWN d3 = ≪UNKNOWN
cond'-mono {UNKNOWN} {INT} {t3} {ERROR} {t2'} {t3'} d1 ≪Refl ≪UNKNOWN = ≪UNKNOWN
cond'-mono {UNKNOWN} {BOOL} {t3} {ERROR} {t2'} {t3'} d1 ≪Refl ≪UNKNOWN = ≪UNKNOWN
cond'-mono {UNKNOWN} {ERROR} {t3} {ERROR} {t2'} {t3'} d1 ≪Refl ≪UNKNOWN = ≪UNKNOWN
cond'-mono {UNKNOWN} {UNKNOWN} {t3} {ERROR} {t2'} {t3'} d1 ≪Refl ≪UNKNOWN = ≪UNKNOWN
cond'-mono {UNKNOWN} {INT} {INT} {ERROR} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {INT} {BOOL} {ERROR} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {INT} {ERROR} {ERROR} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {INT} {UNKNOWN} {ERROR} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {BOOL} {INT} {ERROR} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {BOOL} {BOOL} {ERROR} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {BOOL} {ERROR} {ERROR} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {BOOL} {UNKNOWN} {ERROR} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {ERROR} {INT} {ERROR} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {ERROR} {BOOL} {ERROR} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {ERROR} {ERROR} {ERROR} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪Refl
cond'-mono {UNKNOWN} {ERROR} {UNKNOWN} {ERROR} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {UNKNOWN} {INT} {ERROR} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {UNKNOWN} {BOOL} {ERROR} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {UNKNOWN} {ERROR} {ERROR} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {UNKNOWN} {UNKNOWN} {ERROR} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {t2} {t3} {UNKNOWN} {t2'} {t3'} d1 ≪UNKNOWN ≪UNKNOWN = ≪UNKNOWN
cond'-mono {UNKNOWN} {t2} {t3} {UNKNOWN} {t2'} {t3'} d1 ≪UNKNOWN ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {INT} {t3} {UNKNOWN} {t2'} {t3'} d1 ≪Refl ≪UNKNOWN = ≪UNKNOWN
cond'-mono {UNKNOWN} {BOOL} {t3} {UNKNOWN} {t2'} {t3'} d1 ≪Refl ≪UNKNOWN = ≪UNKNOWN
cond'-mono {UNKNOWN} {ERROR} {t3} {UNKNOWN} {t2'} {t3'} d1 ≪Refl ≪UNKNOWN = ≪UNKNOWN
cond'-mono {UNKNOWN} {UNKNOWN} {t3} {UNKNOWN} {t2'} {t3'} d1 ≪Refl ≪UNKNOWN = ≪UNKNOWN
cond'-mono {UNKNOWN} {INT} {INT} {UNKNOWN} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {INT} {BOOL} {UNKNOWN} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {INT} {ERROR} {UNKNOWN} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {INT} {UNKNOWN} {UNKNOWN} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {BOOL} {INT} {UNKNOWN} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {BOOL} {BOOL} {UNKNOWN} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {BOOL} {ERROR} {UNKNOWN} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {BOOL} {UNKNOWN} {UNKNOWN} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {ERROR} {INT} {UNKNOWN} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {ERROR} {BOOL} {UNKNOWN} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {ERROR} {ERROR} {UNKNOWN} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪Refl
cond'-mono {UNKNOWN} {ERROR} {UNKNOWN} {UNKNOWN} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {UNKNOWN} {INT} {UNKNOWN} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {UNKNOWN} {BOOL} {UNKNOWN} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {UNKNOWN} {ERROR} {UNKNOWN} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN
cond'-mono {UNKNOWN} {UNKNOWN} {UNKNOWN} {UNKNOWN} {t2'} {t3'} d1 ≪Refl ≪Refl = ≪UNKNOWN

cond'-soundness : ∀{v1 v2 v3 : Value} →
                 cond' (tval v1) (tval v2) (tval v3) ≪ tval (cond v1 v2 v3)
cond'-soundness {I x} {I x₁} {I x₂} = ≪Refl
cond'-soundness {I x} {I x₁} {B x₂} = ≪Refl
cond'-soundness {I x} {I x₁} {Error} = ≪Refl
cond'-soundness {I x} {B x₁} {I x₂} = ≪Refl
cond'-soundness {I x} {B x₁} {B x₂} = ≪Refl
cond'-soundness {I x} {B x₁} {Error} = ≪Refl
cond'-soundness {I x} {Error} {I x₁} = ≪Refl
cond'-soundness {I x} {Error} {B x₁} = ≪Refl
cond'-soundness {I x} {Error} {Error} = ≪Refl
cond'-soundness {B tt} {I x₁} {I x₂} = ≪Refl
cond'-soundness {B ff} {I x₁} {I x₂} = ≪Refl
cond'-soundness {B x} {I x₁} {B x₂} = ≪UNKNOWN
cond'-soundness {B x} {I x₁} {Error} = ≪UNKNOWN
cond'-soundness {B x} {B x₁} {I x₂} = ≪UNKNOWN
cond'-soundness {B tt} {B x₁} {B x₂} = ≪Refl
cond'-soundness {B ff} {B x₁} {B x₂} = ≪Refl
cond'-soundness {B x} {B x₁} {Error} = ≪UNKNOWN
cond'-soundness {B x} {Error} {I x₁} = ≪UNKNOWN
cond'-soundness {B x} {Error} {B x₁} = ≪UNKNOWN
cond'-soundness {B tt} {Error} {Error} = ≪Refl
cond'-soundness {B ff} {Error} {Error} = ≪Refl
cond'-soundness {Error} {I x} {I x₁} = ≪Refl
cond'-soundness {Error} {I x} {B x₁} = ≪Refl
cond'-soundness {Error} {I x} {Error} = ≪Refl
cond'-soundness {Error} {B x} {I x₁} = ≪Refl
cond'-soundness {Error} {B x} {B x₁} = ≪Refl
cond'-soundness {Error} {B x} {Error} = ≪Refl
cond'-soundness {Error} {Error} {I x} = ≪Refl
cond'-soundness {Error} {Error} {B x} = ≪Refl
cond'-soundness {Error} {Error} {Error} = ≪Refl

soundness : ∀{e : Expr} →
            texp e ≪ tval (eval e)
soundness {Val x} = ≪Refl
soundness {Add e1 e2} = ≪-trans (add'-mono (soundness {e1}) (soundness {e2})) add'-soundness
soundness {If e1 e2 e3} = ≪-trans (cond'-mono (soundness{e1}) (soundness{e2}) (soundness{e3})) cond'-soundness