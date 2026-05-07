{- Extending the ideas from

   The Calculated Typer (Functional Pearl) by Garby, Bahr, and Hutton
   Haskell Symposium 2025.

   by distinguishing between unknown and certainly erroneous.
-}
module SoundnessTyping where

open import lib
open import Sign
open import Syntax
open import Eval
open import Typing
open import SoundnessSign

tval-arith : ∀{v1 v2 : Value}{op : Op} →
            arith' (tval v1) (tval v2) ≪ tval (arith op v1 v2) 
tval-arith {I x} {I x₁} {Add} = ≪Refl
tval-arith {I x} {I x₁} {Mult} = ≪Refl
tval-arith {I x} {B x₁} {op} = ≪Unknown
tval-arith {I x} {Fail} {op} = ≪Unknown
tval-arith {I x} {Loop} {op} = ≪IntLoop
tval-arith {B x} {I x₁} {op} = ≪Unknown
tval-arith {B x} {B x₁} {op} = ≪Refl
tval-arith {B x} {Fail} {op} = ≪Unknown
tval-arith {B x} {Loop} {op} = ≪Unknown
tval-arith {Fail} {I x} {op} = ≪Unknown
tval-arith {Fail} {B x} {op} = ≪Unknown
tval-arith {Fail} {Fail} {op} = ≪Refl
tval-arith {Fail} {Loop} {op} = ≪Unknown
tval-arith {Loop} {I x} {op} = ≪IntLoop
tval-arith {Loop} {B x} {op} = ≪Unknown
tval-arith {Loop} {Fail} {op} = ≪Unknown
tval-arith {Loop} {Loop} {op} = ≪Refl

⊓Unknown : ∀{t : Type} →
           t ⊓ UNKNOWN ≡ UNKNOWN
⊓Unknown {INT x} = refl
⊓Unknown {BOOL x} = refl
⊓Unknown {FAIL} = refl
⊓Unknown {UNKNOWN} = refl
⊓Unknown {LOOP} = refl

⊓-mono : ∀{t1 t2 t1' t2' : Type} →
          t1 ≪ t1' →
          t2 ≪ t2' →
          t1 ⊓ t2 ≪ t1' ⊓ t2'
⊓-mono {t1} {t2} {t1'} {t2'} ≪Unknown d' = ≪Unknown
⊓-mono {t1} {t2} {t1'} {t2'} ≪Refl ≪Unknown rewrite ⊓Unknown{t1} = ≪Unknown
⊓-mono {t1} {t2} {t1'} {t2'} ≪Refl ≪Refl = ≪Refl
⊓-mono {INT x} {t2} {t1'} {t2'} ≪Refl ≪Bool = ≪Unknown
⊓-mono {BOOL tt} {t2} {t1'} {t2'} ≪Refl ≪Bool = ≪Refl
⊓-mono {BOOL ff} {t2} {t1'} {t2'} ≪Refl ≪Bool = ≪Bool
⊓-mono {FAIL} {t2} {t1'} {t2'} ≪Refl ≪Bool = ≪Unknown
⊓-mono {UNKNOWN} {t2} {t1'} {t2'} ≪Refl ≪Bool = ≪Unknown
⊓-mono {LOOP} {t2} {t1'} {t2'} ≪Refl ≪Bool = ≪Refl
⊓-mono {INT tt} {t2} {t1'} {t2'} ≪Refl ≪IntLoop = ≪Refl
⊓-mono {INT ff} {t2} {t1'} {t2'} ≪Refl ≪IntLoop = ≪Refl
⊓-mono {BOOL x} {t2} {t1'} {t2'} ≪Refl ≪IntLoop = ≪Unknown
⊓-mono {FAIL} {t2} {t1'} {t2'} ≪Refl ≪IntLoop = ≪Unknown
⊓-mono {UNKNOWN} {t2} {t1'} {t2'} ≪Refl ≪IntLoop = ≪Unknown
⊓-mono {LOOP} {t2} {t1'} {t2'} ≪Refl ≪IntLoop = ≪IntLoop
⊓-mono {INT x} {t2} {t1'} {t2'} ≪Refl ≪BoolLoop = ≪Unknown
⊓-mono {BOOL tt} {t2} {t1'} {t2'} ≪Refl ≪BoolLoop = ≪Refl
⊓-mono {BOOL ff} {t2} {t1'} {t2'} ≪Refl ≪BoolLoop = ≪Refl
⊓-mono {FAIL} {t2} {t1'} {t2'} ≪Refl ≪BoolLoop = ≪Unknown
⊓-mono {UNKNOWN} {t2} {t1'} {t2'} ≪Refl ≪BoolLoop = ≪Unknown
⊓-mono {LOOP} {t2} {t1'} {t2'} ≪Refl ≪BoolLoop = ≪BoolLoop
⊓-mono {t1} {t2} {t1'} {t2'} ≪Int ≪Unknown = ≪Unknown
⊓-mono {t1} {INT tt} {t1'} {t2'} ≪Int ≪Refl = ≪Refl
⊓-mono {t1} {INT ff} {t1'} {t2'} ≪Int ≪Refl = ≪Int
⊓-mono {t1} {BOOL x} {t1'} {t2'} ≪Int ≪Refl = ≪Unknown
⊓-mono {t1} {FAIL} {t1'} {t2'} ≪Int ≪Refl = ≪Unknown
⊓-mono {t1} {UNKNOWN} {t1'} {t2'} ≪Int ≪Refl = ≪Unknown
⊓-mono {t1} {LOOP} {t1'} {t2'} ≪Int ≪Refl = ≪Refl
⊓-mono {t1} {t2} {t1'} {t2'} ≪Int ≪Int = ≪Int
⊓-mono {t1} {t2} {t1'} {t2'} ≪Int ≪Bool = ≪Unknown
⊓-mono {t1} {t2} {t1'} {t2'} ≪Int ≪IntLoop = ≪Refl
⊓-mono {t1} {t2} {t1'} {t2'} ≪Int ≪BoolLoop = ≪Unknown
⊓-mono {t1} {t2} {t1'} {t2'} ≪Bool ≪Unknown = ≪Unknown
⊓-mono {t1} {INT x} {t1'} {t2'} ≪Bool ≪Refl = ≪Unknown
⊓-mono {t1} {BOOL tt} {t1'} {t2'} ≪Bool ≪Refl = ≪Refl
⊓-mono {t1} {BOOL ff} {t1'} {t2'} ≪Bool ≪Refl = ≪Bool
⊓-mono {t1} {FAIL} {t1'} {t2'} ≪Bool ≪Refl = ≪Unknown
⊓-mono {t1} {UNKNOWN} {t1'} {t2'} ≪Bool ≪Refl = ≪Unknown
⊓-mono {t1} {LOOP} {t1'} {t2'} ≪Bool ≪Refl = ≪Refl
⊓-mono {t1} {t2} {t1'} {t2'} ≪Bool ≪Int = ≪Unknown
⊓-mono {t1} {t2} {t1'} {t2'} ≪Bool ≪Bool = ≪Bool
⊓-mono {t1} {t2} {t1'} {t2'} ≪Bool ≪IntLoop = ≪Unknown
⊓-mono {t1} {t2} {t1'} {t2'} ≪Bool ≪BoolLoop = ≪Refl
⊓-mono {t1} {t2} {t1'} {t2'} ≪IntLoop ≪Unknown = ≪Unknown
⊓-mono {t1} {INT x} {t1'} {t2'} ≪IntLoop ≪Refl = ≪Refl
⊓-mono {t1} {BOOL x} {t1'} {t2'} ≪IntLoop ≪Refl = ≪Unknown
⊓-mono {t1} {FAIL} {t1'} {t2'} ≪IntLoop ≪Refl = ≪Unknown
⊓-mono {t1} {UNKNOWN} {t1'} {t2'} ≪IntLoop ≪Refl = ≪Unknown
⊓-mono {t1} {LOOP} {t1'} {t2'} ≪IntLoop ≪Refl = ≪IntLoop
⊓-mono {t1} {t2} {t1'} {t2'} ≪IntLoop ≪Int = ≪Refl
⊓-mono {t1} {t2} {t1'} {t2'} ≪IntLoop ≪Bool = ≪Unknown
⊓-mono {t1} {t2} {t1'} {t2'} ≪IntLoop ≪IntLoop = ≪IntLoop
⊓-mono {t1} {t2} {t1'} {t2'} ≪IntLoop ≪BoolLoop = ≪Unknown
⊓-mono {t1} {t2} {t1'} {t2'} ≪BoolLoop ≪Unknown = ≪Unknown
⊓-mono {t1} {INT x} {t1'} {t2'} ≪BoolLoop ≪Refl = ≪Unknown
⊓-mono {t1} {BOOL x} {t1'} {t2'} ≪BoolLoop ≪Refl = ≪Refl
⊓-mono {t1} {FAIL} {t1'} {t2'} ≪BoolLoop ≪Refl = ≪Unknown
⊓-mono {t1} {UNKNOWN} {t1'} {t2'} ≪BoolLoop ≪Refl = ≪Unknown
⊓-mono {t1} {LOOP} {t1'} {t2'} ≪BoolLoop ≪Refl = ≪BoolLoop
⊓-mono {t1} {t2} {t1'} {t2'} ≪BoolLoop ≪Int = ≪Unknown
⊓-mono {t1} {t2} {t1'} {t2'} ≪BoolLoop ≪Bool = ≪Refl
⊓-mono {t1} {t2} {t1'} {t2'} ≪BoolLoop ≪IntLoop = ≪Unknown
⊓-mono {t1} {t2} {t1'} {t2'} ≪BoolLoop ≪BoolLoop = ≪BoolLoop
⊓-mono {INT tt} {t2} {t1'} {t2'} ≪Refl ≪Int = ≪Refl
⊓-mono {INT ff} {t2} {t1'} {t2'} ≪Refl ≪Int = ≪Int
⊓-mono {BOOL x} {t2} {t1'} {t2'} ≪Refl ≪Int = ≪Unknown
⊓-mono {FAIL} {t2} {t1'} {t2'} ≪Refl ≪Int = ≪Unknown
⊓-mono {UNKNOWN} {t2} {t1'} {t2'} ≪Refl ≪Int = ≪Unknown
⊓-mono {LOOP} {t2} {t1'} {t2'} ≪Refl ≪Int = ≪Refl

⊓-≪1 : ∀{t t' : Type} →
        t ⊓ t' ≪ t 
⊓-≪1 {INT tt} {INT tt} = ≪Refl
⊓-≪1 {INT tt} {INT ff} = ≪Refl
⊓-≪1 {INT ff} {INT tt} = ≪Int
⊓-≪1 {INT ff} {INT ff} = ≪Refl
⊓-≪1 {INT x} {BOOL y} = ≪Unknown
⊓-≪1 {INT x} {FAIL} = ≪Unknown
⊓-≪1 {INT x} {UNKNOWN} = ≪Unknown
⊓-≪1 {INT tt} {LOOP} = ≪Refl
⊓-≪1 {INT ff} {LOOP} = ≪Int
⊓-≪1 {BOOL x} {INT y} = ≪Unknown
⊓-≪1 {BOOL tt} {BOOL tt} = ≪Refl
⊓-≪1 {BOOL tt} {BOOL ff} = ≪Refl
⊓-≪1 {BOOL ff} {BOOL tt} = ≪Bool
⊓-≪1 {BOOL ff} {BOOL ff} = ≪Refl
⊓-≪1 {BOOL x} {FAIL} = ≪Unknown
⊓-≪1 {BOOL x} {UNKNOWN} = ≪Unknown
⊓-≪1 {BOOL tt} {LOOP} = ≪Refl
⊓-≪1 {BOOL ff} {LOOP} = ≪Bool
⊓-≪1 {FAIL} {INT x} = ≪Unknown
⊓-≪1 {FAIL} {BOOL x} = ≪Unknown
⊓-≪1 {FAIL} {FAIL} = ≪Refl
⊓-≪1 {FAIL} {UNKNOWN} = ≪Unknown
⊓-≪1 {FAIL} {LOOP} = ≪Unknown
⊓-≪1 {UNKNOWN} {INT x} = ≪Unknown
⊓-≪1 {UNKNOWN} {BOOL x} = ≪Unknown
⊓-≪1 {UNKNOWN} {FAIL} = ≪Unknown
⊓-≪1 {UNKNOWN} {UNKNOWN} = ≪Unknown
⊓-≪1 {UNKNOWN} {LOOP} = ≪Unknown
⊓-≪1 {LOOP} {INT x} = ≪IntLoop
⊓-≪1 {LOOP} {BOOL x} = ≪BoolLoop
⊓-≪1 {LOOP} {FAIL} = ≪Unknown
⊓-≪1 {LOOP} {UNKNOWN} = ≪Unknown
⊓-≪1 {LOOP} {LOOP} = ≪Refl

⊓-≪2 : ∀{t t' : Type} →
        t ⊓ t' ≪ t' 
⊓-≪2 {INT tt} {INT tt} = ≪Refl
⊓-≪2 {INT tt} {INT ff} = ≪Int
⊓-≪2 {INT ff} {INT tt} = ≪Refl
⊓-≪2 {INT ff} {INT ff} = ≪Refl
⊓-≪2 {INT x} {BOOL y} = ≪Unknown
⊓-≪2 {INT x} {FAIL} = ≪Unknown
⊓-≪2 {INT x} {UNKNOWN} = ≪Unknown
⊓-≪2 {INT tt} {LOOP} = ≪IntLoop
⊓-≪2 {INT ff} {LOOP} = ≪IntLoop
⊓-≪2 {BOOL x} {INT y} = ≪Unknown
⊓-≪2 {BOOL tt} {BOOL tt} = ≪Refl
⊓-≪2 {BOOL tt} {BOOL ff} = ≪Bool
⊓-≪2 {BOOL ff} {BOOL tt} = ≪Refl
⊓-≪2 {BOOL ff} {BOOL ff} = ≪Refl
⊓-≪2 {BOOL x} {FAIL} = ≪Unknown
⊓-≪2 {BOOL x} {UNKNOWN} = ≪Unknown
⊓-≪2 {BOOL tt} {LOOP} = ≪BoolLoop
⊓-≪2 {BOOL ff} {LOOP} = ≪BoolLoop
⊓-≪2 {FAIL} {INT x} = ≪Unknown
⊓-≪2 {FAIL} {BOOL x} = ≪Unknown
⊓-≪2 {FAIL} {FAIL} = ≪Refl
⊓-≪2 {FAIL} {UNKNOWN} = ≪Unknown
⊓-≪2 {FAIL} {LOOP} = ≪Unknown
⊓-≪2 {UNKNOWN} {INT x} = ≪Unknown
⊓-≪2 {UNKNOWN} {BOOL x} = ≪Unknown
⊓-≪2 {UNKNOWN} {FAIL} = ≪Unknown
⊓-≪2 {UNKNOWN} {UNKNOWN} = ≪Unknown
⊓-≪2 {UNKNOWN} {LOOP} = ≪Unknown
⊓-≪2 {LOOP} {INT tt} = ≪Refl
⊓-≪2 {LOOP} {INT ff} = ≪Int
⊓-≪2 {LOOP} {BOOL tt} = ≪Refl
⊓-≪2 {LOOP} {BOOL ff} = ≪Bool
⊓-≪2 {LOOP} {FAIL} = ≪Unknown
⊓-≪2 {LOOP} {UNKNOWN} = ≪Unknown
⊓-≪2 {LOOP} {LOOP} = ≪Refl

arith'-mono : ∀{t1 t2 t1' t2' : Type} →
              t1 ≪ t1' →
              t2 ≪ t2' →
              arith' t1 t2 ≪ arith' t1' t2'
arith'-mono {t1} {t2} {t1'} {t2'} d d' with keep (t1 ⊓ t2) | ⊓-mono d d' | keep (t1' ⊓ t2')
arith'-mono {t1} {t2} {t1'} {t2'} d d' | INT x , e | u | m , e' rewrite e | e' with u 
arith'-mono {t1} {t2} {t1'} {t2'} d d' | INT x , e | _ | m , e' | ≪Refl = ≪Refl
arith'-mono {t1} {t2} {t1'} {t2'} d d' | INT x , e | _ | m , e' | ≪Int = ≪Int
arith'-mono {t1} {t2} {t1'} {t2'} d d' | INT x , e | _ | m , e' | ≪IntLoop = ≪IntLoop
arith'-mono {t1} {t2} {t1'} {t2'} d d' | BOOL tt , e | u | m , e' rewrite e = ≪Unknown
arith'-mono {t1} {t2} {t1'} {t2'} d d' | BOOL ff , e | u | m , e' rewrite e | e' with u 
arith'-mono {t1} {t2} {t1'} {t2'} d d' | BOOL ff , e | _ | m , e' | ≪Refl = ≪Refl
arith'-mono {t1} {t2} {t1'} {t2'} d d' | FAIL , e | u | m , e' rewrite e | e' with u 
arith'-mono {t1} {t2} {t1'} {t2'} d d' | FAIL , e | u | m , e' | ≪Refl = ≪Refl
arith'-mono {t1} {t2} {t1'} {t2'} d d' | UNKNOWN , e | u | m , e' rewrite e = ≪Unknown
arith'-mono {t1} {t2} {t1'} {t2'} d d' | LOOP , e | u | m , e' rewrite e | e' with u 
arith'-mono {t1} {t2} {t1'} {t2'} d d' | LOOP , e | _ | m , e' | ≪Refl = ≪Refl

↑-mono : ∀{b b' : 𝔹}{m m' : Type} →
          b' imp b ≡ tt →
          m ≪ m' → 
          b ↑ m ≪ b' ↑ m'
↑-mono {tt} {tt} {INT x} {INT y} e ≪Refl = ≪Refl
↑-mono {tt} {ff} {INT tt} {INT y} e ≪Refl = ≪Refl
↑-mono {tt} {ff} {INT ff} {INT y} e ≪Refl = ≪Int
↑-mono {ff} {ff} {INT x} {INT y} e ≪Refl = ≪Refl
↑-mono {b} {tt} {INT x} {INT y} e ≪Int rewrite ||-tt b = ≪Refl
↑-mono {b} {ff} {INT x} {INT y} e ≪Int rewrite ||-tt b = ≪Int
↑-mono {b} {b'} {INT x} {LOOP} e ≪IntLoop rewrite ||-tt b = ≪IntLoop
↑-mono {tt} {tt} {BOOL x} {BOOL x₁} e ≪Refl = ≪Refl
↑-mono {tt} {ff} {BOOL tt} {BOOL x₁} e ≪Refl = ≪Refl
↑-mono {tt} {ff} {BOOL ff} {BOOL x₁} e ≪Refl = ≪Bool
↑-mono {ff} {ff} {BOOL x} {BOOL x₁} e ≪Refl = ≪Refl
↑-mono {b} {tt} {BOOL x} {BOOL x₁} e ≪Bool rewrite ||-tt b = ≪Refl
↑-mono {b} {ff} {BOOL x} {BOOL x₁} e ≪Bool rewrite ||-tt b = ≪Bool
↑-mono {b} {b'} {BOOL x} {LOOP} e ≪BoolLoop rewrite ||-tt b = ≪BoolLoop
↑-mono {tt} {tt} {FAIL} {FAIL} e d = ≪Unknown
↑-mono {tt} {ff} {FAIL} {FAIL} e d = ≪Unknown
↑-mono {ff} {ff} {FAIL} {FAIL} e d = ≪Refl
↑-mono {b} {b'} {UNKNOWN} {m'} e d = ≪Unknown
↑-mono {b} {b'} {LOOP} {LOOP} e d = ≪Refl

↑-loop : ∀{m : Type} → tt ↑ m ≪ LOOP
↑-loop {INT x} = ≪IntLoop
↑-loop {BOOL x} = ≪BoolLoop
↑-loop {FAIL} = ≪Unknown
↑-loop {UNKNOWN} = ≪Unknown
↑-loop {LOOP} = ≪Refl

tt-↑ : ∀{m : Type} → tt ↑ m ≪ m 
tt-↑ {INT tt} = ≪Refl
tt-↑ {INT ff} = ≪Int
tt-↑ {BOOL tt} = ≪Refl
tt-↑ {BOOL ff} = ≪Bool
tt-↑ {FAIL} = ≪Unknown
tt-↑ {UNKNOWN} = ≪Unknown
tt-↑ {LOOP} = ≪Refl

ff-↑ : ∀{m : Type} → ff ↑ m ≡ m 
ff-↑ {INT x} = refl
ff-↑ {BOOL x} = refl
ff-↑ {FAIL} = refl
ff-↑ {UNKNOWN} = refl
ff-↑ {LOOP} = refl

cond'-mono : ∀{t1 t2 t3 t1' t2' t3' : Type} →
            t1 ≪ t1' →
            t2 ≪ t2' →
            t3 ≪ t3' →            
            cond' t1 t2 t3 ≪ cond' t1' t2' t3'
cond'-mono {INT tt} {t2} {t3} {t1'} {t2'} {t3'} ≪Refl db dc = ≪Unknown
cond'-mono {INT ff} {t2} {t3} {t1'} {t2'} {t3'} ≪Refl db dc = ≪Refl
cond'-mono {INT x} {t2} {t3} {t1'} {t2'} {t3'} ≪Int db dc = ≪Unknown
cond'-mono {INT tt} {t2} {t3} {LOOP} {t2'} {t3'} ≪IntLoop db dc = ≪Unknown
cond'-mono {BOOL b} {t2} {t3} {t1'} {t2'} {t3'} da db dc with keep (t2 ⊓ t3) | keep (t2' ⊓ t3') | ⊓-mono{t2}{t3}{t2'}{t3'} db dc
cond'-mono {BOOL b} {t2} {t3} {t1'} {t2'} {t3'} da db dc | m , e | m' , e' | qq with qq 
cond'-mono {BOOL tt} {t2} {t3} {BOOL ff} {t2'} {t3'} ≪Bool db dc | m , e | m' , e' | _ | qq rewrite e | e' = ↑-mono refl qq
cond'-mono {BOOL tt} {t2} {t3} {LOOP} {t2'} {t3'} ≪BoolLoop db dc | m , e | m' , e' | _ | qq rewrite e | e' = ↑-loop
cond'-mono {BOOL b} {t2} {t3} {BOOL b} {t2'} {t3'} ≪Refl db dc | m , e | m' , e' | _ | qq rewrite e | e' = ↑-mono (imp-same b) qq
cond'-mono {FAIL} {t2} {t3} {t2'} {t1'} {t3'} ≪Refl db dc = ≪Refl
cond'-mono {UNKNOWN} {t2} {t3} {t1'} {t2'} {t3'} ≪Unknown db dc = ≪Unknown
cond'-mono {UNKNOWN} {t2} {t3} {t1'} {t2'} {t3'} ≪Refl db dc = ≪Unknown
cond'-mono {LOOP} {t2} {t3} {t1'} {t2'} {t3'} ≪Refl db dc = ≪Refl

tval-cond : ∀{v1 v2 v3 : Value} →
                 cond' (tval v1) (tval v2) (tval v3) ≪ tval (cond v1 v2 v3)
tval-cond {I x} {v2} {v3} = ≪Refl
tval-cond {B tt} {v2} {v3} rewrite ff-↑{tval v2 ⊓ tval v3} = ⊓-≪1
tval-cond {B ff} {v2} {v3} rewrite ff-↑{tval v2 ⊓ tval v3} = ⊓-≪2
tval-cond {Fail} {v2} {v3} = ≪Refl
tval-cond {Loop} {v2} {v3} = ≪Refl

arith'-INT1 : ∀{t1 t2 : Type}{b : 𝔹} → 
                 INT b ≪ (arith' t1 t2) →
                 ∃ 𝔹 (λ b' → INT b' ≪ t1)
arith'-INT1 {INT x} {t2} e = x , ≪Refl
arith'-INT1 {BOOL tt} {BOOL tt} ()
arith'-INT1 {BOOL tt} {BOOL ff} () 
arith'-INT1 {BOOL ff} {BOOL tt} ()
arith'-INT1 {BOOL ff} {BOOL ff} ()
arith'-INT1 {FAIL} {INT x} ()
arith'-INT1 {FAIL} {BOOL x} ()
arith'-INT1 {FAIL} {FAIL} ()
arith'-INT1 {FAIL} {UNKNOWN} ()
arith'-INT1 {FAIL} {LOOP} ()
arith'-INT1 {LOOP} {_} e = tt , ≪IntLoop

arith'-INT2 : ∀{t1 t2 : Type}{b : 𝔹} → 
               INT b ≪ (arith' t1 t2) →
               ∃ 𝔹 (λ b' → INT b' ≪ t2)
arith'-INT2 {t2}{INT x} e = x , ≪Refl
arith'-INT2 {BOOL tt} {BOOL tt} ()
arith'-INT2 {BOOL tt} {BOOL ff} () 
arith'-INT2 {BOOL ff} {BOOL tt} ()
arith'-INT2 {BOOL ff} {BOOL ff} ()
arith'-INT2 {UNKNOWN} {BOOL x} ()
arith'-INT2 {UNKNOWN} {FAIL} ()
arith'-INT2 {UNKNOWN} {UNKNOWN} ()
arith'-INT2 {UNKNOWN} {LOOP} ()
arith'-INT2 {FAIL} {BOOL x} ()
arith'-INT2 {FAIL} {FAIL} ()
arith'-INT2 {FAIL} {UNKNOWN} ()
arith'-INT2 {FAIL} {LOOP} ()
arith'-INT2 {_}{LOOP} e = tt , ≪IntLoop


-- INT b ≪ cond' (texp e) (texp e₁) (texp e₂)

{-

mutual 
 eval-sign-pos : ∀{g : ℕ}{e : Expr}{b : 𝔹} → 
                 sign e ≡ Pos →
                 INT b ≪ texp e → 
                 ∃ ℕ (λ n → eval g e g ≡ I (toℤ (suc n)))
 eval-sign-pos {g} {I (mkℤ (suc n) tt)} q w = n , refl
 eval-sign-pos {g} {Arith Add e1 e2} q w with arith'-INT1{texp e1}{texp e2} w | arith'-INT2{texp e1}{texp e2} w | keep (sign e1) | keep (sign e2)
 eval-sign-pos {g} {Arith Add e1 e2} q w | b1 , q1 | b2 , q2 | Pos , u1 | Pos , u2 
   with eval-sign-pos{g}{e1}{b1} u1 q1 | eval-sign-pos{g}{e2}{b2} u2 q2 
 eval-sign-pos {g} {Arith Add e1 e2} q w | b1 , q1 | b2 , q2 | Pos , u1 | Pos , u2 | n1 , p1 | n2 , p2 rewrite p1 | p2 = n1 + suc n2 , refl
 eval-sign-pos {g} {Arith Add e1 e2} q w | b1 , q1 | b2 , q2 | Pos , u1 | Nonneg , u2 rewrite u1 | u2 
   with eval-sign-pos{g}{e1} u1 q1 | eval-sign-nonneg{g}{e2} u2 q2
 eval-sign-pos {g} {Arith Add e1 e2} q w | b1 , q1 | b2 , q2 | Pos , u1 | Nonneg , u2 | m1 , v1 | 0 , v2 rewrite v1 | v2 = m1 , refl
 eval-sign-pos {g} {Arith Add e1 e2} q w | b1 , q1 | b2 , q2 | Pos , u1 | Nonneg , u2 | m1 , v1 | suc m2 , v2 rewrite v1 | v2 = m1 + suc m2 , refl
 eval-sign-pos {g} {Arith Add e1 e2} q w | b1 , q1 | b2 , q2 | Pos , u1 | Unknown , u2 rewrite u1 | u2 with q
 eval-sign-pos {g} {Arith Add e1 e2} q w | b1 , q1 | b2 , q2 | Pos , u1 | Unknown , u2 | ()
 eval-sign-pos {g} {Arith Add e1 e2} q w | b1 , q1 | b2 , q2 | Nonneg , u1 | Pos , u2 rewrite u1 | u2
   with eval-sign-nonneg{g}{e1} u1 q1 | eval-sign-pos{g}{e2} u2 q2
 eval-sign-pos {g} {Arith Add e1 e2} q w | b1 , q1 | b2 , q2 | Nonneg , u1 | Pos , u2 | 0 , v1 | m2 , v2 rewrite v1 | v2 = m2 , refl
 eval-sign-pos {g} {Arith Add e1 e2} q w | b1 , q1 | b2 , q2 | Nonneg , u1 | Pos , u2 | suc m1 , v1 | m2 , v2 rewrite v1 | v2 = m1 + suc m2 , refl
 eval-sign-pos {g} {Arith Add e1 e2} q w | b1 , q1 | b2 , q2 | Nonneg , u1 | Nonneg , u2 rewrite u1 | u2 with q
 eval-sign-pos {g} {Arith Add e1 e2} q w | b1 , q1 | b2 , q2 | Nonneg , u1 | Nonneg , u2 | ()
 eval-sign-pos {g} {Arith Add e1 e2} q w | b1 , q1 | b2 , q2 | Nonneg , u1 | Unknown , u2 rewrite u1 | u2 with q
 eval-sign-pos {g} {Arith Add e1 e2} q w | b1 , q1 | b2 , q2 | Nonneg , u1 | Unknown , u2 | ()
 eval-sign-pos {g} {Arith Add e1 e2} q w | b1 , q1 | b2 , q2 | Unknown , u1 | Pos , u2 rewrite u1 | u2 with q
 eval-sign-pos {g} {Arith Add e1 e2} q w | b1 , q1 | b2 , q2 | Unknown , u1 | Pos , u2 | ()
 eval-sign-pos {g} {Arith Add e1 e2} q w | b1 , q1 | b2 , q2 | Unknown , u1 | Nonneg , u2 rewrite u1 | u2 with q
 eval-sign-pos {g} {Arith Add e1 e2} q w | b1 , q1 | b2 , q2 | Unknown , u1 | Nonneg , u2 | ()
 eval-sign-pos {g} {Arith Add e1 e2} q w | b1 , q1 | b2 , q2 | Unknown , u1 | Unknown , u2 rewrite u1 | u2 with q
 eval-sign-pos {g} {Arith Add e1 e2} q w | b1 , q1 | b2 , q2 | Unknown , u1 | Unknown , u2 | ()
 eval-sign-pos {g} {Arith Mult e1 e2} q w with arith'-INT1{texp e1}{texp e2} w | arith'-INT2{texp e1}{texp e2} w | keep (sign e1) | keep (sign e2)
 eval-sign-pos {g} {Arith Mult e1 e2} q w | b1 , q1 | b2 , q2 | Pos , u1 | Pos , u2 with eval-sign-pos{g}{e1} u1 q1 | eval-sign-pos{g}{e2} u2 q2
 eval-sign-pos {g} {Arith Mult e1 e2} q w | b1 , q1 | b2 , q2 | Pos , u1 | Pos , u2 | m1 , v1 | m2 , v2 rewrite v1 | v2 = m2 + m1 * suc m2 , refl
 eval-sign-pos {g} {Arith Mult e1 e2} q w | b1 , q1 | b2 , q2 | Pos , u1 | Nonneg , u2 rewrite u1 | u2 with q
 eval-sign-pos {g} {Arith Mult e1 e2} q w | b1 , q1 | b2 , q2 | Pos , u1 | Nonneg , u2 | ()
 eval-sign-pos {g} {Arith Mult e1 e2} q w | b1 , q1 | b2 , q2 | Pos , u1 | Unknown , u2 rewrite u1 | u2 with q
 eval-sign-pos {g} {Arith Mult e1 e2} q w | b1 , q1 | b2 , q2 | Pos , u1 | Unknown , u2 | ()
 eval-sign-pos {g} {Arith Mult e1 e2} q w | b1 , q1 | b2 , q2 | Nonneg , u1 | Pos , u2 rewrite u1 | u2 with q
 eval-sign-pos {g} {Arith Mult e1 e2} q w | b1 , q1 | b2 , q2 | Nonneg , u1 | Pos , u2 | ()
 eval-sign-pos {g} {Arith Mult e1 e2} q w | b1 , q1 | b2 , q2 | Nonneg , u1 | Nonneg , u2 rewrite u1 | u2 with q
 eval-sign-pos {g} {Arith Mult e1 e2} q w | b1 , q1 | b2 , q2 | Nonneg , u1 | Nonneg , u2 | ()
 eval-sign-pos {g} {Arith Mult e1 e2} q w | b1 , q1 | b2 , q2 | Nonneg , u1 | Unknown , u2 rewrite u1 | u2 with q
 eval-sign-pos {g} {Arith Mult e1 e2} q w | b1 , q1 | b2 , q2 | Nonneg , u1 | Unknown , u2 | ()
 eval-sign-pos {g} {Arith Mult e1 e2} q w | b1 , q1 | b2 , q2 | Unknown , u1 | Pos , u2 rewrite u1 | u2 with q 
 eval-sign-pos {g} {Arith Mult e1 e2} q w | b1 , q1 | b2 , q2 | Unknown , u1 | Pos , u2 | ()
 eval-sign-pos {g} {Arith Mult e1 e2} q w | b1 , q1 | b2 , q2 | Unknown , u1 | Nonneg , u2 rewrite u1 | u2 with q
 eval-sign-pos {g} {Arith Mult e1 e2} q w | b1 , q1 | b2 , q2 | Unknown , u1 | Nonneg , u2 | ()
 eval-sign-pos {g} {Arith Mult e1 e2} q w | b1 , q1 | b2 , q2 | Unknown , u1 | Unknown , u2 rewrite u1 | u2 with q
 eval-sign-pos {g} {Arith Mult e1 e2} q w | b1 , q1 | b2 , q2 | Unknown , u1 | Unknown , u2 | ()
 eval-sign-pos {g} {If e e₁ e₂} q w = {!!}
 eval-sign-pos {g} {Search e} q w = {!!}

 eval-sign-nonneg : ∀{g : ℕ}{e : Expr}{b : 𝔹} → 
                    sign e ≡ Nonneg →
                    INT b ≪ texp e → 
                    ∃ ℕ (λ n → eval g e g ≡ I (toℤ n))
 eval-sign-nonneg{g}{e} q = {!!}

tval-search-var : ∀{g g' : ℕ} → INT tt ≪ tval (search g g' Var)
tval-search-var {g}{zero} = ≪Int
tval-search-var {g}{suc g'} = tval-search-var{g}{g'}

search-LOOP : ∀{g g' n : ℕ}{b : 𝔹} →
              search g g' (I (mkℤ (suc n) b)) ≡ Loop
search-LOOP {g} {zero} = refl
search-LOOP {g} {suc g'} = search-LOOP{g}{g'}



tval-search : ∀{e : Expr}{g v : ℕ} →
              search' (tval (eval g e v)) (sign e) ≪ tval (search g g e)
tval-search {Var} {g}{v} = tval-search-var{g}{g}
tval-search {I (mkℤ zero triv)} {g} = ≪Int
tval-search {I (mkℤ (suc n) tt)} {g} rewrite search-LOOP{g}{g}{n}{tt} = ≪Refl
tval-search {I (mkℤ (suc n) ff)} {g} rewrite search-LOOP{g}{g}{n}{ff} = ≪IntLoop
tval-search {B x} {g} = ≪Refl
tval-search {Arith Add e e₁} {g} = {!!}
tval-search {Arith Mult e e₁} {g} = {!!}
tval-search {If e e₁ e₂} {g} = {!!}
tval-search {Search e} {g} = {!!}

-}

search'-mono : ∀{t t' : Type}{s : Sign} →
               t ≪ t' →
               search' t s ≪ search' t' s
search'-mono d = {!!}


texp-soundness : ∀{e : Expr}{g v : ℕ} →
            texp e ≪ tval (eval g e v)
texp-soundness {Val x} = ≪Refl
texp-soundness {Arith op e1 e2} = ≪-trans (arith'-mono (texp-soundness {e1}) (texp-soundness {e2})) tval-arith
texp-soundness {If e1 e2 e3}{g}{v} =
  ≪-trans (cond'-mono (texp-soundness{e1}) (texp-soundness{e2}) (texp-soundness{e3}))
          (tval-cond{eval g e1 v})
texp-soundness {Var} = ≪Refl
texp-soundness {Search e}{g}{v} = 
  ≪-trans (search'-mono (texp-soundness{e}{g}{g}))
           {!!}
