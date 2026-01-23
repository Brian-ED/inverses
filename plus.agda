module plus where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary.Negation using (¬_)
open import Data.Bool using (Bool; not; true; false)
open import Data.Rational using (ℚ; _+_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ)
open import Function

data Primitive : Set where
  num : ℚ → Primitive
--  plus : Primitive
--  plusC : ℚ → Primitive
--  inv : Primitive → Primitive
  err : Primitive → Primitive
  pair : Primitive → Primitive → Primitive

eval : Σ Primitive WellFormed → Σ Primitive WellFormed
eval (num x , snd) = (err (num x)) , (wf-err-num snd)
eval (err fst , snd) = (err (err fst)) , wf-err-err snd
eval (errI fst , snd) = fst , wf-err-errI snd
eval (pair fst fst₁ , snd) = (err (pair fst fst₁)) , wf-err-pair snd

-- (num x) , wf-err-errI wf-errI-num wf-num
-- (num x) , wf-num

unEval : Σ Primitive WellFormed → Σ Primitive WellFormed
unEval (num x , snd) = (errI (num x)) , (wf-errI-num snd)
unEval (err fst , snd) = fst , wf-errI-err snd
unEval (errI fst , snd) = errI (errI fst) , wf-errI-errI snd
unEval (pair fst fst₁ , snd) = errI (pair fst fst₁) , wf-errI-pair snd

open import Level using (_⊔_) renaming (suc to lsuc; zero to lzero)
open import Data.Unit using (⊤)

proveCongruenceEval : Congruent _≡_ _≡_ eval
proveCongruenceEval refl = refl

proveCongruenceUnEval : Congruent _≡_ _≡_ unEval
proveCongruenceUnEval refl = refl

lInv : {x : Σ Primitive WellFormed} → eval (unEval x) ≡ x
lInv {num x , wf-num} = {!   !}
lInv {num x , wf-err-errI snd} = {!   !}
lInv {num x , wf-errI-err snd} = {!   !}
lInv {err fst , snd} = {!   !}
lInv {errI fst , snd} = {!   !}
lInv {pair fst fst₁ , snd} = {!   !}

proveLInv : Inverseˡ _≡_ _≡_ eval unEval
proveLInv refl = lInv

proveRInv : Inverseʳ _≡_ _≡_ eval unEval
proveRInv refl = {!   !}

x : Inverse
      (record { Carrier = Σ Primitive WellFormed ; _≈_ = _≡_ ; isEquivalence = record { refl = refl ; sym = sym ; trans = trans } })
      (record { Carrier = Σ Primitive WellFormed ; _≈_ = _≡_ ; isEquivalence = record { refl = refl ; sym = sym ; trans = trans } })
x = record
  { to = eval
  ; from = unEval
  ; to-cong = proveCongruenceEval
  ; from-cong = proveCongruenceUnEval
  ; inverse = proveLInv , proveRInv
  }


--leftInv  : ∀ b → eval (unEval b) ≡ b
--leftInv ((plus , snd₁) , inj₁ x) = {!   !}
--leftInv ((plus , snd₁) , inj₂ y) = {!   !}
--leftInv ((plusC x , snd₁) , snd) = {!   !}

--rightInv : ∀ a → unEval (eval a) ≡ a
--rightInv = {!   !}

{-

Evaluators are functions from expr → output. Evaluators that can be inverted must the be output → expr. That means the expr is not what we will be inverting, instead it is `→`.

F : ℚ → ℚ → ℚ
cannot invert  F x → (F , x)  because ?
Could invert  Apply ((F , x) , x) → (F , x) , x , o  


-}
