module plus where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Bool using (Bool; not; true; false)
open import Data.Rational using (ℚ; _+_)
open import Data.Product using (_×_; _,_)
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

eval : Primitive → Primitive
eval (pair x snd) = err (pair x snd)
eval (num x  ) = err (num x)
eval (err (num x)) = num x
eval (err (err x)) = err (err x)
eval (err (pair x x₁)) = pair x x₁

unEval : Primitive → Primitive
unEval (num x) = err (num x)
unEval (err (num x)) = num x
unEval (err (err x)) = err (err x)
unEval (err (pair x x₁)) = pair x x₁
unEval (pair x x₁) = err (pair x x₁)
--unEval plus = err plus
--unEval (plusC x) = err (plusC x)

open import Level using (_⊔_) renaming (suc to lsuc; zero to lzero)
open import Data.Unit using (⊤)

proveCongruenceEval : Congruent _≡_ _≡_ eval
proveCongruenceEval refl = refl

proveCongruenceUnEval : Congruent _≡_ _≡_ unEval
proveCongruenceUnEval refl = refl

lInv : {x : Primitive} → eval (unEval x) ≡ x
lInv {num x} = refl
lInv {err (num x)} = refl
lInv {err (err (num x))} = refl
lInv {err (err (err x))} = refl
lInv {err (err (pair x x₁))} = refl
lInv {err (pair x x₁)} = refl
lInv {pair x x₁} = refl

rInv : {x : Primitive} → unEval (eval x) ≡ x
rInv {num x} = refl
rInv {err (num x)} = refl
rInv {err (err x)} = refl
rInv {err (pair x x₁)} = refl
rInv {pair (num x) x₁} = refl
rInv {pair (err x) x₁} = refl
rInv {pair (pair x x₂) x₁} = refl

proveLInv : Inverseˡ _≡_ _≡_ eval unEval
proveLInv refl = lInv

proveRInv : Inverseʳ _≡_ _≡_ eval unEval
proveRInv refl = rInv

x : Inverse
      (record { Carrier = Primitive ; _≈_ = _≡_ ; isEquivalence = record { refl = refl ; sym = sym ; trans = trans } })
      (record { Carrier = Primitive ; _≈_ = _≡_ ; isEquivalence = record { refl = refl ; sym = sym ; trans = trans } })
x = record
  { to = eval
  ; from = unEval
  ; to-cong = proveCongruenceEval
  ; from-cong = proveCongruenceUnEval
  ; inverse = proveLInv , proveRInv
  }

