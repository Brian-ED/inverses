module plus where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Bool using (Bool; not; true; false)
open import Data.Rational using (ℚ; _+_; _-_) renaming (-_ to neg_)
open import Data.Integer using (pos; ℤ)
open import Data.Rational.Properties as ℤₚ
open import Data.Nat.Coprimality using (coprime-/gcd)
zero = (Data.Rational.mkℚ (ℤ.pos 0) 0 (coprime-/gcd 0 1))

open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ)

open import Function

data Primitive : Set where
  num : ℚ → Primitive
--  plus : Primitive
  plusC : ℚ → Primitive
--  inv : Primitive → Primitive
  err : Primitive → Primitive
  call : Primitive → Primitive → Primitive

eval : Primitive → Primitive
eval (call (num x) snd) = err (call (num x) snd)
eval (call (plusC x) (num x₁)) = call (plusC x) (num (x₁ + x))
eval (call (plusC x) (plusC x₁)) = err (call (plusC x) (plusC x₁))
eval (call (plusC x) (err snd)) = err (call (plusC x) (err snd))
eval (call (plusC x) (call snd snd₁)) = err (call (plusC x) (call snd snd₁))
eval (call (err x) snd) = err (call (err x) snd)
eval (call (call x x₁) snd) = err (call (call x x₁) snd)
eval (num x  ) = err (num x)
eval (err (num x)) = num x
eval (err (err x)) = err (err x)
eval (err (call (num x) x₁)) = call (num x) x₁
eval (err (call (plusC x) (num x₁))) = err (call (plusC x) (num x₁))
eval (err (call (plusC x) (plusC x₁))) = call (plusC x) (plusC x₁)
eval (err (call (plusC x) (err x₁))) = call (plusC x) (err x₁)
eval (err (call (plusC x) (call x₁ x₂))) = call (plusC x) (call x₁ x₂)
eval (err (call (err x) x₁)) = call (err x) x₁
eval (err (call (call x x₂) x₁)) = call (call x x₂) x₁
eval (plusC x) = err (plusC x)
eval (err (plusC x)) = plusC x

unEval : Primitive → Primitive
unEval (num x) = err (num x)
unEval (err (num x)) = num x
unEval (err (err x)) = err (err x)
unEval (err (call (num x) x₁)) = call (num x) x₁
unEval (err (call (plusC x) (num x₁))) = err (call (plusC x) (num x₁))
unEval (err (call (plusC x) (plusC x₁))) = call (plusC x) (plusC x₁)
unEval (err (call (plusC x) (err x₁))) = call (plusC x) (err x₁)
unEval (err (call (plusC x) (call x₁ x₂))) = (call (plusC x) (call x₁ x₂))
unEval (err (call (err x) x₁)) = call (err x) x₁
unEval (err (call (call x x₂) x₁)) = call (call x x₂) x₁
unEval (call (num x) x₁) = err (call (num x) x₁)
unEval (call (plusC x) (num x₁)) = call (plusC x) (num (x₁ - x))
unEval (call (plusC x) (plusC x₁)) = err (call (plusC x) (plusC x₁))
unEval (call (plusC x) (err x₁)) = err (call (plusC x) (err x₁))
unEval (call (plusC x) (call x₁ x₂)) = err (call (plusC x) (call x₁ x₂))
unEval (call (err x) x₁) = err (call (err x) x₁)
unEval (call (call x x₂) x₁) = err (call (call x x₂) x₁) -- err (call x x₁)
unEval (plusC x) = err (plusC x)
unEval (err (plusC x)) = plusC x

open import Level using (_⊔_) renaming (suc to lsuc; zero to lzero)
open import Data.Unit using (⊤)

proveCongruenceEval : Congruent _≡_ _≡_ eval
proveCongruenceEval refl = refl

proveCongruenceUnEval : Congruent _≡_ _≡_ unEval
proveCongruenceUnEval refl = refl

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning

+-cancel :
  ∀ x x₁ →
  x₁ + (neg x) + x ≡ x₁
+-cancel x x₁ = begin
    x₁ + (neg x) + x
  ≡⟨ ℤₚ.+-assoc x₁ (neg x) x ⟩
    x₁ + ((neg x) + x)
  ≡⟨ cong (x₁ +_) (ℤₚ.+-inverseˡ x) ⟩
    x₁ + zero
  ≡⟨ +-identityʳ x₁ ⟩
    x₁
  ∎

-+cancel :
  ∀ x x₁ →
  x₁ + x + (neg x) ≡ x₁
-+cancel x x₁ = begin
    x₁ + x + (neg x)
  ≡⟨ ℤₚ.+-assoc x₁ x (neg x) ⟩
    x₁ + (x + (neg x))
  ≡⟨ cong (x₁ +_) (ℤₚ.+-inverseʳ x) ⟩
    x₁ + zero
  ≡⟨ +-identityʳ x₁ ⟩
    x₁
  ∎

proofOfPlusC-L : ∀{x x₁} → eval (unEval (call (plusC x) (num x₁))) ≡ call (plusC x) (num x₁)
proofOfPlusC-L {x} {x₁} = cong (call (plusC x) ∘ num) (+-cancel x x₁)
proofOfPlusC-R : ∀{x x₁} → unEval (eval (call (plusC x) (num x₁))) ≡ call (plusC x) (num x₁)
proofOfPlusC-R {x} {x₁} = cong (call (plusC x) ∘ num) (-+cancel x x₁)

lInv : {x : Primitive} → eval (unEval x) ≡ x
lInv {num x} = refl
lInv {err (num x)} = refl
lInv {err (err (num x))} = refl
lInv {err (err (err x))} = refl
lInv {err (err (call x x₁))} = refl
lInv {err (call (num x) x₁)} = refl
lInv {err (call (plusC x) (num x₁))} = refl
lInv {err (call (plusC x) (plusC x₁))} = refl
lInv {err (call (plusC x) (err x₁))} = refl
lInv {err (call (plusC x) (call x₁ x₂))} = refl
lInv {err (call (err x) x₁)} = refl
lInv {err (call (call x x₂) x₁)} = refl
lInv {call (num x) x₁} = refl
lInv {call (plusC x) (num x₁)} = proofOfPlusC-L
lInv {call (plusC x) (plusC x₁)} = refl
lInv {call (plusC x) (err x₁)} = refl
lInv {call (plusC x) (call x₁ x₂)} = refl
lInv {call (err x) x₁} = refl
lInv {call (call x x₂) x₁} = refl
lInv {plusC x} = refl
lInv {err (plusC x)} = refl
lInv {err (err (plusC x))} = refl

rInv : {x : Primitive} → unEval (eval x) ≡ x
rInv {num x} = refl
rInv {err (num x)} = refl
rInv {err (err x)} = refl
rInv {err (call (num x) x₁)} = refl
rInv {err (call (plusC x) (num x₁))} = refl
rInv {err (call (plusC x) (plusC x₁))} = refl
rInv {err (call (plusC x) (err x₁))} = refl
rInv {err (call (plusC x) (call x₁ x₂))} = refl
rInv {err (call (err x) x₁)} = refl
rInv {err (call (call x x₂) x₁)} = refl
rInv {call (num x) x₁} = refl
rInv {call (err x) x₁} = refl
rInv {call (call x x₂) x₁} = refl
rInv {plusC x} = refl
rInv {err (plusC x)} = refl
rInv {call (plusC x) (num x₁)} = proofOfPlusC-R
rInv {call (plusC x) (plusC x₁)} = refl
rInv {call (plusC x) (err x₁)} = refl
rInv {call (plusC x) (call x₁ x₂)} = refl

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
