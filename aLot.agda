module aLot where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Function.Indexed.Relation.Binary.Equality using (≡-setoid)
open import Relation.Binary using (Setoid)
open import Data.Bool using (Bool; not; true; false)
open import Data.Rational using (ℚ; _+_; _-_) renaming (-_ to neg_)
open import Data.Integer using (pos; ℤ)
open import Data.Nat.Coprimality using (coprime-/gcd)
open import Level using (Level) renaming (zero to lzero)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ)
open import Function using (_∘_; Inverseˡ; Inverseʳ; Inverse)

import Data.Rational.Properties as ℤₚ

zero = Data.Rational.mkℚ (ℤ.pos 0) 0 (coprime-/gcd 0 1)

data Primitive : Set where
  num : ℚ → Primitive
  plusC : ℚ → Primitive
  err : Primitive → Primitive
  call : Primitive → Primitive → Primitive

eval : Primitive → Primitive
eval (call (plusC x) (num x₁)) = call (plusC x) (num (x₁ + x))
eval (err (err x)) = err (err x)
eval (err (call (plusC x) (num x₁))) = err (call (plusC x) (num x₁))
eval (err x) = x
eval x = err x

unEval : Primitive → Primitive
unEval (call (plusC x) (num x₁)) = call (plusC x) (num (x₁ - x))
unEval (err (err x)) = err (err x)
unEval (err (call (plusC x) (num x₁))) = err (call (plusC x) (num x₁))
unEval (err x) = x
unEval x = err x

infixr 2 _≡⟨_⟩_

_≡⟨_⟩_ : {a : Level} {A : Set a} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
_≡⟨_⟩_ x y z = trans y z

+-cancel : ∀ x x₁ → x₁ + (neg x) + x ≡ x₁
+-cancel x x₁ =
    x₁ + neg x + x
  ≡⟨ ℤₚ.+-assoc x₁ (neg x) x ⟩
    x₁ + (neg x + x)
  ≡⟨ cong (x₁ +_) (ℤₚ.+-inverseˡ x) ⟩
    x₁ + zero
  ≡⟨ ℤₚ.+-identityʳ x₁ ⟩
    refl

-+cancel : ∀ x x₁ → x₁ + x + (neg x) ≡ x₁
-+cancel x x₁ =
    x₁ + x + (neg x)
  ≡⟨ ℤₚ.+-assoc x₁ x (neg x) ⟩
    x₁ + (x + neg x)
  ≡⟨ cong (x₁ +_) (ℤₚ.+-inverseʳ x) ⟩
    x₁ + zero
  ≡⟨ ℤₚ.+-identityʳ x₁ ⟩
    refl


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
lInv {call (plusC x) (num x₁)} = cong (call (plusC x) ∘ num) (+-cancel x x₁)
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
rInv {call (plusC x) (num x₁)} = cong (call (plusC x) ∘ num) (-+cancel x x₁)
rInv {call (plusC x) (plusC x₁)} = refl
rInv {call (plusC x) (err x₁)} = refl
rInv {call (plusC x) (call x₁ x₂)} = refl

matchSetoid : Setoid lzero lzero
matchSetoid = record
  { Carrier = Primitive
  ; _≈_ = _≡_
  ; isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
  }

x : Inverse matchSetoid matchSetoid
x = record
  { to = eval
  ; from = unEval
  ; to-cong = cong eval
  ; from-cong = cong unEval
  ; inverse = proveLInv , proveRInv
  }
    where
      proveLInv : Inverseˡ _≡_ _≡_ eval unEval
      proveLInv refl = lInv

      proveRInv : Inverseʳ _≡_ _≡_ eval unEval
      proveRInv refl = rInv
