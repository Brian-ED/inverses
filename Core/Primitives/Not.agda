module Core.Primitives.Not where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid)
open import Relation.Binary using (Setoid)
open import Function using (Inverse)
open import Data.Bool using (Bool; true; false; not)
open import Data.Product using (proj₁; proj₂)

notInv : ∀ {x} → not (not x) ≡ x
notInv {false} = refl
notInv {true} = refl

areInv : Inverse (setoid Bool) (setoid Bool)
areInv .Inverse.to = not
areInv .Inverse.from = not
areInv .Inverse.to-cong = cong not
areInv .Inverse.from-cong = cong not
areInv .Inverse.inverse .proj₁ refl = notInv
areInv .Inverse.inverse .proj₂ refl = notInv
