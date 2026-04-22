module xor where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid)
open import Relation.Binary using (Setoid)
open import Function using (Inverse)
open import Data.Bool using (Bool; true; false; not)
open import Data.Product using (proj₁; proj₂; _,_; _×_)

_≠_ : Bool → Bool → Bool
false ≠ x = x
true ≠ x = not x

xor : Bool × Bool → Bool × Bool
xor (fst , snd) = fst , (fst ≠ snd)

xorInv : ∀ {x} → xor (xor x) ≡ x
xorInv {false , false} = refl
xorInv {false , true} = refl
xorInv {true , false} = refl
xorInv {true , true} = refl

areInv : Inverse (setoid (Bool × Bool)) (setoid (Bool × Bool))
areInv .Inverse.to = xor
areInv .Inverse.from = xor
areInv .Inverse.to-cong = cong xor
areInv .Inverse.from-cong = cong xor
areInv .Inverse.inverse .proj₁ refl = xorInv
areInv .Inverse.inverse .proj₂ refl = xorInv
