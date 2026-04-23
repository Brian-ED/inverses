module xor where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid)
open import Relation.Binary using (Setoid)
open import Function using (Inverse)
open import Data.Bool using (Bool; true; false; not)
open import Data.Product using (proj₁; proj₂; _,_; _×_)

_≠_ : Bool → Bool → Bool
false ≠ x = x
true ≠ x = not x

xorInv : ∀ curry → ∀ {x} → curry ≠ (curry ≠ x) ≡ x
xorInv false {false} = refl
xorInv false {true} = refl
xorInv true {false} = refl
xorInv true {true} = refl

areInv : ∀ curry → Inverse (setoid Bool) (setoid Bool)
areInv curry .Inverse.to = curry ≠_
areInv curry .Inverse.from = curry ≠_
areInv curry .Inverse.to-cong = cong (curry ≠_)
areInv curry .Inverse.from-cong = cong (curry ≠_)
areInv curry .Inverse.inverse .proj₁ refl = xorInv curry
areInv curry .Inverse.inverse .proj₂ refl = xorInv curry
