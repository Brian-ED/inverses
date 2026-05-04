module Core.Primitives.Plus where

open import Data.Integer using (_+_; _-_) renaming (-_ to ¯_)
import Data.Integer.Properties as ℤp
open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong) renaming (trans to infixl 10 _»≡«_)

open import Core.Value using (enum)
open import Core.Primitive using (Primitive)
open import Core.DyadInt using (intFuncToPrim)

_-˜_ = λ x y → y - x

l : ∀ x y → x -˜ (x + y) ≡ y
l x y = cong (_+ ¯ x) (ℤp.+-comm x y)
    »≡« ℤp.+-assoc y x (¯ x)
    »≡« cong (y +_) (ℤp.+-inverseʳ x)
    »≡« ℤp.+-identityʳ y

r : ∀ x y → x + (x -˜ y) ≡ y
r x y = sym (ℤp.+-assoc x y (¯ x)) »≡« l x y

+ₚ : Primitive 2 2
+ₚ = intFuncToPrim _+_ _-˜_ r l (enum 0)
