module Core.Primitives where

import Data.Integer as ℤ
import Data.Integer.Properties as ℤp
import Data.Nat as ℕ
import Data.List as L
open import Data.String using (String)


data Statement : Set where
  xxx : Statement

data errType : Set where
  plus : errType

data Value : Set where
  list : (li : L.List Value) → Value
  int : (i : ℤ.ℤ) → Value
  string : (str : String) → Value
  function : (args : L.List String) → (stmt : Statement) → Value
  error : (t : errType) → (arg : Value) → Value

open import Data.Product using (Σ; ∃; _,_)

Stack : ℕ.ℕ → Set
Stack n = Σ (L.List Value) (λ s → n ℕ.≤ L.length s)

+˙ : (s : Stack 2) → Stack 2
+˙ (x L.∷ L.[] , ℕ.s≤s ())
+˙ (int i₁ L.∷ int i₂ L.∷ s , l) = int (i₁ ℤ.+ i₂) L.∷ int i₂ L.∷ s , l
+˙ (error plus (error plus x) L.∷ s , l) = error plus (error plus x) L.∷ s , l
+˙ (error plus (int i₁) L.∷ int i₂ L.∷ s , l) = error plus (int i₁) L.∷ int i₂ L.∷ s , l
+˙ (error plus v₁ L.∷ v₂ L.∷ s , l) = v₁ L.∷ v₂ L.∷ s , l
+˙ (v₁ L.∷ v₂ L.∷ s , l) = error plus v₁ L.∷ v₂ L.∷ s , l

+⁼ : (s : Stack 2) → Stack 2
+⁼ (x L.∷ L.[] , ℕ.s≤s ())
+⁼ (int i₁ L.∷ int i₂ L.∷ s , l) = int (i₁ ℤ.- i₂) L.∷ int i₂ L.∷ s , l
+⁼ (error plus (error plus x) L.∷ s , l) = error plus (error plus x) L.∷ s , l
+⁼ (error plus (int i₁) L.∷ int i₂ L.∷ s , l) = error plus (int i₁) L.∷ int i₂ L.∷ s , l
+⁼ (error plus v₁ L.∷ v₂ L.∷ s , l) = v₁ L.∷ v₂ L.∷ s , l
+⁼ (v₁ L.∷ v₂ L.∷ s , l) = error plus v₁ L.∷ v₂ L.∷ s , l

module _ where
  open import Relation.Binary.PropositionalEquality using (_≡_; sym; refl; cong; setoid)
  open import Relation.Binary using (Setoid)
  open import Function using (Inverse)
  open import Data.Bool using (Bool; true; false; not)
  open import Data.Product using (proj₁; proj₂)

  +invʳ : ∀ {x} → +˙ (+⁼ x) ≡ x
  +invʳ {x L.∷ L.[] , ℕ.s≤s ()}
  +invʳ {error plus (int v₁) L.∷ int v₂ L.∷ s , l} = refl
  +invʳ {error plus (list li) L.∷ v₂ L.∷ s , l} = refl
  +invʳ {error plus (int i) L.∷ list li L.∷ s , l} = refl
  +invʳ {error plus (int i) L.∷ string str L.∷ s , l} = refl
  +invʳ {error plus (int i) L.∷ error t v₂ L.∷ s , l} = refl
  +invʳ {error plus (string str) L.∷ v₂ L.∷ s , l} = refl
  +invʳ {error plus (error plus v₁) L.∷ v₂ L.∷ s , l} = refl
  +invʳ {int i₁ L.∷ int i₂ L.∷ s , l}
    rewrite ℤp.+-assoc i₁ (ℤ.- i₂) i₂
    rewrite ℤp.+-inverseˡ i₂
    rewrite ℤp.+-identityʳ i₁ = refl
  +invʳ {list li L.∷ v₂ L.∷ s , l} = refl
  +invʳ {string str L.∷ v₂ L.∷ s , l} = refl
  +invʳ {error plus (int i) L.∷ function args stmt L.∷ s , l} = refl
  +invʳ {int i L.∷ list li L.∷ s , l} = refl
  +invʳ {int i L.∷ string str L.∷ s , l} = refl
  +invʳ {int i L.∷ error t v₂ L.∷ s , l} = refl
  +invʳ {function args stmt L.∷ list li L.∷ fst , snd} = refl
  +invʳ {error plus (function args stmt) L.∷ list li L.∷ fst , snd} = refl
  +invʳ {function args stmt L.∷ int i L.∷ fst , snd} = refl
  +invʳ {error plus (function args stmt) L.∷ int i L.∷ fst , snd} = refl
  +invʳ {function args stmt L.∷ string str L.∷ fst , snd} = refl
  +invʳ {int i L.∷ function args stmt L.∷ fst , snd} = refl
  +invʳ {function args stmt L.∷ function args₁ stmt₁ L.∷ fst , snd} = refl
  +invʳ {function args stmt L.∷ error t x L.∷ fst , snd} = refl
  +invʳ {error plus (function args stmt) L.∷ string str L.∷ fst , snd} = refl
  +invʳ {error plus (function args stmt) L.∷ function args₁ stmt₁ L.∷ fst , snd} = refl
  +invʳ {error plus (function args stmt) L.∷ error t x L.∷ fst , snd} = refl


  +invˡ : ∀ {x} → +⁼ (+˙ x) ≡ x
  +invˡ {x L.∷ L.[] , ℕ.s≤s ()}
  +invˡ {error plus (int v₁) L.∷ int v₂ L.∷ s , l} = refl
  +invˡ {error plus (list li) L.∷ v₂ L.∷ s , l} = refl
  +invˡ {error plus (int i) L.∷ list li L.∷ s , l} = refl
  +invˡ {error plus (int i) L.∷ string str L.∷ s , l} = refl
  +invˡ {error plus (int i) L.∷ error t v₂ L.∷ s , l} = refl
  +invˡ {error plus (string str) L.∷ v₂ L.∷ s , l} = refl
  +invˡ {error plus (error plus v₁) L.∷ v₂ L.∷ s , l} = refl
  +invˡ {int i₁ L.∷ int i₂ L.∷ s , l}
    rewrite ℤp.+-assoc i₁ i₂ (ℤ.- i₂)
    rewrite ℤp.+-inverseʳ i₂
    rewrite ℤp.+-identityʳ i₁ = refl
  +invˡ {list li L.∷ v₂ L.∷ s , l} = refl
  +invˡ {string str L.∷ v₂ L.∷ s , l} = refl
  +invˡ {error plus (int i) L.∷ function args stmt L.∷ s , l} = refl
  +invˡ {int i L.∷ list li L.∷ s , l} = refl
  +invˡ {int i L.∷ string str L.∷ s , l} = refl
  +invˡ {int i L.∷ error t v₂ L.∷ s , l} = refl
  +invˡ {function args stmt L.∷ list li L.∷ fst , snd} = refl
  +invˡ {error plus (function args stmt) L.∷ list li L.∷ fst , snd} = refl
  +invˡ {function args stmt L.∷ int i L.∷ fst , snd} = refl
  +invˡ {error plus (function args stmt) L.∷ int i L.∷ fst , snd} = refl
  +invˡ {function args stmt L.∷ string str L.∷ fst , snd} = refl
  +invˡ {function args stmt L.∷ function args₁ stmt₁ L.∷ fst , snd} = refl
  +invˡ {function args stmt L.∷ error t x L.∷ fst , snd} = refl
  +invˡ {error plus (function args stmt) L.∷ string str L.∷ fst , snd} = refl
  +invˡ {error plus (function args stmt) L.∷ function args₁ stmt₁ L.∷ fst , snd} = refl
  +invˡ {error plus (function args stmt) L.∷ error t x L.∷ fst , snd} = refl
  +invˡ {int i L.∷ function args stmt L.∷ fst , snd} = refl

  areInv : Inverse (setoid (Stack 2)) (setoid (Stack 2))
  areInv .Inverse.to = +˙
  areInv .Inverse.from = +⁼
  areInv .Inverse.to-cong = cong +˙
  areInv .Inverse.from-cong = cong +⁼
  areInv .Inverse.inverse .proj₁ refl = +invʳ
  areInv .Inverse.inverse .proj₂ refl = +invˡ
