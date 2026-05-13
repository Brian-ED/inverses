import Data.Nat as ℕ
import Data.Nat.Properties as ℕp
import Data.Nat.ListAction as ℕL
import Data.Bool.ListAction as BL
import Data.List as L
import Data.Vec as V
open import Data.String using (String)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; refl; cong; setoid; inspect; [_]; subst)
open import Relation.Binary using (Setoid)
open import Function using (Inverse)
open import Data.Bool using (Bool; true; false; not; _∧_; if_then_else_; T)
open import Data.Product using (proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_; map′)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary.Decidable using (no; yes)

module Core.Primitive (Stack : ℕ.ℕ → Set) where

record Primitive (n m : ℕ.ℕ) : Set where
  constructor ⟨_˙,_⁼,_ʳ,_ˡ⟩
  field
    f˙ : (s : Stack n) → Stack m
    f⁼ : (s : Stack m) → Stack n
    f-invʳ : ∀ {x} → f˙ (f⁼ x) ≡ x
    f-invˡ : ∀ {x} → f⁼ (f˙ x) ≡ x

  inv : Inverse (setoid (Stack n)) (setoid (Stack m))
  inv .Inverse.to = f˙
  inv .Inverse.from = f⁼
  inv .Inverse.to-cong = cong f˙
  inv .Inverse.from-cong = cong f⁼
  inv .Inverse.inverse .proj₁ refl = f-invʳ
  inv .Inverse.inverse .proj₂ refl = f-invˡ
