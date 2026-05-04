module Core.Primitive where

import Data.Integer as ℤ
import Data.Integer.Properties as ℤp
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

open import Core.Value

Stack : ℕ.ℕ → Set
Stack = V.Vec Value

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

incrErrorUnit : (v : Value) → Value
incrErrorUnit (error (enum n) x) = error (enum (ℕ.suc n)) (incrErrorUnit x)
incrErrorUnit x = x

decrErrorUnit : (v : Value) → Value
decrErrorUnit (error (enum (ℕ.suc n)) x) = error (enum n) (decrErrorUnit x)
decrErrorUnit x = x

incrInvUnit : ∀ x → decrErrorUnit (incrErrorUnit x) ≡ x
incrInvUnit (list li) = refl
incrInvUnit (int i) = refl
incrInvUnit (string str) = refl
incrInvUnit (function args stmt) = refl
incrInvUnit (error (enum n) x) rewrite incrInvUnit x = refl

incrError : (s : Stack 2) → Stack 2
incrError ((error (enum n) x) V.∷ s) = (incrErrorUnit (error (enum n) x)) V.∷ s
incrError x = x


decrError : (s : Stack 2) → Stack 2
decrError ((error (enum n) x) V.∷ s) = (decrErrorUnit (error (enum n) x)) V.∷ s
decrError x = x

incrInv : ∀ x → decrError (incrError x) ≡ x
incrInv (list li V.∷ fst) = refl
incrInv (int i V.∷ fst) = refl
incrInv (string str V.∷ fst) = refl
incrInv (function args stmt V.∷ fst) = refl
incrInv (error (enum n) x V.∷ fst) rewrite incrInvUnit x = refl

impossible : ⊥ → false ≡ true
impossible ()

reflLemma : ∀ x → (x ℕ.≡ᵇ x) ≡ true
reflLemma ℕ.zero = refl
reflLemma (ℕ.suc x) = reflLemma x

--notReflReflLemma : ∀ x y → ¬ x ≡ x → (x ℕ.≡ᵇ x) ≡ false

≡ᵇ-sound : ∀ m n → (m ℕ.≡ᵇ n) ≡ true → m ≡ n
≡ᵇ-sound m n x = ℕp.≡ᵇ⇒≡ m n (subst T (sym x) tt)

notReflLemma : ∀ x y → ¬ x ≡ y → (x ℕ.≡ᵇ y) ≡ false
notReflLemma x y x≢y with x ℕ.≡ᵇ y | inspect (x ℕ.≡ᵇ_) y
... | false | _      = refl
... | true  | [ eq ] = ⊥-elim (x≢y (≡ᵇ-sound x y eq))
