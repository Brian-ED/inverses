module Core.Primitives where

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

open import Data.Product using (Σ; ∃; _,_)

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

module nArg where

  intFuncToPrim : (f˙ f⁼ : ℤ.ℤ → ℤ.ℤ → ℤ.ℤ)
                → (f-invʳ : ∀ x y → f˙ x (f⁼ x y) ≡ y)
                → (f-invˡ : ∀ x y → f⁼ x (f˙ x y) ≡ y)
                → (errVal : errType)
                → Primitive 2 2
  intFuncToPrim f˙ f⁼ f-invʳ f-invˡ (enum errO) = ⟨
    f˙´ ˙,
    f⁼´ ⁼,
    invʳ ʳ,
    invˡ ˡ⟩
    where
      f˙´ : (s : Stack 2) → Stack 2
      f˙´ (int i₁ V.∷ int i₂ V.∷ s) = int (f˙ i₂ i₁) V.∷ int i₂ V.∷ s
      f˙´ (error (enum n₁) (error (enum n₂) x) V.∷ s) =
        if n₁ ℕ.≡ᵇ errO
        then if n₂ ℕ.≡ᵇ errO
          then error (enum errO) (error (enum errO) x) V.∷ s
          else error (enum n₂) x V.∷ s
        else error (enum errO) (error (enum n₁) (error (enum n₂) x)) V.∷ s
      f˙´ (error (enum n) (int i₁) V.∷ int i₂ V.∷ s) =
        if n ℕ.≡ᵇ errO
        then error (enum errO) (int i₁) V.∷ int i₂ V.∷ s
        else error (enum errO) (error (enum n) (int i₁)) V.∷ int i₂ V.∷ s
      f˙´ (error (enum n) v₁ V.∷ v₂ V.∷ s) =
        if n ℕ.≡ᵇ errO
        then v₁ V.∷ v₂ V.∷ s
        else error (enum errO) (error (enum n) v₁) V.∷ v₂ V.∷ s
      f˙´ (v₁ V.∷ v₂ V.∷ s) = error (enum errO) v₁ V.∷ v₂ V.∷ s


      f⁼´ : (s : Stack 2) → Stack 2
      f⁼´ (int i₁ V.∷ int i₂ V.∷ s) = int (f⁼ i₂ i₁) V.∷ int i₂ V.∷ s
      f⁼´ (error (enum n₁) (error (enum n₂) x) V.∷ s) =
        if n₁ ℕ.≡ᵇ errO
        then if n₂ ℕ.≡ᵇ errO
          then error (enum errO) (error (enum errO) x) V.∷ s
          else error (enum n₂) x V.∷ s
        else error (enum errO) (error (enum n₁) (error (enum n₂) x)) V.∷ s
      f⁼´ (error (enum n) (int i₁) V.∷ int i₂ V.∷ s) =
        if n ℕ.≡ᵇ errO
        then error (enum errO) (int i₁) V.∷ int i₂ V.∷ s
        else error (enum errO) (error (enum n) (int i₁)) V.∷ int i₂ V.∷ s
      f⁼´ (error (enum n) v₁ V.∷ v₂ V.∷ s) =
        if n ℕ.≡ᵇ errO
        then v₁ V.∷ v₂ V.∷ s
        else error (enum errO) (error (enum n) v₁) V.∷ v₂ V.∷ s
      f⁼´ (v₁ V.∷ v₂ V.∷ s) = error (enum errO) v₁ V.∷ v₂ V.∷ s

      invʳ : ∀ {x} → f˙´ (f⁼´ x) ≡ x
      invʳ {list li V.∷ x V.∷ s} rewrite reflLemma errO = refl
      invʳ {string str V.∷ x V.∷ s} rewrite reflLemma errO = refl
      invʳ {function args stmt V.∷ x V.∷ s} rewrite reflLemma errO = refl
      invʳ {error (enum n) (list li) V.∷ x₁ V.∷ s} with n ℕ.≟ errO
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      ... | yes q rewrite q rewrite reflLemma errO = refl
      invʳ {error (enum n) (string str) V.∷ x₁ V.∷ s} with n ℕ.≟ errO
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      ... | yes q rewrite q rewrite reflLemma errO = refl
      invʳ {error (enum n) (function args stmt) V.∷ x₁ V.∷ s} with n ℕ.≟ errO
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      ... | yes q rewrite q rewrite reflLemma errO = refl
      invʳ {error (enum n) (error (enum n₁) (list li)) V.∷ x₁ V.∷ s} with n ℕ.≟ errO
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      ... | yes q rewrite q rewrite reflLemma errO with n₁ ℕ.≟ errO
      ... | no p rewrite notReflLemma n₁ errO p rewrite notReflLemma n₁ errO p = refl
      ... | yes p rewrite p rewrite reflLemma errO rewrite reflLemma errO = refl
      invʳ {error (enum n) (error (enum n₁) (string str)) V.∷ x₁ V.∷ s} with n ℕ.≟ errO
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      ... | yes q rewrite q rewrite reflLemma errO with n₁ ℕ.≟ errO
      ... | no p rewrite notReflLemma n₁ errO p rewrite notReflLemma n₁ errO p = refl
      ... | yes p rewrite p rewrite reflLemma errO rewrite reflLemma errO = refl
      invʳ {error (enum n) (error (enum n₁) (error (enum n₂) x)) V.∷ x₁ V.∷ s} with n ℕ.≟ errO
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      ... | yes q rewrite q rewrite reflLemma errO with n₁ ℕ.≟ errO
      ... | no p rewrite notReflLemma n₁ errO p rewrite notReflLemma n₁ errO p = refl
      ... | yes p rewrite p rewrite reflLemma errO rewrite reflLemma errO = refl
      invʳ {error (enum n) (error (enum n₁) (function args stmt)) V.∷ x₁ V.∷ s} with n ℕ.≟ errO
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      ... | yes q rewrite q rewrite reflLemma errO with n₁ ℕ.≟ errO
      ... | no p rewrite notReflLemma n₁ errO p rewrite notReflLemma n₁ errO p = refl
      ... | yes p rewrite p rewrite reflLemma errO rewrite reflLemma errO = refl
      invʳ {int i V.∷ list li V.∷ s} rewrite reflLemma errO = refl
      invʳ {int i₁ V.∷ int i₂ V.∷ s} rewrite f-invʳ i₂ i₁  = refl
      invʳ {int i V.∷ string str V.∷ s} rewrite reflLemma errO = refl
      invʳ {int i V.∷ function args stmt V.∷ s} rewrite reflLemma errO = refl
      invʳ {int i V.∷ error t x V.∷ s} rewrite reflLemma errO = refl
      invʳ {error (enum n) (int i) V.∷ list li V.∷ s} with n ℕ.≟ errO
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      ... | yes q rewrite q rewrite reflLemma errO = refl
      invʳ {error (enum n) (error (enum n₁) (int x)) V.∷ list li V.∷ s} with n ℕ.≟ errO
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      ... | yes q rewrite q rewrite reflLemma errO with n₁ ℕ.≟ errO
      ... | no q2 rewrite notReflLemma n₁ errO q2 rewrite notReflLemma n₁ errO q2 = refl
      ... | yes q2 rewrite q2 rewrite reflLemma errO rewrite reflLemma errO = refl
      invʳ {error (enum n) (int i₁) V.∷ int i V.∷ s} with n ℕ.≟ errO
      ... | yes q rewrite q rewrite reflLemma errO rewrite reflLemma errO = refl
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      invʳ {error (enum n₁) (error (enum n₂) (int x)) V.∷ int i V.∷ s} with n₁ ℕ.≟ errO
      ... | no q rewrite notReflLemma n₁ errO q rewrite reflLemma errO rewrite notReflLemma n₁ errO q = refl
      ... | yes q rewrite q rewrite reflLemma errO with n₂ ℕ.≟ errO
      ... | yes q2 rewrite q2 rewrite reflLemma errO rewrite reflLemma errO = refl
      ... | no q2 rewrite notReflLemma n₂ errO q2 rewrite notReflLemma n₂ errO q2 = refl
      invʳ {error (enum n) (int i) V.∷ string str V.∷ s} with n ℕ.≟ errO
      ... | yes q rewrite q rewrite reflLemma errO = refl
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      invʳ {error (enum n) (error (enum n₂) (int i)) V.∷ string str V.∷ s} with n ℕ.≟ errO
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      ... | yes q rewrite q rewrite reflLemma errO with n₂ ℕ.≟ errO
      ... | no q2 rewrite notReflLemma n₂ errO q2 rewrite notReflLemma n₂ errO q2 = refl
      ... | yes q2 rewrite q2 rewrite reflLemma errO rewrite reflLemma errO = refl
      invʳ {error (enum n) (int i) V.∷ function args stmt V.∷ s} with n ℕ.≟ errO
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      ... | yes q rewrite q rewrite reflLemma errO = refl
      invʳ {error (enum n) (error (enum n₂) (int i)) V.∷ function args stmt V.∷ s} with n ℕ.≟ errO
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      ... | yes q rewrite q rewrite reflLemma errO with n₂ ℕ.≟ errO
      ... | no q2 rewrite notReflLemma n₂ errO q2 rewrite notReflLemma n₂ errO q2 = refl
      ... | yes q2 rewrite q2 rewrite reflLemma errO rewrite reflLemma errO = refl
      invʳ {error (enum n) (int i) V.∷ error t x V.∷ s} with n ℕ.≟ errO
      ... | yes p rewrite p rewrite reflLemma errO = refl
      ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
      invʳ {error (enum n) (error (enum n₁) (int i)) V.∷ error (enum n₂) x₁ V.∷ s} with n ℕ.≟ errO
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      ... | yes q rewrite q rewrite reflLemma errO with n₁ ℕ.≟ errO
      ... | no p rewrite notReflLemma n₁ errO p rewrite notReflLemma n₁ errO p = refl
      ... | yes p rewrite p rewrite reflLemma errO rewrite reflLemma errO = refl

      invˡ : ∀ {x} → f⁼´ (f˙´ x) ≡ x
      invˡ {list li V.∷ x V.∷ s} rewrite reflLemma errO = refl
      invˡ {string str V.∷ x V.∷ s} rewrite reflLemma errO = refl
      invˡ {function args stmt V.∷ x V.∷ s} rewrite reflLemma errO = refl
      invˡ {error (enum n) (list li) V.∷ x₁ V.∷ s} with n ℕ.≟ errO
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      ... | yes q rewrite q rewrite reflLemma errO = refl
      invˡ {error (enum n) (string str) V.∷ x₁ V.∷ s} with n ℕ.≟ errO
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      ... | yes q rewrite q rewrite reflLemma errO = refl
      invˡ {error (enum n) (function args stmt) V.∷ x₁ V.∷ s} with n ℕ.≟ errO
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      ... | yes q rewrite q rewrite reflLemma errO = refl
      invˡ {error (enum n) (error (enum n₁) (list li)) V.∷ x₁ V.∷ s} with n ℕ.≟ errO
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      ... | yes q rewrite q rewrite reflLemma errO with n₁ ℕ.≟ errO
      ... | no p rewrite notReflLemma n₁ errO p rewrite notReflLemma n₁ errO p = refl
      ... | yes p rewrite p rewrite reflLemma errO rewrite reflLemma errO = refl
      invˡ {error (enum n) (error (enum n₁) (string str)) V.∷ x₁ V.∷ s} with n ℕ.≟ errO
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      ... | yes q rewrite q rewrite reflLemma errO with n₁ ℕ.≟ errO
      ... | no p rewrite notReflLemma n₁ errO p rewrite notReflLemma n₁ errO p = refl
      ... | yes p rewrite p rewrite reflLemma errO rewrite reflLemma errO = refl
      invˡ {error (enum n) (error (enum n₁) (error (enum n₂) x)) V.∷ x₁ V.∷ s} with n ℕ.≟ errO
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      ... | yes q rewrite q rewrite reflLemma errO with n₁ ℕ.≟ errO
      ... | no p rewrite notReflLemma n₁ errO p rewrite notReflLemma n₁ errO p = refl
      ... | yes p rewrite p rewrite reflLemma errO rewrite reflLemma errO = refl
      invˡ {error (enum n) (error (enum n₁) (function args stmt)) V.∷ x₁ V.∷ s} with n ℕ.≟ errO
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      ... | yes q rewrite q rewrite reflLemma errO with n₁ ℕ.≟ errO
      ... | no p rewrite notReflLemma n₁ errO p rewrite notReflLemma n₁ errO p = refl
      ... | yes p rewrite p rewrite reflLemma errO rewrite reflLemma errO = refl
      invˡ {int i V.∷ list li V.∷ s} rewrite reflLemma errO = refl
      invˡ {int i₁ V.∷ int i₂ V.∷ s} rewrite f-invˡ i₂ i₁ = refl
      invˡ {int i V.∷ string str V.∷ s} rewrite reflLemma errO = refl
      invˡ {int i V.∷ function args stmt V.∷ s} rewrite reflLemma errO = refl
      invˡ {int i V.∷ error t x V.∷ s} rewrite reflLemma errO = refl
      invˡ {error (enum n) (int i) V.∷ list li V.∷ s} with n ℕ.≟ errO
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      ... | yes q rewrite q rewrite reflLemma errO = refl
      invˡ {error (enum n) (error (enum n₁) (int x)) V.∷ list li V.∷ s} with n ℕ.≟ errO
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      ... | yes q rewrite q rewrite reflLemma errO with n₁ ℕ.≟ errO
      ... | no q2 rewrite notReflLemma n₁ errO q2 rewrite notReflLemma n₁ errO q2 = refl
      ... | yes q2 rewrite q2 rewrite reflLemma errO rewrite reflLemma errO = refl
      invˡ {error (enum n) (int i₁) V.∷ int i V.∷ s} with n ℕ.≟ errO
      ... | yes q rewrite q rewrite reflLemma errO rewrite reflLemma errO = refl
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      invˡ {error (enum n₁) (error (enum n₂) (int x)) V.∷ int i V.∷ s} with n₁ ℕ.≟ errO
      ... | no q rewrite notReflLemma n₁ errO q rewrite reflLemma errO rewrite notReflLemma n₁ errO q = refl
      ... | yes q rewrite q rewrite reflLemma errO with n₂ ℕ.≟ errO
      ... | yes q2 rewrite q2 rewrite reflLemma errO rewrite reflLemma errO = refl
      ... | no q2 rewrite notReflLemma n₂ errO q2 rewrite notReflLemma n₂ errO q2 = refl
      invˡ {error (enum n) (int i) V.∷ string str V.∷ s} with n ℕ.≟ errO
      ... | yes q rewrite q rewrite reflLemma errO = refl
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      invˡ {error (enum n) (error (enum n₂) (int i)) V.∷ string str V.∷ s} with n ℕ.≟ errO
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      ... | yes q rewrite q rewrite reflLemma errO with n₂ ℕ.≟ errO
      ... | no q2 rewrite notReflLemma n₂ errO q2 rewrite notReflLemma n₂ errO q2 = refl
      ... | yes q2 rewrite q2 rewrite reflLemma errO rewrite reflLemma errO = refl
      invˡ {error (enum n) (int i) V.∷ function args stmt V.∷ s} with n ℕ.≟ errO
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      ... | yes q rewrite q rewrite reflLemma errO = refl
      invˡ {error (enum n) (error (enum n₂) (int i)) V.∷ function args stmt V.∷ s} with n ℕ.≟ errO
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      ... | yes q rewrite q rewrite reflLemma errO with n₂ ℕ.≟ errO
      ... | no q2 rewrite notReflLemma n₂ errO q2 rewrite notReflLemma n₂ errO q2 = refl
      ... | yes q2 rewrite q2 rewrite reflLemma errO rewrite reflLemma errO = refl
      invˡ {error (enum n) (int i) V.∷ error t x V.∷ s} with n ℕ.≟ errO
      ... | yes p rewrite p rewrite reflLemma errO = refl
      ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
      invˡ {error (enum n) (error (enum n₁) (int i)) V.∷ error (enum n₂) x₁ V.∷ s} with n ℕ.≟ errO
      ... | no q rewrite notReflLemma n errO q rewrite reflLemma errO rewrite notReflLemma n errO q = refl
      ... | yes q rewrite q rewrite reflLemma errO with n₁ ℕ.≟ errO
      ... | no p rewrite notReflLemma n₁ errO p rewrite notReflLemma n₁ errO p = refl
      ... | yes p rewrite p rewrite reflLemma errO rewrite reflLemma errO = refl

module + where

  _-˜_ : ℤ.ℤ → ℤ.ℤ → ℤ.ℤ
  _-˜_ x y = y ℤ.- x

  l : (x y : ℤ.ℤ) → x -˜ (x ℤ.+ y) ≡ y
  l x y = trans (cong (ℤ._+ (ℤ.- x)) (ℤp.+-comm x y))
        (trans (ℤp.+-assoc y x (ℤ.- x))
        (trans (cong (ℤ._+_ y) (ℤp.+-inverseʳ x))
                (ℤp.+-identityʳ y)))

  r : (x y : ℤ.ℤ) → x ℤ.+ (x -˜ y) ≡ y
  r x y = trans (sym (ℤp.+-assoc x y (ℤ.- x))) (l x y)

  +ₚ : Primitive 2 2
  +ₚ = nArg.intFuncToPrim ℤ._+_ _-˜_ r l (enum 0)
