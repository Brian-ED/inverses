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
open import Core.Primitive

module Core.DyadInt where

intFuncToPrim : (f˙ f⁼ : ℤ.ℤ → ℤ.ℤ → ℤ.ℤ)
              → (f-invʳ : ∀ x y → f˙ x (f⁼ x y) ≡ y)
              → (f-invˡ : ∀ x y → f⁼ x (f˙ x y) ≡ y)
              → (errNum : ℕ.ℕ)
              → Primitive 2 2
intFuncToPrim f˙ f⁼ f-invʳ f-invˡ errO = ⟨
  f˙´ ˙,
  f⁼´ ⁼,
  invʳ ʳ,
  invˡ ˡ⟩
  where
    f˙´ : (s : Stack 2) → Stack 2
    f˙´ (int i₁ V.∷ int i₂ V.∷ s) = int (f˙ i₂ i₁) V.∷ int i₂ V.∷ s
    f˙´ (error (enum⁼ n₁) (error (enum˙ n₂) v₁) V.∷ v₂ V.∷ V.[]) =
      if n₁ ℕ.≡ᵇ errO
      then if n₂ ℕ.≡ᵇ errO
        then (error (enum˙ n₁) (error (enum⁼ n₂) v₁) V.∷ v₂ V.∷ V.[])
        else error (enum˙ n₂) v₁ V.∷ v₂ V.∷ V.[]
      else error (enum˙ errO) (error (enum⁼ n₁) (error (enum˙ n₂) v₁)) V.∷ v₂ V.∷ V.[]

    f˙´ (error (enum⁼ n) (int v₁) V.∷ (int v₂) V.∷ s) =
      if n ℕ.≡ᵇ errO
      then error (enum˙ n) (int v₁) V.∷ (int v₂) V.∷ s
      else error (enum˙ errO) (error (enum⁼ n) (int v₁)) V.∷ int v₂ V.∷ s

    f˙´ (error (enum⁼ n) v₁ V.∷ v₂ V.∷ s) =
      if n ℕ.≡ᵇ errO
      then v₁ V.∷ v₂ V.∷ s
      else error (enum˙ errO) (error (enum⁼ n) v₁) V.∷ v₂ V.∷ s

    f˙´ (v₁ V.∷ v₂ V.∷ s) = error (enum˙ errO) v₁ V.∷ v₂ V.∷ s


    f⁼´ : (s : Stack 2) → Stack 2
    f⁼´ (int i₁ V.∷ int i₂ V.∷ s) = int (f⁼ i₂ i₁) V.∷ int i₂ V.∷ s
    f⁼´ (error (enum˙ n₁) (error (enum⁼ n₂) v₁) V.∷ v₂ V.∷ V.[]) =
      if n₁ ℕ.≡ᵇ errO
      then if n₂ ℕ.≡ᵇ errO
        then (error (enum⁼ n₁) (error (enum˙ n₂) v₁) V.∷ v₂ V.∷ V.[])
        else error (enum⁼ n₂) v₁ V.∷ v₂ V.∷ V.[]
      else error (enum⁼ errO) (error (enum˙ n₁) (error (enum⁼ n₂) v₁)) V.∷ v₂ V.∷ V.[]

    f⁼´ (error (enum˙ n) (int v₁) V.∷ (int v₂) V.∷ s) =
      if n ℕ.≡ᵇ errO
      then error (enum⁼ n) (int v₁) V.∷ (int v₂) V.∷ s
      else error (enum⁼ errO) (error (enum˙ n) (int v₁)) V.∷ int v₂ V.∷ s

    f⁼´ (error (enum˙ n) v₁ V.∷ v₂ V.∷ s) =
      if n ℕ.≡ᵇ errO
      then v₁ V.∷ v₂ V.∷ s
      else error (enum⁼ errO) (error (enum˙ n) v₁) V.∷ v₂ V.∷ s

    f⁼´ (v₁ V.∷ v₂ V.∷ s) = error (enum⁼ errO) v₁ V.∷ v₂ V.∷ s


    invʳ : ∀ {x} → f˙´ (f⁼´ x) ≡ x
    invʳ {list li V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invʳ {string str V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invʳ {function args stmt V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invʳ {int i V.∷ list li V.∷ V.[]} rewrite reflLemma errO = refl
    invʳ {int i V.∷ string str V.∷ V.[]} rewrite reflLemma errO = refl
    invʳ {int i V.∷ function args stmt V.∷ V.[]} rewrite reflLemma errO = refl
    invʳ {int i₁ V.∷ int i₂ V.∷ V.[]} rewrite f-invʳ i₂ i₁ = refl
    invʳ {int i V.∷ error (enum˙ n) x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invʳ {int i V.∷ error (enum⁼ n) x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invʳ {error (enum˙ n) (list li) V.∷ x₂ V.∷ V.[]} with n ℕ.≟ errO
    ... | yes p rewrite p rewrite reflLemma errO = refl
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    invʳ {error (enum˙ n) (string str) V.∷ x₂ V.∷ V.[]} with n ℕ.≟ errO
    ... | yes p rewrite p rewrite reflLemma errO = refl
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    invʳ {error (enum˙ n) (function args stmt) V.∷ x₂ V.∷ V.[]} with n ℕ.≟ errO
    ... | yes p rewrite p rewrite reflLemma errO = refl
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    invʳ {error (enum˙ n) (error (enum˙ n₁) x₁) V.∷ x₂ V.∷ V.[]} with n ℕ.≟ errO
    ... | yes p rewrite p rewrite reflLemma errO = refl
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    invʳ {error (enum˙ n₁) (error (enum⁼ n₂) x₁) V.∷ x₂ V.∷ V.[]} with n₁ ℕ.≟ errO
    ... | no p rewrite notReflLemma n₁ errO p rewrite reflLemma errO rewrite notReflLemma n₁ errO p = refl
    ... | yes p rewrite p rewrite reflLemma errO with n₂ ℕ.≟ errO
    ... | yes q rewrite q rewrite reflLemma errO rewrite reflLemma errO = refl
    ... | no q rewrite notReflLemma n₂ errO q with x₁
    ... | list li rewrite notReflLemma n₂ errO q = refl
    ... | string str rewrite notReflLemma n₂ errO q = refl
    ... | function args stmt rewrite notReflLemma n₂ errO q = refl
    ... | error (enum˙ t₁) x₃ rewrite notReflLemma n₂ errO q = refl
    ... | error (enum⁼ t₁) x₃ rewrite notReflLemma n₂ errO q = refl
    ... | int i with x₂
    ... |   list li rewrite notReflLemma n₂ errO q = refl
    ... |   int i₁ rewrite notReflLemma n₂ errO q = refl
    ... |   string str rewrite notReflLemma n₂ errO q = refl
    ... |   function args stmt rewrite notReflLemma n₂ errO q = refl
    ... |   error (enum˙ t) v rewrite notReflLemma n₂ errO q = refl
    ... |   error (enum⁼ t) v rewrite notReflLemma n₂ errO q = refl
    invʳ {error (enum˙ n) (int i) V.∷ list li V.∷ V.[]} with n ℕ.≟ errO
    ... | yes p rewrite p rewrite reflLemma errO = refl
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    invʳ {error (enum˙ n) (int i₁) V.∷ int i₂ V.∷ V.[]} with n ℕ.≟ errO
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    ... | yes p rewrite p rewrite reflLemma errO rewrite reflLemma errO = refl
    invʳ {error (enum˙ n) (int i) V.∷ string str V.∷ V.[]} with n ℕ.≟ errO
    ... | yes p rewrite p rewrite reflLemma errO = refl
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    invʳ {error (enum˙ n) (int i) V.∷ function args stmt V.∷ V.[]} with n ℕ.≟ errO
    ... | yes p rewrite p rewrite reflLemma errO = refl
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    invʳ {error (enum˙ n) (int i) V.∷ error (enum˙ n₁) x₂ V.∷ V.[]} with n ℕ.≟ errO
    ... | yes p rewrite p rewrite reflLemma errO = refl
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    invʳ {error (enum˙ n) (int i) V.∷ error (enum⁼ n₁) x₂ V.∷ V.[]} with n ℕ.≟ errO
    ... | yes p rewrite p rewrite reflLemma errO = refl
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    invʳ {error (enum⁼ n) (list li) V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invʳ {error (enum⁼ n) (int i) V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invʳ {error (enum⁼ n) (string str) V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invʳ {error (enum⁼ n) (function args stmt) V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invʳ {error (enum⁼ n) (error (enum˙ n₁) x) V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invʳ {error (enum⁼ n) (error (enum⁼ n₁) x) V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl

    invˡ : ∀ {x} → f⁼´ (f˙´ x) ≡ x
    invˡ {list li V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invˡ {string str V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invˡ {function args stmt V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invˡ {int i V.∷ list li V.∷ V.[]} rewrite reflLemma errO = refl
    invˡ {int i V.∷ string str V.∷ V.[]} rewrite reflLemma errO = refl
    invˡ {int i V.∷ function args stmt V.∷ V.[]} rewrite reflLemma errO = refl
    invˡ {int i₁ V.∷ int i₂ V.∷ V.[]} rewrite f-invˡ i₂ i₁ = refl
    invˡ {int i V.∷ error (enum˙ n) x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invˡ {int i V.∷ error (enum⁼ n) x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invˡ {error (enum⁼ n) (list li) V.∷ x₂ V.∷ V.[]} with n ℕ.≟ errO
    ... | yes p rewrite p rewrite reflLemma errO = refl
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    invˡ {error (enum⁼ n) (string str) V.∷ x₂ V.∷ V.[]} with n ℕ.≟ errO
    ... | yes p rewrite p rewrite reflLemma errO = refl
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    invˡ {error (enum⁼ n) (function args stmt) V.∷ x₂ V.∷ V.[]} with n ℕ.≟ errO
    ... | yes p rewrite p rewrite reflLemma errO = refl
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    invˡ {error (enum⁼ n) (error (enum⁼ n₁) x₁) V.∷ x₂ V.∷ V.[]} with n ℕ.≟ errO
    ... | yes p rewrite p rewrite reflLemma errO = refl
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    invˡ {error (enum⁼ n₁) (error (enum˙ n₂) x₁) V.∷ x₂ V.∷ V.[]} with n₁ ℕ.≟ errO
    ... | no p rewrite notReflLemma n₁ errO p rewrite reflLemma errO rewrite notReflLemma n₁ errO p = refl
    ... | yes p rewrite p rewrite reflLemma errO with n₂ ℕ.≟ errO
    ... | yes q rewrite q rewrite reflLemma errO rewrite reflLemma errO = refl
    ... | no q rewrite notReflLemma n₂ errO q with x₁
    ... | list li rewrite notReflLemma n₂ errO q = refl
    ... | string str rewrite notReflLemma n₂ errO q = refl
    ... | function args stmt rewrite notReflLemma n₂ errO q = refl
    ... | error (enum⁼ t₁) x₃ rewrite notReflLemma n₂ errO q = refl
    ... | error (enum˙ t₁) x₃ rewrite notReflLemma n₂ errO q = refl
    ... | int i with x₂
    ... |   list li rewrite notReflLemma n₂ errO q = refl
    ... |   int i₁ rewrite notReflLemma n₂ errO q = refl
    ... |   string str rewrite notReflLemma n₂ errO q = refl
    ... |   function args stmt rewrite notReflLemma n₂ errO q = refl
    ... |   error (enum˙ t) v rewrite notReflLemma n₂ errO q = refl
    ... |   error (enum⁼ t) v rewrite notReflLemma n₂ errO q = refl
    invˡ {error (enum⁼ n) (int i) V.∷ list li V.∷ V.[]} with n ℕ.≟ errO
    ... | yes p rewrite p rewrite reflLemma errO = refl
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    invˡ {error (enum⁼ n) (int i₁) V.∷ int i₂ V.∷ V.[]} with n ℕ.≟ errO
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    ... | yes p rewrite p rewrite reflLemma errO rewrite reflLemma errO = refl
    invˡ {error (enum⁼ n) (int i) V.∷ string str V.∷ V.[]} with n ℕ.≟ errO
    ... | yes p rewrite p rewrite reflLemma errO = refl
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    invˡ {error (enum⁼ n) (int i) V.∷ function args stmt V.∷ V.[]} with n ℕ.≟ errO
    ... | yes p rewrite p rewrite reflLemma errO = refl
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    invˡ {error (enum⁼ n) (int i) V.∷ error (enum⁼ n₁) x₂ V.∷ V.[]} with n ℕ.≟ errO
    ... | yes p rewrite p rewrite reflLemma errO = refl
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    invˡ {error (enum⁼ n) (int i) V.∷ error (enum˙ n₁) x₂ V.∷ V.[]} with n ℕ.≟ errO
    ... | yes p rewrite p rewrite reflLemma errO = refl
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    invˡ {error (enum˙ n) (list li) V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invˡ {error (enum˙ n) (int i) V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invˡ {error (enum˙ n) (string str) V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invˡ {error (enum˙ n) (function args stmt) V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invˡ {error (enum˙ n) (error (enum˙ n₁) x) V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invˡ {error (enum˙ n) (error (enum⁼ n₁) x) V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
