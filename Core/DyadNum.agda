import Data.Rational as ℚ
import Data.Rational.Properties as ℚp
import Data.Nat as ℕ
import Data.Nat.Properties as ℕp
import Data.Nat.ListAction as ℕL
import Data.Bool.Properties as Bp
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

import Function as F

module Core.DyadNnt where

≡ᵇt→≡ : ∀ n m → (n ℕ.≡ᵇ m) ≡ true → n ≡ m
≡ᵇt→≡ n m x = ℕp.≡ᵇ⇒≡ n m ((Bp.T-≡ {n ℕ.≡ᵇ m} .F.Equivalence.from) x)

≡ᵇf→≡ : ∀ n m → (n ℕ.≡ᵇ m) ≡ false → ¬ n ≡ m
≡ᵇf→≡ (ℕ.suc n) (ℕ.suc m) x refl = ≡ᵇf→≡ n m x refl


numFuncToPrim : (f˙ f⁼ : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ)
              → (f-invʳ : ∀ x y → f˙ x (f⁼ x y) ≡ y)
              → (f-invˡ : ∀ x y → f⁼ x (f˙ x y) ≡ y)
              → (errNum : ℕ.ℕ)
              → Primitive 2 2
numFuncToPrim f˙ f⁼ f-invʳ f-invˡ errO = ⟨
  f˙´ ˙,
  f⁼´ ⁼,
  invʳ ʳ,
  invˡ ˡ⟩
  where
    f˙´ : (s : Stack 2) → Stack 2
    f˙´ (num i₁ V.∷ num i₂ V.∷ s) = num (f˙ i₂ i₁) V.∷ num i₂ V.∷ s
    f˙´ (error (enum⁼ n₁) (error (enum˙ n₂) v₁) V.∷ v₂ V.∷ V.[]) =
      if n₁ ℕ.≡ᵇ errO
      then if n₂ ℕ.≡ᵇ errO
        then (error (enum˙ n₁) (error (enum⁼ n₂) v₁) V.∷ v₂ V.∷ V.[])
        else error (enum˙ n₂) v₁ V.∷ v₂ V.∷ V.[]
      else error (enum˙ errO) (error (enum⁼ n₁) (error (enum˙ n₂) v₁)) V.∷ v₂ V.∷ V.[]

    f˙´ (error (enum⁼ n) (num v₁) V.∷ (num v₂) V.∷ s) =
      if n ℕ.≡ᵇ errO
      then error (enum˙ n) (num v₁) V.∷ (num v₂) V.∷ s
      else error (enum˙ errO) (error (enum⁼ n) (num v₁)) V.∷ num v₂ V.∷ s

    f˙´ (error (enum⁼ n) v₁ V.∷ v₂ V.∷ s) =
      if n ℕ.≡ᵇ errO
      then v₁ V.∷ v₂ V.∷ s
      else error (enum˙ errO) (error (enum⁼ n) v₁) V.∷ v₂ V.∷ s

    f˙´ (v₁ V.∷ v₂ V.∷ s) = error (enum˙ errO) v₁ V.∷ v₂ V.∷ s


    f⁼´ : (s : Stack 2) → Stack 2
    f⁼´ (num i₁ V.∷ num i₂ V.∷ s) = num (f⁼ i₂ i₁) V.∷ num i₂ V.∷ s
    f⁼´ (error (enum˙ n₁) (error (enum⁼ n₂) v₁) V.∷ v₂ V.∷ V.[]) =
      if n₁ ℕ.≡ᵇ errO
      then if n₂ ℕ.≡ᵇ errO
        then (error (enum⁼ n₁) (error (enum˙ n₂) v₁) V.∷ v₂ V.∷ V.[])
        else error (enum⁼ n₂) v₁ V.∷ v₂ V.∷ V.[]
      else error (enum⁼ errO) (error (enum˙ n₁) (error (enum⁼ n₂) v₁)) V.∷ v₂ V.∷ V.[]

    f⁼´ (error (enum˙ n) (num v₁) V.∷ (num v₂) V.∷ s) =
      if n ℕ.≡ᵇ errO
      then error (enum⁼ n) (num v₁) V.∷ (num v₂) V.∷ s
      else error (enum⁼ errO) (error (enum˙ n) (num v₁)) V.∷ num v₂ V.∷ s

    f⁼´ (error (enum˙ n) v₁ V.∷ v₂ V.∷ s) =
      if n ℕ.≡ᵇ errO
      then v₁ V.∷ v₂ V.∷ s
      else error (enum⁼ errO) (error (enum˙ n) v₁) V.∷ v₂ V.∷ s

    f⁼´ (v₁ V.∷ v₂ V.∷ s) = error (enum⁼ errO) v₁ V.∷ v₂ V.∷ s


    invʳ : ∀ {x} → f˙´ (f⁼´ x) ≡ x
    invʳ {list li V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invʳ {string str V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invʳ {function args stmt V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invʳ {num i V.∷ list li V.∷ V.[]} rewrite reflLemma errO = refl
    invʳ {num i V.∷ string str V.∷ V.[]} rewrite reflLemma errO = refl
    invʳ {num i V.∷ function args stmt V.∷ V.[]} rewrite reflLemma errO = refl
    invʳ {num i₁ V.∷ num i₂ V.∷ V.[]} rewrite f-invʳ i₂ i₁ = refl
    invʳ {num i V.∷ error (enum˙ n) x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invʳ {num i V.∷ error (enum⁼ n) x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invʳ {error (enum˙ n) (list li) V.∷ x₂ V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true rewrite ≡ᵇt→≡ n errO p = refl
    ... | false rewrite reflLemma errO rewrite p = refl
    invʳ {error (enum˙ n) (string str) V.∷ x₂ V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true rewrite ≡ᵇt→≡ n errO p = refl
    ... | false rewrite reflLemma errO rewrite p = refl
    invʳ {error (enum˙ n) (function args stmt) V.∷ x₂ V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true rewrite ≡ᵇt→≡ n errO p = refl
    ... | false rewrite reflLemma errO rewrite p = refl
    invʳ {error (enum˙ n) (error (enum˙ n₁) x₁) V.∷ x₂ V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true rewrite ≡ᵇt→≡ n errO p = refl
    ... | false rewrite reflLemma errO rewrite p = refl
    invʳ {error (enum˙ n₁) (error (enum⁼ n₂) x₁) V.∷ x₂ V.∷ V.[]} with n₁ ℕ.≡ᵇ errO in p | n₂ ℕ.≡ᵇ errO in q | x₁ | x₂
    ... | false | B | a | b rewrite reflLemma errO rewrite p = refl
    ... | true | true | a | b rewrite ≡ᵇt→≡ n₁ errO p rewrite ≡ᵇt→≡ n₂ errO q rewrite reflLemma errO = refl
    ... | true | false | list li | n rewrite q rewrite ≡ᵇt→≡ n₁ errO p = refl
    ... | true | false | string str | b rewrite q rewrite ≡ᵇt→≡ n₁ errO p = refl
    ... | true | false | function args stmt | b rewrite q rewrite ≡ᵇt→≡ n₁ errO p = refl
    ... | true | false | error (enum˙ t) x | b rewrite q rewrite ≡ᵇt→≡ n₁ errO p = refl
    ... | true | false | error (enum⁼ t) x | b rewrite q rewrite ≡ᵇt→≡ n₁ errO p = refl
    ... | true | false | num i | list li rewrite q rewrite ≡ᵇt→≡ n₁ errO p = refl
    ... | true | false | num i | string str rewrite q rewrite ≡ᵇt→≡ n₁ errO p = refl
    ... | true | false | num i | function args stmt rewrite q rewrite ≡ᵇt→≡ n₁ errO p = refl
    ... | true | false | num i | error t b rewrite q rewrite ≡ᵇt→≡ n₁ errO p = refl
    ... | true | false | num i₁ | num i₂ rewrite q rewrite ≡ᵇt→≡ n₁ errO p = refl
    invʳ {error (enum˙ n) (num i) V.∷ list li V.∷ V.[]} with n ℕ.≟ errO
    ... | yes p rewrite p rewrite reflLemma errO = refl
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    invʳ {error (enum˙ n) (num i₁) V.∷ num i₂ V.∷ V.[]} with n ℕ.≟ errO
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    ... | yes p rewrite p rewrite reflLemma errO rewrite reflLemma errO = refl
    invʳ {error (enum˙ n) (num i) V.∷ string str V.∷ V.[]} with n ℕ.≟ errO
    ... | yes p rewrite p rewrite reflLemma errO = refl
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    invʳ {error (enum˙ n) (num i) V.∷ function args stmt V.∷ V.[]} with n ℕ.≟ errO
    ... | yes p rewrite p rewrite reflLemma errO = refl
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    invʳ {error (enum˙ n) (num i) V.∷ error (enum˙ n₁) x₂ V.∷ V.[]} with n ℕ.≟ errO
    ... | yes p rewrite p rewrite reflLemma errO = refl
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    invʳ {error (enum˙ n) (num i) V.∷ error (enum⁼ n₁) x₂ V.∷ V.[]} with n ℕ.≟ errO
    ... | yes p rewrite p rewrite reflLemma errO = refl
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    invʳ {error (enum⁼ n) (list li) V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invʳ {error (enum⁼ n) (num i) V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invʳ {error (enum⁼ n) (string str) V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invʳ {error (enum⁼ n) (function args stmt) V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invʳ {error (enum⁼ n) (error n₁ x) V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl

    invˡ : ∀ {x} → f⁼´ (f˙´ x) ≡ x
    invˡ {list li V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invˡ {string str V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invˡ {function args stmt V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invˡ {num i V.∷ list li V.∷ V.[]} rewrite reflLemma errO = refl
    invˡ {num i V.∷ string str V.∷ V.[]} rewrite reflLemma errO = refl
    invˡ {num i V.∷ function args stmt V.∷ V.[]} rewrite reflLemma errO = refl
    invˡ {num i₁ V.∷ num i₂ V.∷ V.[]} rewrite f-invˡ i₂ i₁ = refl
    invˡ {num i V.∷ error (enum˙ n) x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invˡ {num i V.∷ error (enum⁼ n) x₁ V.∷ V.[]} rewrite reflLemma errO = refl
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
    invˡ {error (enum⁼ n₁) (error (enum˙ n₂) x₁) V.∷ x₂ V.∷ V.[]} with n₁ ℕ.≡ᵇ errO in p | n₂ ℕ.≡ᵇ errO in q | x₁ | x₂
    ... | false | B | a | b rewrite reflLemma errO rewrite p = refl
    ... | true | true | a | b rewrite ≡ᵇt→≡ n₁ errO p rewrite ≡ᵇt→≡ n₂ errO q rewrite reflLemma errO = refl
    ... | true | false | list li | n rewrite q rewrite ≡ᵇt→≡ n₁ errO p = refl
    ... | true | false | string str | b rewrite q rewrite ≡ᵇt→≡ n₁ errO p = refl
    ... | true | false | function args stmt | b rewrite q rewrite ≡ᵇt→≡ n₁ errO p = refl
    ... | true | false | error (enum˙ t) x | b rewrite q rewrite ≡ᵇt→≡ n₁ errO p = refl
    ... | true | false | error (enum⁼ t) x | b rewrite q rewrite ≡ᵇt→≡ n₁ errO p = refl
    ... | true | false | num i | list li rewrite q rewrite ≡ᵇt→≡ n₁ errO p = refl
    ... | true | false | num i | string str rewrite q rewrite ≡ᵇt→≡ n₁ errO p = refl
    ... | true | false | num i | function args stmt rewrite q rewrite ≡ᵇt→≡ n₁ errO p = refl
    ... | true | false | num i | error t b rewrite q rewrite ≡ᵇt→≡ n₁ errO p = refl
    ... | true | false | num i₁ | num i₂ rewrite q rewrite ≡ᵇt→≡ n₁ errO p = refl
    invˡ {error (enum⁼ n) (num i) V.∷ list li V.∷ V.[]} with n ℕ.≟ errO
    ... | yes p rewrite p rewrite reflLemma errO = refl
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    invˡ {error (enum⁼ n) (num i₁) V.∷ num i₂ V.∷ V.[]} with n ℕ.≟ errO
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    ... | yes p rewrite p rewrite reflLemma errO rewrite reflLemma errO = refl
    invˡ {error (enum⁼ n) (num i) V.∷ string str V.∷ V.[]} with n ℕ.≟ errO
    ... | yes p rewrite p rewrite reflLemma errO = refl
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    invˡ {error (enum⁼ n) (num i) V.∷ function args stmt V.∷ V.[]} with n ℕ.≟ errO
    ... | yes p rewrite p rewrite reflLemma errO = refl
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    invˡ {error (enum⁼ n) (num i) V.∷ error (enum⁼ n₁) x₂ V.∷ V.[]} with n ℕ.≟ errO
    ... | yes p rewrite p rewrite reflLemma errO = refl
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    invˡ {error (enum⁼ n) (num i) V.∷ error (enum˙ n₁) x₂ V.∷ V.[]} with n ℕ.≟ errO
    ... | yes p rewrite p rewrite reflLemma errO = refl
    ... | no p rewrite notReflLemma n errO p rewrite reflLemma errO rewrite notReflLemma n errO p = refl
    invˡ {error (enum˙ n) (list li) V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invˡ {error (enum˙ n) (num i) V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invˡ {error (enum˙ n) (string str) V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invˡ {error (enum˙ n) (function args stmt) V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
    invˡ {error (enum˙ n) (error t x) V.∷ x₁ V.∷ V.[]} rewrite reflLemma errO = refl
