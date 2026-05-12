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

module Core.DyadNum where

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
        then error (enum˙ n₁) (error (enum⁼ n₂) v₁) V.∷ v₂ V.∷ V.[]
        else error (enum˙ n₂) v₁ V.∷ v₂ V.∷ V.[]
      else error (enum˙ errO) (error (enum⁼ n₁) (error (enum˙ n₂) v₁)) V.∷ v₂ V.∷ V.[]

    f˙´ (error (enum⁼ n) (num v₁) V.∷ (num v₂) V.∷ s) =
      if n ℕ.≡ᵇ errO
      then error (enum˙ n) (num v₁) V.∷ num v₂ V.∷ s
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
        then error (enum⁼ n₁) (error (enum˙ n₂) v₁) V.∷ v₂ V.∷ V.[]
        else error (enum⁼ n₂) v₁ V.∷ v₂ V.∷ V.[]
      else error (enum⁼ errO) (error (enum˙ n₁) (error (enum⁼ n₂) v₁)) V.∷ v₂ V.∷ V.[]

    f⁼´ (error (enum˙ n) (num v₁) V.∷ num v₂ V.∷ s) =
      if n ℕ.≡ᵇ errO
      then error (enum⁼ n) (num v₁) V.∷ (num v₂) V.∷ s
      else error (enum⁼ errO) (error (enum˙ n) (num v₁)) V.∷ num v₂ V.∷ s

    f⁼´ (error (enum˙ n) v₁ V.∷ v₂ V.∷ s) =
      if n ℕ.≡ᵇ errO
      then v₁ V.∷ v₂ V.∷ s
      else error (enum⁼ errO) (error (enum˙ n) v₁) V.∷ v₂ V.∷ s

    f⁼´ (v₁ V.∷ v₂ V.∷ s) = error (enum⁼ errO) v₁ V.∷ v₂ V.∷ s

    ifRefl : ∀ {x y} → (if errO ℕ.≡ᵇ errO then x else y) ≡ x
    ifRefl = Bp.if-cong (reflLemma errO)

    ifNotRefl : ∀ {x y : Stack 2} n → (p : (n ℕ.≡ᵇ errO) ≡ false) → (if n ℕ.≡ᵇ errO then x else y) ≡ y
    ifNotRefl n p = Bp.if-cong (notReflLemma n errO (≡ᵇf→≡ n errO p))

    if_≡errO-then_else_ : ∀ n → {x y z w : Stack 2} → (l : (n ℕ.≡ᵇ errO) ≡ true → x ≡ z) → (r : (n ℕ.≡ᵇ errO) ≡ false → y ≡ w) → (if n ℕ.≡ᵇ errO then x else y) ≡ (if n ℕ.≡ᵇ errO then z else w)
    if_≡errO-then_else_ n l r with n ℕ.≡ᵇ errO
    ... | true = l refl
    ... | false = r refl

    invʳ : ∀ {x} → f˙´ (f⁼´ x) ≡ x
    invʳ {list li V.∷ x₁ V.∷ V.[]} = ifRefl
    invʳ {string str V.∷ x₁ V.∷ V.[]} = ifRefl
    invʳ {function args stmt V.∷ x₁ V.∷ V.[]} = ifRefl
    invʳ {num i V.∷ list li V.∷ V.[]} = ifRefl
    invʳ {num i V.∷ string str V.∷ V.[]} = ifRefl
    invʳ {num i V.∷ function args stmt V.∷ V.[]} = ifRefl
    invʳ {num i₁ V.∷ num i₂ V.∷ V.[]} = cong (V._∷ num i₂ V.∷ V.[]) (cong num (f-invʳ i₂ i₁))
    invʳ {num i V.∷ error (enum˙ n) x₁ V.∷ V.[]} = ifRefl
    invʳ {num i V.∷ error (enum⁼ n) x₁ V.∷ V.[]} = ifRefl
    invʳ {error (enum˙ n) (list li) V.∷ x₂ V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong (V._∷ x₂ V.∷ V.[]) (cong (λ x → error (enum˙ x) (list li)) (sym (≡ᵇt→≡ n errO p)))
    ... | false = trans ifRefl (Bp.if-cong p)
    invʳ {error (enum˙ n) (string str) V.∷ x₂ V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong (V._∷ x₂ V.∷ V.[]) (cong (λ x → error (enum˙ x) (string str)) (sym (≡ᵇt→≡ n errO p)))
    ... | false = trans ifRefl (ifNotRefl n p)
    invʳ {error (enum˙ n) (function args stmt) V.∷ x₂ V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong (V._∷ x₂ V.∷ V.[]) (cong (λ x → error (enum˙ x) (function args stmt)) (sym (≡ᵇt→≡ n errO p)))
    ... | false = trans ifRefl (ifNotRefl n p)
    invʳ {error (enum˙ n) (error (enum˙ n₁) x₁) V.∷ x₂ V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong (V._∷ x₂ V.∷ V.[]) (cong (λ x → error (enum˙ x) (error (enum˙ n₁) x₁)) (sym (≡ᵇt→≡ n errO p)))
    ... | false = trans ifRefl (ifNotRefl n p)
    invʳ {error (enum˙ n₁) (error (enum⁼ n₂) x₁) V.∷ x₂ V.∷ V.[]} with n₁ ℕ.≡ᵇ errO in p | n₂ ℕ.≡ᵇ errO in q | x₁ | x₂
    ... | false | B | a | b = trans ifRefl (ifNotRefl n₁ p)
    ... | true | true | a | b = trans (Bp.if-cong p) (Bp.if-cong q)
    ... | true | false | list li | n = trans (ifNotRefl n₂ q) (cong (λ x → error (enum˙ x) (error (enum⁼ n₂) (list li)) V.∷ n V.∷ V.[]) (sym (≡ᵇt→≡ n₁ errO p)))
    ... | true | false | string str | b = trans (ifNotRefl n₂ q) (cong (V._∷ b V.∷ V.[]) (cong (λ x → error (enum˙ x) (error (enum⁼ n₂) (string str))) (sym (≡ᵇt→≡ n₁ errO p))))
    ... | true | false | function args stmt | b = trans (ifNotRefl n₂ q) (cong (V._∷ b V.∷ V.[]) (cong (λ x → error (enum˙ x) (error (enum⁼ n₂) (function args stmt))) (sym (≡ᵇt→≡ n₁ errO p))))
    ... | true | false | error (enum˙ t) x | b = trans (ifNotRefl n₂ q) (cong (V._∷ b V.∷ V.[]) (cong (λ x2 → error (enum˙ x2) (error (enum⁼ n₂) (error (enum˙ t) x))) (sym (≡ᵇt→≡ n₁ errO p))))
    ... | true | false | error (enum⁼ t) x | b = trans (ifNotRefl n₂ q) (cong (V._∷ b V.∷ V.[]) (cong (λ x2 → error (enum˙ x2) (error (enum⁼ n₂) (error (enum⁼ t) x))) (sym (≡ᵇt→≡ n₁ errO p))))
    ... | true | false | num i | list li = trans (ifNotRefl n₂ q) (cong (V._∷ list li V.∷ V.[]) (cong (λ x2 → error (enum˙ x2) (error (enum⁼ n₂) (num i))) (sym (≡ᵇt→≡ n₁ errO p))))
    ... | true | false | num i | string str = trans (ifNotRefl n₂ q) (cong (V._∷ string str V.∷ V.[]) (cong (λ x2 → error (enum˙ x2) (error (enum⁼ n₂) (num i))) (sym (≡ᵇt→≡ n₁ errO p))))
    ... | true | false | num i | function args stmt = trans (ifNotRefl n₂ q) (cong (V._∷ function args stmt V.∷ V.[]) (cong (λ x2 → error (enum˙ x2) (error (enum⁼ n₂) (num i))) (sym (≡ᵇt→≡ n₁ errO p))))
    ... | true | false | num i | error t b = trans (ifNotRefl n₂ q) (cong (V._∷ error t b V.∷ V.[]) (cong (λ x2 → error (enum˙ x2) (error (enum⁼ n₂) (num i))) (sym (≡ᵇt→≡ n₁ errO p))))
    ... | true | false | num i₁ | num i₂ = trans (ifNotRefl n₂ q) (cong (V._∷ num i₂ V.∷ V.[]) (cong (λ x2 → error (enum˙ x2) (error (enum⁼ n₂) (num i₁))) (sym (≡ᵇt→≡ n₁ errO p))))
    invʳ {error (enum˙ n) (num i) V.∷ list li V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong (V._∷ list li V.∷ V.[]) (cong (λ x → error (enum˙ x) (num i)) (sym (≡ᵇt→≡ n errO p)))
    ... | false = trans ifRefl (ifNotRefl n p)
    invʳ {error (enum˙ n) (num i₁) V.∷ num i₂ V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = Bp.if-cong p
    ... | false = trans ifRefl (ifNotRefl n p)
    invʳ {error (enum˙ n) (num i) V.∷ string str V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong (V._∷ string str V.∷ V.[]) (cong (λ x → error (enum˙ x) (num i)) (sym (≡ᵇt→≡ n errO p)))
    ... | false = trans ifRefl (ifNotRefl n p)
    invʳ {error (enum˙ n) (num i) V.∷ function args stmt V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong (V._∷ function args stmt V.∷ V.[]) (cong (λ x → error (enum˙ x) (num i)) (sym (≡ᵇt→≡ n errO p)))
    ... | false = trans ifRefl (ifNotRefl n p)
    invʳ {error (enum˙ n) (num i) V.∷ error (enum˙ n₁) x₂ V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong (V._∷ error (enum˙ n₁) x₂ V.∷ V.[]) (cong (λ x → error (enum˙ x) (num i)) (sym (≡ᵇt→≡ n errO p)))
    ... | false = trans ifRefl (ifNotRefl n p)
    invʳ {error (enum˙ n) (num i) V.∷ error (enum⁼ n₁) x₂ V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong (V._∷ error (enum⁼ n₁) x₂ V.∷ V.[]) (cong (λ x → error (enum˙ x) (num i)) (sym (≡ᵇt→≡ n errO p)))
    ... | false = trans ifRefl (ifNotRefl n p)
    invʳ {error (enum⁼ n) (list li) V.∷ x₁ V.∷ V.[]} = Bp.if-cong (reflLemma errO)
    invʳ {error (enum⁼ n) (num i) V.∷ x₁ V.∷ V.[]} = Bp.if-cong (reflLemma errO)
    invʳ {error (enum⁼ n) (string str) V.∷ x₁ V.∷ V.[]} = Bp.if-cong (reflLemma errO)
    invʳ {error (enum⁼ n) (function args stmt) V.∷ x₁ V.∷ V.[]} = Bp.if-cong (reflLemma errO)
    invʳ {error (enum⁼ n) (error n₁ x) V.∷ x₁ V.∷ V.[]} = Bp.if-cong (reflLemma errO)

    invˡ : ∀ {x} → f⁼´ (f˙´ x) ≡ x
    invˡ {list li V.∷ x₁ V.∷ V.[]} = ifRefl
    invˡ {string str V.∷ x₁ V.∷ V.[]} = ifRefl
    invˡ {function args stmt V.∷ x₁ V.∷ V.[]} = ifRefl
    invˡ {num i V.∷ list li V.∷ V.[]} = ifRefl
    invˡ {num i V.∷ string str V.∷ V.[]} = ifRefl
    invˡ {num i V.∷ function args stmt V.∷ V.[]} = ifRefl
    invˡ {num i₁ V.∷ num i₂ V.∷ V.[]} = cong (V._∷ num i₂ V.∷ V.[]) (cong num (f-invˡ i₂ i₁))
    invˡ {num i V.∷ error (enum⁼ n) x₁ V.∷ V.[]} = ifRefl
    invˡ {num i V.∷ error (enum˙ n) x₁ V.∷ V.[]} = ifRefl
    invˡ {error (enum⁼ n) (list li) V.∷ x₂ V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong (V._∷ x₂ V.∷ V.[]) (cong (λ x → error (enum⁼ x) (list li)) (sym (≡ᵇt→≡ n errO p)))
    ... | false = trans ifRefl (Bp.if-cong p)
    invˡ {error (enum⁼ n) (string str) V.∷ x₂ V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong (V._∷ x₂ V.∷ V.[]) (cong (λ x → error (enum⁼ x) (string str)) (sym (≡ᵇt→≡ n errO p)))
    ... | false = trans ifRefl (ifNotRefl n p)
    invˡ {error (enum⁼ n) (function args stmt) V.∷ x₂ V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong (V._∷ x₂ V.∷ V.[]) (cong (λ x → error (enum⁼ x) (function args stmt)) (sym (≡ᵇt→≡ n errO p)))
    ... | false = trans ifRefl (ifNotRefl n p)
    invˡ {error (enum⁼ n) (error (enum⁼ n₁) x₁) V.∷ x₂ V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong (V._∷ x₂ V.∷ V.[]) (cong (λ x → error (enum⁼ x) (error (enum⁼ n₁) x₁)) (sym (≡ᵇt→≡ n errO p)))
    ... | false = trans ifRefl (ifNotRefl n p)
    invˡ {error (enum⁼ n₁) (error (enum˙ n₂) x₁) V.∷ x₂ V.∷ V.[]} with n₁ ℕ.≡ᵇ errO in p | n₂ ℕ.≡ᵇ errO in q | x₁ | x₂
    ... | false | B | a | b = trans ifRefl (ifNotRefl n₁ p)
    ... | true | true | a | b = trans (Bp.if-cong p) (Bp.if-cong q)
    ... | true | false | list li | n = trans (ifNotRefl n₂ q) (cong (λ x → error (enum⁼ x) (error (enum˙ n₂) (list li)) V.∷ n V.∷ V.[]) (sym (≡ᵇt→≡ n₁ errO p)))
    ... | true | false | string str | b = trans (ifNotRefl n₂ q) (cong (V._∷ b V.∷ V.[]) (cong (λ x → error (enum⁼ x) (error (enum˙ n₂) (string str))) (sym (≡ᵇt→≡ n₁ errO p))))
    ... | true | false | function args stmt | b = trans (ifNotRefl n₂ q) (cong (V._∷ b V.∷ V.[]) (cong (λ x → error (enum⁼ x) (error (enum˙ n₂) (function args stmt))) (sym (≡ᵇt→≡ n₁ errO p))))
    ... | true | false | error (enum⁼ t) x | b = trans (ifNotRefl n₂ q) (cong (V._∷ b V.∷ V.[]) (cong (λ x2 → error (enum⁼ x2) (error (enum˙ n₂) (error (enum⁼ t) x))) (sym (≡ᵇt→≡ n₁ errO p))))
    ... | true | false | error (enum˙ t) x | b = trans (ifNotRefl n₂ q) (cong (V._∷ b V.∷ V.[]) (cong (λ x2 → error (enum⁼ x2) (error (enum˙ n₂) (error (enum˙ t) x))) (sym (≡ᵇt→≡ n₁ errO p))))
    ... | true | false | num i | list li = trans (ifNotRefl n₂ q) (cong (V._∷ list li V.∷ V.[]) (cong (λ x2 → error (enum⁼ x2) (error (enum˙ n₂) (num i))) (sym (≡ᵇt→≡ n₁ errO p))))
    ... | true | false | num i | string str = trans (ifNotRefl n₂ q) (cong (V._∷ string str V.∷ V.[]) (cong (λ x2 → error (enum⁼ x2) (error (enum˙ n₂) (num i))) (sym (≡ᵇt→≡ n₁ errO p))))
    ... | true | false | num i | function args stmt = trans (ifNotRefl n₂ q) (cong (V._∷ function args stmt V.∷ V.[]) (cong (λ x2 → error (enum⁼ x2) (error (enum˙ n₂) (num i))) (sym (≡ᵇt→≡ n₁ errO p))))
    ... | true | false | num i | error t b = trans (ifNotRefl n₂ q) (cong (V._∷ error t b V.∷ V.[]) (cong (λ x2 → error (enum⁼ x2) (error (enum˙ n₂) (num i))) (sym (≡ᵇt→≡ n₁ errO p))))
    ... | true | false | num i₁ | num i₂ = trans (ifNotRefl n₂ q) (cong (V._∷ num i₂ V.∷ V.[]) (cong (λ x2 → error (enum⁼ x2) (error (enum˙ n₂) (num i₁))) (sym (≡ᵇt→≡ n₁ errO p))))
    invˡ {error (enum⁼ n) (num i) V.∷ list li V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong (V._∷ list li V.∷ V.[]) (cong (λ x → error (enum⁼ x) (num i)) (sym (≡ᵇt→≡ n errO p)))
    ... | false = trans ifRefl (ifNotRefl n p)
    invˡ {error (enum⁼ n) (num i₁) V.∷ num i₂ V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = Bp.if-cong p
    ... | false = trans ifRefl (ifNotRefl n p)
    invˡ {error (enum⁼ n) (num i) V.∷ string str V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong (V._∷ string str V.∷ V.[]) (cong (λ x → error (enum⁼ x) (num i)) (sym (≡ᵇt→≡ n errO p)))
    ... | false = trans ifRefl (ifNotRefl n p)
    invˡ {error (enum⁼ n) (num i) V.∷ function args stmt V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong (V._∷ function args stmt V.∷ V.[]) (cong (λ x → error (enum⁼ x) (num i)) (sym (≡ᵇt→≡ n errO p)))
    ... | false = trans ifRefl (ifNotRefl n p)
    invˡ {error (enum⁼ n) (num i) V.∷ error (enum⁼ n₁) x₂ V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong (V._∷ error (enum⁼ n₁) x₂ V.∷ V.[]) (cong (λ x → error (enum⁼ x) (num i)) (sym (≡ᵇt→≡ n errO p)))
    ... | false = trans ifRefl (ifNotRefl n p)
    invˡ {error (enum⁼ n) (num i) V.∷ error (enum˙ n₁) x₂ V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong (V._∷ error (enum˙ n₁) x₂ V.∷ V.[]) (cong (λ x → error (enum⁼ x) (num i)) (sym (≡ᵇt→≡ n errO p)))
    ... | false = trans ifRefl (ifNotRefl n p)
    invˡ {error (enum˙ n) (list li) V.∷ x₁ V.∷ V.[]} = Bp.if-cong (reflLemma errO)
    invˡ {error (enum˙ n) (num i) V.∷ x₁ V.∷ V.[]} = Bp.if-cong (reflLemma errO)
    invˡ {error (enum˙ n) (string str) V.∷ x₁ V.∷ V.[]} = Bp.if-cong (reflLemma errO)
    invˡ {error (enum˙ n) (function args stmt) V.∷ x₁ V.∷ V.[]} = Bp.if-cong (reflLemma errO)
    invˡ {error (enum˙ n) (error n₁ x) V.∷ x₁ V.∷ V.[]} = Bp.if-cong (reflLemma errO)
