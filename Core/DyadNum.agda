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
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; refl; cong; cong₂; setoid; inspect; [_]; subst)
open import Relation.Binary using (Setoid)
open import Function using (Inverse)
open import Data.Bool using (Bool; true; false; not; _∧_; if_then_else_; T)
open import Data.Product using (proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_; map′)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary.Decidable using (no; yes)

import Function as F

module Core.DyadNum
  (amount-of-primitives : ℕ.ℕ)
  (inArgCounts : V.Vec ℕ.ℕ amount-of-primitives)
  (outArgCounts : V.Vec ℕ.ℕ amount-of-primitives)
  where

open import Core.Value amount-of-primitives inArgCounts outArgCounts
open import Core.Primitive Stack

≡ᵇt→≡ : ∀ {n m} → (n ℕ.≡ᵇ m) ≡ true → n ≡ m
≡ᵇt→≡ {n} {m} x = ℕp.≡ᵇ⇒≡ n m ((Bp.T-≡ {n ℕ.≡ᵇ m} .F.Equivalence.from) x)

≡ᵇf→≡ : ∀ {n m} → (n ℕ.≡ᵇ m) ≡ false → ¬ n ≡ m
≡ᵇf→≡ {ℕ.suc n} {ℕ.suc m} x refl = ≡ᵇf→≡ {n} {m} x refl


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
    ifNotRefl n p = Bp.if-cong (notReflLemma n errO (≡ᵇf→≡ p))

    invʳ : ∀ {x} → f˙´ (f⁼´ x) ≡ x
    invʳ {list li V.∷ x₁ V.∷ V.[]} = ifRefl
    invʳ {string str V.∷ x₁ V.∷ V.[]} = ifRefl
    invʳ {function _ _ _ V.∷ x₁ V.∷ V.[]} = ifRefl
    invʳ {num i V.∷ list li V.∷ V.[]} = ifRefl
    invʳ {num i V.∷ string str V.∷ V.[]} = ifRefl
    invʳ {num i V.∷ function _ _ _ V.∷ V.[]} = ifRefl
    invʳ {num i₁ V.∷ num i₂ V.∷ V.[]} = cong (V._∷ num i₂ V.∷ V.[]) (cong num (f-invʳ i₂ i₁))
    invʳ {num i V.∷ error (enum˙ n) x₁ V.∷ V.[]} = ifRefl
    invʳ {num i V.∷ error (enum⁼ n) x₁ V.∷ V.[]} = ifRefl
    invʳ {error (enum˙ n) (list li) V.∷ x₂ V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong (V._∷ x₂ V.∷ V.[]) (cong (λ x → error (enum˙ x) (list li)) (sym (≡ᵇt→≡ p)))
    ... | false = trans ifRefl (Bp.if-cong p)
    invʳ {error (enum˙ n) (string str) V.∷ x₂ V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong (V._∷ x₂ V.∷ V.[]) (cong (λ x → error (enum˙ x) (string str)) (sym (≡ᵇt→≡ p)))
    ... | false = trans ifRefl (ifNotRefl n p)
    invʳ {error (enum˙ n) (function inp out stmt) V.∷ x₂ V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong (V._∷ x₂ V.∷ V.[]) (cong (λ x → error (enum˙ x) (function inp out stmt)) (sym (≡ᵇt→≡ p)))
    ... | false = trans ifRefl (ifNotRefl n p)
    invʳ {error (enum˙ n) (error (enum˙ n₁) x₁) V.∷ x₂ V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong (V._∷ x₂ V.∷ V.[]) (cong (λ x → error (enum˙ x) (error (enum˙ n₁) x₁)) (sym (≡ᵇt→≡ p)))
    ... | false = trans ifRefl (ifNotRefl n p)
    invʳ {error (enum˙ n₁) (error (enum⁼ n₂) x₁) V.∷ x₂ V.∷ V.[]} with n₁ ℕ.≡ᵇ errO in p | n₂ ℕ.≡ᵇ errO in q | x₁ | x₂
    ... | false | B | a | b = trans ifRefl (ifNotRefl n₁ p)
    ... | true | true | a | b = trans (Bp.if-cong p) (Bp.if-cong q)
    ... | true | false | list li | n = trans (ifNotRefl n₂ q) (cong (λ x → error (enum˙ x) (error (enum⁼ n₂) (list li)) V.∷ n V.∷ V.[]) (sym (≡ᵇt→≡ p)))
    ... | true | false | string str | b = trans (ifNotRefl n₂ q) (cong (V._∷ b V.∷ V.[]) (cong (λ x → error (enum˙ x) (error (enum⁼ n₂) (string str))) (sym (≡ᵇt→≡ p))))
    ... | true | false | function inp out stmt | b = trans (ifNotRefl n₂ q) (cong (V._∷ b V.∷ V.[]) (cong (λ x → error (enum˙ x) (error (enum⁼ n₂) (function inp out stmt))) (sym (≡ᵇt→≡ p))))
    ... | true | false | error (enum˙ t) x | b = trans (ifNotRefl n₂ q) (cong (V._∷ b V.∷ V.[]) (cong (λ x2 → error (enum˙ x2) (error (enum⁼ n₂) (error (enum˙ t) x))) (sym (≡ᵇt→≡ p))))
    ... | true | false | error (enum⁼ t) x | b = trans (ifNotRefl n₂ q) (cong (V._∷ b V.∷ V.[]) (cong (λ x2 → error (enum˙ x2) (error (enum⁼ n₂) (error (enum⁼ t) x))) (sym (≡ᵇt→≡ p))))
    ... | true | false | num i | list li = trans (ifNotRefl n₂ q) (cong (V._∷ list li V.∷ V.[]) (cong (λ x2 → error (enum˙ x2) (error (enum⁼ n₂) (num i))) (sym (≡ᵇt→≡ p))))
    ... | true | false | num i | string str = trans (ifNotRefl n₂ q) (cong (V._∷ string str V.∷ V.[]) (cong (λ x2 → error (enum˙ x2) (error (enum⁼ n₂) (num i))) (sym (≡ᵇt→≡ p))))
    ... | true | false | num i | function inp out stmt = trans (ifNotRefl n₂ q) (cong (V._∷ function inp out stmt V.∷ V.[]) (cong (λ x2 → error (enum˙ x2) (error (enum⁼ n₂) (num i))) (sym (≡ᵇt→≡ p))))
    ... | true | false | num i | error t b = trans (ifNotRefl n₂ q) (cong (V._∷ error t b V.∷ V.[]) (cong (λ x2 → error (enum˙ x2) (error (enum⁼ n₂) (num i))) (sym (≡ᵇt→≡ p))))
    ... | true | false | num i₁ | num i₂ = trans (ifNotRefl n₂ q) (cong (V._∷ num i₂ V.∷ V.[]) (cong (λ x2 → error (enum˙ x2) (error (enum⁼ n₂) (num i₁))) (sym (≡ᵇt→≡ p))))
    invʳ {error (enum˙ n) (num i) V.∷ list li V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong (V._∷ list li V.∷ V.[]) (cong (λ x → error (enum˙ x) (num i)) (sym (≡ᵇt→≡ p)))
    ... | false = trans ifRefl (ifNotRefl n p)
    invʳ {error (enum˙ n) (num i₁) V.∷ num i₂ V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = Bp.if-cong p
    ... | false = trans ifRefl (ifNotRefl n p)
    invʳ {error (enum˙ n) (num i) V.∷ string str V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong (V._∷ string str V.∷ V.[]) (cong (λ x → error (enum˙ x) (num i)) (sym (≡ᵇt→≡ p)))
    ... | false = trans ifRefl (ifNotRefl n p)
    invʳ {error (enum˙ n) (num i) V.∷ function inp out stmt V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong (V._∷ function inp out stmt V.∷ V.[]) (cong (λ x → error (enum˙ x) (num i)) (sym (≡ᵇt→≡ p)))
    ... | false = trans ifRefl (ifNotRefl n p)
    invʳ {error (enum˙ n) (num i) V.∷ error (enum˙ n₁) x₂ V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong (V._∷ error (enum˙ n₁) x₂ V.∷ V.[]) (cong (λ x → error (enum˙ x) (num i)) (sym (≡ᵇt→≡ p)))
    ... | false = trans ifRefl (ifNotRefl n p)
    invʳ {error (enum˙ n) (num i) V.∷ error (enum⁼ n₁) x₂ V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong (V._∷ error (enum⁼ n₁) x₂ V.∷ V.[]) (cong (λ x → error (enum˙ x) (num i)) (sym (≡ᵇt→≡ p)))
    ... | false = trans ifRefl (ifNotRefl n p)
    invʳ {error (enum⁼ n) (list li) V.∷ x₁ V.∷ V.[]} = Bp.if-cong (reflLemma errO)
    invʳ {error (enum⁼ n) (num i) V.∷ x₁ V.∷ V.[]} = Bp.if-cong (reflLemma errO)
    invʳ {error (enum⁼ n) (string str) V.∷ x₁ V.∷ V.[]} = Bp.if-cong (reflLemma errO)
    invʳ {error (enum⁼ n) (function inp out stmt) V.∷ x₁ V.∷ V.[]} = Bp.if-cong (reflLemma errO)
    invʳ {error (enum⁼ n) (error n₁ x) V.∷ x₁ V.∷ V.[]} = Bp.if-cong (reflLemma errO)

    invˡ : ∀ {x} → f⁼´ (f˙´ x) ≡ x
    invˡ {num i₁                           V.∷ num i₂            V.∷ V.[]} = cong (V._∷ num i₂ V.∷ V.[]) (cong num (f-invˡ i₂ i₁))
    invˡ {list _                           V.∷ _                 V.∷ V.[]} = ifRefl
    invˡ {string _                         V.∷ _                 V.∷ V.[]} = ifRefl
    invˡ {function _ _ _                   V.∷ _                 V.∷ V.[]} = ifRefl
    invˡ {num _                            V.∷ list _            V.∷ V.[]} = ifRefl
    invˡ {num _                            V.∷ string _          V.∷ V.[]} = ifRefl
    invˡ {num _                            V.∷ function _ _ _    V.∷ V.[]} = ifRefl
    invˡ {num _                            V.∷ error (enum⁼ _) _ V.∷ V.[]} = ifRefl
    invˡ {num _                            V.∷ error (enum˙ _) _ V.∷ V.[]} = ifRefl
    invˡ {error (enum˙ _) (list _)         V.∷ _                 V.∷ V.[]} = Bp.if-cong (reflLemma errO)
    invˡ {error (enum˙ _) (num _)          V.∷ _                 V.∷ V.[]} = Bp.if-cong (reflLemma errO)
    invˡ {error (enum˙ _) (string _)       V.∷ _                 V.∷ V.[]} = Bp.if-cong (reflLemma errO)
    invˡ {error (enum˙ _) (function _ _ _) V.∷ _                 V.∷ V.[]} = Bp.if-cong (reflLemma errO)
    invˡ {error (enum˙ _) (error _ _)      V.∷ _                 V.∷ V.[]} = Bp.if-cong (reflLemma errO)
    invˡ {error (enum⁼ n) (list _) V.∷ _ V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong₂ V._∷_ (cong₂ error (cong enum⁼ (sym (≡ᵇt→≡ p))) refl) refl
    ... | false = trans ifRefl (Bp.if-cong p)
    invˡ {error (enum⁼ n) (string _) V.∷ _ V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong₂ V._∷_ (cong₂ error (cong enum⁼ (sym (≡ᵇt→≡ p))) refl) refl
    ... | false = trans ifRefl (ifNotRefl n p)
    invˡ {error (enum⁼ n) (function _ _ _) V.∷ _ V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong₂ V._∷_ (cong₂ error (cong enum⁼ (sym (≡ᵇt→≡ p))) refl) refl
    ... | false = trans ifRefl (ifNotRefl n p)
    invˡ {error (enum⁼ n) (error (enum⁼ _) _) V.∷ _ V.∷ V.[]} with n ℕ.≡ᵇ errO in p
    ... | true = cong₂ V._∷_ (cong₂ error (cong enum⁼ (sym (≡ᵇt→≡ p))) refl) refl
    ... | false = trans ifRefl (ifNotRefl n p)

    invˡ {error (enum⁼ n) (num i) V.∷ x V.∷ V.[]} with n ℕ.≡ᵇ errO in p | x
    ... | true  | num _             = trans (cong f⁼´ (Bp.if-cong p)) (Bp.if-cong p)
    ... | true  | list _            = trans (cong f⁼´ (Bp.if-cong p)) (cong₂ V._∷_ (cong₂ error (cong enum⁼ (sym (≡ᵇt→≡ p))) refl) refl)
    ... | true  | string _          = trans (cong f⁼´ (Bp.if-cong p)) (cong₂ V._∷_ (cong₂ error (cong enum⁼ (sym (≡ᵇt→≡ p))) refl) refl)
    ... | true  | function _ _ _    = trans (cong f⁼´ (Bp.if-cong p)) (cong₂ V._∷_ (cong₂ error (cong enum⁼ (sym (≡ᵇt→≡ p))) refl) refl)
    ... | true  | error (enum⁼ _) _ = trans (cong f⁼´ (Bp.if-cong p)) (cong₂ V._∷_ (cong₂ error (cong enum⁼ (sym (≡ᵇt→≡ p))) refl) refl)
    ... | true  | error (enum˙ _) _ = trans (cong f⁼´ (Bp.if-cong p)) (cong₂ V._∷_ (cong₂ error (cong enum⁼ (sym (≡ᵇt→≡ p))) refl) refl)
    ... | false | num _             = trans (cong f⁼´ (ifNotRefl n p)) (trans ifRefl (ifNotRefl n p))
    ... | false | list _            = trans (cong f⁼´ (ifNotRefl n p)) (trans ifRefl (ifNotRefl n p))
    ... | false | string _          = trans (cong f⁼´ (ifNotRefl n p)) (trans ifRefl (ifNotRefl n p))
    ... | false | function _ _ _    = trans (cong f⁼´ (ifNotRefl n p)) (trans ifRefl (ifNotRefl n p))
    ... | false | error (enum⁼ _) _ = trans (cong f⁼´ (ifNotRefl n p)) (trans ifRefl (ifNotRefl n p))
    ... | false | error (enum˙ a) b = trans (cong f⁼´ (ifNotRefl n p)) (trans ifRefl (ifNotRefl n p))
    invˡ {error (enum⁼ n₁) (error (enum˙ n₂) x₁) V.∷ x₂ V.∷ V.[]} with n₁ ℕ.≡ᵇ errO in p | n₂ ℕ.≡ᵇ errO in q | x₁ | x₂
    ... | false | B     | a                     | b                     = trans ifRefl (ifNotRefl n₁ p)
    ... | true  | true  | a                     | b                     = trans (Bp.if-cong p) (Bp.if-cong q)
    ... | true  | false | list li               | n                     = trans (ifNotRefl n₂ q) (cong₂ V._∷_ (cong₂ error (cong enum⁼ (sym (≡ᵇt→≡ p))) refl) refl)
    ... | true  | false | string str            | b                     = trans (ifNotRefl n₂ q) (cong₂ V._∷_ (cong₂ error (cong enum⁼ (sym (≡ᵇt→≡ p))) refl) refl)
    ... | true  | false | function inp out stmt | b                     = trans (ifNotRefl n₂ q) (cong₂ V._∷_ (cong₂ error (cong enum⁼ (sym (≡ᵇt→≡ p))) refl) refl)
    ... | true  | false | error (enum⁼ t) x     | b                     = trans (ifNotRefl n₂ q) (cong₂ V._∷_ (cong₂ error (cong enum⁼ (sym (≡ᵇt→≡ p))) refl) refl)
    ... | true  | false | error (enum˙ t) x     | b                     = trans (ifNotRefl n₂ q) (cong₂ V._∷_ (cong₂ error (cong enum⁼ (sym (≡ᵇt→≡ p))) refl) refl)
    ... | true  | false | num i                 | list li               = trans (ifNotRefl n₂ q) (cong₂ V._∷_ (cong₂ error (cong enum⁼ (sym (≡ᵇt→≡ p))) refl) refl)
    ... | true  | false | num i                 | string str            = trans (ifNotRefl n₂ q) (cong₂ V._∷_ (cong₂ error (cong enum⁼ (sym (≡ᵇt→≡ p))) refl) refl)
    ... | true  | false | num i                 | function inp out stmt = trans (ifNotRefl n₂ q) (cong₂ V._∷_ (cong₂ error (cong enum⁼ (sym (≡ᵇt→≡ p))) refl) refl)
    ... | true  | false | num i                 | error t b             = trans (ifNotRefl n₂ q) (cong₂ V._∷_ (cong₂ error (cong enum⁼ (sym (≡ᵇt→≡ p))) refl) refl)
    ... | true  | false | num i₁                | num i₂                = trans (ifNotRefl n₂ q) (cong₂ V._∷_ (cong₂ error (cong enum⁼ (sym (≡ᵇt→≡ p))) refl) refl)
