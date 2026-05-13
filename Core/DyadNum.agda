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

    if_≡errO-then_else_ : ∀ n → {x y z w : Stack 2} → (l : (n ℕ.≡ᵇ errO) ≡ true → x ≡ z) → (r : (n ℕ.≡ᵇ errO) ≡ false → y ≡ w) → (if n ℕ.≡ᵇ errO then x else y) ≡ (if n ℕ.≡ᵇ errO then z else w)
    if_≡errO-then_else_ n l r with n ℕ.≡ᵇ errO
    ... | true = l refl
    ... | false = r refl

    distrib-if : (b : Bool) {x y : Stack 2} → (f : Stack 2 → Stack 2) → (f (if b then x else y)) ≡ (if b then f x else f y)
    distrib-if false f = refl
    distrib-if true  f = refl

    invʳ : ∀ {x} → f˙´ (f⁼´ x) ≡ x
    invʳ {num i₁                                        V.∷ num i₂            V.∷ V.[]} = cong (V._∷ num i₂ V.∷ V.[]) (cong num (f-invʳ i₂ i₁))
    invʳ {list _                                        V.∷ _                 V.∷ V.[]} = ifRefl
    invʳ {string _                                      V.∷ _                 V.∷ V.[]} = ifRefl
    invʳ {function _ _ _                                V.∷ _                 V.∷ V.[]} = ifRefl
    invʳ {num _                                         V.∷ list _            V.∷ V.[]} = ifRefl
    invʳ {num _                                         V.∷ string _          V.∷ V.[]} = ifRefl
    invʳ {num _                                         V.∷ function _ _ _    V.∷ V.[]} = ifRefl
    invʳ {num _                                         V.∷ error (enum˙ _) _ V.∷ V.[]} = ifRefl
    invʳ {num _                                         V.∷ error (enum⁼ _) _ V.∷ V.[]} = ifRefl
    invʳ {error (enum⁼ _) (list _)                      V.∷ _                 V.∷ V.[]} = Bp.if-cong (reflLemma errO)
    invʳ {error (enum⁼ _) (num _)                       V.∷ _                 V.∷ V.[]} = Bp.if-cong (reflLemma errO)
    invʳ {error (enum⁼ _) (string _)                    V.∷ _                 V.∷ V.[]} = Bp.if-cong (reflLemma errO)
    invʳ {error (enum⁼ _) (function _ _ _)              V.∷ _                 V.∷ V.[]} = Bp.if-cong (reflLemma errO)
    invʳ {error (enum⁼ _) (error _ _)                   V.∷ _                 V.∷ V.[]} = Bp.if-cong (reflLemma errO)
    invʳ {error (enum˙ n) (list li)                     V.∷ _                 V.∷ V.[]} = trans (distrib-if (n ℕ.≡ᵇ errO) f˙´) (trans (if n ≡errO-then (λ x₁ → cong₂ V._∷_ (cong₂ error (cong enum˙ (sym (≡ᵇt→≡ x₁))) refl) refl)  else λ x₁ → trans ifRefl (trans (Bp.if-cong (notReflLemma n errO (≡ᵇf→≡ x₁))) refl)) (trans (Bp.if-cong₂ (n ℕ.≡ᵇ errO) refl  refl) (Bp.if-eta (n ℕ.≡ᵇ errO))))
    invʳ {error (enum˙ n) (string _)                    V.∷ _                 V.∷ V.[]} = trans (distrib-if (n ℕ.≡ᵇ errO) f˙´) (trans (if n ≡errO-then (λ x₁ → cong₂ V._∷_ (cong₂ error (cong enum˙ (sym (≡ᵇt→≡ x₁))) refl) refl)  else λ x₁ → trans ifRefl (trans (Bp.if-cong (notReflLemma n errO (≡ᵇf→≡ x₁))) refl)) (trans (Bp.if-cong₂ (n ℕ.≡ᵇ errO) refl  refl) (Bp.if-eta (n ℕ.≡ᵇ errO))))
    invʳ {error (enum˙ n) (function _ _ _)              V.∷ _                 V.∷ V.[]} = trans (distrib-if (n ℕ.≡ᵇ errO) f˙´) (trans (if n ≡errO-then (λ x₁ → cong₂ V._∷_ (cong₂ error (cong enum˙ (sym (≡ᵇt→≡ x₁))) refl) refl)  else λ x₁ → trans ifRefl (trans (Bp.if-cong (notReflLemma n errO (≡ᵇf→≡ x₁))) refl)) (trans (Bp.if-cong₂ (n ℕ.≡ᵇ errO) refl  refl) (Bp.if-eta (n ℕ.≡ᵇ errO))))
    invʳ {error (enum˙ n) (error (enum˙ _) _)           V.∷ _                 V.∷ V.[]} = trans (distrib-if (n ℕ.≡ᵇ errO) f˙´) (trans (if n ≡errO-then (λ x₁ → cong₂ V._∷_ (cong₂ error (cong enum˙ (sym (≡ᵇt→≡ x₁))) refl) refl)  else λ x₁ → trans ifRefl (trans (Bp.if-cong (notReflLemma n errO (≡ᵇf→≡ x₁))) refl)) (trans (Bp.if-cong₂ (n ℕ.≡ᵇ errO) refl  refl) (Bp.if-eta (n ℕ.≡ᵇ errO))))
    invʳ {error (enum˙ n) (num i)                       V.∷ list _            V.∷ V.[]} = trans (distrib-if (n ℕ.≡ᵇ errO) f˙´) (trans (if n ≡errO-then (λ x₁ → cong₂ V._∷_ (cong₂ error (cong enum˙ (sym (≡ᵇt→≡ x₁))) refl) refl)  else λ x₁ → trans ifRefl (trans (Bp.if-cong (notReflLemma n errO (≡ᵇf→≡ x₁))) refl)) (trans (Bp.if-cong₂ (n ℕ.≡ᵇ errO) refl  refl) (Bp.if-eta (n ℕ.≡ᵇ errO))))
    invʳ {error (enum˙ n) (num i)                       V.∷ string _          V.∷ V.[]} = trans (distrib-if (n ℕ.≡ᵇ errO) f˙´) (trans (if n ≡errO-then (λ x₁ → cong₂ V._∷_ (cong₂ error (cong enum˙ (sym (≡ᵇt→≡ x₁))) refl) refl)  else λ x₁ → trans ifRefl (trans (Bp.if-cong (notReflLemma n errO (≡ᵇf→≡ x₁))) refl)) (trans (Bp.if-cong₂ (n ℕ.≡ᵇ errO) refl  refl) (Bp.if-eta (n ℕ.≡ᵇ errO))))
    invʳ {error (enum˙ n) (num i)                       V.∷ function _ _ _    V.∷ V.[]} = trans (distrib-if (n ℕ.≡ᵇ errO) f˙´) (trans (if n ≡errO-then (λ x₁ → cong₂ V._∷_ (cong₂ error (cong enum˙ (sym (≡ᵇt→≡ x₁))) refl) refl)  else λ x₁ → trans ifRefl (trans (Bp.if-cong (notReflLemma n errO (≡ᵇf→≡ x₁))) refl)) (trans (Bp.if-cong₂ (n ℕ.≡ᵇ errO) refl  refl) (Bp.if-eta (n ℕ.≡ᵇ errO))))
    invʳ {error (enum˙ n) (num i)                       V.∷ error (enum˙ _) _ V.∷ V.[]} = trans (distrib-if (n ℕ.≡ᵇ errO) f˙´) (trans (if n ≡errO-then (λ x₁ → cong₂ V._∷_ (cong₂ error (cong enum˙ (sym (≡ᵇt→≡ x₁))) refl) refl)  else λ x₁ → trans ifRefl (trans (Bp.if-cong (notReflLemma n errO (≡ᵇf→≡ x₁))) refl)) (trans (Bp.if-cong₂ (n ℕ.≡ᵇ errO) refl  refl) (Bp.if-eta (n ℕ.≡ᵇ errO))))
    invʳ {error (enum˙ n) (num i)                       V.∷ error (enum⁼ a) b V.∷ V.[]} = trans (distrib-if (n ℕ.≡ᵇ errO) f˙´) (trans (if n ≡errO-then (λ x₁ → cong₂ V._∷_ (cong₂ error (cong enum˙ (sym (≡ᵇt→≡ x₁))) refl) refl)  else λ x₁ → trans ifRefl (trans (Bp.if-cong (notReflLemma n errO (≡ᵇf→≡ x₁))) refl)) (trans (Bp.if-cong₂ (n ℕ.≡ᵇ errO) refl  refl) (Bp.if-eta (n ℕ.≡ᵇ errO))))
    invʳ {error (enum˙ n) (num i)                       V.∷ num _             V.∷ V.[]} = trans (distrib-if (n ℕ.≡ᵇ errO) f˙´) (trans (if n ≡errO-then (λ x₁ → Bp.if-cong x₁) else λ x₁ → trans ifRefl (trans (Bp.if-cong (notReflLemma n errO (≡ᵇf→≡ x₁))) refl)) (trans (Bp.if-cong₂ (n ℕ.≡ᵇ errO) refl  refl) (Bp.if-eta (n ℕ.≡ᵇ errO))))

    invʳ {error (enum˙ n₁) (error (enum⁼ n₂) x₁) V.∷ x₂ V.∷ V.[]} with n₁ ℕ.≡ᵇ errO in p | n₂ ℕ.≡ᵇ errO in q | x₁ | x₂
    ... | false | B     | a                     | b                     = trans ifRefl (ifNotRefl n₁ p)
    ... | true  | true  | a                     | b                     = trans (Bp.if-cong p) (Bp.if-cong q)
    ... | true  | false | list li               | n                     = trans (ifNotRefl n₂ q) (cong₂ V._∷_ (cong₂ error (cong enum˙ (sym (≡ᵇt→≡ p))) refl) refl)
    ... | true  | false | string str            | b                     = trans (ifNotRefl n₂ q) (cong₂ V._∷_ (cong₂ error (cong enum˙ (sym (≡ᵇt→≡ p))) refl) refl)
    ... | true  | false | function inp out stmt | b                     = trans (ifNotRefl n₂ q) (cong₂ V._∷_ (cong₂ error (cong enum˙ (sym (≡ᵇt→≡ p))) refl) refl)
    ... | true  | false | error (enum˙ t) x     | b                     = trans (ifNotRefl n₂ q) (cong₂ V._∷_ (cong₂ error (cong enum˙ (sym (≡ᵇt→≡ p))) refl) refl)
    ... | true  | false | error (enum⁼ t) x     | b                     = trans (ifNotRefl n₂ q) (cong₂ V._∷_ (cong₂ error (cong enum˙ (sym (≡ᵇt→≡ p))) refl) refl)
    ... | true  | false | num i                 | list li               = trans (ifNotRefl n₂ q) (cong₂ V._∷_ (cong₂ error (cong enum˙ (sym (≡ᵇt→≡ p))) refl) refl)
    ... | true  | false | num i                 | string str            = trans (ifNotRefl n₂ q) (cong₂ V._∷_ (cong₂ error (cong enum˙ (sym (≡ᵇt→≡ p))) refl) refl)
    ... | true  | false | num i                 | function inp out stmt = trans (ifNotRefl n₂ q) (cong₂ V._∷_ (cong₂ error (cong enum˙ (sym (≡ᵇt→≡ p))) refl) refl)
    ... | true  | false | num i                 | error t b             = trans (ifNotRefl n₂ q) (cong₂ V._∷_ (cong₂ error (cong enum˙ (sym (≡ᵇt→≡ p))) refl) refl)
    ... | true  | false | num i₁                | num i₂                = trans (ifNotRefl n₂ q) (cong₂ V._∷_ (cong₂ error (cong enum˙ (sym (≡ᵇt→≡ p))) refl) refl)


    invˡ : ∀ {x} → f⁼´ (f˙´ x) ≡ x
    invˡ {num i₁                                        V.∷ num i₂            V.∷ V.[]} = cong (V._∷ num i₂ V.∷ V.[]) (cong num (f-invˡ i₂ i₁))
    invˡ {list _                                        V.∷ _                 V.∷ V.[]} = ifRefl
    invˡ {string _                                      V.∷ _                 V.∷ V.[]} = ifRefl
    invˡ {function _ _ _                                V.∷ _                 V.∷ V.[]} = ifRefl
    invˡ {num _                                         V.∷ list _            V.∷ V.[]} = ifRefl
    invˡ {num _                                         V.∷ string _          V.∷ V.[]} = ifRefl
    invˡ {num _                                         V.∷ function _ _ _    V.∷ V.[]} = ifRefl
    invˡ {num _                                         V.∷ error (enum⁼ _) _ V.∷ V.[]} = ifRefl
    invˡ {num _                                         V.∷ error (enum˙ _) _ V.∷ V.[]} = ifRefl
    invˡ {error (enum˙ _) (list _)                      V.∷ _                 V.∷ V.[]} = Bp.if-cong (reflLemma errO)
    invˡ {error (enum˙ _) (num _)                       V.∷ _                 V.∷ V.[]} = Bp.if-cong (reflLemma errO)
    invˡ {error (enum˙ _) (string _)                    V.∷ _                 V.∷ V.[]} = Bp.if-cong (reflLemma errO)
    invˡ {error (enum˙ _) (function _ _ _)              V.∷ _                 V.∷ V.[]} = Bp.if-cong (reflLemma errO)
    invˡ {error (enum˙ _) (error _ _)                   V.∷ _                 V.∷ V.[]} = Bp.if-cong (reflLemma errO)
    invˡ {error (enum⁼ n) (list li)                     V.∷ _                 V.∷ V.[]} = trans (distrib-if (n ℕ.≡ᵇ errO) f⁼´) (trans (if n ≡errO-then (λ x₁ → cong₂ V._∷_ (cong₂ error (cong enum⁼ (sym (≡ᵇt→≡ x₁))) refl) refl)  else λ x₁ → trans ifRefl (trans (Bp.if-cong (notReflLemma n errO (≡ᵇf→≡ x₁))) refl)) (trans (Bp.if-cong₂ (n ℕ.≡ᵇ errO) refl  refl) (Bp.if-eta (n ℕ.≡ᵇ errO))))
    invˡ {error (enum⁼ n) (string _)                    V.∷ _                 V.∷ V.[]} = trans (distrib-if (n ℕ.≡ᵇ errO) f⁼´) (trans (if n ≡errO-then (λ x₁ → cong₂ V._∷_ (cong₂ error (cong enum⁼ (sym (≡ᵇt→≡ x₁))) refl) refl)  else λ x₁ → trans ifRefl (trans (Bp.if-cong (notReflLemma n errO (≡ᵇf→≡ x₁))) refl)) (trans (Bp.if-cong₂ (n ℕ.≡ᵇ errO) refl  refl) (Bp.if-eta (n ℕ.≡ᵇ errO))))
    invˡ {error (enum⁼ n) (function _ _ _)              V.∷ _                 V.∷ V.[]} = trans (distrib-if (n ℕ.≡ᵇ errO) f⁼´) (trans (if n ≡errO-then (λ x₁ → cong₂ V._∷_ (cong₂ error (cong enum⁼ (sym (≡ᵇt→≡ x₁))) refl) refl)  else λ x₁ → trans ifRefl (trans (Bp.if-cong (notReflLemma n errO (≡ᵇf→≡ x₁))) refl)) (trans (Bp.if-cong₂ (n ℕ.≡ᵇ errO) refl  refl) (Bp.if-eta (n ℕ.≡ᵇ errO))))
    invˡ {error (enum⁼ n) (error (enum⁼ _) _)           V.∷ _                 V.∷ V.[]} = trans (distrib-if (n ℕ.≡ᵇ errO) f⁼´) (trans (if n ≡errO-then (λ x₁ → cong₂ V._∷_ (cong₂ error (cong enum⁼ (sym (≡ᵇt→≡ x₁))) refl) refl)  else λ x₁ → trans ifRefl (trans (Bp.if-cong (notReflLemma n errO (≡ᵇf→≡ x₁))) refl)) (trans (Bp.if-cong₂ (n ℕ.≡ᵇ errO) refl  refl) (Bp.if-eta (n ℕ.≡ᵇ errO))))
    invˡ {error (enum⁼ n) (num i)                       V.∷ list _            V.∷ V.[]} = trans (distrib-if (n ℕ.≡ᵇ errO) f⁼´) (trans (if n ≡errO-then (λ x₁ → cong₂ V._∷_ (cong₂ error (cong enum⁼ (sym (≡ᵇt→≡ x₁))) refl) refl)  else λ x₁ → trans ifRefl (trans (Bp.if-cong (notReflLemma n errO (≡ᵇf→≡ x₁))) refl)) (trans (Bp.if-cong₂ (n ℕ.≡ᵇ errO) refl  refl) (Bp.if-eta (n ℕ.≡ᵇ errO))))
    invˡ {error (enum⁼ n) (num i)                       V.∷ string _          V.∷ V.[]} = trans (distrib-if (n ℕ.≡ᵇ errO) f⁼´) (trans (if n ≡errO-then (λ x₁ → cong₂ V._∷_ (cong₂ error (cong enum⁼ (sym (≡ᵇt→≡ x₁))) refl) refl)  else λ x₁ → trans ifRefl (trans (Bp.if-cong (notReflLemma n errO (≡ᵇf→≡ x₁))) refl)) (trans (Bp.if-cong₂ (n ℕ.≡ᵇ errO) refl  refl) (Bp.if-eta (n ℕ.≡ᵇ errO))))
    invˡ {error (enum⁼ n) (num i)                       V.∷ function _ _ _    V.∷ V.[]} = trans (distrib-if (n ℕ.≡ᵇ errO) f⁼´) (trans (if n ≡errO-then (λ x₁ → cong₂ V._∷_ (cong₂ error (cong enum⁼ (sym (≡ᵇt→≡ x₁))) refl) refl)  else λ x₁ → trans ifRefl (trans (Bp.if-cong (notReflLemma n errO (≡ᵇf→≡ x₁))) refl)) (trans (Bp.if-cong₂ (n ℕ.≡ᵇ errO) refl  refl) (Bp.if-eta (n ℕ.≡ᵇ errO))))
    invˡ {error (enum⁼ n) (num i)                       V.∷ error (enum⁼ _) _ V.∷ V.[]} = trans (distrib-if (n ℕ.≡ᵇ errO) f⁼´) (trans (if n ≡errO-then (λ x₁ → cong₂ V._∷_ (cong₂ error (cong enum⁼ (sym (≡ᵇt→≡ x₁))) refl) refl)  else λ x₁ → trans ifRefl (trans (Bp.if-cong (notReflLemma n errO (≡ᵇf→≡ x₁))) refl)) (trans (Bp.if-cong₂ (n ℕ.≡ᵇ errO) refl  refl) (Bp.if-eta (n ℕ.≡ᵇ errO))))
    invˡ {error (enum⁼ n) (num i)                       V.∷ error (enum˙ a) b V.∷ V.[]} = trans (distrib-if (n ℕ.≡ᵇ errO) f⁼´) (trans (if n ≡errO-then (λ x₁ → cong₂ V._∷_ (cong₂ error (cong enum⁼ (sym (≡ᵇt→≡ x₁))) refl) refl)  else λ x₁ → trans ifRefl (trans (Bp.if-cong (notReflLemma n errO (≡ᵇf→≡ x₁))) refl)) (trans (Bp.if-cong₂ (n ℕ.≡ᵇ errO) refl  refl) (Bp.if-eta (n ℕ.≡ᵇ errO))))
    invˡ {error (enum⁼ n) (num i)                       V.∷ num _             V.∷ V.[]} = trans (distrib-if (n ℕ.≡ᵇ errO) f⁼´) (trans (if n ≡errO-then (λ x₁ → Bp.if-cong x₁) else λ x₁ → trans ifRefl (trans (Bp.if-cong (notReflLemma n errO (≡ᵇf→≡ x₁))) refl)) (trans (Bp.if-cong₂ (n ℕ.≡ᵇ errO) refl  refl) (Bp.if-eta (n ℕ.≡ᵇ errO))))

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
