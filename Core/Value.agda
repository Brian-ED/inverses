import Data.Integer as ℤ
import Data.Integer.Properties as ℤp
import Data.Nat as ℕ
import Data.Nat.Properties as ℕp
import Data.Nat.ListAction as ℕL
import Data.Bool.ListAction as BL
import Data.List as L
import Data.Vec as V
import Data.String as S
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; refl; cong; setoid; inspect; [_]; subst; cong₂)
open import Relation.Binary using (Setoid)
open import Function using (Inverse)
open import Data.Bool using (Bool; true; false; not; _∧_; if_then_else_; T)
open import Data.Product using (proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_; map′)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary.Decidable using (no; yes)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (DecidableEquality)

module Core.Value where

data Statement : Set where
  xxx : Statement

data errType : Set where
  enum : (n : ℕ.ℕ) → errType

data Value : Set where
  list : (li : L.List Value) → Value
  int : (i : ℤ.ℤ) → Value
  string : (str : S.String) → Value
  function : (args : L.List S.String) → (stmt : Statement) → Value
  error : (t : errType) → (arg : Value) → Value

≟ˡˢ-dec : DecidableEquality (L.List S.String)
≟ˡˢ-dec L.[] L.[] = yes refl
≟ˡˢ-dec (x₁ L.∷ l₁) (x₂ L.∷ l₂) with ≟ˡˢ-dec l₁ l₂ | x₁ S.≟ x₂
... | yes p | yes q = yes (cong₂ L._∷_ q p)
... | _ | no q = no (λ { refl → q refl })
... | no p | _ = no (λ { refl → p refl })
≟ˡˢ-dec L.[] (x L.∷ y) = no (λ ())
≟ˡˢ-dec (x L.∷ x₁) L.[] = no (λ ())

≟ˢᵗ-dec : DecidableEquality Statement
≟ˢᵗ-dec xxx xxx = yes refl


≟ᵛ-dec : DecidableEquality Value
≟ˡ-dec : DecidableEquality (L.List Value)

≟ᵛ-dec (int (ℤ.+ n))    (int (ℤ.+ n₂))    with n ℕ.≟ n₂
... | yes p = yes (cong int (cong ℤ.+_ p))
... | no  p = no  (λ { refl → p refl })

≟ᵛ-dec (int (ℤ.+ _))    (int ℤ.-[1+ _ ]) = no (λ ())

≟ᵛ-dec (list l₁) (list l₂) with ≟ˡ-dec l₁ l₂
... | yes p = yes (cong list p)
... | no  p = no  (λ { refl → p refl })

≟ᵛ-dec (error (enum n₁) v₁) (error (enum n₂) v₂) with n₁ ℕ.≟ n₂ | ≟ᵛ-dec v₁ v₂
... | yes p | yes q = yes (cong₂ error (cong enum p) q)
... | no  p | _     = no  (λ { refl → p refl })
... | _     | no  q = no  (λ { refl → q refl })

≟ᵛ-dec (int (ℤ.-[1+_] n₁)) (int (ℤ.-[1+_] n₂)) with n₁ ℕ.≟ n₂
... | yes p = yes (cong int (cong ℤ.-[1+_] p))
... | no  p = no  (λ { refl → p refl })

≟ᵛ-dec (string str₁) (string str₂) with str₁ S.≟ str₂
... | yes p = yes (cong string p)
... | no  p = no  (λ { refl → p refl })

≟ᵛ-dec (function args₁ stmt₁) (function args₂ stmt₂) with ≟ˡˢ-dec args₁ args₂ | ≟ˢᵗ-dec stmt₁ stmt₂
... | yes p | yes q = yes (cong₂ function p q)
... | no  p | _     = no  (λ { refl → p refl })
... | _     | no  q = no  (λ { refl → q refl })

-- all cross-constructor cases
≟ᵛ-dec (int _)           (list _)          = no (λ ())
≟ᵛ-dec (string _)        (list _)          = no (λ ())
≟ᵛ-dec (function _ _)    (list _)          = no (λ ())
≟ᵛ-dec (error _ _)       (list _)          = no (λ ())
≟ᵛ-dec (list _)          (int _)           = no (λ ())
≟ᵛ-dec (int ℤ.-[1+ _ ])  (int (ℤ.+ _))    = no (λ ())
≟ᵛ-dec (string _)        (int _)           = no (λ ())
≟ᵛ-dec (function _ _)    (int _)           = no (λ ())
≟ᵛ-dec (error _ _)       (int _)           = no (λ ())
≟ᵛ-dec (list _)          (string _)        = no (λ ())
≟ᵛ-dec (int _)           (string _)        = no (λ ())
≟ᵛ-dec (function _ _)    (string _)        = no (λ ())
≟ᵛ-dec (error _ _)       (string _)        = no (λ ())
≟ᵛ-dec (list _)          (function _ _)    = no (λ ())
≟ᵛ-dec (int _)           (function _ _)    = no (λ ())
≟ᵛ-dec (string _)        (function _ _)    = no (λ ())
≟ᵛ-dec (error _ _)       (function _ _)    = no (λ ())
≟ᵛ-dec (list _)          (error _ _)       = no (λ ())
≟ᵛ-dec (int _)           (error _ _)       = no (λ ())
≟ᵛ-dec (string _)        (error _ _)       = no (λ ())
≟ᵛ-dec (function _ _)    (error _ _)       = no (λ ())

≟ˡ-dec L.[] L.[] = yes refl
≟ˡ-dec L.[] (_ L.∷ _) = no (λ ())
≟ˡ-dec (_ L.∷ _) L.[] = no (λ ())
≟ˡ-dec (x L.∷ xs) (y L.∷ ys) with ≟ᵛ-dec x y | ≟ˡ-dec xs ys
... | yes p | yes q = yes (cong₂ L._∷_ p q)
... | no  p | _     = no  (λ { refl → p refl })
... | _     | no  q = no  (λ { refl → q refl })
