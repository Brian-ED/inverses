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
open import Data.Product using (proj₁; proj₂; _×_; ∃; _,_)
open import Relation.Nullary using (Dec; yes; no; ¬_; map′)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary.Decidable using (no; yes; ⌊_⌋)

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

_≟ˡˢ_ : DecidableEquality (L.List S.String)
_≟ˡˢ_ L.[] L.[] = yes refl
_≟ˡˢ_ (x L.∷ xs) (y L.∷ ys) with x S.≟ y | xs ≟ˡˢ ys
... | yes p | yes q = yes (cong₂ L._∷_ p q)
... | _ | no q = no (λ { refl → q refl })
... | no p | _ = no (λ { refl → p refl })
_≟ˡˢ_ L.[] (x L.∷ y) = no (λ ())
_≟ˡˢ_ (x L.∷ x₁) L.[] = no (λ ())

_≟ˢᵗ_ : DecidableEquality Statement
_≟ˢᵗ_ xxx xxx = yes refl


_≟ᵛ_ : DecidableEquality Value
_≟ˡ_ : DecidableEquality (L.List Value)

int (ℤ.+ n) ≟ᵛ int (ℤ.+ n₂)    with n ℕ.≟ n₂
... | yes p = yes (cong int (cong ℤ.+_ p))
... | no  p = no  (λ { refl → p refl })

int (ℤ.+ _) ≟ᵛ int ℤ.-[1+ _ ] = no (λ ())

_≟ᵛ_ (list xs) (list ys) with _≟ˡ_ xs ys
... | yes p = yes (cong list p)
... | no  p = no  (λ { refl → p refl })

_≟ᵛ_ (error (enum n₁) v₁) (error (enum n₂) v₂) with n₁ ℕ.≟ n₂ | v₁ ≟ᵛ v₂
... | yes p | yes q = yes (cong₂ error (cong enum p) q)
... | no  p | _     = no  (λ { refl → p refl })
... | _     | no  q = no  (λ { refl → q refl })

_≟ᵛ_ (int (ℤ.-[1+_] n₁)) (int (ℤ.-[1+_] n₂)) with n₁ ℕ.≟ n₂
... | yes p = yes (cong int (cong ℤ.-[1+_] p))
... | no  p = no  (λ { refl → p refl })

_≟ᵛ_ (string str₁) (string str₂) with str₁ S.≟ str₂
... | yes p = yes (cong string p)
... | no  p = no  (λ { refl → p refl })

_≟ᵛ_ (function args₁ stmt₁) (function args₂ stmt₂) with args₁ ≟ˡˢ args₂ | stmt₁ ≟ˢᵗ stmt₂
... | yes p | yes q = yes (cong₂ function p q)
... | no  p | _     = no  (λ { refl → p refl })
... | _     | no  q = no  (λ { refl → q refl })

-- all cross-constructor cases
_≟ᵛ_ (int _)           (list _)          = no (λ ())
_≟ᵛ_ (string _)        (list _)          = no (λ ())
_≟ᵛ_ (function _ _)    (list _)          = no (λ ())
_≟ᵛ_ (error _ _)       (list _)          = no (λ ())
_≟ᵛ_ (list _)          (int _)           = no (λ ())
_≟ᵛ_ (int ℤ.-[1+ _ ])  (int (ℤ.+ _))    = no (λ ())
_≟ᵛ_ (string _)        (int _)           = no (λ ())
_≟ᵛ_ (function _ _)    (int _)           = no (λ ())
_≟ᵛ_ (error _ _)       (int _)           = no (λ ())
_≟ᵛ_ (list _)          (string _)        = no (λ ())
_≟ᵛ_ (int _)           (string _)        = no (λ ())
_≟ᵛ_ (function _ _)    (string _)        = no (λ ())
_≟ᵛ_ (error _ _)       (string _)        = no (λ ())
_≟ᵛ_ (list _)          (function _ _)    = no (λ ())
_≟ᵛ_ (int _)           (function _ _)    = no (λ ())
_≟ᵛ_ (string _)        (function _ _)    = no (λ ())
_≟ᵛ_ (error _ _)       (function _ _)    = no (λ ())
_≟ᵛ_ (list _)          (error _ _)       = no (λ ())
_≟ᵛ_ (int _)           (error _ _)       = no (λ ())
_≟ᵛ_ (string _)        (error _ _)       = no (λ ())
_≟ᵛ_ (function _ _)    (error _ _)       = no (λ ())

_≟ˡ_ L.[] L.[] = yes refl
_≟ˡ_ L.[] (_ L.∷ _) = no (λ ())
_≟ˡ_ (_ L.∷ _) L.[] = no (λ ())
_≟ˡ_ (x L.∷ xs) (y L.∷ ys) with x ≟ᵛ y | xs ≟ˡ ys
... | yes p | yes q = yes (cong₂ L._∷_ p q)
... | no  p | _     = no  (λ { refl → p refl })
... | _     | no  q = no  (λ { refl → q refl })

_==ᵛ_ : Value → Value → Bool
x ==ᵛ y = ⌊ x ≟ᵛ y ⌋

==ᵛ⇒≡ : ∀ m n → T ⌊ m ≟ᵛ n ⌋ → m ≡ n
==ᵛ⇒≡ m n p with m ≟ᵛ n
... | yes q = q
... | no  q = ⊥-elim p

≡⇒==ᵛ : ∀ m n → m ≡ n → T ⌊ m ≟ᵛ n ⌋
≡⇒==ᵛ m n refl with m ≟ᵛ n
... | yes _ = tt
... | no  q = q refl

==ᵛ-sound : ∀ m n → (m ==ᵛ n) ≡ true → m ≡ n
==ᵛ-sound m n x = ==ᵛ⇒≡ m n (subst T (sym x) tt)

notReflLemmaᵛ : ∀ x y → ¬ x ≡ y → (x ==ᵛ y) ≡ false
notReflLemmaᵛ x y x≢y with x ==ᵛ y | inspect (x ==ᵛ_) y
... | false | _      = refl
... | true  | [ eq ] = ⊥-elim (x≢y (==ᵛ-sound x y eq))
