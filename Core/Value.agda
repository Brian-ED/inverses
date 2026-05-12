import Data.Rational as ℚ
import Data.Rational.Properties as ℚp
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

infixr 4 _≟ˡ_
infixr 4 _≟ᵛ_
infixr 4 _≟ˡˢ_

data Statement : Set where
  xxx : Statement

data errType : Set where
  enum˙ : (n : ℕ.ℕ) → errType
  enum⁼ : (n : ℕ.ℕ) → errType

data Value : Set where
  list : (li : L.List Value) → Value
  num : (i : ℚ.ℚ) → Value
  string : (str : S.String) → Value
  function : (args : L.List S.String) → (stmt : Statement) → Value
  error : (t : errType) → (arg : Value) → Value

_≟ᵉ_ : DecidableEquality errType
enum˙ n₁ ≟ᵉ enum˙ n₂ with n₁ ℕ.≟ n₂
... | yes p = yes (cong enum˙ p)
... | no  p = no λ { refl → p refl }
enum˙ n₁ ≟ᵉ enum⁼ n₂ = no λ ()
enum⁼ n₁ ≟ᵉ enum˙ n₂ = no λ ()
enum⁼ n₁ ≟ᵉ enum⁼ n₂ with n₁ ℕ.≟ n₂
... | yes p = yes (cong enum⁼ p)
... | no  p = no λ { refl → p refl }

_≟ˡˢ_ : DecidableEquality (L.List S.String)
L.[] ≟ˡˢ L.[] = yes refl
x L.∷ xs ≟ˡˢ y L.∷ ys with x S.≟ y | xs ≟ˡˢ ys
... | yes p | yes q = yes (cong₂ L._∷_ p q)
... | _ | no q = no λ { refl → q refl }
... | no p | _ = no λ { refl → p refl }
L.[] ≟ˡˢ x L.∷ y = no λ ()
x L.∷ x₁ ≟ˡˢ L.[] = no λ ()

_≟ˢᵗ_ : DecidableEquality Statement
xxx ≟ˢᵗ xxx = yes refl


_≟ᵛ_ : DecidableEquality Value
_≟ˡ_ : DecidableEquality (L.List Value)

num n ≟ᵛ num n₂ with n ℚ.≟ n₂
... | yes p = yes (cong num p)
... | no  p = no λ { refl → p refl }

list xs ≟ᵛ list ys with _≟ˡ_ xs ys
... | yes p = yes (cong list p)
... | no  p = no λ { refl → p refl }

error (enum⁼ n₁) v₁ ≟ᵛ error (enum⁼ n₂) v₂ with n₁ ℕ.≟ n₂ | v₁ ≟ᵛ v₂
... | yes p | yes q = yes (cong₂ error (cong enum⁼ p) q)
... | no  p | _     = no λ { refl → p refl }
... | _     | no  q = no λ { refl → q refl }

error (enum˙ n₁) v₁ ≟ᵛ error (enum˙ n₂) v₂ with n₁ ℕ.≟ n₂ | v₁ ≟ᵛ v₂
... | yes p | yes q = yes (cong₂ error (cong enum˙ p) q)
... | no  p | _     = no λ { refl → p refl }
... | _     | no  q = no λ { refl → q refl }

string str₁ ≟ᵛ string str₂ with str₁ S.≟ str₂
... | yes p = yes (cong string p)
... | no  p = no λ { refl → p refl }

function args₁ stmt₁ ≟ᵛ function args₂ stmt₂ with args₁ ≟ˡˢ args₂ | stmt₁ ≟ˢᵗ stmt₂
... | yes p | yes q = yes (cong₂ function p q)
... | no  p | _     = no λ { refl → p refl }
... | _     | no  q = no λ { refl → q refl }

-- all cross-constructor cases
num _             ≟ᵛ list _            = no λ ()
string _          ≟ᵛ list _            = no λ ()
function _ _      ≟ᵛ list _            = no λ ()
error _ _         ≟ᵛ list _            = no λ ()
list _            ≟ᵛ num _             = no λ ()
string _          ≟ᵛ num _             = no λ ()
function _ _      ≟ᵛ num _             = no λ ()
error _ _         ≟ᵛ num _             = no λ ()
list _            ≟ᵛ string _          = no λ ()
num _             ≟ᵛ string _          = no λ ()
function _ _      ≟ᵛ string _          = no λ ()
error _ _         ≟ᵛ string _          = no λ ()
list _            ≟ᵛ function _ _      = no λ ()
num _             ≟ᵛ function _ _      = no λ ()
string _          ≟ᵛ function _ _      = no λ ()
error _ _         ≟ᵛ function _ _      = no λ ()
list _            ≟ᵛ error _ _         = no λ ()
num _             ≟ᵛ error _ _         = no λ ()
string _          ≟ᵛ error _ _         = no λ ()
function _ _      ≟ᵛ error _ _         = no λ ()
error (enum˙ _) _ ≟ᵛ error (enum⁼ _) _ = no λ ()
error (enum⁼ _) _ ≟ᵛ error (enum˙ _) _ = no λ ()

L.[]     ≟ˡ L.[]    = yes refl
L.[]     ≟ˡ _ L.∷ _ = no λ ()
_ L.∷ _  ≟ˡ L.[]    = no λ ()
x L.∷ xs ≟ˡ y L.∷ ys with x ≟ᵛ y | xs ≟ˡ ys
... | yes p | yes q = yes (cong₂ L._∷_ p q)
... | no  p | _     = no λ { refl → p refl }
... | _     | no  q = no λ { refl → q refl }

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
