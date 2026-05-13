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
open import Relation.Binary.PropositionalEquality using (_≡_; trans; sym; refl; cong; setoid; inspect; [_]; subst; cong₂)
open import Relation.Binary using (Setoid)
open import Function using (Inverse)
open import Data.Bool using (Bool; true; false; not; _∧_; if_then_else_; T)
open import Data.Product using (proj₁; proj₂; _×_; Σ; ∃; _,_)
open import Relation.Nullary using (Dec; yes; no; ¬_; map′)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary.Decidable using (no; yes; ⌊_⌋)
open import Data.Fin as Fin

module Core.Value
  (amount-of-primitives : ℕ.ℕ)
  (inArgCounts : V.Vec ℕ.ℕ amount-of-primitives)
  (outArgCounts : V.Vec ℕ.ℕ amount-of-primitives)
  where

infixr 4 _≟ˡ_
infixr 4 _≟ᵛ_
infixr 4 _≟ˡˢ_

data Statement : Set where
  primIndex : (p-i : Fin.Fin amount-of-primitives) → Statement

data errType : Set where
  enum˙ : (n : ℕ.ℕ) → errType
  enum⁼ : (n : ℕ.ℕ) → errType

data Value : Set where
  list : (li : L.List Value) → Value
  num : (i : ℚ.ℚ) → Value
  string : (str : S.String) → Value
  function : (inArgs outArgs : ℕ.ℕ) → (stmt : Statement) → Value
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
primIndex p-i₁ ≟ˢᵗ primIndex p-i₂ with p-i₁ Fin.≟ p-i₂
... | yes refl = yes refl
... | no p = no λ { refl → p refl }

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

function inArgCount₁ outArgCount₁ stmt₁ ≟ᵛ function inArgCount₂ outArgCount₂ stmt₂ with inArgCount₁ ℕ.≟ inArgCount₂ | outArgCount₁ ℕ.≟ outArgCount₂ | stmt₁ ≟ˢᵗ stmt₂
... | yes p | yes q | yes pq = yes (trans (cong (λ x → function x outArgCount₁ stmt₁) p) (trans (cong (λ x → function inArgCount₂ x stmt₁) q) (cong (λ x → function inArgCount₂ outArgCount₂ x) pq))) -- | yes q = ? -- yes (cong₂ function p pq q)
... | no  p | _     | _      = no λ { refl → p refl }
... | _     | no  q | _      = no λ { refl → q refl }
... | _     | _     | no  pq = no λ { refl → pq refl }

-- all cross-constructor cases
num _             ≟ᵛ list _            = no λ ()
string _          ≟ᵛ list _            = no λ ()
function _ _ _    ≟ᵛ list _            = no λ ()
error _ _         ≟ᵛ list _            = no λ ()
list _            ≟ᵛ num _             = no λ ()
string _          ≟ᵛ num _             = no λ ()
function _ _ _    ≟ᵛ num _             = no λ ()
error _ _         ≟ᵛ num _             = no λ ()
list _            ≟ᵛ string _          = no λ ()
num _             ≟ᵛ string _          = no λ ()
function _ _ _    ≟ᵛ string _          = no λ ()
error _ _         ≟ᵛ string _          = no λ ()
list _            ≟ᵛ function _ _ _    = no λ ()
num _             ≟ᵛ function _ _ _    = no λ ()
string _          ≟ᵛ function _ _ _    = no λ ()
error _ _         ≟ᵛ function _ _ _    = no λ ()
list _            ≟ᵛ error _ _         = no λ ()
num _             ≟ᵛ error _ _         = no λ ()
string _          ≟ᵛ error _ _         = no λ ()
function _ _ _    ≟ᵛ error _ _         = no λ ()
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

incrErrorUnit : (v : Value) → Value
incrErrorUnit (error (enum˙ n) x) = error (enum˙ (ℕ.suc n)) (incrErrorUnit x)
incrErrorUnit x = x

decrErrorUnit : (v : Value) → Value
decrErrorUnit (error (enum˙ (ℕ.suc n)) x) = error (enum˙ n) (decrErrorUnit x)
decrErrorUnit x = x

incrInvUnit : ∀ x → decrErrorUnit (incrErrorUnit x) ≡ x
incrInvUnit (list li) = refl
incrInvUnit (num i) = refl
incrInvUnit (string str) = refl
incrInvUnit (function _ _ _) = refl
incrInvUnit (error (enum˙ n) x) rewrite incrInvUnit x = refl
incrInvUnit (error (enum⁼ n) x) = refl

Stack : ℕ.ℕ → Set
Stack = V.Vec Value

incrError : (s : Stack 2) → Stack 2
incrError ((error (enum˙ n) x) V.∷ s) = incrErrorUnit (error (enum˙ n) x) V.∷ s
incrError x = x

decrError : (s : Stack 2) → Stack 2
decrError ((error (enum˙ n) x) V.∷ s) = (decrErrorUnit (error (enum˙ n) x)) V.∷ s
decrError x = x

incrInv : ∀ x → decrError (incrError x) ≡ x
incrInv (list li V.∷ fst) = refl
incrInv (num i V.∷ fst) = refl
incrInv (string str V.∷ fst) = refl
incrInv (function _ _ _ V.∷ fst) = refl
incrInv (error (enum˙ n) x V.∷ fst) rewrite incrInvUnit x = refl
incrInv (error (enum⁼ n) x V.∷ x₁) = refl

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
