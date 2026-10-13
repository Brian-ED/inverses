
open import Function
  using
    ( _∘_
    ; Inverse
    ; Inverseᵇ
    )

open import Data.Product using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Product.Properties using (,-injective)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (Level; _⊔_; suc)

variable
  ℓ a b ℓ₁ ℓ₂ : Level

open import Relation.Binary.Bundles using (DecSetoid)
open DecSetoid using (setoid; Carrier)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

variable
  A B C D L R LR RL O : DecSetoid ℓ₁ ℓ₂

-- Invertible function
infixr 1 _⇄_
record _⇄_ (fTi fTo : DecSetoid ℓ₁ ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    i : Inverse (setoid fTi) (setoid fTo)

  open Inverse i public

---------------
-- Functions --
---------------

-- All functions assume right to left evaluation
-- *and* right to left operators binding.
-- In Invla it would be reversed but should be equivalent.

-- Monadic
_∘ₘ_ : A ⇄ B → B ⇄ C → A ⇄ C
record { i = ai } ∘ₘ record { i = bi } = record
  { i = record
    { to        = bi .to ∘ ai .to
    ; from      = ai .from ∘ bi .from
    ; to-cong   = to-cong bi ∘ to-cong ai
    ; from-cong = from-cong ai ∘ from-cong bi
    ; inverse   = inverse bi .proj₁ ∘ inverse ai .proj₁
                , inverse ai .proj₂ ∘ inverse bi .proj₂
    }
  }
  where open Inverse

--(bˡ , bʳ , gˡ , gʳ) ∘ₘ (aˡ , aʳ , fˡ , fʳ) =
--  aˡ ∘ bˡ , bʳ ∘ aʳ , fˡ ∘ gˡ , gʳ ∘ fʳ


--infixr 9 _∘ₘ_ -- _∘ᵈ_

--_⇉o_ : Set ℓ → Set ℓ → Set ℓ
--fTi ⇉o fTo = Σ (fTi → fTo) λ x → Σ (fTo → fTi) λ y → Inverseᵇ _≡_ _≡_ x y


-- Monadic
--_∘ₘ_ : A ⇉ B → B ⇉ C → A ⇉ C
--(bˡ , bʳ , gˡ , gʳ) ∘ₘ (aˡ , aʳ , fˡ , fʳ) =
--  aˡ ∘ bˡ , bʳ ∘ aʳ , fˡ ∘ gˡ , gʳ ∘ fʳ
--
--_⋈ : {C L : Set ℓ} → (l : L) → C ⇉ (C × Σ L (λ r → r ≡ l))
--l ⋈ = (λ r → r , l , refl) , proj₁ , f , cong proj₁
--  where
--    f : Inverseˡ _≡_ _≡_ (_,(l , refl)) proj₁
--    f {_ , _ , refl} = cong (_, l , refl)


--_⋈2_ : {C L : Set ℓ} → L ⊎ (C ⊎ (C × L) ⇉ C × L) ⇉ C ⊎ (C × L) ⇉ C × L
--_⋈2_ = {!   !} -- ? , ? , {!   !} , ?


-- Dyadic

-- _∘ᵈ_ : L ⇉ A ⇉ B → B ⇉ C → L ⇉ A ⇉ C × L
-- The above cannot give a result L ⇉ A ⇉ C × L
-- if L, A, and C have atleast 2 elements. This is because the
-- left and right side of ⇉ must have equal cardinality,
-- so Card(L) ≡ Card(A)*Card(C)*Card(L)
-- so 1 ≡ Card(A)*Card(C)

--_∘ᵈ_ : L ⇉ A ⇉ B → B ⇉ C → (L ⊎ (A ⇉ C × L)) ⇉ A ⇉ C × L
--(bˡ , bʳ , gˡ , gʳ) ∘ᵈ r@(aˡ , aʳ , fˡ , fʳ) = {!   !} , {!   !}
--  --λ l →
--  --bˡ l ∘ₘ r ∘ₘ (l ⋈)
