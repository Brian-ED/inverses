
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
  A B C D L R LR RL O : Set ℓ

-- Invertible function
infixr 1 _⇄_
--data Invertible2 (fTi fTo : DecSetoid ℓ₁ ℓ₂) (invable : Inverse (setoid fTi) (setoid fTo)) : Set (ℓ₁ ⊔ ℓ₂) where
--  inv : Invertible2 fTi fTo invable



_⇄_ : A → B → Set ℓ
_⇄_ {A} {B} a b = {! Inverse ? ? !}
--  open DecSetoid fTi renaming
--    ( Carrier          to Carrierˡ
--    ; _≈_              to _≈ˡ_
--    ; isDecEquivalence to isDecEquivalenceˡ
--    )
--  open DecSetoid fTo renaming
--    ( Carrier          to Carrierʳ
--    ; _≈_              to _≈ʳ_
--    ; isDecEquivalence to isDecEquivalenceʳ
--    )
--  open Inverse i public

-----------------
-- Composition --
-----------------

-- All functions assume right to left evaluation
-- *and* right to left operators binding.
-- In Invla it would be reversed but should be equivalent.

-- Monadic
--infixr 9 _∘ₘ_
--_∘ₘ_ : A ⇄ B → B ⇄ C → A ⇄ C
--record { i = ai } ∘ₘ record { i = bi } = record
--  { i = record
--    { to        = bi .to ∘ ai .to
--    ; from      = ai .from ∘ bi .from
--    ; to-cong   = to-cong bi ∘ to-cong ai
--    ; from-cong = from-cong ai ∘ from-cong bi
--    ; inverse   = inverse bi .proj₁ ∘ inverse ai .proj₁
--                , inverse ai .proj₂ ∘ inverse bi .proj₂
--    }
--  }
--  where open Inverse
--
--_×ᵈ_ : (a b : DecSetoid ℓ₁ ℓ₂) → DecSetoid ℓ₁ ℓ₂
--record { Carrier = a ; _≈_ = _≈a_ ; isDecEquivalence = aEq } ×ᵈ record { Carrier = b ; _≈_ = _≈b_ ; isDecEquivalence = bEq } = record
--  { Carrier = a × b
--  ; _≈_ = λ x y → (x .proj₁ ≈a y .proj₁) × (x .proj₂ ≈b y .proj₂)
--  ; isDecEquivalence = record
--    { isEquivalence = record
--      { refl
--        = e-refl (e-isEquivalence aEq) ,
--          e-refl (e-isEquivalence bEq)
--        ; sym = λ z →
--          sym (e-isEquivalence aEq) (z .proj₁) ,
--          sym (e-isEquivalence bEq) (z .proj₂)
--        ; trans = λ z z₁ →
--          trans (e-isEquivalence aEq) (z .proj₁) (z₁ .proj₁) ,
--          trans (e-isEquivalence bEq) (z .proj₂) (z₁ .proj₂)
--      } ;
--      _≟_ = λ x y → (aEq ._≟_) (x .proj₁) (y .proj₁)
--              ×-dec (bEq ._≟_) (x .proj₂) (y .proj₂)
--    }
--  }
--  where
--    open import Relation.Nullary.Decidable
--    open import Data.Bool hiding (_≟_)
--    open Inverse
--    open DecSetoid
--    open import Relation.Nullary.Decidable using (_×-dec_)
--    open import Relation.Binary.Structures using (IsEquivalence; IsDecEquivalence)
--    open IsEquivalence using (sym; trans) renaming (refl to e-refl)
--    open IsDecEquivalence using (_≟_) renaming (isEquivalence to e-isEquivalence)
--
--⋈ : {B : DecSetoid ℓ₁ ℓ₂} → A ⇄ {!  B ⇄ (? ×ᵈ ?) !}
--⋈ = {!   !}
--  (λ r → r , l , refl) , proj₁ , f , cong proj₁
--  where
--    f : Inverseˡ _≡_ _≡_ (_,(l , refl)) proj₁
--    f {_ , _ , refl} = cong (_, l , refl)


--_⋈2_ : {C L : Set ℓ} → L ⊎ (C ⊎ (C × L) ⇄ C × L) ⇄ C ⊎ (C × L) ⇄ C × L
--_⋈2_ = {!   !} -- ? , ? , {!   !} , ?


-- Dyadic

-- _∘ᵈ_ : L ⇄ A ⇄ B → B ⇄ C → L ⇄ A ⇄ C × L
-- The above cannot give a result L ⇄ A ⇄ C × L
-- if L, A, and C have atleast 2 elements. This is because the
-- left and right side of ⇄ must have equal cardinality,
-- so Card(L) ≡ Card(A)*Card(C)*Card(L)
-- so 1 ≡ Card(A)*Card(C)

--_∘ᵈ_ : L ⇄ A ⇄ B → B ⇄ C → (L ⊎ (A ⇄ C × L)) ⇄ A ⇄ C × L
--(bˡ , bʳ , gˡ , gʳ) ∘ᵈ r@(aˡ , aʳ , fˡ , fʳ) = {!   !} , {!   !}
--  --λ l →
--  --bˡ l ∘ₘ r ∘ₘ (l ⋈)
