
open import Function
  using
    ( Inverseˡ
    ; Inverseʳ
    ; Inverseᵇ
    ; _∘_
    ; _∘₂_
    )
open import Data.Product using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Product.Properties using (,-injective)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; refl; cong; ≡-≟-identity)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable.Core public
open import Data.Bool using (true; false; if_then_else_)
open import Level using (Level; suc)

variable
  ℓ : Level
  A B C D L R LR RL O : Set ℓ

data ⊥ {ℓ : Level} : Set ℓ where

-- Invertible function
infixr 1 _⟨_⟩⇉_
_⟨_⟩⇉_ : (e : Set ℓ) → DecidableEquality e → Set ℓ → Set _
Ti ⟨ _≟_ ⟩⇉ To = Σ (Ti → To) λ x → Σ (To → Ti) λ y → Inverseᵇ _≡_ _≡_ x y

-- All functions assume right to left evaluation
-- *and* right to left operators binding.
-- In Invla it would be reversed but should be equivalent.

infixr 9 ⟨_⟩_∘ₘ_ -- _∘ᵈ_

changeEquality : DecidableEquality A → (f : A → B) → (g : B → A) → Inverseᵇ _≡_ _≡_ f g → DecidableEquality B
changeEquality _≟a_ f g (l , r) a b = map′ (λ p → trans (sym (l refl)) (l p)) (cong g) (g a ≟a g b)

-- Monadic
-- aF .proj₂ .proj₂ .proj₁
⟨_⟩_∘ₘ_ : (_≟a_ : DecidableEquality A) → (aF : A ⟨ _≟a_ ⟩⇉ B) → B ⟨ changeEquality _≟a_ (aF .proj₁) (aF .proj₂ .proj₁) (aF .proj₂ .proj₂) ⟩⇉ C → A ⟨ _≟a_ ⟩⇉ C
⟨_⟩_∘ₘ_ = {!   !}
--⟨ _≟a_ , _≟b_ ⟩ (aˡ , aʳ , aIˡ , aIʳ) ∘ₘ (bˡ , bʳ , bIˡ , bIʳ) = {!   !} -- bˡ ∘ aˡ , aˡ≟ , aʳ ∘ bʳ , bʳ≟ , (λ x → bIˡ {! aIˡ x !}) , {!   !} -- aIʳ ∘ bIʳ
--(bˡ , bʳ , gˡ , gʳ) ∘ₘ (aˡ , aʳ , fˡ , fʳ) =
--  aˡ ∘ₒ bˡ , bʳ ∘ₒ aʳ , fˡ ∘ₒ gˡ , gʳ ∘ₒ fʳ
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
