module Core.Primitives where

import Data.Integer as ℤ
import Data.Integer.Properties as ℤp
import Data.Nat as ℕ
import Data.Nat.Properties as ℕp
import Data.List as L
import Data.Vec as V
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; refl; cong; setoid)
open import Relation.Binary using (Setoid)
open import Function using (Inverse)
open import Data.Bool using (Bool; true; false; not)
open import Data.Product using (proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (no; yes)
data Statement : Set where
  xxx : Statement

data errType : Set where
  enum : (n : ℕ.ℕ) → errType

data Value : Set where
  list : (li : L.List Value) → Value
  int : (i : ℤ.ℤ) → Value
  string : (str : String) → Value
  function : (args : L.List String) → (stmt : Statement) → Value
  error : (t : errType) → (arg : Value) → Value

open import Data.Product using (Σ; ∃; _,_)

Stack : ℕ.ℕ → Set
Stack n = Σ (L.List Value) (λ s → n ℕ.≤ L.length s)

record Primitive (n m : ℕ.ℕ) : Set where
  constructor ⟨_˙,_⁼,_ʳ,_ˡ⟩
  field
    f˙ : (s : Stack n) → Stack m
    f⁼ : (s : Stack m) → Stack n
    f-invʳ : ∀ {x} → f˙ (f⁼ x) ≡ x
    f-invˡ : ∀ {x} → f⁼ (f˙ x) ≡ x

  inv : Inverse (setoid (Stack n)) (setoid (Stack m))
  inv .Inverse.to = f˙
  inv .Inverse.from = f⁼
  inv .Inverse.to-cong = cong f˙
  inv .Inverse.from-cong = cong f⁼
  inv .Inverse.inverse .proj₁ refl = f-invʳ
  inv .Inverse.inverse .proj₂ refl = f-invˡ

incrErrorUnit : (v : Value) → Value
incrErrorUnit (error (enum n) x) = error (enum (ℕ.suc n)) (incrErrorUnit x)
incrErrorUnit x = x

decrErrorUnit : (v : Value) → Value
decrErrorUnit (error (enum (ℕ.suc n)) x) = error (enum n) (decrErrorUnit x)
decrErrorUnit x = x

incrInvUnit : ∀ x → decrErrorUnit (incrErrorUnit x) ≡ x
incrInvUnit (list li) = refl
incrInvUnit (int i) = refl
incrInvUnit (string str) = refl
incrInvUnit (function args stmt) = refl
incrInvUnit (error (enum n) x) rewrite incrInvUnit x = refl

incrError : (s : Stack 2) → Stack 2
incrError ((error (enum n) x) L.∷ s , l) = (incrErrorUnit (error (enum n) x)) L.∷ s , l
incrError x = x


decrError : (s : Stack 2) → Stack 2
decrError ((error (enum n) x) L.∷ s , l) = (decrErrorUnit (error (enum n) x)) L.∷ s , l
decrError x = x

incrInv : ∀ x → decrError (incrError x) ≡ x
incrInv (list li L.∷ fst , snd) = refl
incrInv (int i L.∷ fst , snd) = refl
incrInv (string str L.∷ fst , snd) = refl
incrInv (function args stmt L.∷ fst , snd) = refl
incrInv (error (enum n) x L.∷ fst , snd) rewrite incrInvUnit x = refl

module nArg where
  import Data.Maybe as M

  vecOnStack : ∀ {n m} → Stack n → V.Vec Value m → Stack (n ℕ.+ m)
  vecOnStack {n} s V.[] rewrite ℕp.+-identityʳ n = s
  vecOnStack {n} {ℕ.suc m} (s , l) (x V.∷ x₁) rewrite ℕp.+-suc n m = vecOnStack {ℕ.suc n} {m} ((x L.∷ s) , ℕ.s≤s l) x₁

  addElemLemma : ∀ {n m} → {x : Value} → {s : L.List Value} → n ℕ.+ ℕ.suc m ℕ.≤ L.length (x L.∷ s) → n ℕ.+ m ℕ.≤ L.length s
  addElemLemma {n} {m} {x} {s} p rewrite ℕp.+-suc n m = ℕ.s≤s⁻¹ p

  vecOffStack : ∀ {m} → (n : ℕ.ℕ) → Stack (m ℕ.+ n) → Stack m × V.Vec Value n
  vecOffStack {n} ℕ.zero s rewrite ℕp.+-identityʳ n = s , V.[]
  vecOffStack {ℕ.zero} (ℕ.suc m) (L.[] , ())
  vecOffStack {ℕ.suc n} (ℕ.suc m) (L.[] , ())
  vecOffStack {n} (ℕ.suc m) (x L.∷ s , l) with vecOffStack {n} m (s , addElemLemma {n} {m} {x} {s} l)
  ... | p , snd = p , x V.∷ snd

  intFuncToPrim : (f˙ f⁼ : ℤ.ℤ → ℤ.ℤ → ℤ.ℤ)
                → (f-invʳ : ∀ {x y} → f˙ x (f⁼ x y) ≡ y)
                → (f-invˡ : ∀ {x y} → f⁼ x (f˙ x y) ≡ y)
                → (errVal : errType)
                → Primitive 2 2
  intFuncToPrim f˙ f⁼ f-invʳ f-invˡ (enum errNum) = ⟨
      f˙´ (enum errNum) ˙,
      f⁼´ (enum errNum) ⁼,
      invʳ ʳ,
      invˡ ˡ⟩
      where
        f˙´ : (err : errType) → (s : Stack 2) → Stack 2
        f˙´ err (x L.∷ L.[] , ℕ.s≤s ())
        f˙´ err (int i₁ L.∷ int i₂ L.∷ s , l) = int (f˙ i₂ i₁) L.∷ int i₂ L.∷ s , l
        f˙´ (enum 0) (error (enum 0) (error (enum 0) x) L.∷ s , l) = error (enum 0) (error (enum 0) x) L.∷ s , l
        f˙´ (enum (ℕ.suc n)) (error (enum (ℕ.suc n₂)) (error (enum (ℕ.suc n₃)) x) L.∷ s , l) = incrError (f˙´ (enum n) (error (enum n₂) (error (enum n₃) x) L.∷ s , l))
        f˙´ (enum 0) (error (enum 0) (int i₁) L.∷ int i₂ L.∷ s , l) = error (enum 0) (int i₁) L.∷ int i₂ L.∷ s , l
        f˙´ (enum (ℕ.suc n₁)) (error (enum (ℕ.suc n₂)) (int i₁) L.∷ int i₂ L.∷ s , l) = incrError (f˙´ (enum n₁) (error (enum n₂) (int i₁) L.∷ int i₂ L.∷ s , l))
        f˙´ (enum 0         ) (error (enum 0         ) v₁ L.∷ v₂ L.∷ s , l) = v₁ L.∷ v₂ L.∷ s , l
        f˙´ (enum (ℕ.suc n₁)) (error (enum (ℕ.suc n₂)) v₁ L.∷ v₂ L.∷ s , l) = incrError (f˙´ (enum n₁) (error (enum n₂) v₁ L.∷ v₂ L.∷ s , l))
        f˙´ err (v₁ L.∷ v₂ L.∷ s , l) = error err v₁ L.∷ v₂ L.∷ s , l


        f⁼´ : errType → (s : Stack 2) → Stack 2
        f⁼´ err (x L.∷ L.[] , ℕ.s≤s ())
        f⁼´ err (int i₁ L.∷ int i₂ L.∷ s , l) = int (f⁼ i₂ i₁) L.∷ int i₂ L.∷ s , l
        f⁼´ (enum 0) (error (enum 0) (error (enum 0) x) L.∷ s , l) = error (enum 0) (error (enum 0) x) L.∷ s , l
        f⁼´ (enum (ℕ.suc n)) (error (enum (ℕ.suc n₂)) (error (enum (ℕ.suc n₃)) x) L.∷ s , l) = incrError (f⁼´ (enum n) (error (enum n₂) (error (enum n₃) x) L.∷ s , l))
        f⁼´ (enum 0) (error (enum 0) (int i₁) L.∷ int i₂ L.∷ s , l) = error (enum 0) (int i₁) L.∷ int i₂ L.∷ s , l
        f⁼´ (enum (ℕ.suc n₁)) (error (enum (ℕ.suc n₂)) (int i₁) L.∷ int i₂ L.∷ s , l) = incrError (f⁼´ (enum n₁) (error (enum n₂) (int i₁) L.∷ int i₂ L.∷ s , l))
        f⁼´ (enum 0         ) (error (enum 0         ) v₁ L.∷ v₂ L.∷ s , l) = v₁ L.∷ v₂ L.∷ s , l
        f⁼´ (enum (ℕ.suc n₁)) (error (enum (ℕ.suc n₂)) v₁ L.∷ v₂ L.∷ s , l) = incrError (f⁼´ (enum n₁) (error (enum n₂) v₁ L.∷ v₂ L.∷ s , l))
        f⁼´ err (v₁ L.∷ v₂ L.∷ s , l) = error err v₁ L.∷ v₂ L.∷ s , l

        invʳ : ∀ {x err} → f˙´ err (f⁼´ err x) ≡ x
        invʳ {x L.∷ L.[] , ℕ.s≤s ()}
        invʳ {list li L.∷ list li₁ L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {list li L.∷ int i L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {list li L.∷ string str L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {list li L.∷ function args stmt L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {list li L.∷ error t x L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {int i L.∷ list li L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {int i L.∷ int i₁ L.∷ fst , snd} {enum ℕ.zero} rewrite f-invʳ {i₁} {i} = refl
        invʳ {int i L.∷ string str L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {int i L.∷ function args stmt L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {int i L.∷ error t x L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {string str L.∷ list li L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {string str L.∷ int i L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {string str L.∷ string str₁ L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {string str L.∷ function args stmt L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {string str L.∷ error t x L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {function args stmt L.∷ list li L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {function args stmt L.∷ int i L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {function args stmt L.∷ string str L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {function args stmt L.∷ function args₁ stmt₁ L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {function args stmt L.∷ error t x L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (list li₁) L.∷ list li L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (int i) L.∷ list li L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (string str) L.∷ list li L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (function args stmt) L.∷ list li L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (error (enum ℕ.zero) x) L.∷ list li L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (error (enum (ℕ.suc n)) x) L.∷ list li L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (list li) L.∷ int i L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (int i₁) L.∷ int i L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (string str) L.∷ int i L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (function args stmt) L.∷ int i L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (error (enum ℕ.zero) x) L.∷ int i L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (error (enum (ℕ.suc n)) x) L.∷ int i L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (list li) L.∷ string str L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (int i) L.∷ string str L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (string str₁) L.∷ string str L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (function args stmt) L.∷ string str L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (error (enum ℕ.zero) x) L.∷ string str L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (error (enum (ℕ.suc n)) x) L.∷ string str L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (list li) L.∷ function args stmt L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (int i) L.∷ function args stmt L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (string str) L.∷ function args stmt L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (function args₁ stmt₁) L.∷ function args stmt L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (error (enum ℕ.zero) x) L.∷ function args stmt L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (error (enum (ℕ.suc n)) x) L.∷ function args stmt L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (list li) L.∷ error t x₁ L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (int i) L.∷ error t x₁ L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (string str) L.∷ error t x₁ L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (function args stmt) L.∷ error t x₁ L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (error (enum ℕ.zero) x) L.∷ error t x₁ L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum ℕ.zero) (error (enum (ℕ.suc n)) x) L.∷ error t x₁ L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {error (enum (ℕ.suc n)) x L.∷ x₁ L.∷ fst , snd} {enum ℕ.zero} = refl
        invʳ {x} {enum (ℕ.suc n)} = {!   !}



        invˡ : ∀ {x err} → f⁼´ err (f˙´ err x) ≡ x
        invˡ = {!   !}

module + where

  +˙ : (s : Stack 2) → Stack 2
  +˙ (x L.∷ L.[] , ℕ.s≤s ())
  +˙ (int i₁ L.∷ int i₂ L.∷ s , l) = int (i₁ ℤ.+ i₂) L.∷ int i₂ L.∷ s , l
  +˙ (error (enum 0) (error (enum 0) x) L.∷ s , l) = error (enum 0) (error (enum 0) x) L.∷ s , l
  +˙ (error (enum 0) (int i₁) L.∷ int i₂ L.∷ s , l) = error (enum 0) (int i₁) L.∷ int i₂ L.∷ s , l
  +˙ (error (enum 0) v₁ L.∷ s , l) = v₁ L.∷ s , l
  +˙ (v₁ L.∷ s , l) = error (enum 0) v₁ L.∷ s , l

  +⁼ : (s : Stack 2) → Stack 2
  +⁼ (x L.∷ L.[] , ℕ.s≤s ())
  +⁼ (int i₁ L.∷ int i₂ L.∷ s , l) = int (i₁ ℤ.- i₂) L.∷ int i₂ L.∷ s , l
  +⁼ (error (enum 0) (error (enum 0) x) L.∷ s , l) = error (enum 0) (error (enum 0) x) L.∷ s , l
  +⁼ (error (enum 0) (int i₁) L.∷ int i₂ L.∷ s , l) = error (enum 0) (int i₁) L.∷ int i₂ L.∷ s , l
  +⁼ (error (enum 0) v₁ L.∷ s , l) = v₁ L.∷ s , l
  +⁼ (v₁ L.∷ s , l) = error (enum 0) v₁ L.∷ s , l

  +invʳ : ∀ {x} → +˙ (+⁼ x) ≡ x
  +invʳ {x L.∷ L.[] , ℕ.s≤s ()}
  +invʳ {error (enum 0) (int v₁) L.∷ int v₂ L.∷ s , l} = refl
  +invʳ {error (enum 0) (int i) L.∷ list li L.∷ s , l} = refl
  +invʳ {error (enum 0) (int i) L.∷ string str L.∷ s , l} = refl
  +invʳ {error (enum 0) (int i) L.∷ error t v₂ L.∷ s , l} = refl
  +invʳ {error (enum 0) (error (enum 0) v₁) L.∷ v₂ L.∷ s , l} = refl
  +invʳ {error (enum 0) (error (enum (ℕ.suc n)) v₁) L.∷ v₂ L.∷ s , l} = refl
  +invʳ {error (enum 0) (int i) L.∷ function args stmt L.∷ s , l} = refl
  +invʳ {error (enum 0) (list li) L.∷ v₂ L.∷ s , l} = refl
  +invʳ {error (enum 0) (string str) L.∷ v₂ L.∷ s , l} = refl
  +invʳ {error (enum 0) (function args stmt) L.∷ v₂ L.∷ s , l} = refl
  +invʳ {error (enum (ℕ.suc n)) e L.∷ v₂ L.∷ s , l} = refl
  +invʳ {int i₁ L.∷ int i₂ L.∷ s , l}
    rewrite ℤp.+-assoc i₁ (ℤ.- i₂) i₂
    rewrite ℤp.+-inverseˡ i₂
    rewrite ℤp.+-identityʳ i₁ = refl
  +invʳ {int i L.∷ list li L.∷ s , l} = refl
  +invʳ {int i L.∷ string str L.∷ s , l} = refl
  +invʳ {int i L.∷ error t v₂ L.∷ s , l} = refl
  +invʳ {int i L.∷ function args stmt L.∷ s , l} = refl
  +invʳ {list li L.∷ v₂ L.∷ s , l} = refl
  +invʳ {string str L.∷ v₂ L.∷ s , l} = refl
  +invʳ {function args stmt L.∷ v₂ L.∷ s , l} = refl


  +invˡ : ∀ {x} → +⁼ (+˙ x) ≡ x
  +invˡ {x L.∷ L.[] , ℕ.s≤s ()}
  +invˡ {error (enum 0) (int v₁) L.∷ int v₂ L.∷ s , l} = refl
  +invˡ {error (enum 0) (list li) L.∷ v₂ L.∷ s , l} = refl
  +invˡ {error (enum 0) (int i) L.∷ list li L.∷ s , l} = refl
  +invˡ {error (enum 0) (int i) L.∷ string str L.∷ s , l} = refl
  +invˡ {error (enum 0) (int i) L.∷ error t v₂ L.∷ s , l} = refl
  +invˡ {error (enum 0) (string str) L.∷ v₂ L.∷ s , l} = refl
  +invˡ {error (enum 0) (error (enum 0) v₁) L.∷ v₂ L.∷ s , l} = refl
  +invˡ {error (enum 0) (error (enum (ℕ.suc n)) v₁) L.∷ v₂ L.∷ s , l} = refl
  +invˡ {error (enum 0) (int i) L.∷ function args stmt L.∷ s , l} = refl
  +invˡ {error (enum 0) (function args stmt) L.∷ v₂ L.∷ s , l} = refl
  +invˡ {error (enum (ℕ.suc n)) v₁ L.∷ v₂ L.∷ s , l} = refl
  +invˡ {int i₁ L.∷ int i₂ L.∷ s , l}
    rewrite ℤp.+-assoc i₁ i₂ (ℤ.- i₂)
    rewrite ℤp.+-inverseʳ i₂
    rewrite ℤp.+-identityʳ i₁ = refl
  +invˡ {int i L.∷ list li L.∷ s , l} = refl
  +invˡ {int i L.∷ string str L.∷ s , l} = refl
  +invˡ {int i L.∷ error t v₂ L.∷ s , l} = refl
  +invˡ {int i L.∷ function args stmt L.∷ s , l} = refl
  +invˡ {list li L.∷ v₂ L.∷ s , l} = refl
  +invˡ {string str L.∷ v₂ L.∷ s , l} = refl
  +invˡ {function args stmt L.∷ v L.∷ s , l} = refl

  +ₚ : Primitive 2 2
  +ₚ = ⟨ +˙ ˙, +⁼ ⁼, +invʳ ʳ, +invˡ ˡ⟩
