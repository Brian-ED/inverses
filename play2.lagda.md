(1,v1)=1(); (1,v2)=1(); (+,f) = +(v1); f(v2)

1 is just a no-input function that creates instances of 1s, where all instances are equal. And you'd have to also assume that the function after executing returns itself and implciitly assigns a new instance of 1.

# Imports
```agda
open import Data.List using (List; []; _∷_; _++_; deduplicate; zipWith; map; foldr; foldl; length; tabulate) renaming (lookup to indexList)
open import Data.List.Properties using (≡-dec)
open import Data.Vec using (Vec)
open import Data.String using (String; _<_; _<?_; _==_; _≟_)
open import Data.Integer using (ℤ)
open import Data.Product using (∃; Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; if_then_else_; _∧_; _∨_; not; true; false; T?; T) renaming (_≟_ to _≟bool_)
open import Relation.Nullary.Decidable using (¬?)
open import Data.Bool.ListAction using (and; or)
open import Data.Nat as ℕ using (suc; ℕ)
open import Data.Nat using (z<s; s≤s)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (yes; no)
import Level
open import Relation.Nary using (⌊_⌋)
open import Data.List.Fresh using (List#; cons; []; _∷#_; fresh; toList) renaming (length to lengthF)
open import Data.Fin using (Fin; zero; suc)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_; _∘₂_)
```

# Code
```agda
data 𝕍 : Set where
  int_ : (i : ℤ) → 𝕍
  str_ : (s : String) → 𝕍
  -- TODO add function type to be able to represent them e.g plus

NSize : {m : ℕ} (n : ℕ) → n ℕ.≤ n ℕ.+ m
NSize 0 = ℕ.z≤n
NSize (ℕ.suc n) = s≤s (NSize n)

open import Data.String using (String; _<_; _<?_; _==_) renaming (_≟_ to _≟str_)
<<str = λ a b c → <-isStrictPartialOrder-≈ .IsStrictPartialOrder.trans {a} {b} {c}
    where
        open import Relation.Binary.Structures using (IsStrictPartialOrder)
        open import Data.String.Properties using (<-isStrictPartialOrder-≈)

open import States 𝕍 String _<_ <<str _<?_ _==_ using (States; _<<_; lookup; joinOverwrite) renaming (delete to clearKey)

ArgsList = List# String ⌊ _<?_ ⌋

exists : ArgsList → String → Bool
exists [] x = false
exists (v ∷# rest) x = (x == v) ∨ (exists rest x)

toDec : ∀ {s₁ s} → s₁ < s → ⌊ s₁ <? s ⌋
toDec {s₁} {s} x with s₁ <? s
... | yes _ = _
... | no p = Level.lift (p x)

fromDec : ∀ {id} {id₁} → ⌊ id <? id₁ ⌋ → id < id₁
fromDec {id} {id₁} _ with yes p ← id <? id₁ = p

appendFresh : ∀ {s id xs₁} x → s < id → fresh String ⌊ _<?_ ⌋ s (cons id xs₁ x)
appendFresh {s} {id} {xs₁ = []} _ ordered = toDec {s} {id} ordered , _
appendFresh {s} {id} {xs₁ = cons id₁ xs₁ lower} (lower₁ , snd₁) ordered = toDec {s} {id} ordered , (appendFresh lower (<<str s id id₁ ordered (fromDec {id} {id₁} lower₁)))

_+←_ : (s : ArgsList) → (id : String) → ArgsList
[] +← id = id ∷# []
cons id₁ _ p₁ +← id with id <? id₁ | id₁ <? id
cons s₁ [] p₁ +← id | yes p | q = cons id (s₁ ∷# []) (toDec {id} {s₁} p , _)
cons s₁ [] p₁ +← id | no  p | yes q = cons s₁ (id ∷# []) (toDec {s₁} {id} q , _)
cons s₁ [] p₁ +← id | no  p | no  q = id ∷# []
cons s₁ s p₁ +← id | yes p | q = cons id (cons s₁ s p₁) (appendFresh p₁ p)
cons id₁ (cons id₂ s p₂) p₁ +← id | no p | no  q = cons id₁ (cons id₂ s p₂) (appendFresh p₂ (fromDec {id₁} {id₂} (proj₁ p₁)))
cons id₁ (cons id₂ s p₂) p₁ +← id | no p | yes q
    with (cons id₂ s p₂)    +← id
... | [] = id₁ ∷# []
... | cons idᵣ₁ r pᵣ₁ with id₁ <? idᵣ₁
... | yes pp = cons id₁ (cons idᵣ₁ r pᵣ₁) (appendFresh pᵣ₁ pp)
... | no  pp = []


clear : (l : ArgsList) → (id : String) → ArgsList
clear [] id = []
clear (cons id₁ xs o) id = if id == id₁ then xs else clear xs id +← id₁

clearMulti : (tk : ArgsList) → (args : List String) → ArgsList
clearMulti tk args = foldl clear tk args

addMulti : (tk : ArgsList) → (args : List String) → ArgsList
addMulti tk args = foldl _+←_ tk args

--import Relation.Binary.Construct.Closure.ReflexiveTransitive as ReflTrans
--open ReflTrans
--    using (Star)
--    renaming (ε to x⇒x; _◅_ to _⇒∘⇒*_)
--    public


data Stmt : (tk : ArgsList) → Set where -- tk = TaKen names
  begin : Stmt ("+" ∷# "1" ∷# [])
  _end_ : ∀ {tk} → Stmt tk → (output : List String) → Stmt (clearMulti tk output)
  _⋄⟨_⟩_→⟨_⟩ :
    ∀ {tk}
    → (prev : Stmt tk)
    → (fn : String)
    → {fnP : T (exists tk fn)}  -- fn needs to be defined
    → (args : List String)
    → {argsU : ⌊ ≡-dec _≟str_ args (deduplicate _≟_ args) ⌋}
    → {argsP : (T ∘ and ∘ tabulate) (exists (clear tk fn) ∘ indexList args)}  -- All names in ins need to be defined
    → (outs : List String)
    → {outsU : ⌊ ≡-dec _≟str_ outs (deduplicate _≟_ outs)⌋}
    → {outsP : (T ∘ not ∘ or ∘ tabulate) (exists (clearMulti (clear tk fn) args) ∘ indexList outs)} -- All names in outs need to not be defined
    → Stmt (addMulti (clearMulti (clear tk fn) args) outs) -- tkₚ but remove ins and function and add outs

infixr 10 _⋄⟨_⟩_→⟨_⟩
infixl 9 _end_

```

```
data _⇒_ : (l r : Σ ArgsList λ tk → (Stmt tk) × (Vec 𝕍 (lengthF tk))) → Set where
  step+ : ∀ {tk S fnName fnP arg outPlus outApplied argsU outsU argsP outsP s s´}
    → ( addMulti
        (clear (clear tk fnName) arg)
        (outPlus ∷ outApplied ∷ [])
      , _⋄⟨_⟩_→⟨_⟩ S
        fnName {fnP}  -- TODO fix mistake, this shouldnt care about the argument name, its the value of the name that should be plus
        (arg ∷ []) {argsU} {argsP}
        (outPlus ∷ outApplied ∷ []) {outsU} {outsP}
      , s
    )⇒(tk , S , s´) -- TODO instead of s´, figure out a way to compute s´ from the inputs (or work out the inputs from the output, both are fine since it should be invertible)

-- Template
--  step  : ∀ {tk S fn fnP args outs argsP outsP s s´ argsU outsU}
--          → (addMulti (clearMulti (clear tk fn) args) outs , S ⋄⟨ fn , fnP ⟩⟨ args , argsU , argsP ⟩→⟨ outs , outsU , outsP ⟩ , s)⇒(tk , S , s´)

```

The abstract syntax can be used to formulate this basic progrm to show how you can compute 1+1:
```
prog1 : Stmt ("+" ∷# "1" ∷# [])
prog1 = begin

prog2 : Stmt ("+" ∷# "1" ∷# [])
prog2 = begin
  ⋄⟨ "1" ⟩ []        →⟨ "1" ∷ "v1" ∷ [] ⟩ -- (1,v1)=1()
  ⋄⟨ "1" ⟩ []        →⟨ "1" ∷ "v2" ∷ [] ⟩ -- (1,v2)=1()
  ⋄⟨ "+" ⟩ "v1" ∷ [] →⟨ "+" ∷ "f"  ∷ [] ⟩ -- (+,f) = +(v1)
  ⋄⟨ "f" ⟩ "v2" ∷ [] →⟨ "o" ∷ []        ⟩ -- (o) = f(v2)
  end ("o" ∷ [])
```

The above program can be interpreted by transitioning it with a transition sequence:

TODO



### EXTRA EXPERIMENT 1 (Success!)
I'm trying to simplify linearity in the transition system to just be a star relation of variables to
other variables only via valid additions and removals.
```
--module EXPERIMENT-1 where
--  import Relation.Binary.Construct.Closure.ReflexiveTransitive as ReflTrans
--
--  open ReflTrans
--      using (Star)
--      renaming (ε to x⇒x; _◅_ to _⇒∘⇒*_)
--      public
--
--  data _⇒ᵛ_ : ArgsList → ArgsList → Set where
--    _+⇐_ : (l : ArgsList) → (name : String) → l ⇒ᵛ (l +← name)
--    _-⇐_ : (l : ArgsList) → (name : String) → (l +← name) ⇒ᵛ l
--
--  _⇒*_ = Star _⇒ᵛ_
--
--  example1 : ("hello" ∷# []) ⇒* ("hi" ∷# [])
--  example1 = [] -⇐ "hello" ⇒∘⇒* [] +⇐ "hi" ⇒∘⇒* x⇒x

```
