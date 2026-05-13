# SOGAT Reading Group — Michail's Notes

## Preamble

```agda
module notes where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool.Base
open import Data.Bool.Properties
open import Relation.Binary.PropositionalEquality
```

## Monoid
### Exercise 2
- Prove the equations for the monoids.
```agda
record Monoid : Set₁ where
  field
    C : Set
    _·_ : C → C → C
    ∪ : C
    ass : ∀ x y z → x · (y · z) ≡ (x · y) · z
    idl : ∀ x → ∪ · x ≡ x
    idr : ∀ x → x · ∪ ≡ x



MonoidNatPlus : Monoid
MonoidNatPlus = record
  { C = ℕ
  ; _·_  = _+_
  ; ∪ = 0
  ; ass = λ x y z → sym (+-assoc x y z)
  ; idl = λ x → +-identityˡ x
  ; idr = λ x → +-identityʳ x
  }

MonoidNatTimes : Monoid
MonoidNatTimes = record
  { C = ℕ
  ; _·_ = _*_
  ; ∪ = 1
  ; ass = λ x y z → sym (*-assoc x y z)
  ; idl = λ x → *-identityˡ x
  ; idr = λ x → *-identityʳ x
  }

data One : Set where
  ⋆ : One


MonoidStar : Monoid
MonoidStar = record
  { C = One
  ; _·_ = λ ⋆ ⋆ → ⋆
  ; ∪ = ⋆
  ; ass = λ x y z → refl
  ; idl = λ x → refl
  ; idr = λ {⋆ → refl}
  }

MonoidBoolAnd : Monoid
MonoidBoolAnd = record
  { C = Bool
  ; _·_ = _∧_
  ; ∪ = true
  ; ass = λ x y z → sym (∧-assoc x y z)
  ; idl = λ x → ∧-identityˡ x
  ; idr = λ x → ∧-identityʳ x
  }
```
- Define all the monoids with sort {tt, ff}
  - Skipped

## Exercise 3
```
record MonoidMorphism (M N : Monoid) : Set where
  open Monoid M renaming (C to Cₘ; _·_ to _·ₘ_; ∪ to ∪ₘ)
  open Monoid N renaming (C to Cₙ; _·_ to _·ₙ_; ∪ to ∪ₙ)
  field
    f : Cₘ → Cₙ
    _·_ : ∀ (x y : Cₘ) →  f (x ·ₘ y) ≡ f x ·ₙ f y
    ∪ : f ∪ₘ ≡ ∪ₙ

Morph+to* : ℕ →  MonoidMorphism MonoidNatPlus MonoidNatTimes
Morph+to* k = record
  { f = λ n → k ^ n
  ; _·_ = λ x y → ^-distribˡ-+-* k x y
  ; ∪ = refl
  }

```

## Exercise 4
- Working through this ATM
- Looking at Callum's notes
- They utilise `subst`
  ```agda
  subst′ : ∀ {A : Set} → (P : A → Set) {x y : A} → x
           ≡
           y → P x → P y
  subst′ P refl px = px
  ```
  - `subst′`
    - takes
      1. Some type `A`
      2. Predicate P over A
      3. Proof that two elements {x y : A} are equal,
      4. Element of P x,
      5. Gives back an element of P y.
    - In other words, if you know x ≡ y, you can convert something that works for x into something that works for y.
    - In other words, a functor (?)

```
open Monoid
record DependentModel (M : Monoid) : Set₁ where
  open Monoid M renaming (_·_ to _·ₘ_; ∪ to ∪ₘ)
  field
    Cₒ : Monoid.C M → Set
    _∘_ : ∀ {xₘ yₘ : M Monoid.C} → Cₒ xₘ → Cₒ yₘ → Cₒ (xₘ ·ₘ yₘ)
    ass : ∀ xₘ yₘ zₘ → xₘ ∘ (yₘ ∘ zₘ) ≡ (xₘ ∘ yₘ) ∘ zₘ
    ∪ : Cₒ ∪ₘ
    idl : ∀ xₘ → ∪ ∘ xₘ ≡ xₘ
    idr : ∀ xₘ → xₘ ∘ ∪ ≡ xₘ
