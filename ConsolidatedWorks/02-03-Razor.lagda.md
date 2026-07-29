<!--
```agda
module 02-03-Razor where
open import Data.Nat
open import Data.Product
open import Data.Empty renaming (⊥ to ⊥ᵘ)
open import Data.Bool using (_∧_) renaming (Bool to StdBool; false to ⊥ᵇ; true to ⊤ᵇ)
open import Relation.Binary.PropositionalEquality
open import Shorthands
```
-->

# 2.3 Razor

Following [section 2.3](../sogat-paris.pdf#subsection.2.3)

- [Razor](#Razor)
  - [Exercise-15](#Exercise-15)
  - [Exercise-16](#Exercise-16)
  - [Exercise-17](#Exercise-17)
  - [Exercise-18](#Exercise-18)
  - [Exercise-19](#Exercise-19)
- [Razor-Hom](#Razor-Hom)

## Razor
```agda
private 
  variable
    n m : ℕ

record R : Set₂ where
  field
    Ty     : Set₁
    Tm     : Ty → Set
    Bool   : Ty
    Nat    : Ty
    true   : Tm Bool
    false  : Tm Bool
    ite    : ∀ {A : Ty} → Tm Bool → Tm A → Tm A → Tm A
    num    : ℕ → Tm Nat
    _+`_   : Tm Nat → Tm Nat → Tm Nat
    isZero : Tm Nat → Tm Bool
    iteβ₁  : ∀ {A : Ty} {u v : Tm A} → ite true  u v ≡ u
    iteβ₂  : ∀ {A : Ty} {u v : Tm A} → ite false u v ≡ v
    +β     : num m +` num n ≡ num (m + n)
    isZeroβ₁ : isZero (num 0) ≡ true
    isZeroβ₂ : isZero (num (suc n)) ≡ false
```

### Exercise-15
> If in any model $\text{true} = \text{false}$ then for any $A$ and $u, v : Tm\space A$, we have $u = v$

```agda
module Exercise-15 (r : R) where
  open R r

  ex15 : true ≡ false → ∀ (A : Ty) (u v : Tm A) → u ≡ v
  ex15 refl A u v = (sym (iteβ₁ {A} {u} {v})) ⊡ iteβ₂ {A} {u} {v}
```
### Exercise-16
```agda
module Exercise-16 (r : R) where
  open R r
  open Exercise-15 r

  ex16 : num 0 ≡ num 1 → ∀ (A : Ty) (u v : Tm A) → u ≡ v
  ex16 prf A u v = ex15 (sym isZeroβ₁ ⊡ cong isZero prf ⊡ isZeroβ₂) A u v
```

### Exercise-17
```agda
module Exercise-17 where 
  open R

  ex17 : ∃ λ (m : R) → num m 1 ≡ num m 2 × true m ≢ false m
  proj₁ ex17 = record { 
                  Ty = Set
                ; Tm = λ A → A
                ; Bool = StdBool
                ; Nat = StdBool
                ; true = ⊤ᵇ
                ; false = ⊥ᵇ
                ; ite = λ {⊤ᵇ → λ x _ → x ; ⊥ᵇ → λ _ y → y }
                ; num = λ {zero → ⊤ᵇ ; (suc n) → ⊥ᵇ}
                ; _+`_ = _∧_
                ; isZero = λ x → x
                ; iteβ₁ = refl
                ; iteβ₂ = refl
                ; +β = λ { {zero } {zero } → refl 
                         ; {zero } {suc n} → refl
                         ; {suc m} {zero } → refl
                         ; {suc m} {suc n} → refl
                         }
                ; isZeroβ₁ = refl
                ; isZeroβ₂ = refl
                }
  proj₂ ex17 = refl , λ ()
```

### Exercise-18
```agda
module Exercise-18 where
  open R

  data Troolean : Set where
    ⊤ᵇ : Troolean
    ⊥ᵇ : Troolean
    ⊢ᵇ : Troolean

  ex18 : R
  Ty       ex18 = Set
  Tm       ex18 = λ A → A
  Bool     ex18 = Troolean
  Nat      ex18 = ℕ
  true     ex18 = ⊤ᵇ
  false    ex18 = ⊥ᵇ
  ite      ex18 = λ { ⊤ᵇ x _ → x
                    ; ⊥ᵇ _ y → y
                    ; ⊢ᵇ x _ → x
                    }
  num      ex18 = λ { n → n }
  _+`_     ex18 = _+_
  isZero   ex18 = λ { zero → ⊤ᵇ ; (suc n) → ⊥ᵇ }
  iteβ₁    ex18 = refl
  iteβ₂    ex18 = refl
  +β       ex18 = refl
  isZeroβ₁ ex18 = refl
  isZeroβ₂ ex18 = refl
```

### Exercise-19
Currently part 2 and 3 of this exercise are not done
```agda
module Exercise-19 where
  open R
  open Exercise-18

  ℕ𝔹-model : R
  ℕ𝔹-model = record { Ty = Set
                ; Tm = λ A → A
                ; Bool = StdBool
                ; Nat = ℕ
                ; true = ⊤ᵇ
                ; false = ⊥ᵇ
                ; ite = λ {⊤ᵇ → λ x _ → x ; ⊥ᵇ → λ _ y → y }
                ; num = λ n → n
                ; _+`_ = λ x y → x + y
                ; isZero = λ {zero → ⊤ᵇ ; (suc _) → ⊥ᵇ}
                ; iteβ₁ = refl
                ; iteβ₂ = refl
                ; +β = refl
                ; isZeroβ₁ = refl
                ; isZeroβ₂ = refl
                }


  ex19₁ : ∃ λ (m : R) → true m ≢ false m × (∀ (t : Tm m (Bool m)) (ty : Ty m) (u : Tm m ty) → ite m t u u ≡ u) 
  proj₁ ex19₁ = ℕ𝔹-model 
  proj₁ (proj₂ ex19₁) = λ ()
  proj₂ (proj₂ ex19₁) =
                        λ { ⊤ᵇ _ _ → refl
                          ; ⊥ᵇ _ _ → refl
                          }

  {- INCOMPLETE
  ex19₂′ : ∃ λ (m : R) → ∀ (t : Tm m (Bool m)) {ty : Ty m} (u : Tm m ty) → ite m t u u ≢ u  
  -- OR
  ex19₂ : ∀ (m : R) → ∀ (t : Tm m (Bool m)) {ty : Ty m} (u : Tm m ty) → ite m t u u ≡ u  

  ex19₃ : ∃ λ (m : R) → isZero m (num m 0) ≡ false m
  -- OR
  ex19₃′ : (∃ λ (m : R) → isZero m (num m 0) ≡ false m) → ⊥ᵘ
  -}

  ex19₄ : ∀ (m : R) → isZero m (num m 3) ≡ isZero m (num m 5)
  ex19₄ m = isZeroβ₂ m ⊡ (sym (isZeroβ₂ m))

  ex19₅′ : ∃ λ (m : R) → ∀ (t : Tm m (Bool m)) {ty : Ty m} (u : Tm m ty) → Tm m (Bool m) ≡ ℕ
  proj₁ ex19₅′ = record
                { Ty       = Set
                ; Tm       = λ A → A
                ; Bool     = ℕ
                ; Nat      = ℕ
                ; true     = 1
                ; false    = 0
                ; ite      = λ {0 a b → b ; (suc n) a b → a}
                ; num      = λ x → x
                ; _+`_     = _+_
                ; isZero   = λ { 0 → 1 ; (suc n) → 0 }
                ; iteβ₁    = refl
                ; iteβ₂    = refl
                ; +β       = refl
                ; isZeroβ₁ = refl
                ; isZeroβ₂ = refl
                }
  proj₂ ex19₅′ t u = refl
```

# R-Hom

We can then define what a morphism of the Razor language is

> [!TODO]
> Change this so it uses Ty not Mor-Ty etc etc
```agda
module R-Hom where
  open R

  record R-Hom (R₁ R₂ : R) : Set₁ where
    field
      Mor-Ty     : Ty R₁ → Ty R₂
      Mor-Tm     : {A : Ty R₁} → Tm R₁ A → Tm R₂ (Mor-Ty A)
      Mor-Bool   : Mor-Ty (Bool  R₁) ≡ Bool R₂
      Mor-Nat    : Mor-Ty (Nat   R₁) ≡ Nat  R₂
      Mor-true   : Mor-Tm (true  R₁) ≡ subst (Tm R₂) (sym Mor-Bool) (true  R₂)
      Mor-false  : Mor-Tm (false R₁) ≡ subst (Tm R₂) (sym Mor-Bool) (false R₂)
      Mor-ite    : ∀ {A : Ty R₁} (bₘ : Tm R₁ (Bool R₁)) (tₘ fₘ : Tm R₁ A) → Mor-Tm (ite R₁ bₘ tₘ fₘ) ≡ ite R₂ (subst (Tm R₂) Mor-Bool (Mor-Tm bₘ)) (Mor-Tm tₘ) (Mor-Tm fₘ) 
      Mor-Num    : ∀ {n : ℕ} → Mor-Tm (num R₁ n) ≡ subst (Tm R₂) (sym Mor-Nat) (num R₂ n)
      Mor-_+_    : ∀ (uₘ vₘ : Tm R₁ (Nat R₁)) → Mor-Tm (_+`_ R₁ uₘ vₘ) ≡ subst (Tm R₂) (sym Mor-Nat) (_+`_ R₂ (subst (Tm R₂) Mor-Nat (Mor-Tm uₘ)) (subst (Tm R₂) Mor-Nat (Mor-Tm vₘ)))
      Mor-izZero : ∀ (uₘ : Tm R₁ (Nat R₁)) → Mor-Tm (isZero R₁ uₘ) ≡ subst (Tm R₂) (sym Mor-Bool) (isZero R₂ (subst (Tm R₂) Mor-Nat (Mor-Tm uₘ)))
```

# Normal Form
To define normal form, we first need to define Syntax I

```agda
module Syntax where
  open R

  R-Syn : (R : R) → Set₁
  R-Syn = ?
```
```agda
module NormalForm where
  open R

  Nf : Ty ? → Set
```






