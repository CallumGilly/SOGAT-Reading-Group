<!--
```agda
module _ where
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
- [Dependent-Razor](#Dependent-Razor)
- [Dependent-Morphism](#Dependent-Morphism)

## Razor
```agda
private 
  variable
    n m : ℕ

module _ (Ty : Set₁) (Tm : Ty → Set) where

  private variable
    A : Ty
    u v : Tm A

  record R : Set₂ where
    field
      Bool   : Ty
      Nat    : Ty
      true   : Tm Bool
      false  : Tm Bool
      ite    : Tm Bool → Tm A → Tm A → Tm A
      num    : ℕ → Tm Nat
      _+`_   : Tm Nat → Tm Nat → Tm Nat
      isZero : Tm Nat → Tm Bool
      iteβ₁  : ite true  u v ≡ u
      iteβ₂  : ite false u v ≡ v
      +β     : num m +` num n ≡ num (m + n)
      isZeroβ₁ : isZero (num 0) ≡ true
      isZeroβ₂ : isZero (num (suc n)) ≡ false
```
### Exists-Razor
I then can create a small shorthand to represent the common need to represent 
"there exists a razor such that property P holds"

```agda
module _ where
```

### Exercise-15
> If in any model $\text{true} = \text{false}$ then for any $A$ and $u, v : Tm\space A$, we have $u = v$

```agda
module Exercise-15 {Ty : Set₁} {Tm : Ty → Set} (r : R Ty Tm) where
  open R r

  ex15 : true ≡ false → ∀ (A : Ty) (u v : Tm A) → u ≡ v
  ex15 refl A u v = (sym iteβ₁) ⊡ iteβ₂
```
### Exercise-16
> If in any model $\text{num } 0 = \text{num } 1$ then for any $A$ and $u, v : Tm\space A$ we have $u = v$

```agda
module Exercise-16 {Ty : Set₁} {Tm : Ty → Set} (r : R Ty Tm) where
  open R r
  open Exercise-15 r

  ex16 : num 0 ≡ num 1 → ∀ (A : Ty) (u v : Tm A) → u ≡ v
  ex16 prf = ex15 (sym isZeroβ₁ ⊡ cong isZero prf ⊡ isZeroβ₂)
```

### Exercise-17
> There is a model where $\text{num } 1 = \text{num } 2$ but $\text{true }\neq \text{false}$

```agda
module Exercise-17 where 
  open R 

  ex17 : ∃₃ λ (Ty : Set₁) (Tm : Ty → Set) (r : R Ty Tm) 
       → num r 1 ≡ num r 2 × true r ≢ false r
  ex17 = -, -, r , refl , λ ()
    where 
      -- Omitting the type of r makes agda fail silently
      r : R Set (λ A → A)
      r = record { Bool = StdBool
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
```

### Exercise-18
> There is a model where $\text{Tm Bool}$ has three elements (nonstandard model)
```agda
module Exercise-18 where
  open R

  data Troolean : Set where
    ⊤ᵇ : Troolean
    ⊥ᵇ : Troolean
    ⊢ᵇ : Troolean

  ex18 : R Set (λ A → A)
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
  open Exercise-18

  module Part-01 where
    open R
    ℕ𝔹-model : R Set (λ A → A)
    ℕ𝔹-model = record { 
                    Bool = StdBool
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


    ex19₁ : ∃₃ λ (Ty : Set₁) (Tm : Ty → Set) (m : R Ty Tm) 
          → true m ≢ false m × (∀ (t : Tm (Bool m)) (ty : Ty) (u : Tm ty) → ite m t u u ≡ u) 
    ex19₁ = -, -, ℕ𝔹-model , (λ ()) , λ { ⊤ᵇ _ _ → refl ; ⊥ᵇ _ _ → refl }
    

  module Part-02 where
    {- INCOMPLETE
    ex19₂′ : ∃ λ (m : R) → ∀ (t : Tm m (Bool m)) {ty : Ty m} (u : Tm m ty) → ite m t u u ≢ u  
    -- OR
    ex19₂ : ∀ (m : R) → ∀ (t : Tm m (Bool m)) {ty : Ty m} (u : Tm m ty) → ite m t u u ≡ u  
    -}

  module Part-03 where
    {- INCOMPLETE
    ex19₃ : ∃ λ (m : R) → isZero m (num m 0) ≡ false m
    -- OR
    ex19₃′ : (∃ λ (m : R) → isZero m (num m 0) ≡ false m) → ⊥ᵘ
    -}

  module Part-04 (Ty : Set₁) (Tm : Ty → Set) (r : R Ty Tm) where
    open R r 

    ex19₄ : isZero (num 3) ≡ isZero (num 5)
    ex19₄ = isZeroβ₂ ⊡ (sym isZeroβ₂)

  module Part-05 where
    open R

    ex19₅′ : ∃₃ λ (Ty : Set₁) (Tm : Ty → Set) (r : R Ty Tm) 
           → ∀ (t : Tm (Bool r)) {τ : Ty} (u : Tm τ) → Tm (Bool r) ≡ ℕ
    ex19₅′ = -, -, r , λ _ _ → refl
      where
        r : R Set (λ A → A)
        r = record
            { Bool     = ℕ
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
    
```

# R-Hom

We can then define what a morphism of the Razor language is

```agda
module R-Hom 
    {Ty₁ Ty₂ : Set₁} 
    {Tm₁ : Ty₁ → Set} 
    {Tm₂ : Ty₂ → Set} 
    (R₁ : R Ty₁ Tm₁) 
    (R₂ : R Ty₂ Tm₂) 
    (Ty     : Ty₁ → Ty₂)
    (Tm     : ∀ {A : Ty₁} → Tm₁ A → Tm₂ (Ty A))
  where
  open R R₁ using () renaming (Bool to Bool₁ ; Nat to Nat₁    ;
                               true to true₁ ; false to false₁;
                               ite  to ite₁  ; num   to num₁  ;
                               _+`_ to _+`₁_ ; isZero to isZero₁
                               )
  open R R₂ using () renaming (Bool to Bool₂; Nat to Nat₂    ;
                               true to true₂; false to false₂;
                               ite  to ite₂ ; num   to num₂  ;
                               _+`_ to _+`₂_; isZero to isZero₂
                               )
  
  private 
    variable
      A : Ty₁
      bₘ    : Tm₁ Bool₁
      nₘ mₘ : Tm₁ Nat₁
      xₘ yₘ : Tm₁ A

  record R-Hom : Set₁ where
    field
      Bool   : Ty Bool₁           ≡ Bool₂
      Nat    : Ty Nat₁            ≡ Nat₂
      true   : Tm true₁           ≡ subst Tm₂ (sym Bool) true₂
      false  : Tm false₁          ≡ subst Tm₂ (sym Bool) false₂
      ite    : Tm (ite₁ bₘ xₘ yₘ) ≡ ite₂ (subst Tm₂ Bool (Tm bₘ)) (Tm xₘ) (Tm yₘ) 
      num    : Tm (num₁ n)        ≡ subst Tm₂ (sym Nat)  (num₂ n)
      _+`_   : Tm (_+`₁_ nₘ mₘ)   ≡ subst Tm₂ (sym Nat)  (_+`₂_ (subst Tm₂ Nat (Tm nₘ)) (subst Tm₂ Nat (Tm mₘ)))
      izZero : Tm (isZero₁ nₘ)    ≡ subst Tm₂ (sym Bool) (isZero₂ (subst (Tm₂) Nat (Tm nₘ)))
```

# Dependent-Razor
```agda
module _ 
              {Tyₘ : Set₁}
              {Tmₘ : Tyₘ → Set}
              (r   : R Tyₘ Tmₘ) 
              (Ty  : Tyₘ → Set) 
              (Tm  : {Aₘ : Tyₘ} → Ty Aₘ → Tmₘ Aₘ → Set) 
      where
  open R r renaming (Bool to Boolₘ  ; Nat to Natₘ      ;
                     true to trueₘ  ; false to falseₘ  ;
                     ite  to iteₘ   ; num   to numₘ    ;
                     _+`_ to _+`ₘ_  ; isZero to isZeroₘ;
                     iteβ₁ to iteβ₁ₘ; iteβ₂ to iteβ₂ₘ  ;
                     +β to +βₘ      ;
                     isZeroβ₁ to isZeroβ₁ₘ; isZeroβ₂ to isZeroβ₂ₘ)

  private variable
    Aₘ : Tyₘ
    A  : Ty Aₘ
    tₘ fₘ : Tmₘ Aₘ
    nₘ mₘ : Tmₘ Natₘ
    bₘ    : Tmₘ Boolₘ
    u : Tm A tₘ
    v : Tm A fₘ

  record R-Dep : Set₁ where
    field
      Bool   : Ty Boolₘ
      Nat    : Ty Natₘ
      true   : Tm Bool trueₘ 
      false  : Tm Bool falseₘ 
      ite    : Tm Bool bₘ → Tm A tₘ → Tm A fₘ → Tm A (iteₘ bₘ tₘ fₘ)
      num    : (n : ℕ) → Tm Nat (numₘ n)
      _+`_   : Tm Nat nₘ → Tm Nat mₘ → Tm Nat (nₘ +`ₘ mₘ)
      isZero : Tm Nat nₘ → Tm Bool (isZeroₘ nₘ)
      iteβ₁  : ite true  u v ≡ subst (Tm A) (sym iteβ₁ₘ) u
      iteβ₂  : ite false u v ≡ subst (Tm A) (sym iteβ₂ₘ) v
      +β     : num m +` num n ≡ subst (Tm Nat) (sym +βₘ) (num (m + n))
      isZeroβ₁ : isZero (num 0) ≡ subst (Tm Bool) (sym isZeroβ₁ₘ) true
      isZeroβ₂ : isZero (num (suc n)) ≡ subst (Tm Bool) (sym isZeroβ₂ₘ) false
```

# Dependent-Morphism
```agda
module _ 
    {Tyₘ : Set₁}
    {Tmₘ : Tyₘ → Set}
    (r : R Tyₘ Tmₘ) 
    {Tyᵈ : Tyₘ → Set}
    {Tmᵈ : {Aₘ : Tyₘ} → Tyᵈ Aₘ → Tmₘ Aₘ → Set}
    (rᵈ  : R-Dep r Tyᵈ Tmᵈ)
    (Ty  : (Aₘ : Tyₘ) → Tyᵈ Aₘ)
    (Tm  : {Aₘ : Tyₘ} → (uₘ : Tmₘ Aₘ) → (Tmᵈ (Ty Aₘ) uₘ))
  where
  open R r using () renaming (Bool to Boolₘ  ; Nat to Natₘ      ;
                   true to trueₘ  ; false to falseₘ  ;
                   ite  to iteₘ   ; num   to numₘ    ;
                   _+`_ to _+`ₘ_  ; isZero to isZeroₘ;
                   iteβ₁ to iteβ₁ₘ; iteβ₂ to iteβ₂ₘ  ;
                   +β to +βₘ      ;
                   isZeroβ₁ to isZeroβ₁ₘ; isZeroβ₂ to isZeroβ₂ₘ)
  open R-Dep rᵈ using () renaming (Bool to Boolᵈ  ; Nat to Natᵈ      ;
                   true to trueᵈ  ; false to falseᵈ  ;
                   ite  to iteᵈ   ; num   to numᵈ    ;
                   _+`_ to _+`ᵈ_  ; isZero to isZeroᵈ;
                   iteβ₁ to iteβ₁ᵈ; iteβ₂ to iteβ₂ᵈ  ;
                   +β to +βᵈ      ;
                   isZeroβ₁ to isZeroβ₁ᵈ; isZeroβ₂ to isZeroβ₂ᵈ)

  record R-Sec : Set₁ where
    field
      Bool  : Ty Boolₘ  ≡ Boolᵈ
      Nat   : Ty Natₘ   ≡ Natᵈ
      true  : Tm trueₘ  ≡ subst₂ Tmᵈ (sym Bool) refl trueᵈ
      false : Tm falseₘ ≡ subst₂ Tmᵈ (sym Bool) refl falseᵈ
      ite   : (bₘ : Tmₘ Boolₘ) (Aₘ : Tyₘ) (tₘ : Tmₘ Aₘ) (fₘ : Tmₘ Aₘ) 
            → Tm (iteₘ bₘ tₘ fₘ) ≡ iteᵈ (subst₂ Tmᵈ Bool refl (Tm bₘ)) (Tm tₘ) (Tm fₘ)
      num   : (n : ℕ) → Tm (numₘ n) ≡ subst₂ Tmᵈ (sym Nat) refl (numᵈ n)
      _+`_  : (mₘ nₘ : Tmₘ Natₘ) 
            → Tm (mₘ +`ₘ nₘ) ≡ subst₂ Tmᵈ (sym Nat) refl (subst₂ Tmᵈ Nat refl (Tm mₘ) +`ᵈ subst₂ Tmᵈ Nat refl (Tm nₘ))
      isZero : (mₘ : Tmₘ Natₘ) → Tm (isZeroₘ mₘ) ≡ subst₂ Tmᵈ (sym Bool) refl (isZeroᵈ (subst₂ Tmᵈ Nat refl (Tm mₘ)))
```

# Syntax

```agda
module Syntax 
    (Tyₘ : Set₁)
    (Tmₘ : Tyₘ → Set)
  where
  open R

  R-Syn : R Tyₘ Tmₘ → Set₁
  R-Syn rₘ = ∀ {Tyᵈ : Tyₘ → Set}
           → ∀ {Tmᵈ : {Aₘ : Tyₘ} → Tyᵈ Aₘ → Tmₘ Aₘ → Set}
           → ∀ (rᵈ : R-Dep rₘ Tyᵈ Tmᵈ) 
           → ∃₂ (R-Sec rₘ rᵈ)
```
# Unique

```agda
module R-Unq 
    {Tyₘ₁ Tyₘ₂ : Set₁}
    {Tmₘ₁ : Tyₘ₁ → Set}
    {Tmₘ₂ : Tyₘ₂ → Set}
    {r₁ : R Tyₘ₁ Tmₘ₁}
    {r₂ : R Tyₘ₂ Tmₘ₂} 
  where
  open R-Hom

  R-Unq : {Ty₁ : Tyₘ₁ → Tyₘ₂}
        → {Tm₁ : ∀ {A : Tyₘ₁} → Tmₘ₁ A → Tmₘ₂ (Ty₁ A)}
        → R-Hom r₁ r₂ Ty₁ Tm₁
        → Set₁
  R-Unq {Ty₁} {Tm₁} r-hom₁ =
          ∀ {Ty₂ : Tyₘ₁ → Tyₘ₂}
        → ∀ {Tm₂ : ∀ {A : Tyₘ₁} → Tmₘ₁ A → Tmₘ₂ (Ty₂ A)}
        → ∀ (r-hom₂ : R-Hom r₁ r₂ Ty₁ Tm₁)
        → Σ (∀ (x : Tyₘ₁) → Ty₁ x ≡ Ty₂ x) 
        λ ty₁≡ty₂ → ∀ (x : Tyₘ₁) (y : Tmₘ₁ x) → Tm₁ y ≡ subst Tmₘ₂ (sym (ty₁≡ty₂ x)) (Tm₂ y)
```

# Initial-Model
```agda
module R-Int 
    {Tyₘ : Set₁}
    {Tmₘ : Tyₘ → Set}
  where
  open R-Hom
  open R-Unq
  R-Int : R Tyₘ Tmₘ → Set₂
  R-Int rₘ = ∀ {Tyₘ′ : Set₁}
           → ∀ {Tmₘ′ : Tyₘ′ → Set}
           → ∀ (rₘ′  : R Tyₘ′ Tmₘ′)
           → ∃₃ λ 
              (Ty : Tyₘ → Tyₘ′) 
              (Tm : ∀ {A : Tyₘ} → Tmₘ A → Tmₘ′ (Ty A)) 
              (r-hom : R-Hom rₘ rₘ′ Ty Tm) 
            → R-Unq r-hom
```
# Normal-Form

```agda
module NormalForm (Tyₘ : Set₁) (Tmₘ : Tyₘ → Set) (rₘ : R Tyₘ Tmₘ) where
  open R
  open R-Hom
```






