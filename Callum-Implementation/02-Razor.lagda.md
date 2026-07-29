```
module _ where
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality

private 
  variable
    n m : ℕ

record Razor : Set₂ where
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

data B : Set where
  tt : B
  ff : B

example-model : Razor
example-model = record { Ty = Set
              ; Tm = λ A → A
              ; Bool = B
              ; Nat = ℕ
              ; true = tt
              ; false = ff
              ; ite = λ {tt → λ x _ → x ; ff → λ _ y → y }
              ; num = λ n → n
              ; _+`_ = λ x y → x + y
              ; isZero = λ {zero → tt ; (suc _) → ff}
              ; iteβ₁ = refl
              ; iteβ₂ = refl
              ; +β = refl
              ; isZeroβ₁ = refl
              ; isZeroβ₂ = refl
              }

```

We can then attempt exercise 15 for any model

```agda
_⊡_ = trans
infixr 6 _⊡_

module Ex15 (model : Razor) where
  open Razor model

  ex15 : true ≡ false → ∀ (A : Ty) (u v : Tm A) → u ≡ v
  ex15 refl A u v = (sym (iteβ₁ {A} {u} {v})) ⊡ iteβ₂ {A} {u} {v}

module Ex16 (model : Razor) where
  open Razor model
  open Ex15 model

  ex16 : num 0 ≡ num 1 → ∀ (A : Ty) (u v : Tm A) → u ≡ v
  ex16 prf A u v = ex15 (sym isZeroβ₁ ⊡ cong isZero prf ⊡ isZeroβ₂) A u v

module Ex17 where 
  open Razor

  _∧_ : B → B → B
  tt ∧ tt = tt
  tt ∧ ff = ff
  ff ∧ tt = ff
  ff ∧ ff = ff

  ex17 : ∃ λ (m : Razor) → num m 1 ≡ num m 2 × true m ≢ false m
  proj₁ ex17 = record { 
                  Ty = Set
                ; Tm = λ A → A
                ; Bool = B
                ; Nat = B
                ; true = tt
                ; false = ff
                ; ite = λ {tt → λ x _ → x ; ff → λ _ y → y }
                ; num = λ {zero → tt ; (suc n) → ff}
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

module Ex18 where
  open Razor

  data Troolean : Set where
    tt : Troolean
    ff : Troolean
    tf : Troolean
    -- Although I would absolutely love to use emojis, and agda supports them, 
    -- nvim-agda does not
    --🤷 : Troolean

  ex18 : Razor
  Ty       ex18 = Set
  Tm       ex18 = λ A → A
  Bool     ex18 = Troolean
  Nat      ex18 = ℕ
  true     ex18 = tt
  false    ex18 = ff
  ite      ex18 = λ { tt x _ → x
                    ; ff _ y → y
                    --; 🤷 x _ → ? 
                    ; tf x _ → x
                    }
  num      ex18 = λ { n → n }
  _+`_     ex18 = _+_
  isZero   ex18 = λ { zero → tt ; (suc n) → ff }
  iteβ₁    ex18 = refl
  iteβ₂    ex18 = refl
  +β       ex18 = refl
  isZeroβ₁ ex18 = refl
  isZeroβ₂ ex18 = refl

module Ex19 where
  open Razor
  open Ex17 using (_∧_)
  open Ex18

  ex19₁ : ∃ λ (m : Razor) → true m ≢ false m × (∀ (t : Tm m (Bool m)) (ty : Ty m) (u : Tm m ty) → ite m t u u ≡ u) 
  proj₁ ex19₁ = example-model 
  proj₁ (proj₂ ex19₁) = λ ()
  proj₂ (proj₂ ex19₁) =
                        λ { tt _ _ → refl
                          ; ff _ _ → refl
                          }

  _∧₃_ : Troolean → Troolean → Troolean
  ff ∧₃ y = ff
  tt ∧₃ ff = ff
  tt ∧₃ tt = tt
  tt ∧₃ tf = tf
  tf ∧₃ tt = tf
  tf ∧₃ ff = ff
  tf ∧₃ tf = tf

  ex19₂′ : ∃ λ (m : Razor) → ∀ (t : Tm m (Bool m)) {ty : Ty m} (u : Tm m ty) → ite m t u u ≢ u  
  proj₁ ex19₂′ = record
                { Ty       = Set
                ; Tm       = λ A → Troolean
                ; Bool     = Troolean
                ; Nat      = Troolean
                ; true     = tt
                ; false    = ff
                ; ite      = λ 
                            { tt x₁ x₂ → x₁
                            ; ff x₁ x₂ → x₂
                            ; {A} tf x₁ x₂ → ff
                            --; {A} tf x₁ x₂ → tf
                            }
                ; num      = λ { zero → tt ; (suc n) → ff }
                ; _+`_     = _∧₃_
                ; isZero   = λ x → x
                ; iteβ₁    = refl
                ; iteβ₂    = refl
                ; +β       = λ { 
                      {zero} {zero}   → refl
                    ; {zero} {suc n}  → refl
                    ; {suc m} {zero}  → refl
                    ; {suc m} {suc n} → refl
                  }
                ; isZeroβ₁ = refl
                ; isZeroβ₂ = refl
                }
  proj₂ ex19₂′ tt u x = ?
  proj₂ ex19₂′ ff u x = ?
  proj₂ ex19₂′ tf tt ()


  ex19₂ : ∀ (m : Razor) → ∀ (t : Tm m (Bool m)) {ty : Ty m} (u : Tm m ty) → ite m t u u ≡ u  
  ex19₂ m t u = ?
    --let tm = iteβ₁ m {_} {u} {u} in 

  lemma : ∀ (m : Razor) → true m ≢ false m
  lemma m x = ?

  ex19₃ : ∃ λ (m : Razor) → isZero m (num m 0) ≡ false m
  proj₁ ex19₃ = record
                 { Ty = Set
                 ; Tm = λ A → A
                 ; Bool = B
                 ; Nat = ℕ
                 ; true = tt
                 ; false = ff
                 ; ite = λ { tt x₁ x₂ → x₁ ; ff x₁ x₂ → x₂ }
                 ; num = λ n → n
                 ; _+`_ = _+_
                 ; isZero = λ { zero → ff ; (suc n) → tt }
                 ; iteβ₁ = refl 
                 ; iteβ₂ = refl
                 ; +β = refl
                 ; isZeroβ₁ = ?
                 ; isZeroβ₂ = ?
                 }
  proj₂ ex19₃ = ?


  ex19₃′ : (∃ λ (m : Razor) → isZero m (num m 0) ≡ false m) → ⊥
  ex19₃′ (m , snd) = let tm = (snd ⊡ sym (isZeroβ₂ m {1})) in ?
    --let tm = sym (isZeroβ₁ m) ⊡ snd in ?

  ex19₄ : ∀ (m : Razor) → isZero m (num m 3) ≡ isZero m (num m 5)
  ex19₄ m = isZeroβ₂ m ⊡ (sym (isZeroβ₂ m))

  ex19₅′ : ∃ λ (m : Razor) → ∀ (t : Tm m (Bool m)) {ty : Ty m} (u : Tm m ty) → Tm m (Bool m) ≡ ℕ
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

# Morphisms

We can then define what a morphism of the Razor language is

```agda
module Morphism where
  open Razor

  record Morphism (R₁ R₂ : Razor) : Set₁ where
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
  open Razor

  Razor-Syn : (R : Razor) → Set₁
  Razor-Syn = ?
```
```agda
module NormalForm where
  open Razor

  Nf : Ty ? → Set
```




