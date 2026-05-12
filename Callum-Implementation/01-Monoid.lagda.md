```agda
{-# OPTIONS --without-K #-}
```

Here is my (attempt) at implementing monoids as GATs.

I feel that it is important to note: The text in these notes is me talking/ 
explaining to myself, and contains zero polish, the interesting bits are the 
Agda.
These notes can also be loaded quite nicely as an obsidian Valut which - when 
in reading mode only - highlights the Agda and hides some imports/ openings.
<!--
```agda
module 01-Monoid where
import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning

```
-->

We first define a record type which models Monoid.

```agda
record Monoid : Set₁ where

  infixr 6 M-Prod

  field 
    C : Set₀
    M-Prod : C → C → C
    ass : ∀ {x y z : C} → M-Prod x (M-Prod y z) ≡ M-Prod (M-Prod x y) z
    u : C
    idl : ∀ {x : C} → M-Prod u x ≡ x
    idr : ∀ {x : C} → M-Prod x u ≡ x
```


We can then make an instance of this model of monoid for any monoid. Take 
addition as our first example.

```agda
open Monoid
open import Data.Nat
open import Data.Nat.Properties

Plus-Mon : Monoid
C   Plus-Mon = ℕ
M-Prod Plus-Mon = _+_
ass Plus-Mon {x} {y} {z} = sym (+-assoc x y z)
u   Plus-Mon = 0
idl Plus-Mon = +-identityˡ _
idr Plus-Mon = +-identityʳ _
```

And true and false as our second example

```agda
data Bool : Set where
  tt : Bool
  ff : Bool

infixr 6 _∧_
_∧_ : Bool → Bool → Bool
tt ∧ tt = tt
tt ∧ ff = ff
ff ∧ _  = ff

private
  variable 
    x y z : Bool

∧-assoc : x ∧ y ∧ z ≡ (x ∧ y) ∧ z
∧-assoc {tt} {tt} {tt} = refl
∧-assoc {tt} {tt} {ff} = refl
∧-assoc {tt} {ff} {z } = refl
∧-assoc {ff} {y } {z } = refl

∧-Mon : Monoid
C   ∧-Mon = Bool
M-Prod ∧-Mon = _∧_
ass ∧-Mon = ∧-assoc
u   ∧-Mon = tt
idl ∧-Mon {tt} = refl
idl ∧-Mon {ff} = refl
idr ∧-Mon {tt} = refl
idr ∧-Mon {ff} = refl
```

Given our definitions of Monoid, we can then produce morphisms between monoids,
these morphisms require:
1) A function from the carrier set of $C_M$ to the carrier set of $C_N$
2) Conversion of the binary function
3) Conversion of the identity element

```agda
record Morphism (M N : Monoid) : Set where
  field
    C   : M .C → N .C
    M-Prod : (x y : (M .Monoid.C)) → C ((M .M-Prod) x y) ≡ (N .M-Prod) (C x) (C y)
    u   : C (M .u) ≡ N .u
```

<!--
```agda
open Morphism
```
-->

We can then create a morphism from `ℕ` plus to `Bool` and. We do this by mapping
non-zero naturals to false, and zero to true.

```agda
ℕ+→𝔹∧ : Morphism Plus-Mon ∧-Mon
C ℕ+→𝔹∧ zero = tt
C ℕ+→𝔹∧ (suc x) = ff
M-Prod ℕ+→𝔹∧  zero    zero    = refl
M-Prod ℕ+→𝔹∧  zero    (suc y) = refl
M-Prod ℕ+→𝔹∧  (suc x) y       = refl
u ℕ+→𝔹∧ = refl
```

# Dependent models

We can then define dependent models. Dependent models have the same number of 
components as the model they are dependent over. The dependent model over a 
monoid is shown below.

Here Myself and Jairo have been... having a fun time trying... to work out how 
to define the properties in a nice way. 
I initially attempted an implementation using heterogeneous equality, but have 
now moved away from such an implementation as to avoid dependency on K.

![[01-Monoid-WithK.lagda]]

## `subst` Reminder
As we cannot use heterogeneous equality, we need some way to represent 
the propertys within our model.
This cannot be done simply with `_≡_` because we need equality between elements 
of different types.
Take left identity for example:
- The left hand side is `DM-Prod {y} {x} u xm` and has the type `DC (M .M-Prod y x)`
- Meanwhile the right hand side is `xm` and has the type `DC x`
When evaluated, these types both reduce to the same type (`DC x`?), but this 
doesn't help us in our record definition, so we need  some way to compare two 
elements with type `A` and `B` given a proof that `A ≡ B` (in this case our prior
left identity proof).

This is where `subst` can be used.

```agda
subst′ : ∀ {A : Set} → (P : A → Set) {x y : A}
          → x ≡ y
          → P x → P y
subst′ P refl px = px
```
Here we can see that subst takes 


## Without Heterogeneous Equality

```agda
record D-Monoid (M : Monoid) : Set₁ where
  field 
    DC : M .C → Set
    DM-Prod : ∀ {x y : M .Monoid.C} → DC x → DC y → DC ((M .M-Prod) x y)
    Dass : ∀ {x y z : M .Monoid.C} 
        → ∀ {xm : DC x}{ym : DC y}{zm : DC z} 
        → _≡_ 
            (subst DC (M .ass {x} {y} {z}) (DM-Prod xm (DM-Prod ym zm)))
            (DM-Prod (DM-Prod xm ym) zm) 
    Du  : DC (M .u)
    Didl : ∀ {x : M .C} {xm : DC x} 
      → subst DC (M .idl) (DM-Prod Du xm) ≡ xm
      --→ subst {_} {M .C} {_} DC {M .M-Prod (M .u) x} {x} (M .idl) (DM-Prod {M .u} {x} Du xm) ≡ xm
    Didr : ∀ {x : M .C} {xm : DC x}
      → subst DC (M .idr) (DM-Prod xm Du) ≡ xm
```

<!--
```agda
open D-Monoid
```
-->

With this new subst filled definition, we can attempt exercise 4 once more

> Any model can be turned into a dependent model where we ignore the dependency

```agda

infixr 6 _⊡_
_⊡_ = trans

subst-lemma : ∀ {A : Set}
       → ∀ {x x′ : A} 
       → ∀ (prf : x ≡ x′) 
       → ∀ (i : A) 
       → subst (λ _ → A) prf i ≡ i
subst-lemma refl _ = refl

ignored : ∀ {M : Monoid} → D-Monoid M
ignored {M} = DM
  where

    DM : D-Monoid M
    DC      DM = λ _ → M .C
    DM-Prod DM = M .M-Prod
    Dass    DM =  cong (subst (λ _ → M .C) (M .ass)) (M .ass)
                ⊡ subst-lemma (M .ass) _
    Du      DM = M .u
    Didl DM {x} {xm} =
      begin
        subst (λ _ → M .C) (M .idl) (M .M-Prod (M .u) xm)
      ≡⟨ cong (subst (λ _ → M .C) (M .idl)) (M .idl) ⟩
        subst (λ _ → M .C) (M .idl) xm 
      ≡⟨ subst-lemma (M .idl) xm ⟩ 
        xm
      ∎
    Didr    DM {x} {xm} =
        cong (subst (λ _ → M .C) (M .idr)) (M .idr)
      ⊡ subst-lemma (M .idr) xm
```


---


I can then attempt Exercise 5:

> Any dependent model $D$ over $M$ can be turned into a model together with a morphism into $M$.
> The carrier will be $(x_M : CM ) \times CD x_M$ (a dependent Descartes-product, or $\Sigma$-type in the metatheory)

Descartes-product ≡ Cartesian Product

```agda
open import Data.Product
open import Data.Product.Properties
model : ∀ {M : Monoid} → D-Monoid M → Monoid
model {M} D = N
  where
    N : Monoid
    C N = Σ (M .C) (D .DC)
    M-Prod N (x₁ , dx₁) (x₂ , dx₂) = (M .M-Prod x₁ x₂) , (D .DM-Prod dx₁ dx₂)
    ass N {x , dx} {y , dy} {z , dz} = Σ-≡,≡→≡ (M .ass , D .Dass)
    u N = M .u , D .Du
    idl N {x , dx} = Σ-≡,≡→≡ ((M .idl) , (D .Didl))
    idr N {x , dx} = Σ-≡,≡→≡ ((M .idr) , (D .Didr))
```





