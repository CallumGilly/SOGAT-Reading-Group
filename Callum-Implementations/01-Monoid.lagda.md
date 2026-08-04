```agda
--{-# OPTIONS --without-K #-}
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
open import Function using (_$_; id)
open import Level
open import Agda.Builtin.Unit
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
_∧ _ : Bool → Bool → Bool
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

Later (for ex. 7) we will also require a monoid where the carrier contains only 
one element.
```agda
singleton : Monoid
C singleton = ⊤
M-Prod singleton _ _ = tt
ass singleton = refl
u singleton = tt
idl singleton = refl
idr singleton = refl
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

subst-lemma : ∀ {A B : Set}
       → ∀ {x x′ : A} 
       → ∀ (prf : x ≡ x′) 
       → ∀ (i : B) 
       → subst (λ _ → B) prf i ≡ i
subst-lemma refl _ = refl

-- Exercise 4 using the same mon
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

We can then do exercise 4 and make the Dependent Monoid depend on any Monoid.
```agda
lift-M→DM$M′ : ∀ {M′ : Monoid} → (M : Monoid) → D-Monoid M′
lift-M→DM$M′ {M′} M = DM
  where
    DM : D-Monoid M′
    DC DM = λ _ → M .C
    DM-Prod DM = M .M-Prod
    Dass DM = cong (subst _ _) (M .ass)
              ⊡ (subst-lemma (M′ .ass) _)
    Du DM = M .u
    Didl DM = cong (subst _ _) (M .idl)
            ⊡ subst-lemma _ _
    Didr DM = cong (subst _ _) (M .idr)
            ⊡ subst-lemma _ _
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

I can then define the dependent morphism
```agda
record D-Morphism (M : Monoid) (DM : D-Monoid M) : Set₁ where
  field
    MorC : (x : M .C) → (DM .DC) x
    Mor-Prod : (x y : M .C)
             → MorC ((M .M-Prod) x y) 
             ≡ 
               ((DM .DM-Prod) (MorC x) (MorC y))
    MorU : MorC (M .u) ≡ (DM .Du)
open D-Morphism
```

> The syntax is a model from which there is a dependent morphism into any 
> dependent model (the dependent model has to be over the syntax for this to 
> make sense). 

Syntax is a model - AKA syntax is a specific monoid in this case

The function which takes a dependent model over the syntax and returns the 
dependent morphism is called induction. This is also known as the dependent,
eliminator, or the universal property


```agda
--Syntax : ∃(M : Monoid) → (DM : D-Monoid M) → D-Morphism M DM
Syntax : Monoid → Set₁
Syntax M = ∀ (DM : D-Monoid M) → D-Morphism M DM
```

We can then also define the dependent morphism called induction

```agda
Induction : (syn : Monoid) → (Syntax syn) → (DM : D-Monoid syn) → D-Morphism syn DM
Induction mon I = I
```

# Exercise 7

> For a given Model $M$, show that the following two are equivalent
> - There is a dependent morphism into any model over $M$
> - There is a unique homomorphism from $M$ into any model, this we know as initiality.

First, I need to define what it means for a model to be initial.
To be initial, there needs to exist a morphism, and it needs to be unique.
```agda
Unique : ∀ {M M′ : Monoid} → (Mo : Morphism M M′) → Set
Unique {M} {M′} Mo = ∀ (Mo′ : Morphism M M′) (x : M .C) → (Mo .C x) ≡ (Mo′ .C x)

Initial : ∀ (M : Monoid) → Set₁
Initial M = ∀ (M′ : Monoid) → Σ (Morphism M M′) Unique 
```

We then also need Uniqueness of Identity, which we can define as so. 
```agda
UIP : ∀ {ℓ : Level} → (A : Set ℓ) → Set ℓ
UIP {ℓ} A = ∀ {x y : A} → ∀ (a b : x ≡ y) → a ≡ b

uip : ∀ {a} {A : Set a} → UIP A
uip refl refl = refl
```

Then we can create the first direction of exercise 7, such that if a monoid is 
a Syntax, then that monoid must be Initial.

For this we make the carrier of our morphism by
1) Creating a Dependent Monoid, which is dependent on M, who's carrier is the 
   carrier of M′
2) Creating a Dependent Morphism into this
3) Use the carrier of this dependent morphism to build the carrier of our 
   non dependent morphism
```agda
ex7₁ : ∀ {M : Monoid} → Syntax M → Initial M
C      (proj₁ (ex7₁ {M} I M′)) = I (lift-M→DM$M′ {M} M′) .MorC
M-Prod (proj₁ (ex7₁ I M′)) x y = I (lift-M→DM$M′ M′) .Mor-Prod x y
u      (proj₁ (ex7₁ I M′)) = I (lift-M→DM$M′ M′) .MorU
proj₂ (ex7₁ {M} I M′) Mo₂ x = DMor .MorC x 
  where 
    -- We create the Dependent Monoid on M where the carrier is "Evidence"(?) 
    -- that, for all values of M, our two morphisms will "produce" the same value?
    DM : D-Monoid M
    DC DM x = (I (lift-M→DM$M′ M′)) .MorC x ≡ Mo₂ .C x
    DM-Prod DM {x} {y} prf₁ prf₂ = 
          I (lift-M→DM$M′ M′) .Mor-Prod x y
        ⊡ cong₂ (M′ .M-Prod) prf₁ prf₂
        ⊡ sym (Mo₂ .M-Prod x y)
    Dass DM {x} {y} {z} {xm} {ym} {zm} = uip _ _
    Du   DM = I (lift-M→DM$M′ M′) .MorU
            ⊡ sym (Mo₂ .u)
    Didl DM = uip _ _
    Didr DM = uip _ _
    
    
    DMor : D-Morphism M DM
    DMor = I DM
```

For part two, we need a proof that if we have some initial model, every element
of its carrier is unit.

```agda
MorId : ∀ {M : Monoid} → Morphism M M
C MorId = id
M-Prod MorId x y = refl
u MorId = refl

MorU′ : ∀ {M : Monoid} → Morphism M M
C (MorU′ {M}) _ = M .u
M-Prod (MorU′ {M}) _ _ = sym $ M .idr
u MorU′ = refl

Initial⇒unit : ∀ {M : Monoid} → Initial M → ∀ (x : M .C) → x ≡ M .u
Initial⇒unit {M} initial x = let I→U M′ = proj₂ (initial M′) in let tmp = I→U M MorId (M .u) in ?

ex7₂ : ∀ {M : Monoid} → Initial M → Syntax M
MorC (ex7₂ {M} initial DM) x = subst (DM .DC) (sym (Initial⇒unit initial x)) (DM .Du)
Mor-Prod (ex7₂ initial DM) = ?
MorU     (ex7₂ initial DM) = ?
    
--ex7 : ∀ {M M′ : Monoid} {DM : D-Monoid M} → D-Morphism M DM → Σ (Morphism M M′) (λ UMor → Initial M)
    --C      = ? 
    --M-Prod = ? 
    --u      = ?
{-
C (proj₁ (ex7 x@(record { MorC = MorC ; Mor-Prod = Mor-Prod ; MorU = MorU }))) y = let tmp = (x .MorC) y in ?
M-Prod (proj₁ (ex7 x)) = ?
u (proj₁ (ex7 x)) = ?
proj₂ (ex7 x) = ?
-}
```

Moving on to leave that for another time...

---

The dependent models and morphisms we have introduced allow us to specify 
Syntax and induction. 
Induction has the special cases of iteration and recuresion.
Because the syntax has induction, for any model $M$ there is a morphism from
$I$ to $M$
> Special cases of induction are iteration and recursion.
> The syntax has iteration, which means that for any model $M$, there is a 
> morphism from $I$ to $M$ 

(Where $I$ is the syntax)



Admissible operations and equtions are defined as those which can be defined or
proven for the syntax via induction.
For the syntax of monoids, we prove that $∀ x : C_I \mid x=u_I$, where $I$ is our syntax. 
We do this by defin`


TODO: 7, 11, and in between.
Do 11 using the eliminator we can define.
elim : (P : ℕ → Set)
       (ze : P zero)
       (su : ∀ n → P n → P (suc n))
       → ∀ n → P n




Initial models only have the necassary components

For pointed set with endofunction we don't need to define it for a syntax or 
initial model - We can just create a set of rules much like what we do in $9$

```agda

```


