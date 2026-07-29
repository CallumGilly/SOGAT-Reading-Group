```agda
{-# OPTIONS --with-K #-}
module 01-Monoid-WithK where
open import 01-Monoid using (Monoid)
open Monoid
```

## Using Heterogeneous Equality
I have attempted here to use Heterogeneous Equality
in my file here, but as this requires K I have now moved to attempting without. 

Heterogeneous equality is defined like so, this allows us to create equality 
relations between an element `x : A` and an element `y : B`. To then prove this 
equality we first need to prove `A ≡ B`, and then we can prove that `x ≡ y`.

```agda

private module _ where
  open import Level
  variable
    a b : Level

  -- For reference - this is how Heterogeneous equality is defined
  data HetEq {A : Set a} (x : A) : {B : Set b} → B → Set a where
     refl : HetEq {_} {A} x {_} {A} x

open import Relation.Binary.HeterogeneousEquality.Core
```
Using this we can then define our dependent monoid.
```agda
record D-Monoid (M : Monoid) : Set₁ where
  field 
    C : M .C → Set
    DM-Prod : ∀ {x y : M .Monoid.C} → C x → C y → C ((M .M-Prod) x y)
    ass : ∀ {x y z : M .Monoid.C} 
        → ∀ {xm : C x}{ym : C y}{zm : C z} 
        → _≅_ 
            {_} {C (M .M-Prod x (M .M-Prod y z))} 
            (DM-Prod xm (DM-Prod ym zm)) 
            {_} {C (M .M-Prod (M .M-Prod x y) z)} 
            (DM-Prod (DM-Prod xm ym) zm)
    u  : {x : M .Monoid.C} → C x
    idl : ∀ {x y : M .Monoid.C} {xm : C x} → DM-Prod {y} {x} u xm ≅ xm
    idr : ∀ {x y : M .Monoid.C} {xm : C x} → DM-Prod {x} {y} xm u ≅ xm
```


I then attempt Exercise 4:

> Any model can be turned into a dependent model where we ignore the dependency

```agda
ignored : ∀ {M : Monoid} → D-Monoid M
open D-Monoid 
ignored {M} = DM
  where
    DM : D-Monoid M
    C DM       = λ _ → M .C
    DM-Prod DM = M .M-Prod 
    ass DM     = ≡-to-≅ (M .ass)
    u   DM     = M .u
    idl DM     = ≡-to-≅ (M .idl)
    idr DM     = ≡-to-≅ (M .idr)
```
