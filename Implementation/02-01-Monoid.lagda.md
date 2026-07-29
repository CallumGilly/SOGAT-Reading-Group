<!--
```agda
open import Relation.Binary.PropositionalEquality

open import Shorthands

module 02-01-Monoid where
```
-->

# 2.1 Monoid
Following [section 2.1](../sogat-paris.pdf#subsection.2.1):
- [Monoid](#monoid)
  - [Exercise 2](#exercise-02)
- [Homomorphism](#homomorphism)
  - [Exercise-03](#Exercise-03)
- [Dependent-Monoid](#Dependent-Monoid)
  - [Exercise-04](#Exercise-04)
  - [Exercise-05](#Exercise-05)
- [Dependent-Morphism](#Dependent-Morphism)

## Monoid
```agda
  module _ (C : Set) where
    variable
      x y z : C

    record M : Set where
      field
        _∙_ : ∀ (x y : C) → C
        ass : x ∙ ( y ∙ z) ≡  ( x ∙ y) ∙ z
        u : C
        idl :  u ∙ x ≡ x
        idr :  x ∙ u ≡ x

  open M
```
  
### Exercise-02
```agda
  module Exercise-02 where
    record Unit' : Set where
      constructor unit
     
    uM : M Unit'
    uM ._∙_ x y = unit
    uM .ass = refl
    uM .u = unit
    uM .idl = refl
    uM .idr = refl
```

## Homomorphism
Given our definitions of Monoid `M`, we can define the set of morphisms between 
monoids, which require the function from one carrier to another, and evidence 
of equvilance(?) between the products and unit instances.
```agda
  record M-Hom {X Y : Set} (m : M X) (n : M Y) : Set where
    open M m renaming (_∙_ to _∙ˣ_)
    open M n renaming (_∙_ to _∙ʸ_)
    field
      C : X → Y
      prod-eq : C (x ∙ˣ y) ≡ (C x) ∙ʸ (C y)
      u-eq : C (m .u) ≡ n .u
```
### Exercise-03
```agda
  module Exercise-03 where
    --TODO
```

## Dependent-Monoid
```agda
  module _ (X : Set) (F : X → Set) where
    variable
      fx : F x
      fy : F y
      fz : F z

    record M-Dep (m : M X) : Set₁ where
      open M m renaming (_∙_ to _∙ˣ_; u to uˣ)
      field
        _∙_  : F x → F y → F (x ∙ˣ y)
        ass  : ∀ {eqt} 
            → subst F eqt (fx ∙ (fy ∙ fz)) ≡ (fx ∙ fy) ∙ fz
        u    : F uˣ
        idl  : ∀ {eqt} → subst F eqt (u  ∙ fx) ≡ fx
        idr  : ∀ {eqt} → subst F eqt (fx ∙ u) ≡ fx
```
### Exercise-04
```agda
  module Exercise-04 where
    --TODO
```
### Exercise-05
```agda
  module Exercise-05 where 
    --TODO
```


### Dependent-Morphism
```agda
  record M-Sec
           {X : Set} {m : M X} {F : X → Set} 
           (d : M-Dep X F m) : Set where
    field
       C : (x : X) → (F x)
            --prod-eq : {x y : M .Monoid.C } → C (M .prod x y) ≡ DM .prod (C x) (C y)
            --u-eq : C (M .u) ≡  DM .u
```
