{-# OPTIONS --without-K #-}

open import Data.List as L
open import Data.Nat
open import Data.Product
open import Data.Product.Properties
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

infixr 6 _⊡_
_⊡_ = trans

-- definition 1 (Monoid)
record Monoid : Set₁ where
    field
        C : Set
        prod : ∀ (x y : C) → C
        ass : ∀ {x y z} →
            prod x (prod y z) ≡ prod (prod x y) z
        u : C
        idl : ∀ {x} → prod u x ≡ x
        idr : ∀ {x} → prod x u ≡ x

open Monoid

-- Example: Unit monoid

data Unit' : Set where
    unit : Unit'

uM : Monoid
uM .C = Unit'
uM .prod x y = unit
uM .ass {unit} {unit} {unit} = refl
uM .u = unit
uM .idl {unit} = refl
uM .idr {unit} = refl

-- Morphism
record M-Morphism (M N : Monoid) : Set₁ where
    field
        C : (M .C) → N .C
        prod-eq : ∀ {x y}
            →  C (M .prod x y) ≡ N .prod (C x) (C y)
        u-eq : C (M .u) ≡ N .u
open M-Morphism

-- Dependent model
record D-Monoid (M : Monoid) : Set₁ where
    field
        F : M .C → Set
        prod : ∀ {m1 m2} → (x : F m1) → (y : F m2) → F (M .prod m1 m2)
        ass  : ∀ {m1 m2 m3} {x : F m1} {y : F m2} {z : F m3}
             → subst F (M .ass) (prod x (prod y z)) ≡ prod (prod x y) z
        u    : F (M .u)
        idl  : ∀ {m} {x : F m} → subst F (M .idl) (prod u x) ≡ x
        idr  : ∀ {m} {x : F m} → subst F (M .idr) (prod x u) ≡ x
open D-Monoid

subst-id : ∀ {A B : Set} {a a' : A} {x : B} {tt : a ≡ a'}
         → subst (λ _ → B) tt x ≡ x
subst-id {tt = refl} = refl

subst' : ∀ {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
subst' P refl px = px

-- Exercise 4
exercise4 : {M' : Monoid} (M : Monoid) → D-Monoid M'
exercise4 M .F _ = M .C
exercise4 M .prod = M .prod
exercise4 M .u = M .u
exercise4 M .idl {m} {x} rewrite (M .idl {x}) = subst-id
exercise4 M .idr {m} {x} rewrite (M .idr {x}) = subst-id
exercise4 M .ass {x = x} {y = y} {z = z}
    rewrite (M .ass {x = x} {y = y} {z = z})= subst-id

-- Exercise 5
exercise5 : ∀ {M} → D-Monoid M → Monoid
exercise5 {M'} DM .C = ∃ λ x → DM .F x
exercise5 {M'} DM .prod (xm , xd) (ym , yd) = M' .prod xm ym , DM .prod xd yd
exercise5 {M'} DM .u = M' .u , DM .u
exercise5 {M'} DM .idl = Σ-≡,≡→≡ (M' .idl , DM .idl)
exercise5 {M'} DM .idr = Σ-≡,≡→≡ (M' .idr , DM .idr)
exercise5 {M'} DM .ass = Σ-≡,≡→≡ (M' .ass , DM .ass)

-- Dependent Morphism
record DM-Morphism {M : Monoid} (DM : D-Monoid M) : Set₁ where
    field
        C : (x : M .C) → (DM .F x)
        prod-eq : {x y : M .Monoid.C } → C (M .prod x y) ≡ DM .prod (C x) (C y)
        u-eq : C (M .u) ≡  DM .u
open DM-Morphism

M-Syntax : (M : Monoid) → Set₁
M-Syntax M = ∀ (DM : D-Monoid M) → DM-Morphism DM

-- Exercise 6
exercise6 : ∃ λ M → M-Syntax M
exercise6 .proj₁ = uM
exercise6 .proj₂ DM .C unit = DM .u
exercise6 .proj₂ DM .prod-eq {unit} {unit} = sym (DM .idl)
exercise6 .proj₂ DM .u-eq = refl

M-Initial : (M : Monoid) → Set₁
M-Initial M = (M' : Monoid) →
                M-Morphism M M' × (∀ (Mo Mo' : M-Morphism M M') x → (Mo .C x) ≡ Mo' .C x)

-- Exercise 7
exercise7-1 : (M : Monoid) → M-Syntax M → M-Initial M
exercise7-1 M DM→DMo M' .proj₁ = G where
    DM : D-Monoid M
    DM = exercise4 M'

    DMo : DM-Morphism DM
    DMo = DM→DMo DM

    G : M-Morphism M M'
    G .C = DMo .C
    G .prod-eq = DMo .prod-eq
    G .u-eq = DMo .u-eq
exercise7-1 M DM→DMo M' .proj₂ Mo Mo' x = {!   !}


{-
-- Exercise 4
exercise4 : (M : Monoid) → D-Monoid M
exercise4 M = DM where
    DM : D-Monoid M
    DM .F = λ _ → M .C
    DM .prod = M .prod
    DM .ass {x = x} {y = y} {z = z}
        rewrite (M .ass {x = x} {y = y} {z = z})= subst-id
    DM .u = M .u
    DM .idl {m} {x} rewrite (M .idl {x}) = subst-id
    DM .idr {m} {x} rewrite (M .idr {x}) = subst-id

exercise4' : {M' : Monoid} (M : Monoid) → D-Monoid M'
exercise4' M .F _ = M .C
exercise4' M .prod = M .prod
exercise4' M .u = M .u
exercise4' M .idl {m} {x} rewrite (M .idl {x}) = {!   !}
exercise4' M .idr = {!   !}
exercise4' M .ass = {!   !}

-- Exercise 5
exercise5 : ∀ {M} → D-Monoid M → Monoid
exercise5 {M'} DM .C = ∃ λ x → DM .F x
exercise5 {M'} DM .prod (xm , xd) (ym , yd) = M' .prod xm ym , DM .prod xd yd
exercise5 {M'} DM .u = M' .u , DM .u
exercise5 {M'} DM .idl = Σ-≡,≡→≡ (M' .idl , DM .idl)
exercise5 {M'} DM .idr = Σ-≡,≡→≡ (M' .idr , DM .idr)
exercise5 {M'} DM .ass = Σ-≡,≡→≡ (M' .ass , DM .ass)

-- Dependent Morphism
record DM-Morphism {M : Monoid} (DM : D-Monoid M) : Set₁ where
    field
        C : (x : M .C) → (DM .F x)
        prod : (x y : M .Monoid.C ) → C (M .prod x y) ≡ DM .prod (C x) (C y)
        u : C (M .u) ≡  DM .u
open DM-Morphism

M-Syntax : (M : Monoid) → Set₁
M-Syntax M = ∀ (DM : D-Monoid M) → DM-Morphism DM

-- Exercise 6
exercise6 : ∃ λ M → M-Syntax M
exercise6 .proj₁ = uM
exercise6 .proj₂ DM .C unit = DM .u
exercise6 .proj₂ DM .prod unit unit = sym (DM .idl)
exercise6 .proj₂ DM .u = refl

M-Initial : (M : Monoid) → Set₁
M-Initial M = (M' : Monoid) →
                M-Morphism M M' × ((Mo Mo' : M-Morphism M M') → Mo ≡ Mo')

-- Exercise 7
exercise7-1 : (M : Monoid) → M-Syntax M → M-Initial M
exercise7-1 M DM→DMo M' .proj₁ = G where
    DM : D-Monoid M
    DM = exercise4 M

    DMo : {!   !}
    DMo = DM→DMo {!   !}

    G : M-Morphism M M'
    G .C = {!   !}
    G .prod-eq = {!   !}
    G .u-eq = {!   !}

exercise7-1 M DM→DMo M' .proj₂ = {!   !}
-}