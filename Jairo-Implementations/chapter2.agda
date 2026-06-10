--{-# OPTIONS --without-K #-}

open import Data.List as L
open import Data.Nat
open import Data.Product
open import Data.Product.Properties
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Axiom.UniquenessOfIdentityProofs using (UIP)

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
        idl  : ∀ {m tt} {x : F m} → subst F tt (prod u x) ≡ x
        idr  : ∀ {m tt} {x : F m} → subst F tt (prod x u) ≡ x
open D-Monoid

subst-id : ∀ {A B : Set} {a a' : A} {x : B} {tt : a ≡ a'}
         → subst (λ _ → B) tt x ≡ x
subst-id {tt = refl} = refl

subst-ref : ∀ {A : Set} {P : A → Set} {a : A} {x : P a} {tt : a ≡ a}
         → subst P tt x ≡ x
subst-ref {A} {P} {a} {x} {refl} = refl

subst-inv : ∀ {A : Set} {P : A → Set} {a a' : A} {x : P a} {y : P a'}
            {tt : a ≡ a'} {tt' : a' ≡ a} → subst P tt x ≡ y → x ≡ subst P tt' y
subst-inv {A} {P} {a} {a'} {x} {y} {refl} {refl} refl = refl

-- subst' : ∀ {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
-- subst' P refl px = px

DM-ldi : ∀ {M : Monoid} {DM : D-Monoid M} {m tt} {x : DM .F m}
    → DM .prod (DM .u) x ≡ subst (DM .F) tt x
DM-ldi {M} {DM} {m} {tt} {x} = subst-inv {tt = M .idl} (DM .idl)

DM-rdi : ∀ {M : Monoid} {DM : D-Monoid M} {m tt} {x : DM .F m}
    → DM .prod x (DM .u) ≡ subst (DM .F) tt x
DM-rdi {M} {DM} {m} {tt} {x} = subst-inv {tt = M .idr} (DM .idr)

DM-uu : ∀ {M tt} {DM : D-Monoid M}
        → DM .prod (DM .u) (DM .u) ≡ subst (DM .F) tt (DM .u)
DM-uu {M} {tt} {DM} = DM-rdi {M = M} {DM = DM}

-- Exercise 4
exercise4 : {M' : Monoid} (M : Monoid) → D-Monoid M'
exercise4 M .F a = M .C
exercise4 M .prod = M .prod
exercise4 M .u = M .u
exercise4 M .idl {m} {tt} {x} rewrite (M .idl {x}) = subst-id
exercise4 M .idr {m} {tt} {x} rewrite (M .idr {x}) = subst-id
exercise4 M .ass {x = x} {y = y} {z = z}
    rewrite (M .ass {x = x} {y = y} {z = z})= subst-id

-- Exercise 5
exercise5-1 : ∀ {M} → D-Monoid M → Monoid
exercise5-1 {M'} DM .C = ∃ λ x → DM .F x
exercise5-1 {M'} DM .prod (xm , xd) (ym , yd) = M' .prod xm ym , DM .prod xd yd
exercise5-1 {M'} DM .u = M' .u , DM .u
exercise5-1 {M'} DM .idl = Σ-≡,≡→≡ (M' .idl , DM .idl)
exercise5-1 {M'} DM .idr = Σ-≡,≡→≡ (M' .idr , DM .idr)
exercise5-1 {M'} DM .ass = Σ-≡,≡→≡ (M' .ass , DM .ass)

exercise5-2 : ∀ {M} → (DM : D-Monoid M) → M-Morphism (exercise5-1 DM) M
exercise5-2 {M} DM .C (x , _) = x
exercise5-2 {M} DM .prod-eq {x , Fx} {y , Fy} = refl
exercise5-2 {M} DM .u-eq = refl

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

uM-Syntax : M-Syntax uM
uM-Syntax = proj₂ exercise6

M-Initial : (M : Monoid) → Set₁
M-Initial M = (M' : Monoid) →
                M-Morphism M M' × (∀ (Mo Mo' : M-Morphism M M') x → (Mo .C x) ≡ Mo' .C x)

Mo-id : ∀ {M} → M-Morphism M M
Mo-id .C x = x
Mo-id .prod-eq = refl
Mo-id .u-eq = refl

Mo-u : ∀ {M} → M-Morphism M M
Mo-u {M} .C _ = M .u
Mo-u {M} .prod-eq = sym (M .idl)
Mo-u {M} .u-eq = refl

I-is-u : ∀ {I} → M-Initial I → (x : I .C) → x ≡ I .u
I-is-u {I} I→IoxU = let I→U M' = proj₂ (I→IoxU M') in I→U I Mo-id Mo-u

I-is-sing : ∀ {I} → M-Initial I → (x y : I .C) → x ≡ y
I-is-sing isI x y = I-is-u isI x ⊡ sym (I-is-u isI y)

-- Uniqueness of equality proofs
UIP' = ∀ {a} {A : Set a} → UIP A

-- Exercise 7
exercise7-1 : UIP' → (M : Monoid) → M-Syntax M → M-Initial M
exercise7-1 _ M DM→DMo M' .proj₁ = G where
    DM : D-Monoid M
    DM = exercise4 M'

    DMo : DM-Morphism DM
    DMo = DM→DMo DM

    G : M-Morphism M M'
    G .C = DMo .C
    G .prod-eq = DMo .prod-eq
    G .u-eq = DMo .u-eq
exercise7-1 uip M DM→DMo M' .proj₂ Mo Mo' x = G where
    P : M .C → Set
    P x = Mo .C x ≡ Mo' .C x

    DM : D-Monoid M
    DM .F x = P x
    DM .prod {m1} {m2} x y =
        Mo .prod-eq ⊡ cong (λ e → M' .prod e _) x
        ⊡ cong (λ e →  M' .prod _ e) y ⊡ sym (Mo' .prod-eq)
    DM .u = Mo .u-eq ⊡ sym (Mo' .u-eq)
    DM .idl {m} {x} = uip _ _
    DM .idr = uip _ _
    DM .ass {m1} {m2} {m3} {x} {y} {z} = uip _ _

    DMo : DM-Morphism DM
    DMo = DM→DMo DM

    G = DMo .C x

uM-Initial : UIP' → M-Initial uM
uM-Initial uip M' = exercise7-1 uip uM (proj₂ exercise6) M'

-- No UIP!
exercise7-2 : (M : Monoid) → M-Initial M → M-Syntax M
exercise7-2 I isIn DI = G where

    M : Monoid
    M = exercise5-1 DI

    DMo : DM-Morphism DI
    DMo .C x = subst (DI .F) (sym (I-is-u isIn x)) (DI .u)
    DMo .prod-eq {x} {y} with (I-is-u isIn x) | (I-is-u isIn y)
    ... | refl | refl = sym (DM-uu {DM = DI})
    DMo .u-eq = subst-ref

    G = DMo
