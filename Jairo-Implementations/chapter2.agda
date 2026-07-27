--{-# OPTIONS --without-K #-}

open import Data.List as L
open import Data.Nat
open import Data.Product
open import Data.Product.Properties
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Axiom.UniquenessOfIdentityProofs using (UIP)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base
open import Data.Bool.Base


infixr 6 _⊡_
_⊡_ = trans

module Chapter2-1 where

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
            ass  : ∀ {m1 m2 m3 eqt} {x : F m1} {y : F m2} {z : F m3}
                → subst F eqt (prod x (prod y z)) ≡ prod (prod x y) z
            u    : F (M .u)
            idl  : ∀ {m eqt} {x : F m} → subst F eqt (prod u x) ≡ x
            idr  : ∀ {m eqt} {x : F m} → subst F eqt (prod x u) ≡ x
    open D-Monoid

    subst-id : ∀ {A B : Set} {a a' : A} {x : B} {eqt : a ≡ a'}
            → subst (λ _ → B) eqt x ≡ x
    subst-id {eqt = refl} = refl

    subst-ref : ∀ {A : Set} {P : A → Set} {a : A} {x : P a} {eqt : a ≡ a}
            → subst P eqt x ≡ x
    subst-ref {A} {P} {a} {x} {refl} = refl

    subst-com : ∀ {A : Set} {P : A → Set} {a a' : A} {x : P a} {y : P a'}
                {eqt : a ≡ a'} {eqt' : a' ≡ a} → subst P eqt x ≡ y → x ≡ subst P eqt' y
    subst-com {A} {P} {a} {a'} {x} {y} {refl} {refl} refl = refl

    -- subst-test : ∀ {A : Set} {P : A → Set} {a a' : A} {x : P a} {y : P a'} {eqt : P a ≡ P a'}
    --          → subst P eqt x ≡ y
    -- subst-test = ?

    -- subst' : ∀ {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
    -- subst' P refl px = px

    DM-ldi : ∀ {M : Monoid} {DM : D-Monoid M} {m eqt} {x : DM .F m}
        → DM .prod (DM .u) x ≡ subst (DM .F) eqt x
    DM-ldi {M} {DM} {m} {eqt} {x} = subst-com {eqt = M .idl} (DM .idl)

    DM-rdi : ∀ {M : Monoid} {DM : D-Monoid M} {m eqt} {x : DM .F m}
        → DM .prod x (DM .u) ≡ subst (DM .F) eqt x
    DM-rdi {M} {DM} {m} {eqt} {x} = subst-com {eqt = M .idr} (DM .idr)

    DM-rdiu : ∀ {M eqt} {DM : D-Monoid M}
            → DM .prod (DM .u) (DM .u) ≡ subst (DM .F) eqt (DM .u)
    DM-rdiu {M} {eqt} {DM} = DM-rdi {M = M} {DM = DM}

    -- Exercise 4
    exercise4 : {M' : Monoid} (M : Monoid) → D-Monoid M'
    exercise4 M .F a = M .C
    exercise4 M .prod = M .prod
    exercise4 M .u = M .u
    exercise4 M .idl {m} {eqt} {x} rewrite (M .idl {x}) = subst-id
    exercise4 M .idr {m} {eqt} {x} rewrite (M .idr {x}) = subst-id
    exercise4 M .ass {x = x} {y = y} {z = z}
        rewrite (M .ass {x = x} {y = y} {z = z})= subst-id

    M→DM = exercise4

    -- Exercise 5
    exercise5-1 : ∀ {M} → D-Monoid M → Monoid
    exercise5-1 {M'} DM .C = ∃ λ x → DM .F x
    exercise5-1 {M'} DM .prod (xm , xd) (ym , yd) = M' .prod xm ym , DM .prod xd yd
    exercise5-1 {M'} DM .u = M' .u , DM .u
    exercise5-1 {M'} DM .idl = Σ-≡,≡→≡ (M' .idl , DM .idl)
    exercise5-1 {M'} DM .idr = Σ-≡,≡→≡ (M' .idr , DM .idr)
    exercise5-1 {M'} DM .ass = Σ-≡,≡→≡ (M' .ass , DM .ass)

    DM→∃M = exercise5-1

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

    uM-Syntax = proj₂ exercise6

    M-Initial : (M : Monoid) → Set₁
    M-Initial M = (M' : Monoid) →
                    M-Morphism M M' × (∀ (Mo Mo' : M-Morphism M M') x
                        → (Mo .C x) ≡ Mo' .C x)

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

    M-Syntax→Initial = exercise7-1

    uM-Initial : UIP' → M-Initial uM
    uM-Initial uip M' = exercise7-1 uip uM (proj₂ exercise6) M'

    -- No UIP!
    exercise7-2 : (M : Monoid) → M-Initial M → M-Syntax M
    exercise7-2 I I→IoxU DI = DMo where
        M : Monoid
        M = exercise5-1 DI

        DMo : DM-Morphism DI
        DMo .C x = subst (DI .F) (sym (I-is-u I→IoxU x)) (DI .u)
        DMo .prod-eq {x} {y} with (I-is-u I→IoxU x) | (I-is-u I→IoxU y)
        ... | refl | refl = sym (DM-rdiu {DM = DI})
        DMo .u-eq = subst-ref

    M-Intial→Syntax = exercise7-2

    exercise8-1 : {M : Monoid} → M-Morphism M M
    exercise8-1 = Mo-id

    exercise8-2 : ∀ {M1 M2 M3} (Mo : M-Morphism M1 M2) (Mo : M-Morphism M2 M3)
        → M-Morphism M1 M3
    exercise8-2 {M1} {M2} {M3} Mo Mo' .C x = Mo' .C (Mo .C x)
    exercise8-2 {M1} {M2} {M3} Mo Mo' .prod-eq {x} {y}
        rewrite (Mo .prod-eq {x} {y}) = Mo' .prod-eq
    exercise8-2 {M1} {M2} {M3} Mo Mo' .u-eq rewrite (Mo .u-eq) = Mo' .u-eq

    Mo-comp : ∀ {M1 M2 M3} (Mo : M-Morphism M1 M2) (Mo : M-Morphism M2 M3)
        → M-Morphism M1 M3
    Mo-comp = exercise8-2

    Mo-Iso : {M N : Monoid} (Mo : M-Morphism M N) (Mo' : M-Morphism N M) → Set
    Mo-Iso {M} {N} Mo Mo' = ∀ x → Mo-comp Mo Mo' .C x ≡  Mo-id {M} .C x

    M-Iso : (M N : Monoid) → Set₁
    M-Iso M N = ∃ λ (Mo : M-Morphism M N)
        → ∃ (λ (Mo' : M-Morphism N M) → Mo-Iso Mo Mo')

    exercise8-3 : UIP' → ∀ (M N : Monoid) → M-Syntax M → M-Syntax N → M-Iso M N
    exercise8-3 uip M N DM→DMo DN→DNo = Mo , (Mo' , G) where
        M→MoxU = M-Syntax→Initial uip M DM→DMo

        N→NoxU = M-Syntax→Initial uip N DN→DNo

        Mo : M-Morphism M N
        Mo = proj₁ (M→MoxU N)

        Mo' : M-Morphism N M
        Mo' = proj₁ (N→NoxU M)

        G : ∀ x → _
        G x = I-is-u
            M→MoxU (Mo-comp Mo Mo' .C x) ⊡ sym (I-is-u M→MoxU (Mo-id {M} .C x))

    M-Inv : ∀ {M : Monoid} (x x^-1 : M .C) → Set
    M-Inv {M} x x^-1 = M .prod x x^-1 ≡ M .u × M .prod x^-1 x ≡ M .u

    prod-inv : ∀ {M : Monoid} {x1 x2 x1^-1 x2^-1 : M .C}
            → M-Inv {M} x1 x1^-1 → M-Inv {M} x2 x2^-1
            → M-Inv {M} (M .prod x1 x2) (M .prod x2^-1 x1^-1)
    prod-inv {M} {x1} {x2} {x1^-1} {x2^-1} (l1 , r1) (l2 , r2) .proj₁
        rewrite M .ass {M .prod x1 x2} {x2^-1} {x1^-1}
            | sym (M .ass {x1} {x2} {x2^-1}) | l2 | M .idr {x1} = l1
    prod-inv {M} {x1} {x2} {x1^-1} {x2^-1} (l1 , r1) (l2 , r2) .proj₂
        rewrite M .ass {M .prod x2^-1 x1^-1} {x1} {x2}
            | sym (M .ass {x2^-1} {x1^-1} {x1}) | r1 | M .idr {x2^-1} = r2

    inv-uniq : ∀ {M : Monoid} {x x^-1 y^-1 : M .C}
            → M-Inv {M} x x^-1 → M-Inv {M} x y^-1 → x^-1 ≡ y^-1
    inv-uniq {M} {x} {x^-1} {y^-1} (l1 , r1) (l2 , r2) =
        sym (M .idl {x^-1}) ⊡ cong (λ y → M .prod y x^-1) (sym r2)
        ⊡ sym (M .ass) ⊡ cong (λ y → M .prod y^-1 y) l1 ⊡ M .idr

    ∃inv-uniq : UIP' → ∀ {M} {x : M .C} {ex^-1 ey^-1 : ∃ (M-Inv {M} x)}
        →  ex^-1 ≡ ey^-1
    ∃inv-uniq uip {M} {x} {_ , invx} {_ , invy} =
        Σ-≡,≡→≡ (inv-uniq {M} invx invy , Σ-≡,≡→≡ (uip _ _ , uip _ _))

    DM-group : UIP' → ∀ {M} → D-Monoid M
    DM-group uip {M} .F x = ∃ (λ x^-1 → M-Inv {M} x x^-1)
    DM-group uip {M} .prod {x} {y} (x^-1 , invx) (y^-1 , invy) =
        M .prod y^-1 x^-1 , prod-inv {M = M} invx invy
    DM-group uip {M} .u .proj₁ = M .u
    DM-group uip {M} .u .proj₂ = M .idl , M .idl
    DM-group uip {M} .idl {eqt = eqt} = ∃inv-uniq uip {M}
    DM-group uip {M} .idr {eqt = eqt} = ∃inv-uniq uip {M}
    DM-group uip {M} .ass {eqt = eqt} = ∃inv-uniq uip {M}

    exercise9 : UIP' → ∀ {M} (x) → (M-Syntax M) → (∃ λ x^-1 → M-Inv {M} x x^-1)
    exercise9 uip x DM→DMo = let DMo-gp = DM→DMo (DM-group uip) in DMo-gp .C x


module Chapter2-2 where

    -- Pointed set with endofunction
    record PSE : Set₁ where
        field
            N : Set
            z : N
            s : N → N
    open PSE

    record D-PSE (S : PSE) : Set₁ where
        field
            P : (S .N) → Set
            base : P (S .z)
            ind : ∀ {n} → P n → P (S .s n)
    open D-PSE

    record DPSE-Morphism {S : PSE} (DS : D-PSE S) : Set₁ where
        field
            N : (n : S .N) → (DS .P n)
            z-eq : N (S .z) ≡ DS .base
            s-eq : ∀ {n} → N (S .s n) ≡  DS .ind (N n)
    open DPSE-Morphism

    PSE-Syntax : (S : PSE) → Set₁
    PSE-Syntax S = (DS : D-PSE S) → DPSE-Morphism DS

    natN : PSE
    natN .N = ℕ
    natN .z = zero
    natN .s = suc

    natN-syn : PSE-Syntax natN
    natN-syn DS .N zero = DS .base
    natN-syn DS .N (suc n) = DS .ind (natN-syn DS .N n)
    natN-syn DS .z-eq = refl
    natN-syn DS .s-eq = refl

    Elim : Set₁
    Elim = (P : ℕ → Set) → P zero → (∀ {n} → P n → P (suc n)) → (∀ n → P n)

    elim : Elim
    elim P base ind zero = base
    elim P base ind (suc n) = ind (elim P base ind n)

    e-nadd : ℕ → ℕ → ℕ
    e-nadd n m = elim (λ _ → ℕ) n (λ m → suc m) m

    DN-add : ∀ {S} → D-PSE S
    DN-add {S} .P _ =  S .N → S .N
    DN-add {S} .base n = n
    DN-add {S} .ind {n} f m = S .s (f m)

    s-add : ∀ {S} → (PSE-Syntax S) → S .N → S .N → S .N
    s-add {S} dm→dmo = (dm→dmo DN-add) .N

    s-nadd = s-add natN-syn

    DN-add-idr : ∀ {S} → PSE-Syntax S → D-PSE S
    DN-add-idr {S} dm→dmo = let s-add' = s-add dm→dmo in record {
        P = λ x → s-add' x (S .z) ≡ x ;
        base = cong (λ a → a (S .z)) (z-eq (dm→dmo DN-add)) ;
        ind = λ {n} p →
            cong (λ x → x (S .z)) (s-eq (dm→dmo DN-add))
            ⊡ cong (λ x → S .s x) p}

    0≢1 : (0 ≡ 1) → ⊥
    0≢1 0≡1 = subst aux 0≡1 tt where
        aux : _
        aux zero = ⊤
        aux (suc n) = ⊥

    zesu : ∀ (n : ℕ) → 0 ≡ suc n → ⊥
    zesu = elim _ 0≢1 λ {n} 0≢1+n 0≡2+n → 0≢1+n (cong pred 0≡2+n)

    DN-auxb : ∀ {S} → D-PSE S
    DN-auxb {S} .P _ = Bool
    DN-auxb {S} .base = false
    DN-auxb {S} .ind = λ _ → true

    DN-pred : ∀ {S} → D-PSE S
    DN-pred {S} .P _ = S .N
    DN-pred {S} .base = S .z
    DN-pred {S} .ind {n} _ = n

    exercise12-1 : ∀ {S} → PSE-Syntax S → D-PSE S
    exercise12-1 {S} syn .P x = (S .z ≡ S .s x) → ⊥
    exercise12-1 {S} syn .base z≡sz = subst T aux tt where
        aux : true ≡ false
        aux =
            sym (s-eq (syn _))
            ⊡ sym (sym (z-eq (syn _))
            ⊡ (cong ((syn DN-auxb) .N) z≡sz))

    exercise12-1 {S} syn .ind {n} 0≢sn 0≡ssn = 0≢sn aux where
        DNo = syn DN-pred
        aux =
            sym (z-eq DNo)
            ⊡ cong (DNo . N) 0≡ssn
            ⊡ s-eq DNo