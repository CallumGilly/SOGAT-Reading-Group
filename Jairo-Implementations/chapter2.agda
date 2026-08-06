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
open import Data.Maybe.Base
open import Function using (_$_ ; _∘_)

infixr 6 _⊡_
_⊡_ = trans

-- Uniqueness of equality proofs
UIP' = ∀ {a} {A : Set a} → UIP A

-- Some useful lemmas about substitution
module _ where
    private variable
        A B : Set
        a a1 a2 : A
        b : B
        P : A → Set

    subst-id :{eq : a1 ≡ a2} → subst (λ _ → B) eq b ≡ b
    subst-id {eq = refl} = refl

    subst-ref : ∀ {x : P a} {eq : a ≡ a} → subst P eq x ≡ x
    subst-ref {eq = refl} = refl

    subst-com : {x : P a1} {y : P a2} {eq1 : a1 ≡ a2} {eq2 : a2 ≡ a1}
        → subst P eq1 x ≡ y → x ≡ subst P eq2 y
    subst-com {eq1 = refl} {eq2 = refl} refl = refl

module Chapter2-1 where

    -- Definition : Monoid
    -- We define it inside a parametrized module for readability
    -- C is the carrier of the monoid
    module _ (C : Set) where
        variable x y z : C
        record Monoid : Set where
            field
                _∙_ : (x y : C) → C
                u : C
                idl : u ∙ x ≡ x
                idr : x ∙ u ≡ x
                ass : x ∙ (y ∙ z) ≡  (x ∙ y) ∙ z
            infixr 6 _∙_
    open Monoid

    -- Carried and monoid wrapper
    record M : Set₁ where
        field
            C : Set
            ↑ : Monoid C
    open M

    -- Exercise 2.3: The unary monoid
    -- TODO: finish exercise 2
    ⊤-m : M
    ⊤-m .C = ⊤
    ⊤-m .↑ ._∙_ _ _ = tt
    ⊤-m .↑ .u = tt
    ⊤-m .↑ .idl = refl
    ⊤-m .↑ .idr = refl
    ⊤-m .↑ .ass = refl

    -- Definition : Monoid Morphism
    record M-Hom (m n : M) : Set where
        open Monoid (↑ m) renaming (_∙_ to _∙ᵐ_ ; u to uᵐ)
        open Monoid (↑ n) renaming (_∙_ to _∙ⁿ_ ; u to uⁿ)
        field
            C : m .C → n .C
            u-eq : C uᵐ ≡ uⁿ
            ∙-eq : C (x ∙ᵐ y) ≡ C x ∙ⁿ C y
    open M-Hom

    -- Some useful Morphims
    module _ {m : M} where
        m-id : M-Hom m m
        m-id .C x = x
        m-id .u-eq = refl
        m-id .∙-eq = refl

        m-u : M-Hom m m
        m-u .C x = ↑ m .u
        m-u .u-eq = refl
        m-u .∙-eq = sym (↑ m .idl)

    -- TODO : Exercise 3

    -- Definition : Dependent Monoid
    module _ (m : M) (C : m .C → Set) where
        variable
            cx : C x
            cy : C y
            cz : C z

        record Monoid-Dep : Set₁ where
            open Monoid (↑ m) renaming (_∙_ to _∙ᵐ_; u to uᵐ)
            field
                u    : C uᵐ
                _∙_  : C x → C y → C (x ∙ᵐ y)
                idl  : ∀ {eq} → subst C eq (u ∙ cx) ≡ cx
                idr  : ∀ {eq} → subst C eq (cx ∙ u) ≡ cx
                ass  : ∀ {eq}
                    → subst C eq (cx ∙ (cy ∙ cz)) ≡ (cx ∙ cy) ∙ cz
    open Monoid-Dep

    record M-Dep (m : M) : Set₁ where
        field
            C : m .C → Set
            ↑ : Monoid-Dep m C
    open M-Dep

    -- Exercise 4
    module _ {n : M} (m : M) where
        open Monoid (↑ m) renaming (_∙_ to _∙ᵐ_)

        m→d : M-Dep n
        m→d .C _ = m .C
        m→d .↑ ._∙_ = _∙ᵐ_
        m→d .↑ .u = ↑ m .u
        m→d .↑ .idl {x} {cx} {eq} rewrite (↑ m .idl {cx}) = subst-id
        m→d .↑ .idr {x} {cx} {eq} rewrite (↑ m .idr {cx}) = subst-id
        m→d .↑ .ass {x} {cx} {y} {cy} {z} {cz} {eq}
            rewrite (↑ m .ass {x = cx} {y = cy} {z = cz}) = subst-id

    -- Exercise 5
    module _ {m : M} (d : M-Dep m) where
        open Monoid (↑ m) renaming (_∙_ to _∙ᵐ_)
        open Monoid-Dep (↑ d) renaming (_∙_ to _∙ᵈ_)

        d→∃m : M
        d→∃m .C = ∃ (λ x → d .C x)
        d→∃m .↑ ._∙_ (x , cx) (y , cy) = (x ∙ᵐ y) , (cx ∙ᵈ cy)
        d→∃m .↑ .u = ↑ m .u , ↑ d .u
        d→∃m .↑ .idl = Σ-≡,≡→≡ (↑ m .idl , ↑ d .idl)
        d→∃m .↑ .idr = Σ-≡,≡→≡ (↑ m .idr , ↑ d .idr)
        d→∃m .↑ .ass = Σ-≡,≡→≡ (↑ m .ass , ↑ d .ass)

    -- Definition : Dependent Morphism
    record M-Sec {m : M} (d : M-Dep m) : Set₁ where
        open Monoid (↑ m) renaming (_∙_ to _∙ᵐ_ ; u to uᵐ)
        open Monoid-Dep (↑ d) renaming (_∙_ to _∙ᵈ_ ; u to uᵈ)
        field
            C : ∀ x → d .C x
            u-eq : C uᵐ ≡  uᵈ
            ∙-eq : C (x ∙ᵐ y) ≡ (C x ∙ᵈ C y)
    open M-Sec

    -- Definition: Syntax
    M-Syn : M → Set₁
    M-Syn m = (d : M-Dep m) → M-Sec d

    -- Exercise 6
    ∃-M-Syn : ∃ λ m → M-Syn m
    ∃-M-Syn .proj₁ = ⊤-m
    ∃-M-Syn .proj₂ d .C tt = ↑ d .u
    ∃-M-Syn .proj₂ d .u-eq = refl
    ∃-M-Syn .proj₂ d .∙-eq {tt} {tt} = sym (↑ d .idl)

    ⊤-m-Syn = proj₂ ∃-M-Syn

    -- Definition: Initial
    M-Ini : M → Set₁
    M-Ini m =
        (n : M) → (M-Hom m n × (∀ (mh nh : M-Hom m n) x → mh .C x ≡ nh .C x))

    -- Exercise 7
    -- TODO: The identity morphism is part of exercise 8.
    -- Is there a way to prove exericise 7 without using it?
    module _ (m : M) where
        private variable
            n : M

        m-syn→nh : (M-Syn m) → M-Hom m n
        m-syn→nh {n} md→s = let s = md→s $ m→d n in record {
                C = s .C
                ; u-eq = s .u-eq
                ; ∙-eq = s .∙-eq}

        m-syn-ini : UIP' → (M-Syn m) → ∀ (mh nh : M-Hom m n) x
            → mh .C x ≡ nh .C x
        m-syn-ini {n} uip md→s mh nh = (md→s d) .C where
            d : M-Dep m
            d .C y = mh .C y ≡ nh .C y
            d .↑ .u = (mh .u-eq) ⊡ sym (nh .u-eq)
            d .↑ ._∙_ cx cy =
                mh .∙-eq ⊡ cong₂ (↑ n ._∙_) cx cy ⊡ sym (nh .∙-eq)
            d .↑ .idl = uip _ _
            d .↑ .idr = uip _ _
            d .↑ .ass = uip _ _

        m-syn→ini : UIP' → (M-Syn m) → (M-Ini m)
        m-syn→ini uip md→s n = m-syn→nh md→s , m-syn-ini uip md→s

        m-ini-u : ∀ {m} → M-Ini m → (x : m .C) → x ≡ ↑ m .u
        m-ini-u {m} m-ini = proj₂ (m-ini m) m-id m-u

        md-idu : ∀ {eq} {d : M-Dep m}
            → ↑ d ._∙_ (↑ d .u) (↑ d .u) ≡ subst (d .C) eq (↑ d .u)
        md-idu {eq} {d} = subst-com {eq1 = ↑ m .idl} (↑ d .idr)

        m-ini→syn :  (M-Ini m) → (M-Syn m)
        m-ini→syn m-ini d = s where
            s : M-Sec d
            s .C x = subst (d .C) (sym (m-ini-u m-ini x)) (↑ d .u)
            s .u-eq = subst-ref
            s .∙-eq {x} {y} with (m-ini-u m-ini x) | (m-ini-u m-ini y)
            ... | refl | refl = sym $ md-idu {d = d}

    -- Exercise 8
    module _ where
        private variable
            m n m1 m2 m3 : M

        m-id' : M-Hom m m
        m-id' = m-id

        _∘ₕ_ : M-Hom m1 m2 → M-Hom m2 m3 → M-Hom m1 m3
        _∘ₕ_ h12 h23 .C = h23 .C ∘ h12 .C
        _∘ₕ_ h12 h23 .u-eq rewrite (h12 .u-eq) = h23 .u-eq
        _∘ₕ_ h12 h23 .∙-eq {x} {y} rewrite (h12 .∙-eq {x} {y})= h23 .∙-eq

        ∘ₕ-id : M-Hom m n → M-Hom n m → Set
        ∘ₕ-id {m} {n} nh mh = ∀ x → (nh ∘ₕ mh) .C x ≡ m-id {m} .C x

        _≅ₕ_ : M-Hom m n → M-Hom n m → Set
        _≅ₕ_ {m} {n} nh mh = (∘ₕ-id nh mh) × (∘ₕ-id mh nh)

        _≅ᵐ_ : (m n : M) → Set
        m ≅ᵐ n = ∃₂ λ (mh : M-Hom m n) nh → mh ≅ₕ nh

        syn-≅ᵐ : UIP' → M-Syn m → M-Syn n → m ≅ᵐ n
        syn-≅ᵐ {m} {n} uip md→s nd→s =
            proj₁ (m-ini n) , proj₁ (n-ini m) , m-∘ₕ-id , n-∘ₕ-id
            where
            m-ini = m-syn→ini m uip md→s

            n-ini = m-syn→ini n uip nd→s

            m-∘ₕ-id : _
            m-∘ₕ-id x = (m-ini-u m m-ini _) ⊡ sym (m-ini-u m m-ini _)

            n-∘ₕ-id : _
            n-∘ₕ-id x = (m-ini-u n n-ini _) ⊡ sym (m-ini-u n n-ini _)

    -- Exercise 9
    module _ (m : M) where
        private variable
            -x -y : m .C

        open Monoid (↑ m) renaming
            (_∙_ to _∙ᵐ_ ; u to uᵐ ; idr to idrᵐ ; idl to idlᵐ ; ass to assᵐ )

        M-Inv : (x -x : m .C) → Set
        M-Inv x -x = (x ∙ᵐ -x) ≡ uᵐ × (-x ∙ᵐ x) ≡ uᵐ

        ∙-inv : M-Inv x -x → M-Inv y -y → M-Inv (x ∙ᵐ y) (-y ∙ᵐ -x)
        ∙-inv {x} { -x} {y} { -y} (lx , rx) (ly , ry) .proj₁
            rewrite
                (assᵐ {x ∙ᵐ y} { -y} { -x}) | sym (assᵐ {x} {y} { -y})
                | ly | idrᵐ {x} = lx
        ∙-inv {x} { -x} {y} { -y} (lx , rx) (ly , ry) .proj₂
            rewrite
            (assᵐ { -y ∙ᵐ -x} {x} {y})
            | sym (assᵐ { -y} { -x} {x})
            | rx | idrᵐ { -y} = ry

        inv-uniq : M-Inv x -x → M-Inv x -y → -x ≡ -y
        inv-uniq {x} { -x} { -y} (lx , rx) (ly , ry) =
            sym (idlᵐ { -x})
            ⊡ cong (_∙ᵐ -x) (sym ry)
            ⊡ sym assᵐ
            ⊡ cong (-y ∙ᵐ_) lx
            ⊡ idrᵐ

        group-md : UIP' → M-Dep m
        group-md uip .C x = ∃ λ -x → M-Inv x -x
        group-md uip .↑ = record {
            u = uᵐ , idlᵐ , idlᵐ
            ; _∙_ = λ (-x , invx) (-y , invy) → (-y ∙ᵐ -x) , ∙-inv invx invy
            ; idl = aux
            ; idr = aux
            ; ass = aux }
            where
                aux : {∃x ∃y : ∃ (M-Inv x)} → ∃x ≡ ∃y
                aux {x} {_ , invx} {_ , invy} =
                    Σ-≡,≡→≡ $ inv-uniq invx invy , Σ-≡,≡→≡ (uip _ _ , uip _ _)

module Chapter2-2 where
    -- Definition: Pointed Set with Endofunction
    record PSE : Set₁ where
        field
            N : Set
            z : N
            s : N → N
    open PSE

    -- Definition: PSE Morphism
    record PSE-Hom (p t : PSE) : Set where
        open PSE p renaming (N to Nᵖ ; z to zᵖ ; s to sᵖ)
        open PSE t renaming (N to Nᵗ ; z to zᵗ ; s to sᵗ)
        field
            N  : Nᵖ → Nᵗ
            z-eq : N zᵖ ≡ zᵗ
            s-eq : N (sᵖ zᵖ) ≡ sᵗ (N zᵖ)

    -- Definition: Dependent PSE
    module _ (p : PSE) where
        open PSE p renaming (N to Nᵖ ; z to zᵖ ; s to sᵖ)
        variable n : Nᵖ
        record PSE-Dep : Set₁ where
            field
                N : (n : Nᵖ) → Set
                z : N zᵖ
                s : N n → N (sᵖ n)
    open PSE-Dep

    -- Definition: Dependent PSE Morphism
    record PSE-Sec {p : PSE} (d : PSE-Dep p) : Set₁ where
        open PSE p renaming (N to Nᵖ ; z to zᵖ ; s to sᵖ)
        open PSE-Dep d renaming (N to Nᵈ ; z to zᵈ ; s to sᵈ)
        field
            N : (n : Nᵖ) → Nᵈ n
            z-eq : N zᵖ ≡ zᵈ
            s-eq : N (sᵖ n) ≡ sᵈ (N n)
    open PSE-Sec

    -- Definition: PSE Syntax
    PSE-Syn : (p : PSE) → Set₁
    PSE-Syn p = (d : PSE-Dep p) → PSE-Sec d

    -- Exercise 11
    -- TODO: Finish Exercise 11
    module _ (p : PSE) where
        open PSE p renaming (N to Nᵖ ; z to zᵖ ; s to sᵖ)

        add-pd : PSE-Dep p
        add-pd .N _ = Nᵖ → Nᵖ
        add-pd .z n = n
        add-pd .s {n} f m = sᵖ (f m)

        module _ (p→d : PSE-Syn p) where
            syn-add : Nᵖ → Nᵖ → Nᵖ
            syn-add = (p→d add-pd) .N

            _+ᵖ_ = syn-add

            syn-add-idr-pd : PSE-Dep p
            syn-add-idr-pd .N n = n +ᵖ zᵖ ≡ n
            syn-add-idr-pd .z rewrite z-eq (p→d add-pd) = refl
            syn-add-idr-pd .s {m} eq
                rewrite ((p→d add-pd) .s-eq {m} {zᵖ} {sᵖ}) | eq = refl

            syn-add-idr : n +ᵖ zᵖ ≡ n
            syn-add-idr {n} = (p→d syn-add-idr-pd) .N n

    -- Exercise 12
    -- TODO : Finish Exercise 12
    module _ (p : PSE) where
        open PSE p renaming (N to Nᵖ ; z to zᵖ ; s to sᵖ)

        bool-pd : PSE-Dep p
        bool-pd .N _ = Bool
        bool-pd .z = false
        bool-pd .s _ = true

        pred-pd : PSE-Dep p
        pred-pd .N _ = Nᵖ
        pred-pd .z = zᵖ
        pred-pd .s {n} _ = n

        module _ (p→d : PSE-Syn p) where
            0≢1-pd : PSE-Dep p
            0≢1-pd .N n = zᵖ ≡ sᵖ n → ⊥
            0≢1-pd .z z≡sz = subst T cont tt where
                d = p→d bool-pd
                cont : true ≡ false
                cont = sym (d .s-eq {zᵖ} {zᵖ} {sᵖ})
                    ⊡ sym (sym (d .z-eq)
                    ⊡ cong (d .N) z≡sz)

            0≢1-pd .s {n} 0≢sn 0≡ssn = 0≢sn z≡sn where
                d = p→d pred-pd
                z≡sn : zᵖ ≡ sᵖ n
                z≡sn = (sym (d .z-eq))
                    ⊡ cong (d .N) 0≡ssn
                    ⊡ d .s-eq {sᵖ n} {zᵖ} {sᵖ}

    -- TODO : Exercise 13

    -- record M-Hom {Cᵐ Cⁿ : Set} (m : M Cᵐ) (n : M Cⁿ) : Set where
    --     open M m renaming (_∙_ to _∙ᵐ_) hiding (C)
    --     open M n renaming (_∙_ to _∙ⁿ_) hiding (C)
    --     field
    --         C : Cᵐ → Cⁿ
    --         _∙_ : C (x ∙ᵐ y) ≡  (C x) ∙ⁿ (C y)
    --         u : C (m .u) ≡ n .u

--     -- definition 1 (Monoid)
--     record Monoid : Set₁ where
--         field
--             C : Set
--             prod : ∀ (x y : C) → C
--             ass : ∀ {x y z} →
--                 prod x (prod y z) ≡ prod (prod x y) z
--             u : C
--             idl : ∀ {x} → prod u x ≡ x
--             idr : ∀ {x} → prod x u ≡ x

--     open Monoid

--     -- Example: Unit monoid

--     data Unit' : Set where
--         unit : Unit'

--     uM : Monoid
--     uM .C = Unit'
--     uM .prod x y = unit
--     uM .ass {unit} {unit} {unit} = refl
--     uM .u = unit
--     uM .idl {unit} = refl
--     uM .idr {unit} = refl

--     -- Morphism
--     record M-Morphism (M N : Monoid) : Set₁ where
--         field
--             C : (M .C) → N .C
--             prod-eq : ∀ {x y}
--                 →  C (M .prod x y) ≡ N .prod (C x) (C y)
--             u-eq : C (M .u) ≡ N .u
--     open M-Morphism

--     -- Dependent model
--     record D-Monoid (M : Monoid) : Set₁ where
--         field
--             F : M .C → Set
--             prod : ∀ {m1 m2} → (x : F m1) → (y : F m2) → F (M .prod m1 m2)
--             ass  : ∀ {m1 m2 m3 eqt} {x : F m1} {y : F m2} {z : F m3}
--                 → subst F eqt (prod x (prod y z)) ≡ prod (prod x y) z
--             u    : F (M .u)
--             idl  : ∀ {m eqt} {x : F m} → subst F eqt (prod u x) ≡ x
--             idr  : ∀ {m eqt} {x : F m} → subst F eqt (prod x u) ≡ x
--     open D-Monoid

--     subst-id : ∀ {A B : Set} {a a' : A} {x : B} {eqt : a ≡ a'}
--             → subst (λ _ → B) eqt x ≡ x
--     subst-id {eqt = refl} = refl

--     subst-ref : ∀ {A : Set} {P : A → Set} {a : A} {x : P a} {eqt : a ≡ a}
--             → subst P eqt x ≡ x
--     subst-ref {A} {P} {a} {x} {refl} = refl

--     subst-com : ∀ {A : Set} {P : A → Set} {a a' : A} {x : P a} {y : P a'}
--                 {eqt : a ≡ a'} {eqt' : a' ≡ a} → subst P eqt x ≡ y → x ≡ subst P eqt' y
--     subst-com {A} {P} {a} {a'} {x} {y} {refl} {refl} refl = refl

--     -- subst-test : ∀ {A : Set} {P : A → Set} {a a' : A} {x : P a} {y : P a'} {eqt : P a ≡ P a'}
--     --          → subst P eqt x ≡ y
--     -- subst-test = ?

--     -- subst' : ∀ {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
--     -- subst' P refl px = px

--     DM-ldi : ∀ {M : Monoid} {DM : D-Monoid M} {m eqt} {x : DM .F m}
--         → DM .prod (DM .u) x ≡ subst (DM .F) eqt x
--     DM-ldi {M} {DM} {m} {eqt} {x} = subst-com {eqt = M .idl} (DM .idl)

--     DM-rdi : ∀ {M : Monoid} {DM : D-Monoid M} {m eqt} {x : DM .F m}
--         → DM .prod x (DM .u) ≡ subst (DM .F) eqt x
--     DM-rdi {M} {DM} {m} {eqt} {x} = subst-com {eqt = M .idr} (DM .idr)

--     DM-rdiu : ∀ {M eqt} {DM : D-Monoid M}
--             → DM .prod (DM .u) (DM .u) ≡ subst (DM .F) eqt (DM .u)
--     DM-rdiu {M} {eqt} {DM} = DM-rdi {M = M} {DM = DM}

--     -- Exercise 4
--     exercise4 : {M' : Monoid} (M : Monoid) → D-Monoid M'
--     exercise4 M .F a = M .C
--     exercise4 M .prod = M .prod
--     exercise4 M .u = M .u
--     exercise4 M .idl {m} {eqt} {x} rewrite (M .idl {x}) = subst-id
--     exercise4 M .idr {m} {eqt} {x} rewrite (M .idr {x}) = subst-id
--     exercise4 M .ass {x = x} {y = y} {z = z}
--         rewrite (M .ass {x = x} {y = y} {z = z})= subst-id

--     M→DM = exercise4

--     -- Exercise 5
--     exercise5-1 : ∀ {M} → D-Monoid M → Monoid
--     exercise5-1 {M'} DM .C = ∃ λ x → DM .F x
--     exercise5-1 {M'} DM .prod (xm , xd) (ym , yd) = M' .prod xm ym , DM .prod xd yd
--     exercise5-1 {M'} DM .u = M' .u , DM .u
--     exercise5-1 {M'} DM .idl = Σ-≡,≡→≡ (M' .idl , DM .idl)
--     exercise5-1 {M'} DM .idr = Σ-≡,≡→≡ (M' .idr , DM .idr)
--     exercise5-1 {M'} DM .ass = Σ-≡,≡→≡ (M' .ass , DM .ass)

--     DM→∃M = exercise5-1

--     exercise5-2 : ∀ {M} → (DM : D-Monoid M) → M-Morphism (exercise5-1 DM) M
--     exercise5-2 {M} DM .C (x , _) = x
--     exercise5-2 {M} DM .prod-eq {x , Fx} {y , Fy} = refl
--     exercise5-2 {M} DM .u-eq = refl

--     -- Dependent Morphism
--     record DM-Morphism {M : Monoid} (DM : D-Monoid M) : Set₁ where
--         field
--             C : (x : M .C) → (DM .F x)
--             prod-eq : {x y : M .Monoid.C } → C (M .prod x y) ≡ DM .prod (C x) (C y)
--             u-eq : C (M .u) ≡  DM .u
--     open DM-Morphism

--     M-Syntax : (M : Monoid) → Set₁
--     M-Syntax M = ∀ (DM : D-Monoid M) → DM-Morphism DM

--     -- Exercise 6
--     exercise6 : ∃ λ M → M-Syntax M
--     exercise6 .proj₁ = uM
--     exercise6 .proj₂ DM .C unit = DM .u
--     exercise6 .proj₂ DM .prod-eq {unit} {unit} = sym (DM .idl)
--     exercise6 .proj₂ DM .u-eq = refl

--     uM-Syntax = proj₂ exercise6

--     M-Initial : (M : Monoid) → Set₁
--     M-Initial M = (M' : Monoid) →
--                     M-Morphism M M' × (∀ (Mo Mo' : M-Morphism M M') x
--                         → (Mo .C x) ≡ Mo' .C x)

--     Mo-id : ∀ {M} → M-Morphism M M
--     Mo-id .C x = x
--     Mo-id .prod-eq = refl
--     Mo-id .u-eq = refl

--     Mo-u : ∀ {M} → M-Morphism M M
--     Mo-u {M} .C _ = M .u
--     Mo-u {M} .prod-eq = sym (M .idl)
--     Mo-u {M} .u-eq = refl

--     I-is-u : ∀ {I} → M-Initial I → (x : I .C) → x ≡ I .u
--     I-is-u {I} I→IoxU = let I→U M' = proj₂ (I→IoxU M') in I→U I Mo-id Mo-u

--     -- Uniqueness of equality proofs
--     UIP' = ∀ {a} {A : Set a} → UIP A

--     -- Exercise 7
--     exercise7-1 : UIP' → (M : Monoid) → M-Syntax M → M-Initial M
--     exercise7-1 _ M DM→DMo M' .proj₁ = G where
--         DM : D-Monoid M
--         DM = exercise4 M'

--         DMo : DM-Morphism DM
--         DMo = DM→DMo DM

--         G : M-Morphism M M'
--         G .C = DMo .C
--         G .prod-eq = DMo .prod-eq
--         G .u-eq = DMo .u-eq
--     exercise7-1 uip M DM→DMo M' .proj₂ Mo Mo' x = G where
--         P : M .C → Set
--         P x = Mo .C x ≡ Mo' .C x

--         DM : D-Monoid M
--         DM .F x = P x
--         DM .prod {m1} {m2} x y =
--             Mo .prod-eq ⊡ cong (λ e → M' .prod e _) x
--             ⊡ cong (λ e →  M' .prod _ e) y ⊡ sym (Mo' .prod-eq)
--         DM .u = Mo .u-eq ⊡ sym (Mo' .u-eq)
--         DM .idl {m} {x} = uip _ _
--         DM .idr = uip _ _
--         DM .ass {m1} {m2} {m3} {x} {y} {z} = uip _ _

--         DMo : DM-Morphism DM
--         DMo = DM→DMo DM

--         G = DMo .C x

--     M-Syntax→Initial = exercise7-1

--     uM-Initial : UIP' → M-Initial uM
--     uM-Initial uip M' = exercise7-1 uip uM (proj₂ exercise6) M'

--     -- No UIP!
--     exercise7-2 : (M : Monoid) → M-Initial M → M-Syntax M
--     exercise7-2 I I→IoxU DI = DMo where
--         M : Monoid
--         M = exercise5-1 DI

--         DMo : DM-Morphism DI
--         DMo .C x = subst (DI .F) (sym (I-is-u I→IoxU x)) (DI .u)
--         DMo .prod-eq {x} {y} with (I-is-u I→IoxU x) | (I-is-u I→IoxU y)
--         ... | refl | refl = sym (DM-rdiu {DM = DI})
--         DMo .u-eq = subst-ref

--     M-Intial→Syntax = exercise7-2

--     exercise8-1 : {M : Monoid} → M-Morphism M M
--     exercise8-1 = Mo-id

--     exercise8-2 : ∀ {M1 M2 M3} (Mo : M-Morphism M1 M2) (Mo : M-Morphism M2 M3)
--         → M-Morphism M1 M3
--     exercise8-2 {M1} {M2} {M3} Mo Mo' .C x = Mo' .C (Mo .C x)
--     exercise8-2 {M1} {M2} {M3} Mo Mo' .prod-eq {x} {y}
--         rewrite (Mo .prod-eq {x} {y}) = Mo' .prod-eq
--     exercise8-2 {M1} {M2} {M3} Mo Mo' .u-eq rewrite (Mo .u-eq) = Mo' .u-eq

--     Mo-comp : ∀ {M1 M2 M3} (Mo : M-Morphism M1 M2) (Mo : M-Morphism M2 M3)
--         → M-Morphism M1 M3
--     Mo-comp = exercise8-2

--     Mo-Iso : {M N : Monoid} (Mo : M-Morphism M N) (Mo' : M-Morphism N M) → Set
--     Mo-Iso {M} {N} Mo Mo' = ∀ x → Mo-comp Mo Mo' .C x ≡  Mo-id {M} .C x

--     M-Iso : (M N : Monoid) → Set₁
--     M-Iso M N = ∃ λ (Mo : M-Morphism M N)
--         → ∃ (λ (Mo' : M-Morphism N M) → Mo-Iso Mo Mo')

--     exercise8-3 : UIP' → ∀ (M N : Monoid) → M-Syntax M → M-Syntax N → M-Iso M N
--     exercise8-3 uip M N DM→DMo DN→DNo = Mo , (Mo' , G) where
--         M→MoxU = M-Syntax→Initial uip M DM→DMo

--         N→NoxU = M-Syntax→Initial uip N DN→DNo

--         Mo : M-Morphism M N
--         Mo = proj₁ (M→MoxU N)

--         Mo' : M-Morphism N M
--         Mo' = proj₁ (N→NoxU M)

--         G : ∀ x → _
--         G x = I-is-u
--             M→MoxU (Mo-comp Mo Mo' .C x) ⊡ sym (I-is-u M→MoxU (Mo-id {M} .C x))

--     M-Inv : ∀ {M : Monoid} (x x^-1 : M .C) → Set
--     M-Inv {M} x x^-1 = M .prod x x^-1 ≡ M .u × M .prod x^-1 x ≡ M .u

--     prod-inv : ∀ {M : Monoid} {x1 x2 x1^-1 x2^-1 : M .C}
--             → M-Inv {M} x1 x1^-1 → M-Inv {M} x2 x2^-1
--             → M-Inv {M} (M .prod x1 x2) (M .prod x2^-1 x1^-1)
--     prod-inv {M} {x1} {x2} {x1^-1} {x2^-1} (l1 , r1) (l2 , r2) .proj₁
--         rewrite M .ass {M .prod x1 x2} {x2^-1} {x1^-1}
--             | sym (M .ass {x1} {x2} {x2^-1}) | l2 | M .idr {x1} = l1
--     prod-inv {M} {x1} {x2} {x1^-1} {x2^-1} (l1 , r1) (l2 , r2) .proj₂
--         rewrite M .ass {M .prod x2^-1 x1^-1} {x1} {x2}
--             | sym (M .ass {x2^-1} {x1^-1} {x1}) | r1 | M .idr {x2^-1} = r2

--     inv-uniq : ∀ {M : Monoid} {x x^-1 y^-1 : M .C}
--             → M-Inv {M} x x^-1 → M-Inv {M} x y^-1 → x^-1 ≡ y^-1
--     inv-uniq {M} {x} {x^-1} {y^-1} (l1 , r1) (l2 , r2) =
--         sym (M .idl {x^-1}) ⊡ cong (λ y → M .prod y x^-1) (sym r2)
--         ⊡ sym (M .ass) ⊡ cong (λ y → M .prod y^-1 y) l1 ⊡ M .idr

--     ∃inv-uniq : UIP' → ∀ {M} {x : M .C} {ex^-1 ey^-1 : ∃ (M-Inv {M} x)}
--         →  ex^-1 ≡ ey^-1
--     ∃inv-uniq uip {M} {x} {_ , invx} {_ , invy} =
--         Σ-≡,≡→≡ (inv-uniq {M} invx invy , Σ-≡,≡→≡ (uip _ _ , uip _ _))

--     DM-group : UIP' → ∀ {M} → D-Monoid M
--     DM-group uip {M} .F x = ∃ (λ x^-1 → M-Inv {M} x x^-1)
--     DM-group uip {M} .prod {x} {y} (x^-1 , invx) (y^-1 , invy) =
--         M .prod y^-1 x^-1 , prod-inv {M = M} invx invy
--     DM-group uip {M} .u .proj₁ = M .u
--     DM-group uip {M} .u .proj₂ = M .idl , M .idl
--     DM-group uip {M} .idl {eqt = eqt} = ∃inv-uniq uip {M}
--     DM-group uip {M} .idr {eqt = eqt} = ∃inv-uniq uip {M}
--     DM-group uip {M} .ass {eqt = eqt} = ∃inv-uniq uip {M}

--     exercise9 : UIP' → ∀ {M} (x) → (M-Syntax M) → (∃ λ x^-1 → M-Inv {M} x x^-1)
--     exercise9 uip x DM→DMo = let DMo-gp = DM→DMo (DM-group uip) in DMo-gp .C x


-- module Chapter2-2 where

--     -- Pointed set with endofunction
--     record PSE : Set₁ where
--         field
--             N : Set
--             z : N
--             s : N → N
--     open PSE

--     record D-PSE (S : PSE) : Set₁ where
--         field
--             P : (S .N) → Set
--             base : P (S .z)
--             ind : ∀ {n} → P n → P (S .s n)
--     open D-PSE

--     record DPSE-Morphism {S : PSE} (DS : D-PSE S) : Set₁ where
--         field
--             N : (n : S .N) → (DS .P n)
--             z-eq : N (S .z) ≡ DS .base
--             s-eq : ∀ {n} → N (S .s n) ≡  DS .ind (N n)
--     open DPSE-Morphism

--     PSE-Syntax : (S : PSE) → Set₁
--     PSE-Syntax S = (DS : D-PSE S) → DPSE-Morphism DS

--     natN : PSE
--     natN .N = ℕ
--     natN .z = zero
--     natN .s = suc

--     natN-syn : PSE-Syntax natN
--     natN-syn DS .N zero = DS .base
--     natN-syn DS .N (suc n) = DS .ind (natN-syn DS .N n)
--     natN-syn DS .z-eq = refl
--     natN-syn DS .s-eq = refl

--     Elim : Set₁
--     Elim = (P : ℕ → Set) → P zero → (∀ {n} → P n → P (suc n)) → (∀ n → P n)

--     elim : Elim
--     elim P base ind zero = base
--     elim P base ind (suc n) = ind (elim P base ind n)

--     e-nadd : ℕ → ℕ → ℕ
--     e-nadd n m = elim (λ _ → ℕ) n (λ m → suc m) m

--     DN-add : ∀ {S} → D-PSE S
--     DN-add {S} .P _ =  S .N → S .N
--     DN-add {S} .base n = n
--     DN-add {S} .ind {n} f m = S .s (f m)

--     s-add : ∀ {S} → (PSE-Syntax S) → S .N → S .N → S .N
--     s-add {S} dm→dmo = (dm→dmo DN-add) .N

--     s-nadd = s-add natN-syn

--     DN-add-idr : ∀ {S} → PSE-Syntax S → D-PSE S
--     DN-add-idr {S} dm→dmo = let s-add' = s-add dm→dmo in record {
--         P = λ x → s-add' x (S .z) ≡ x ;
--         base = cong (λ a → a (S .z)) (z-eq (dm→dmo DN-add)) ;
--         ind = λ {n} p →
--             cong (λ x → x (S .z)) (s-eq (dm→dmo DN-add))
--             ⊡ cong (λ x → S .s x) p}

--     0≢1 : (0 ≡ 1) → ⊥
--     0≢1 0≡1 = subst aux 0≡1 tt where
--         aux : _
--         aux zero = ⊤
--         aux (suc n) = ⊥

--     zesu : ∀ (n : ℕ) → 0 ≡ suc n → ⊥
--     zesu = elim _ 0≢1 λ {n} 0≢1+n 0≡2+n → 0≢1+n (cong pred 0≡2+n)

--     DN-auxb : ∀ {S} → D-PSE S
--     DN-auxb {S} .P _ = Bool
--     DN-auxb {S} .base = false
--     DN-auxb {S} .ind = λ _ → true

--     DN-pred : ∀ {S} → D-PSE S
--     DN-pred {S} .P _ = S .N
--     DN-pred {S} .base = S .z
--     DN-pred {S} .ind {n} _ = n

--     exercise12-1 : ∀ {S} → PSE-Syntax S → D-PSE S
--     exercise12-1 {S} syn .P x = (S .z ≡ S .s x) → ⊥
--     exercise12-1 {S} syn .base z≡sz = subst T aux tt where
--         aux : true ≡ false
--         aux =
--             sym (s-eq (syn _))
--             ⊡ sym (sym (z-eq (syn _))
--             ⊡ (cong ((syn DN-auxb) .N) z≡sz))

--     exercise12-1 {S} syn .ind {n} 0≢sn 0≡ssn = 0≢sn aux where
--         DNo = syn DN-pred
--         aux : _
--         aux =
--             sym (z-eq DNo)
--             ⊡ cong (DNo . N) 0≡ssn
--             ⊡ s-eq DNo

-- module Chapter2-3 where
--     record Razor : Set₂ where
--         infixr 6 _+ᵗ_
--         field
--             Ty : Set₁
--             Tm : (A : Ty) → Set
--             Bl : Ty
--             Nt : Ty
--             trueᵗ : Tm Bl
--             falseᵗ : Tm Bl
--             ite : ∀ {A : Ty} → (b : Tm Bl) → (t : Tm A) → (f : Tm A) → Tm A
--             ↑ : (n : ℕ) → Tm Nt
--             _+ᵗ_ : (u : Tm Nt) → (v : Tm Nt) → Tm Nt
--             isZero : (u : Tm Nt) → Tm Bl
--             iteβ₁ : ∀ {A} {u v : Tm A} → ite trueᵗ u v ≡ u
--             iteβ₂ : ∀ {A} {u v : Tm A} → ite falseᵗ u v ≡ v
--             +β : ∀ {n m} → ↑ n +ᵗ ↑ m ≡ ↑ (n + m)
--             isZeroβ₁ : isZero (↑ 0) ≡ trueᵗ
--             isZeroβ₂ : ∀ {n} → isZero (↑ (suc n)) ≡ falseᵗ


--     module Examples (Ra : Razor) where
--         open Razor Ra

--         notᵗ : Tm Bl → Tm Bl
--         notᵗ b = ite b falseᵗ trueᵗ

--         example1 : notᵗ trueᵗ ≡ falseᵗ
--         example1 = iteβ₁

--         example2 : (↑ 1 +ᵗ ↑ 2) +ᵗ (↑ 3 +ᵗ ↑ 4) ≡  ↑ 10
--         example2 = cong (_+ᵗ (_ +ᵗ _)) +β ⊡ cong (_ +ᵗ_) +β ⊡ +β

--     setRa : Razor
--     setRa .Razor.Ty = Set
--     setRa .Razor.Tm A = A
--     setRa .Razor.Bl = Bool
--     setRa .Razor.Nt = ℕ
--     setRa .Razor.trueᵗ = true
--     setRa .Razor.falseᵗ = false
--     setRa .Razor.ite b t f = if b then t else f
--     setRa .Razor.↑ n = n
--     setRa .Razor._+ᵗ_ = _+_
--     setRa .Razor.isZero u = u ≡ᵇ 0
--     setRa .Razor.iteβ₁ = refl
--     setRa .Razor.iteβ₂ = refl
--     setRa .Razor.+β = refl
--     setRa .Razor.isZeroβ₁ = refl
--     setRa .Razor.isZeroβ₂ = refl

--     trilRa : Razor
--     trilRa .Razor.Ty = Set
--     trilRa .Razor.Tm A = A
--     trilRa .Razor.Bl = Maybe Bool
--     trilRa .Razor.Nt = ℕ
--     trilRa .Razor.trueᵗ = just true
--     trilRa .Razor.falseᵗ = just false
--     trilRa .Razor.ite (just false) t f = f
--     trilRa .Razor.ite (just true) t f = t
--     trilRa .Razor.ite {A} nothing t f = t
--     trilRa .Razor.↑ n = n
--     trilRa .Razor._+ᵗ_ = _+_
--     trilRa .Razor.isZero u = just (u ≡ᵇ 0)
--     trilRa .Razor.iteβ₁ = refl
--     trilRa .Razor.iteβ₂ = refl
--     trilRa .Razor.+β = refl
--     trilRa .Razor.isZeroβ₁ = refl
--     trilRa .Razor.isZeroβ₂ = refl

--     module Exercises (Ra : Razor) where
--         open Razor Ra

--         exercise15 : ∀ {A} {u v : Tm A} → trueᵗ ≡ falseᵗ → u ≡ v
--         exercise15 {A} {u} {v} t=f =
--             sym (iteβ₁ {u = u} {v = v})
--             ⊡ cong (λ x → ite x _ _) t=f
--             ⊡ iteβ₂

--         exercise16 : ∀ {A} {u v : Tm A} → ↑ 0 ≡ ↑ 1 → u ≡ v
--         exercise16 0=1 = exercise15 t=f where
--             t=f : _
--             t=f = sym isZeroβ₁ ⊡ cong isZero 0=1 ⊡ isZeroβ₂

--         -- exercise17 : ∃ λ (x : Razor) → Razor.Tm {!   !} {!   !} ≡ Maybe Bool
--         -- exercise17 = {!   !}


