open import Data.String as S
open import Data.List as L
open import Data.Nat

record P₁ : Set₁ where
  Tm : Set
  Tm = String


data Tok : Set where
 `lpar `rpar `true `false `if `then `else `isZero `+ : Tok
 `num : ℕ → Tok

record P₂ : Set₁ where
  Tm : Set
  Tm = List Tok

-- comp₂₁ : (p : P₂) → P₁

record P₃ : Set₁ where
  field
    Tm     : Set
    true   : Tm
    false  : Tm
    ite    : Tm → Tm → Tm → Tm
    num    : ℕ → Tm
    isZero : Tm → Tm
    _`+_   : Tm → Tm → Tm

module Ex₃ (p : P₃) where
  module A = P₃ p

  prog : A.Tm
  prog = A.num 2 A.`+ A.num 2

record P₄ : Set₁ where
  field
    Ty     : Set
    Tm     : Ty → Set
    Bool : Ty
    Nat : Ty
    true   : Tm Bool
    false  : Tm Bool
    ite    : ∀ {A : Ty} → Tm Bool → Tm A → Tm A → Tm A
    num    : ℕ → Tm Nat
    isZero : Tm Nat → Tm Bool
    _`+_   : Tm Nat → Tm Nat → Tm Nat


-- model M -- initial, ∀ N model, ∃! M ⇒ N

data Ty : Set where
  nat bool : Ty

data Tm : Ty → Set where
  true : Tm bool
  ite : ∀ {A : Ty} → Tm bool → Tm A → Tm A → Tm A
  num : ℕ → Tm nat
  isZero : Tm nat → Tm bool
  _`+_ : Tm nat → Tm nat → Tm nat

tm₄ : P₄
P₄.Ty tm₄ = Ty
P₄.Tm tm₄ = Tm
P₄.Bool tm₄ = bool
P₄.Nat tm₄ = nat
P₄.true tm₄ = true
P₄.false tm₄ = true
P₄.ite tm₄ = ite
P₄.num tm₄ = num
P₄.isZero tm₄ = isZero
P₄._`+_ tm₄ = _`+_

-- But then how can we encode the properties for P₅ in this?



