Here we describe a particularly simple pointed set with endfunction
<!--
```agda
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Function

module _ where
```
--!>

We first use a record to define our PSE.

```agda
record PSE : Set₁ where
  field
    N : Set
    z : N
    s : N → N
open PSE
```

We can then define a dependent model over PSE in which induction can be defined

```agda
record D-PSE (pse : PSE) : Set₁ where 
  field
    Predicate : N pse → Set
    Base      : Predicate (z pse)
    Inductive : ∀ {n : N pse} → Predicate n → Predicate (s pse n)
open D-PSE
```

Trying here to understand Jairo Method - at this point he defines a dependent 
morphism, i presume such that he can define syntax

Dependent Morphism allows us to use 

Here we define a dependent morphism, defining the morphism from any PSE, 
into a given Dependent model over the PSE as well as the properties that 
- The base case of the Depended Model is equivalent to the application of the 
  morphism on the z element of PSE
- The inductive case of the Depended Model is equivalent to the application of the 
  morphism on the `s` of any element n in the PSE (Shitty wording) 
```agda
record DPSE-Morphism {pse : PSE} (d-pse : D-PSE pse) : Set₁ where
  field
    Morph : (n : N pse) → (Predicate d-pse n)
    z-is-base : Morph (z pse) ≡ Base d-pse
    s-is-indu : ∀ {n : PSE.N pse} → Morph (s pse n) ≡ Inductive d-pse (Morph n)
open DPSE-Morphism
```

With the three (algebras over Pointed Sets with Endofunctions) we can define the set of PSE's which define a syntax, that 
is, the set of PSE's where we can define a dependent morphism into any 
dependent model
```agda
PSE-Syntax : (pse : PSE) → Set₁
PSE-Syntax pse = Σ (D-PSE pse) DPSE-Morphism
```

# Exercise 11

```agda
module Ex11 (pse : PSE) where
  open PSE pse
  open D-PSE
```

  We can first define addition as a model dependent on any implementation 
  of the PSE.
```agda
  plus : (D-PSE pse) 
  Predicate plus = λ x → (N pse → N pse)
  Base plus = λ n → n
  Inductive plus f n = s pse $ f n
```

We can then define properties of 

```agda
  assoc : PSE-Syntax pse → D-PSE pse
  Predicate (assoc syn) = λ m → (λ n → ?)
  Base (assoc syn) = ?
  Inductive (assoc syn) = ?
```
    --(∀ (n m k : N pse) → plus (plus n m) k ≡ plus n (plus m k))


{-
module Ex11 where
  plus : ∀ (pse : PSE) → Σ (N pse → N pse → N pse) (λ _+_ → 
              (∀ (n m k : N pse) → (n + m) + k ≡ n + (m + k))
            × (∀ (n : N pse) → n + z pse ≡ n)
            × (∀ (n : N pse) → z pse + n ≡ n)
            × (∀ (n m : N pse) → n + m ≡ m + n)
          )
  proj₁ (plus pse) x y = ?
  proj₂ (plus pse) = ?
-}
```
