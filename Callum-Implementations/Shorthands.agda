open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Agda.Primitive

module _ where

infixr 6 _⊡_
_⊡_ = trans

∃₃ : ∀ {a b c d : Level} 
   → ∀ {A : Set a} 
   → ∀ {B : A → Set b} 
   → ∀ {C : (x : A) → B x → Set c}
   → ((x : A) → (y : B x) → C x y → Set d) 
   → Set (a ⊔ b ⊔ c ⊔ d)
∃₃ f = ∃ λ a → ∃ λ b → ∃ λ c → f a b c

