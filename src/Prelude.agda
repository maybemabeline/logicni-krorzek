module Prelude where

_∘_ : {A B : Set} {C : B → Set}
    → ((y : B) → C y) → (f : A → B) → (x : A) → (C (f x))
(f ∘ g) x = f (g x)

infixr 21 _∘_

data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a
