module Prelude where

_∘_ : {A B : Set} {C : B → Set}
    → ((y : B) → C y) → (f : A → B) → (x : A) → (C (f x))
(f ∘ g) x = f (g x)

infixr 21 _∘_

data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a

module _ {A : Set} where

  symm : {x y : A} → x ≡ y → y ≡ x
  symm = {!!}

  concat : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  concat = {!!}

  _∙_ = concat
  infixr 21 _∙_

  concat-assoc : {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
               → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
  concat-assoc = {!!}


  left-unit-concat : {x y : A} (p : x ≡ y) → refl ∙ p ≡ p
  left-unit-concat = {!!}

  right-unit-concat : {x y : A} (p : x ≡ y) → p ∙ refl ≡ p
  right-unit-concat = {!!}


  left-inv-concat : {x y : A} (p : x ≡ y) → (symm p) ∙ p ≡ refl
  left-inv-concat = {!!}

  right-inv-concat : {x y : A} (p : x ≡ y) → p ∙ (symm p) ≡ refl
  right-inv-concat = {!!}
