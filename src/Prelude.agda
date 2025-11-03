module Prelude where

_∘_ : {A B : Set} {C : B → Set}
    → ((y : B) → C y) → (f : A → B) → (x : A) → (C (f x))
(f ∘ g) x = f (g x)

infixr 21 _∘_

data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a

module _ {A : Set} where

  symm : {x y : A} → x ≡ y → y ≡ x
  symm refl = refl

  concat : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  concat p refl = p

  _∙_ = concat
  infixr 21 _∙_

  assoc-concat : {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
               → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
  assoc-concat p q refl = refl


  left-unit-concat : {x y : A} (p : x ≡ y) → refl ∙ p ≡ p
  left-unit-concat refl = refl

  right-unit-concat : {x y : A} (p : x ≡ y) → p ∙ refl ≡ p
  right-unit-concat p = refl


  left-inv-concat : {x y : A} (p : x ≡ y) → (symm p) ∙ p ≡ refl
  left-inv-concat refl = refl

  right-inv-concat : {x y : A} (p : x ≡ y) → p ∙ (symm p) ≡ refl
  right-inv-concat refl = refl

ap : {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
ap f refl = refl
