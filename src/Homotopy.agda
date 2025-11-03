module Homotopy where

open import Prelude

module _ {A : Set} {B : A → Set} where

  _∼_ : ((x : A) → B x) → ((x : A) → B x) → Set
  f ∼ g = (x : A) → f x ≡ g x

  refl-htpy : {f : (x : A) → B x} → f ∼ f
  refl-htpy x = refl

  inv-htpy : {f g : (x : A) → B x} → f ∼ g → g ∼ f
  inv-htpy H x = symm (H x)

  concat-htpy : {f g h : (x : A) → B x} → f ∼ g → g ∼ h → f ∼ h
  concat-htpy H K x = concat (H x) (K x)

  _∙h_ = concat-htpy
  infixr 21 _∙h_

module _ {A : Set} {B : A → Set} where

  assoc-htpy : {f g h i : (x : A) → B x} (H : f ∼ g) (K : g ∼ h) (L : h ∼ i)
             → (H ∙h K) ∙h L ∼ H ∙h (K ∙h L)
  assoc-htpy H K L x = assoc-concat (H x) (K x) (L x)


  left-unit-htpy : {f g : (x : A) → B x} (H : f ∼ g)
                 → refl-htpy ∙h H ∼ H
  left-unit-htpy H x = left-unit-concat (H x)

  right-unit-htpy : {f g : (x : A) → B x} (H : f ∼ g)
                 → H ∙h refl-htpy ∼ H
  right-unit-htpy H x = refl


  left-inv-htpy : {f g : (x : A) → B x} (H : f ∼ g)
                → (inv-htpy H) ∙h H ∼ refl-htpy
  left-inv-htpy H x = left-inv-concat (H x)

  right-inv-htpy : {f g : (x : A) → B x} (H : f ∼ g)
                 → H ∙h (inv-htpy H) ∼ refl-htpy
  right-inv-htpy H x = right-inv-concat (H x)


left-whisker : {A B C : Set} {f g : A → B}
               (h : B → C) (H : f ∼ g)
             → h ∘ f ∼ h ∘ g
left-whisker h H x = ap h (H x)             

right-whisker : {A B : Set} {C : B → Set} {g h : (y : B) → C y}
                (H : g ∼ h) (f : A → B)
              → g ∘ f ∼ h ∘ f
right-whisker H f x = H (f x)


_∙l_ = left-whisker
infixr 21 _∙l_

_∙r_ = right-whisker
infixr 21 _∙r_

  
