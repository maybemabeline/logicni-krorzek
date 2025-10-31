module Homotopy where

open import Prelude

module _ {A : Set} {B : A → Set} where

  _∼_ : ((x : A) → B x) → ((x : A) → B x) → Set
  f ∼ g = (x : A) → f x ≡ g x

  refl-htpy : {f : (x : A) → B x} → f ∼ f
  refl-htpy = {!!}

  inv-htpy : {f g : (x : A) → B x} → f ∼ g → g ∼ f
  inv-htpy = {!!}

  concat-htpy : {f g h : (x : A) → B x} → f ∼ g → g ∼ h → f ∼ h
  concat-htpy = {!!}

  _∙h_ = concat-htpy
  infixr 21 _∙h_

module _ {A : Set} {B : A → Set} where

  assoc-htpy : {f g h i : (x : A) → B x} (H : f ∼ g) (K : g ∼ h) (L : h ∼ i)
             → (H ∙h K) ∙h L ∼ H ∙h (K ∙h L)
  assoc-htpy = {!!}


  left-unit-htpy : {f g : (x : A) → B x} (H : f ∼ g)
                 → refl-htpy ∙h H ∼ H
  left-unit-htpy = {!!}

  right-unit-htpy : {f g : (x : A) → B x} (H : f ∼ g)
                 → H ∙h refl-htpy ∼ H
  right-unit-htpy = {!!}


  left-inv-htpy : {f g : (x : A) → B x} (H : f ∼ g)
                → (inv-htpy H) ∙h H ∼ refl-htpy
  left-inv-htpy = {!!}

  right-inv-htpy : {f g : (x : A) → B x} (H : f ∼ g)
                 → H ∙h (inv-htpy H) ∼ refl-htpy
  right-inv-htpy = {!!}


left-whisker : {A B C : Set} {f g : A → B}
               (h : B → C) (H : f ∼ g)
             → h ∘ f ∼ h ∘ g
left-whisker = {!!}             

right-whisker : {A B : Set} {C : B → Set} {g h : (y : B) → C y}
                (H : g ∼ h) (f : A → B)
              → g ∘ f ∼ h ∘ f
right-whisker = {!!}


_∙l_ = left-whisker
infixr 21 _∙l_

_∙r_ = right-whisker
infixr 21 _∙r_

  
