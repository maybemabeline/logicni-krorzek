data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
n + zero = n
n + (succ m) = succ (n + m)

infixr 21 _+_

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

curry : {A B C : Set} → ((A × B) → C) → (A → B → C)
curry f a b = f (a , b)

data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

ap : {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
ap f refl = refl

_∙_ : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
p ∙ refl = p

infix 21 _∙_

tr : {A : Set} {x y : A} {B : A → Set} → x ≡ y → B x → B y
tr refl b = b

zero-unit-right : (n : ℕ) → n + zero ≡ n
zero-unit-right n = refl

zero-unit-left : (n : ℕ) → zero + n ≡ n
zero-unit-left zero = refl
zero-unit-left (succ n) = ap succ (zero-unit-left n)

concat-assoc : {A : Set} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
             → p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r
concat-assoc p q refl = refl

ap-concat : {A B : Set} {x y z : A} (f : A → B) (p : x ≡ y) (q : y ≡ z)
          → ap f (p ∙ q) ≡ (ap f p) ∙ (ap f q)
ap-concat f p refl = refl
