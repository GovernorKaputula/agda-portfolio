{-# OPTIONS --safe --without-K #-}

module Portfolio where

-- Small self-contained foundations: no standard library dependency.
data Nat : Set where
  zero : Nat
  suc : Nat → Nat

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

-- Constructive logic.
record _×_ (A B : Set) : Set where
  constructor pair
  field
    first : A
    second : B

swap : {A B : Set} → A × B → B × A
swap (pair a b) = pair b a

compose : {A B C : Set} → (B → C) → (A → B) → A → C
compose g f a = g (f a)

-- Arithmetic: recursion and induction.
_+_ : Nat → Nat → Nat
zero + n = n
suc m + n = suc (m + n)

plus-zero-right : (n : Nat) → (n + zero) ≡ n
plus-zero-right zero = refl
plus-zero-right (suc n) = cong suc (plus-zero-right n)

plus-associative : (a b c : Nat) → ((a + b) + c) ≡ (a + (b + c))
plus-associative zero b c = refl
plus-associative (suc a) b c = cong suc (plus-associative a b c)

-- Verified functional program: map preserves list length.
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

length : {A : Set} → List A → Nat
length [] = zero
length (x ∷ xs) = suc (length xs)

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

map-length : {A B : Set} (f : A → B) (xs : List A) → length (map f xs) ≡ length xs
map-length f [] = refl
map-length f (x ∷ xs) = cong suc (map-length f xs)

map-identity : {A : Set} (xs : List A) → map (λ x → x) xs ≡ xs
map-identity [] = refl
map-identity (x ∷ xs) = cong (λ ys → x ∷ ys) (map-identity xs)

-- Dependent types: a vector's length is carried in its type.
data Vec (A : Set) : Nat → Set where
  vnil : Vec A zero
  vcons : {n : Nat} → A → Vec A n → Vec A (suc n)

head : {A : Set} {n : Nat} → Vec A (suc n) → A
head (vcons x xs) = x

mapVec : {A B : Set} {n : Nat} → (A → B) → Vec A n → Vec B n
mapVec f vnil = vnil
mapVec f (vcons x xs) = vcons (f x) (mapVec f xs)
