module plfa.Lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ;
    *-distribʳ-+; +-suc; +-*-suc; *-comm)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import plfa.Isomorphism using (_≃_; _⇔_)

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

{-# BUILTIN LIST List #-}

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

infixr 5 _++_
_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys       = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

reverse : ∀ {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = (reverse xs) ++ [ x ]

++-identityˡ : ∀ {A : Set} → (xs : List A) → [] ++ xs ≡ xs
++-identityˡ _ = refl

++-identityʳ : ∀ {A : Set} → (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) =
  begin
    x ∷ xs ++ []
  ≡⟨⟩
    x ∷ (xs ++ [])
  ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
    x ∷ xs
  ∎

++-assoc : ∀ {A : Set} → (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs =
  begin
    ((x ∷ xs) ++ ys) ++ zs
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ ys ++ zs)
  ≡⟨⟩
    (x ∷ xs) ++ ys ++ zs
  ∎

----------------------------------------------------------------------

reverse-[] : {A : Set} → reverse {A} [] ≡ []
reverse-[] = refl

reverse-++-commute : ∀ {A : Set} → {xs ys : List A}
  → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-commute {A} {[]} {ys} =
  begin
    reverse ([] ++ ys)
  ≡⟨⟩
    (reverse ys)
  ≡⟨ sym (++-identityʳ (reverse ys)) ⟩
    reverse ys ++ reverse []
  ∎
reverse-++-commute {A} {x ∷ xs} {ys} =
  begin
    reverse (xs ++ ys) ++ [ x ]
  ≡⟨ cong (_++ [ x ]) (reverse-++-commute {A} {xs} {ys}) ⟩
    (reverse ys ++ reverse xs) ++ [ x ]
  ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
     reverse ys ++ reverse xs ++ [ x ]
  ∎

reverse-involutive : ∀ {A : Set} → {xs : List A} → reverse (reverse xs) ≡ xs
reverse-involutive {A} {[]} = refl
reverse-involutive {A} {x ∷ xs} =
  begin
    reverse (reverse xs ++ [ x ])
  ≡⟨ reverse-++-commute {A} {reverse xs} {[ x ]} ⟩
    reverse [ x ] ++ reverse (reverse xs)
  ≡⟨ cong ((reverse [ x ] ) ++_) (reverse-involutive {A} {xs}) ⟩
    reverse [ x ] ++ xs
  ≡⟨⟩
    [ x ] ++ xs
  ≡⟨⟩
    x ∷ xs
  ∎

----------------------------------------------------------------------

map : ∀ {A B : Set} → (A → B) → List A → List B
map f []        =  []
map f (x ∷ xs)  =  f x ∷ map f xs

open import plfa.Isomorphism using (extensionality)

map-compose′ : ∀ {A B C : Set} (f : A → B) (g : B → C) (xs : List A)
  → map (g ∘ f) xs ≡ map g ((map f) xs)
map-compose′ _ _ [] = refl
map-compose′ f g (x ∷ xs) =
  begin
    (g ∘ f) x ∷ map (g ∘ f) xs
  ≡⟨ cong (g (f x) ∷_) (map-compose′ f g xs) ⟩
    (g ∘ f) x ∷ map g ((map f) xs)
  ≡⟨⟩
    map g (f x ∷ (map f) xs)
  ≡⟨⟩
    map g (map f (x ∷ xs))
  ∎

map-compose : ∀ {A B C : Set} {f : A → B} {g : B → C}
  → map (g ∘ f) ≡ map g ∘ map f
map-compose {A} {B} {C} {f} {g} = extensionality (map-compose′ {A} {B} {C} f g)

map-++-commute : ∀ {A B : Set} {f : A → B} {xs ys : List A}
   →  map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-commute {A} {B} {f} {[]} = refl
map-++-commute {A} {B} {f} {x ∷ xs} {ys} =
  begin
    f x ∷ map f (xs ++ ys)
  ≡⟨ cong (f x ∷_) (map-++-commute {A} {B} {f} {xs} {ys}) ⟩
    f x ∷ map f xs ++ map f ys
  ∎

----------------------------------------------------------------------

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-Tree : ∀ {A B C D : Set}
    → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf x) = leaf (f x)
map-Tree f g (node tₗ x tᵣ) = node (map-Tree f g tₗ) (g x) (map-Tree f g tᵣ)

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e []        =  e
foldr _⊗_ e (x ∷ xs)  =  x ⊗ foldr _⊗_ e xs

product : List ℕ → ℕ
product = foldr _*_ 1

foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A) →
  foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ _⊗_ e [] ys = refl
foldr-++ _⊗_ e (x ∷ xs) ys =
  begin
    (x ⊗ foldr _⊗_ e (xs ++ ys))
  ≡⟨ cong (x ⊗_) (foldr-++ _⊗_ e xs ys)  ⟩
    (x ⊗ foldr _⊗_ (foldr _⊗_ e ys) xs)
  ∎

map-is-foldr : ∀ {A B : Set} {f : A → B} →
  map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr {A} {B} {f} = extensionality h where
  h : ∀ (xs : List A) → (map f) xs ≡ foldr (λ x xs → f x ∷ xs) [] xs
  h [] = refl
  h (x ∷ xs) =
    begin
      map f (x ∷ xs)
    ≡⟨⟩
      (f x) ∷ map f xs
    ≡⟨ cong (f x ∷_) (h xs) ⟩
      (f x) ∷ foldr (λ x xs → f x ∷ xs) [] xs
    ≡⟨⟩
      foldr (λ x' → (f x') ∷_ ) [] (x ∷ xs)
    ∎

fold-Tree : ∀ {A B C : Set}
  → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree f g (leaf x) = f x
fold-Tree f g (node tₗ x tᵣ) = g (fold-Tree f g tₗ) x (fold-Tree f g tᵣ)

map-is-fold-Tree : ∀ {A B C D : Set} (f : A → C) (g : B → D) (t : Tree A B) →
  map-Tree f g t ≡ fold-Tree (leaf ∘ f) (λ tₗ x tᵣ → node tₗ (g x) tᵣ) t
map-is-fold-Tree f g (leaf x) = refl
map-is-fold-Tree f g (node tₗ x tᵣ) =
  begin
    node (map-Tree f g tₗ) (g x) (map-Tree f g tᵣ)
  ≡⟨ cong (\xx → node xx (g x) (map-Tree f g tᵣ)) (map-is-fold-Tree f g tₗ) ⟩
    node
      (fold-Tree (leaf ∘ f) (λ tₗ′ x₁ tᵣ′ → node tₗ′ (g x₁) tᵣ′) tₗ)
      (g x)
      (map-Tree f g tᵣ)
  ≡⟨ cong
       (λ xx →
          node (fold-Tree (leaf ∘ f) (λ tₗ′ x₁ tᵣ′ → node tₗ′ (g x₁) tᵣ′) tₗ)
          (g x) xx)
       ((map-is-fold-Tree f g tᵣ)) ⟩
    node
      (fold-Tree (leaf ∘ f) (λ tₗ′ x₁ tᵣ′ → node tₗ′ (g x₁) tᵣ′) tₗ)
      (g x)
      (fold-Tree (leaf ∘ f) (λ tₗ′ x₁ tᵣ′ → node tₗ′ (g x₁) tᵣ′) tᵣ)
  ∎

downFrom : ℕ → List ℕ
downFrom zero     =  []
downFrom (suc n)  =  n ∷ downFrom n

sum : List ℕ → ℕ
sum = foldr _+_ 0

sum-downFrom : ∀ (n : ℕ) → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-downFrom zero = refl
sum-downFrom (suc n) =
  begin
    sum (n ∷ downFrom n) * 2
  ≡⟨⟩
    (n + sum (downFrom n)) * 2
  ≡⟨ *-distribʳ-+ 2 n (sum (downFrom n)) ⟩
    (n * 2 + (sum (downFrom n)) * 2)
  ≡⟨ cong (λ x → n * 2 + x) (sum-downFrom n) ⟩
    n * 2 + (n * (n ∸ 1))
  ≡⟨ h n ⟩
    n + n * n
  ≡⟨⟩
    (suc n) * (suc n ∸ 1)
  ∎ where -- looking a tad too complicated...
    k : ∀ (n : ℕ) → n * 2 ≡ n + n
    k n rewrite *-comm n 2 = cong (n +_) (+-identityʳ n)
    h : ∀ (n : ℕ) → n * 2 + (n * (n ∸ 1)) ≡ n + n * n
    h zero = refl
    h (suc n) =
      begin
        (suc n) * 2 + ((suc n) * ((suc n) ∸ 1))
      ≡⟨⟩
        suc (suc (n * 2 + (n + n * n)))
      ≡⟨ cong (λ x → suc (suc (x + (n + n * n)))) (k n) ⟩
        suc (suc (n + n + (n + n * n)))
      ≡˘⟨ cong (λ x → suc (suc (n + n + x))) (+-*-suc n n) ⟩
        suc (suc (n + n + (n * suc n)))
      ≡⟨ cong (suc ∘ suc) (+-assoc n n (n * suc n)) ⟩
        suc (suc (n + (n + (n * suc n))))
      ≡˘⟨ cong suc (+-suc n (n + n * suc n)) ⟩
        suc (n + suc (n + n * suc n))
      ≡⟨⟩
        (suc n) + (suc n) * (suc n)
      ∎

----------------------------------------------------------------------

record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid

+-monoid : IsMonoid _+_ 0
+-monoid =
  record
    { assoc = +-assoc
    ; identityˡ = +-identityˡ
    ; identityʳ = +-identityʳ
    }

*-monoid : IsMonoid _*_ 1
*-monoid =
  record
    { assoc = *-assoc
    ; identityˡ = *-identityˡ
    ; identityʳ = *-identityʳ
    }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid =
  record
    { assoc = ++-assoc
    ; identityˡ = ++-identityˡ
    ; identityʳ = ++-identityʳ
    }

foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y = sym (identityˡ ⊗-monoid y)
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
    foldr _⊗_ y (x ∷ xs)
  ≡⟨⟩
    x ⊗ (foldr _⊗_ y xs)
  ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y) ⟩
    x ⊗ ((foldr _⊗_ e xs) ⊗ y)
  ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
    (x ⊗ (foldr _⊗_ e xs)) ⊗ y
  ≡⟨⟩
    (foldr _⊗_ e (x ∷ xs) ⊗ y)
  ∎

foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
foldr-monoid-++ _⊗_ e monoid-⊗ xs ys =
  begin
    foldr _⊗_ e (xs ++ ys)
  ≡⟨ foldr-++ _⊗_ e xs ys ⟩
    foldr _⊗_ (foldr _⊗_ e ys) xs
  ≡⟨ foldr-monoid _⊗_ e monoid-⊗ xs (foldr _⊗_ e ys) ⟩
    foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
  ∎

foldl : ∀ {A B : Set} → (A → B → A) → A → List B → A
foldl _⊗_ e [] = e
foldl _⊗_ e (x ∷ xs) = foldl _⊗_ (e ⊗ x) xs

foldl-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldl _⊗_ y xs ≡ y ⊗ foldl _⊗_ e xs
foldl-monoid _⊗_ e monoid-⊗ [] y = sym (identityʳ monoid-⊗ y)
foldl-monoid _⊗_ e monoid-⊗ (x ∷ xs) y =
  begin
    foldl _⊗_ y (x ∷ xs)
  ≡⟨⟩
    foldl _⊗_ (y ⊗ x) xs
  ≡⟨ foldl-monoid _⊗_ e monoid-⊗ xs (y ⊗ x) ⟩
    (y ⊗ x) ⊗ foldl _⊗_ e xs
  ≡⟨ assoc monoid-⊗ y x (foldl _⊗_ e xs) ⟩
    y ⊗ (x ⊗ foldl _⊗_ e xs)
  ≡⟨ sym (cong (y ⊗_) (foldl-monoid _⊗_ e monoid-⊗ xs x)) ⟩
    y ⊗ foldl _⊗_ x xs
  ≡⟨ sym (cong (λ xx → y ⊗ foldl _⊗_ xx xs) (identityˡ monoid-⊗ x)) ⟩
    y ⊗ foldl _⊗_ (e ⊗ x) xs
  ≡⟨⟩
    y ⊗ foldl _⊗_ e (x ∷ xs)
  ∎

foldr≡foldl-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) → foldl _⊗_ e xs ≡ foldr _⊗_ e xs
foldr≡foldl-monoid _⊗_ e monoid-⊗ [] = refl
foldr≡foldl-monoid _⊗_ e monoid-⊗ (x ∷ xs) =
  begin
    foldl _⊗_ e (x ∷ xs)
  ≡⟨⟩
    foldl _⊗_ (e ⊗ x) xs
  ≡⟨ cong (λ xx → foldl _⊗_ xx xs) (identityˡ monoid-⊗ x) ⟩
    foldl _⊗_ x xs
  ≡⟨ foldl-monoid _⊗_ e monoid-⊗ xs x ⟩
    (x ⊗ foldl _⊗_ e xs)
  ≡⟨ cong (x ⊗_) (foldr≡foldl-monoid _⊗_ e monoid-⊗ xs) ⟩
    (x ⊗ foldr _⊗_ e xs)
  ≡⟨⟩
    foldr _⊗_ e (x ∷ xs)
  ∎



--
