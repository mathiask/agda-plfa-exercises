module plfa.Lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
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

++-identitlyˡ : ∀ {A : Set} → (xs : List A) → [] ++ xs ≡ xs
++-identitlyˡ _ = refl

++-identitlyʳ : ∀ {A : Set} → (xs : List A) → xs ++ [] ≡ xs
++-identitlyʳ [] = refl
++-identitlyʳ (x ∷ xs) =
  begin
    x ∷ xs ++ []
  ≡⟨⟩
    x ∷ (xs ++ [])
  ≡⟨ cong (x ∷_) (++-identitlyʳ xs) ⟩
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
  ≡⟨ sym (++-identitlyʳ (reverse ys)) ⟩
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

--
