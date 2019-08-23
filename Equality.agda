module plfa.Equality where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

sym : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} (f : A → B) → {x y : A}
  → x ≡ y
    ---------
  → f x ≡ f y
cong f refl = refl

subst : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y
    ---------
  → P x → P y
subst P refl px = px

----------------------------------------------------------------------

module ≡-Reasoning {A : Set } where

  infix  1 begin_
  infixr 2 _≡<>_ _≡<_>_
  infix  3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
      -----
    → x ≡ y
  begin_ x≡y = x≡y

  _≡<>_ : ∀ (x : A) {y : A}
    → x ≡ y
      -----
    → x ≡ y
  x ≡<> x≡y = x≡y

  _≡<_>_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
      -----
    → x ≡ z
  x ≡< x≡y > y≡z = trans x≡y y≡z

  _∎ : ∀ (x : A)
       ---------
     → x ≡ x
  _∎ x = refl


open ≡-Reasoning

trans′ : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans′ {A} {x} {y} {z} x≡y y≡z =
  begin
    x
  ≡< x≡y >
    y
  ≡< y≡z >
    z
  ∎

open import Data.Nat using (ℕ; _≤_; z≤n; s≤s)
open import Data.Nat using (zero; suc; _+_)

-- data ℕ : Set where
--   zero : ℕ
--   suc  : ℕ → ℕ
-- 
-- _+_ : ℕ → ℕ → ℕ
-- zero    + n  =  n
-- (suc m) + n  =  suc (m + n)

postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡< +-identity m >
    m
  ≡<>           -- could be 
    zero + m    -- left out
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡< +-suc m n >
    suc (m + n)
  ≡< cong suc (+-comm m n) >
    suc (n + m)
  ≡<>
    suc n + m
  ∎

----------------------------------------------------------------------

module ≤-Reasoning where

  postulate -- Relations.agda
    ≤-refl : {n : ℕ} → n ≤ n
    ≤-trans : {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p

  infix  1 beg_
  infixr 2 _≤<>_ _≤<_>_ _≤≡<_>_
  infix  3 _end

  beg_ : ∀ {m n : ℕ}
    → m ≤ n
      -----
    → m ≤ n
  beg_ x≤y = x≤y

  _≤<>_ : ∀ (m : ℕ) {n : ℕ} → m ≤ n → m ≤ n
  m ≤<> m≤n = m≤n

  _≤<_>_ : ∀ (m : ℕ) {n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
  m ≤< m≤n > n≤p = ≤-trans m≤n n≤p

  _≤≡<_>_ : ∀ (m : ℕ) {n p : ℕ} → m ≡ n → n ≤ p → m ≤ p
  _≤≡<_>_ m {n} {p} m≡n n≤p = subst (_≤ p) (sym m≡n) n≤p 

  _end : ∀ (n : ℕ) → n ≤ n
  _end n = ≤-refl


open ≤-Reasoning

+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = -- p≤q
  beg
    zero + p
  ≤≡< refl >
    p
  ≤< p≤q >
    q
  ≤≡< refl >
    zero + q
  end
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)
  -- unclear how to do this using the reasoning rules

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n =
  beg
    m + p
  ≤≡< +-comm m p >
    p + m
  ≤< +-monoʳ-≤ p m n m≤n > 
    p + n
  ≤≡< +-comm p n >
    n + p
  end

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q =
  beg
    m + p
  ≤< +-monoˡ-≤ m n p m≤n >
    n + p
  ≤< +-monoʳ-≤ n p q p≤q >
    n + q
  end

----------------------------------------------------------------------

-- cannot be re-bound {-# BUILTIN EQUALITY _≡_ #-}

_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y

refl-≐ : ∀ {A : Set} {x : A} → x ≐ x
refl-≐ P Px = Px

trans-≐ : ∀ {A : Set} {x y z : A}
  → x ≐ y
  → y ≐ z
    -----
  → x ≐ z
trans-≐ x≐y y≐z P Px = y≐z P (x≐y P Px)

sym-≐ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → y ≐ x
sym-≐ {A} {x} {y} x≐y P = Qy where
  Q : A → Set
  Q z = P z → P x
  Qx : Q x
  Qx = refl-≐ P
  Qy : Q y
  Qy = x≐y Q Qx

≡-implies-≐ : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → x ≐ y
≡-implies-≐ x≡y P Px = subst P x≡y Px

≐-implies-≡ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → x ≡ y
≐-implies-≡ {A} {x} {y} x≐y = Qy where
  Q : A → Set
  Q z = x ≡ z
  Qx : Q x
  Qx = refl
  Qy = x≐y Q Qx


