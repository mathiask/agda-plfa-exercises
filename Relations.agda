module plfa.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; *-comm; +-suc; +-identityʳ)


-- fancy layout + implicit arguments + optional ∀

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
        ---------
      → zero ≤ n

  s≤s : {m n : ℕ}
      → m ≤ n
        -------------
      → suc m ≤ suc n


infix 4 _≤_

inv-s≤s : ∀ {m n : ℕ}
        → suc m ≤ suc n
          -------------
        → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {n : ℕ}
        → n ≤ zero
          -------------
        → n ≡ zero
inv-z≤n z≤n = refl

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-antisymm : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisymm z≤n z≤n = refl
≤-antisymm (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisymm m≤n n≤m)

-- parametrized data type (i.e. (m n : ℕ) before the ":") rather than
-- an indexed type means that all constructors MUST produce Total m n

data Total (m n : ℕ) : Set where

  forward :
      m ≤ n
      ---------
    → Total m n

  flipped :
      n ≤ m
      ---------
    → Total m n

-- "with" is a shorthand for defining and using an
-- (anonymous) helper function with "where"

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n 
...                     | forward m≤n = forward (s≤s m≤n)
...                     | flipped n≤m = flipped (s≤s n≤m)


-- Addition --

+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)


-- Multiplication --

*-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n * p ≤ n * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q = ≤-trans (+-monoˡ-≤ p q (n * p) p≤q) (+-monoʳ-≤ q (n * p) (n * q) (*-monoʳ-≤ n p q p≤q))

*-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m * p ≤ n * p
*-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n m≤n

*-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)


-- Strict Inequality --

infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
        -----------
      → zero < suc n
  
  s<s : ∀ {m n : ℕ}
      → m < n
        -------------
      → suc m < suc n


<-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

_>_ : ℕ → ℕ → Set
m > n = n < m

data Trichotomy (m n : ℕ) : Set where

  forward′ :
      m < n
      --------------
    → Trichotomy m n

  equal′ :
      m ≡ n
      --------------
    → Trichotomy m n

  flipped′ :
      m > n
      --------------
    → Trichotomy m n


<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
<-trichotomy zero zero = equal′ refl
<-trichotomy zero (suc n) = forward′ z<s
<-trichotomy (suc m) zero = flipped′ z<s
<-trichotomy (suc m) (suc n) with <-trichotomy m n
...                          | forward′ m<n = forward′ (s<s m<n)
...                          | equal′ refl = equal′ refl
...                          | flipped′ m>n = flipped′ (s<s m>n)

+-monoʳ-< : ∀ (n p q : ℕ)
  → p < q
    -------------
  → n + p < n + q
+-monoʳ-< zero p q p<q = p<q
+-monoʳ-< (suc n) p q p<q = s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : ∀ (m n p : ℕ)
  → m < n
    -------------
  → m + p < n + p
+-monoˡ-< m n p m<n rewrite +-comm m p | +-comm n p = +-monoʳ-< p m n m<n

+-mono-< : ∀ (m n p q : ℕ)
  → m < n
  → p < q
    -------------
  → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)

≤-impl-< : ∀ (m n : ℕ) → suc m ≤ n → m < n
≤-impl-< zero .(suc _) (s≤s m≤n) = z<s
≤-impl-< (suc m) (suc n) (s≤s m≤n) = s<s (≤-impl-< m n m≤n)

<-impl-≤ : ∀ (m n : ℕ) → m < n → suc m ≤ n
<-impl-≤ zero (suc n) z<s = s≤s z≤n
<-impl-≤ (suc m) (suc n) (s<s m<n) = s≤s (<-impl-≤ m n m<n)


-- Parity --

data even : ℕ →  Set
data odd : ℕ →  Set

data even where

  zero :
      ---------
      even zero

  suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where

  suc : ∀ {n : ℕ}
    → even n
      ------------
    → odd (suc n)


e+e=e : ∀ {m n : ℕ} → even m → even n → even (m + n)
o+e=o : ∀ {m n : ℕ} → odd m → even n → odd (m + n)

e+e=e zero en = en
e+e=e (suc om) en = suc (o+e=o om en)

o+e=o (suc em) en = suc (e+e=e em en)

o+o=e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
o+o=e {m} {suc n} om (suc en) rewrite +-suc m n = suc (o+e=o om en)


-- More Bin --

data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

data One : Bin → Set where
  leading1 : One (x1 nil)
  binExt0 : ∀ {x : Bin} → One x → One (x0 x)
  binExt1 : ∀ {x : Bin} → One x → One (x1 x)

data Can : Bin → Set where
  can0 : Can (x0 nil)
  can : ∀ {x : Bin} → One x → Can x

inc : Bin → Bin
inc nil = x1 nil
inc (x0 bs) = x1 bs
inc (x1 bs) = x0 inc bs

oneInc : ∀ {x : Bin} → One x → One (inc x)
oneInc leading1 = binExt0 leading1
oneInc (binExt0 ox) = binExt1 ox
oneInc (binExt1 ox) = binExt0 (oneInc ox)

canInc : ∀ {x : Bin} → Can x → Can (inc x)
canInc can0 = can leading1
canInc (can ox) = can (oneInc ox)

to : ℕ → Bin
to zero = x0 nil
to (suc m) = inc (to m)

canTo : ∀ (n : ℕ) → Can (to n)
canTo zero = can0
canTo (suc n) = canInc (canTo n)

from : Bin → ℕ
from nil = zero
from (x0 bs) = 2 * from bs
from (x1 bs) = 1 + 2 * from bs

-- Induction.agda: binInc : ∀ (x : Bin) → from (inc x) ≡ suc(from x)
-- the converse for to is by definition
--
-- Induction.agda: fromToI : ∀ (n : ℕ) → from(to n) ≡ n

data X0Doubles : ℕ → Set where
  x0doublesZero : X0Doubles zero
  x0doubles : ∀ {n : ℕ} → to(n + n) ≡ x0 (to n) → X0Doubles n

x0≡n+n : ∀ (n : ℕ) → X0Doubles n
x0≡n+n zero = x0doublesZero
x0≡n+n (suc n) = x0doubles p where
  p : inc (to (n + suc n)) ≡ (x0 inc (to n))
  p rewrite +-suc n n with x0≡n+n n 
  ...                 | x0doublesZero = refl
  ...                 | x0doubles q rewrite q = refl


-- ==================== WIP ====================

-- x0forFromOne : ∀ (x : Bin) → One x → to((from x) + (from x)) ≡ x0 (to (from x))
-- x0forFromOne x ox = h1 x (from x) refl (x0≡n+n (from x)) ox where
--   h1 : (x : Bin) → (n : ℕ) → from x ≡ n → X0Doubles n → One x → to (from x + from x) ≡ (x0 to (from x))
--   h1 .(x0 _) .0 xn x0doublesZero (binExt0 ox) = {!!}
--   h1 .(x1 nil) n xn (x0doubles x) leading1 = refl
--   h1 .(x0 _) n xn (x0doubles x) (binExt0 ox) = {!!}
--   h1 .(x1 _) n xn (x0doubles x) (binExt1 ox) = {!!}


-- oneToFromI : ∀ (x : Bin) → One x → to(from x) ≡ x
-- oneToFromI (x0 x) (binExt0 ox) rewrite +-identityʳ (from x) = {!!}
-- oneToFromI (x1 .nil) leading1 = {!!}
-- oneToFromI (x1 x) (binExt1 ox) = {!!}

n+n≡2n : ∀ (n : ℕ) → n + n ≡ 2 * n
n+n≡2n zero = refl
n+n≡2n (suc n) rewrite +-identityʳ n = refl

x0≡*2 : ∀ (x : Bin) → from(x0 x) ≡ 2 * from x
x0≡*2 x = refl

x0inc : ∀ (x : Bin) → x0 (inc x) ≡ inc (inc (x0 x))
x0inc _ = refl
