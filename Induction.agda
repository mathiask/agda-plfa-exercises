module plfa.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p rewrite +-assoc m n p = refl

+-identity : (n : ℕ) → n + zero ≡ n
+-identity zero = refl
+-identity (suc n) rewrite +-identity n = refl

+-suc : (m n : ℕ) → m + suc n ≡ suc(m + n)
+-suc zero n = refl
+-suc (suc m) n rewrite +-suc m n = refl

+-comm : (m n : ℕ) → m + n ≡ n + m
+-comm m zero rewrite +-identity m = refl
+-comm m (suc n) rewrite +-suc m n | +-comm m n = refl

+-swap : (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite sym (+-assoc m n p) | +-comm m n | +-assoc n m p = refl

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p +  n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p rewrite *-distrib-+ m n p | sym (+-assoc p (m * p) (n * p)) = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl

*-zero : (n : ℕ) → n * zero ≡ zero
*-zero zero = refl
*-zero (suc n) rewrite *-zero n = refl

*-suc : (m n : ℕ) → m * suc n ≡ m + m * n
*-suc zero n = refl
*-suc (suc m) n rewrite *-suc m n | +-swap n m (m * n) = refl

*-comm : (m n : ℕ) → m * n ≡ n * m
*-comm m zero rewrite *-zero m = refl
*-comm m (suc n) rewrite *-suc m n | *-comm m n = refl

0-monus : (n : ℕ) → 0 ∸ n ≡ 0
0-monus zero = refl
0-monus (suc n) = refl

∸-+-assoc : (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc m zero p = refl
∸-+-assoc zero (suc n) p rewrite 0-monus p = refl
∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ suc n = m * (m ^ n)

+-exp : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
+-exp m zero p rewrite +-identity (m ^ p) = refl
+-exp m (suc n) p rewrite +-exp m n p | sym (*-assoc m (m ^ n) (m ^ p)) = refl

*-swap : (m n p : ℕ) → m * (n * p) ≡ n * (m * p)
*-swap m n p rewrite sym (*-assoc m n p) | *-comm m n | *-assoc n m p = refl

*-exp₁ : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
*-exp₁ m n zero = refl
*-exp₁ m n (suc p) rewrite *-exp₁ m n p
  | *-assoc m n ((m ^ p) * (n ^ p)) 
  | *-assoc m (m ^ p) (n * (n ^ p))
  | *-swap n (m ^ p) (n ^ p) = refl

*-exp₂ : ∀ (m n p : ℕ) → m ^ (n * p) ≡ (m ^ n) ^ p
*-exp₂ m n zero rewrite *-zero n = refl
*-exp₂ m n (suc p) rewrite *-suc n p
  | +-exp m n (n * p)
  | *-exp₂ m n p = refl

----------------------------------------------------------------------

{- Copied (and adapted) from ../et/BooleModule -}
-- reverse binary numbers, i.e. x1 x1 x0 x1 nil = 11
data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

inc : Bin → Bin
inc nil = x1 nil
inc (x0 bs) = x1 bs
inc (x1 bs) = x0 inc bs

from : Bin → ℕ
from nil = zero
from (x0 bs) = 2 * from bs
from (x1 bs) = 1 + 2 * from bs

to : ℕ → Bin
to zero = x0 nil
to (suc m) = inc (to m)

binInc : ∀ (x : Bin) → from (inc x) ≡ suc(from x)
binInc nil = refl
binInc (x0 x) = refl
binInc (x1 x) rewrite binInc x | +-suc (from x) (from x + 0) = refl

fromToI : ∀ (n : ℕ) → from(to n) ≡ n
fromToI zero = refl
fromToI (suc n) rewrite binInc (to n) | fromToI n = refl

-- fromToI only holds for binary numbers without leading zeros.
-- The special "exception" is "0" representing 0 (rather) than nil
