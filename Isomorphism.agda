module plfa.Isomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm)

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

_∘′_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘′ f = λ x → g (f x)


postulate
  extensionatliy : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g


_+′_ : ℕ → ℕ → ℕ
m +′ zero = m
m +′ suc n = suc (m +′ n)

same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m n rewrite +-comm m n = helper m n where
  helper : ∀ (m n : ℕ) → m +′ n ≡ n + m
  helper m zero = refl
  helper m (suc n) = cong suc (helper m n)

same : _+′_ ≡ _+_
same = extensionatliy (λ m → extensionatliy (λ n → same-app m n))


postulate
  ∀-extensionatliy : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

infix 0 _≃_

record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y

open _≃_

≃-refl : ∀ {A : Set} → A ≃ A
≃-refl =
  record
    { to      = λ x → x
    ; from    = λ y → y
    ; from∘to = λ x → refl
    ; to∘from = λ y → refl
    }

≃-sym : ∀ {A B : Set}
  → A ≃ B
    -----
  → B ≃ A
≃-sym A≃B =
  record
    { to      = from A≃B
    ; from    = to A≃B
    ; from∘to = to∘from A≃B
    ; to∘from = from∘to A≃B
    }

≃-trans : ∀ {A B C : Set}
  → A ≃ B
  → B ≃ C
    -----
  → A ≃ C
≃-trans A≃B B≃C =
  record
    { to      = (to B≃C) ∘ (to A≃B)
    ; from    = (from A≃B) ∘ (from B≃C)
      ; from∘to = λ x →
        begin
          from A≃B (from B≃C (to B≃C (to A≃B x)))
        ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
           from A≃B (to A≃B x)
        ≡⟨ from∘to A≃B x ⟩
          x
        ∎
    ; to∘from = λ{y →
        begin
          (to B≃C ∘ to A≃B) ((from A≃B ∘ from B≃C) y)
        ≡⟨⟩
          to B≃C (to A≃B (from A≃B (from B≃C y)))
        ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
          to B≃C (from B≃C y)
        ≡⟨ to∘from B≃C y ⟩
          y
        ∎}
    }
    

module ≃-Reasoning where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set}
    → A ≃ B
      -----
    → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≃ B
    → B ≃ C
      -----
    → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set)
      -----
    → A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning

infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
open _≲_

≲-refl : ∀ {A : Set} → A ≲ A
≲-refl =
  record
    { to      = λ{x → x}
    ; from    = λ{y → y}
    ; from∘to = λ{x → refl}
    }

≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans A≲B B≲C =
  record
    { to      = λ{x → to   B≲C (to   A≲B x)}
    ; from    = λ{y → from A≲B (from B≲C y)}
    ; from∘to = λ{x →
        begin
          from A≲B (from B≲C (to B≲C (to A≲B x)))
        ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B x)) ⟩
          from A≲B (to A≲B x)
        ≡⟨ from∘to A≲B x ⟩
          x
        ∎}
     }

≲-antisym : ∀ {A B : Set}
  → (A≲B : A ≲ B)
  → (B≲A : B ≲ A)
  → (to A≲B ≡ from B≲A)
  → (from A≲B ≡ to B≲A)
    -------------------
  → A ≃ B
≲-antisym A≲B B≲A to≡from from≡to =
  record
    { to      = to A≲B
    ; from    = from A≲B
    ; from∘to = from∘to A≲B
    ; to∘from = λ{y →
        begin
          to A≲B (from A≲B y)
        ≡⟨ cong (to A≲B) (cong-app from≡to y) ⟩
          to A≲B (to B≲A y)
        ≡⟨ cong-app to≡from (to B≲A y) ⟩
          from B≲A (to B≲A y)
        ≡⟨ from∘to B≲A y ⟩
          y
        ∎}
    }

module ≲-Reasoning where

  infix  1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix  3 _≲-∎

  ≲-begin_ : ∀ {A B : Set}
    → A ≲ B
      -----
    → A ≲ B
  ≲-begin A≲B = A≲B

  _≲⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≲ B
    → B ≲ C
      -----
    → A ≲ C
  A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

  _≲-∎ : ∀ (A : Set)
      -----
    → A ≲ A
  A ≲-∎ = ≲-refl

open ≲-Reasoning


≃-implies-≲ : ∀ {A B : Set}
  → A ≃ B
    -----
  → A ≲ B
≃-implies-≲ A≃B =
  record
    { to      = to A≃B
    ; from    = from A≃B
    ; from∘to = from∘to A≃B
    }

record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

⇔-refl : {A : Set} → A ⇔ A
⇔-refl = 
  record
    { to = λ x → x
    ; from = λ x → x
    }

⇔-sym : {A B : Set}
  → A ⇔ B
    -----
  → B ⇔ A
⇔-sym A⇔B =
  record
    { to = _⇔_.from A⇔B
    ; from = _⇔_.to A⇔B
    }
  
⇔-trans : {A B C : Set}
  → A ⇔ B
  → B ⇔ C
    -----
  → A ⇔ C
⇔-trans A⇔B B⇔C =
  record
    { to = (_⇔_.to B⇔C) ∘ (_⇔_.to A⇔B)
    ; from = (_⇔_.from A⇔B) ∘ (_⇔_.from B⇔C)
    }

----------------------------------------------------------------------

data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

inc : Bin → Bin
inc nil = x1 nil
inc (x0 bs) = x1 bs
inc (x1 bs) = x0 inc bs

toBin : ℕ → Bin
toBin zero = x0 nil
toBin (suc m) = inc (toBin m)

fromBin : Bin → ℕ
fromBin nil = zero
fromBin (x0 bs) = 2 * fromBin bs
fromBin (x1 bs) = 1 + 2 * fromBin bs

postulate
  fromToI : ∀ (n : ℕ) → fromBin(toBin n) ≡ n -- s. Induction.agda

ℕ≲Bin : ℕ ≲ Bin
ℕ≲Bin =
  record
    { to      = toBin
    ; from    = fromBin
    ; from∘to = fromToI
    }
