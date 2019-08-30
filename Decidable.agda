module plfa.Decidable where

import Relation.Binary.PropositionalEquality as Eq

open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using () renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import plfa.Relations using (_<_; z<s; s<s)
open import plfa.Isomorphism using (_⇔_)

data Bool : Set where
  true  : Bool
  false : Bool

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

¬s<s : ∀ {m n : ℕ} → ¬ m < n → ¬ suc m < suc n
¬s<s ¬m<n (s<s m<n) = ¬m<n m<n

_<?_ : ∀ (m n : ℕ) → Dec (m < n)
_ <? zero = no λ ()
zero <? suc n = yes z<s
suc m <? suc n with m <? n
...            | yes m<n = yes (s<s m<n)
...            | no ¬m<n = no (¬s<s ¬m<n)

suc-injective : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-injective {m} {n} refl = refl

¬s≡s : ∀ {m n : ℕ} → ¬ m ≡ n → ¬ suc m ≡ suc n
¬s≡s ¬m≢n sm≡sn = ¬m≢n (suc-injective sm≡sn)

_≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero ≡ℕ? zero = yes refl
zero ≡ℕ? suc n = no (λ ())
suc m ≡ℕ? zero = no (λ ())
suc m ≡ℕ? suc n with m ≡ℕ? n
...             | yes m≡n = yes (cong suc m≡n)
...             | no m≢n  = no (¬s≡s m≢n)

⌞_⌟ : ∀ {A : Set} → Dec A → Bool
⌞ yes x ⌟ = true
⌞ no ¬x ⌟ = false

infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true  ∧ true  = true
false ∧ _     = false
_     ∧ false = false

infixr 6 _×-dec_

_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes x ×-dec yes y = yes ⟨ x , y ⟩
no ¬x ×-dec _     = no (λ {⟨ x , y ⟩ → ¬x x})
_     ×-dec no ¬y = no (λ {⟨ x , y ⟩ → ¬y y})

infixr 5 _∨_

_∨_ : Bool → Bool → Bool
true  ∨ _     = true
_     ∨ true  = true
false ∨ false = false

infixr 5 _⊎-dec_

_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎-dec _₁    = yes (inj₁ x)
_     ⊎-dec yes y = yes (inj₂ y)
no ¬x ⊎-dec no ¬y = no (λ { (inj₁ x) → ¬x x ; (inj₂ y) → ¬y y})

not : Bool → Bool
not true  = false
not false = true

¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes x) = no (¬¬-intro x)
¬? (no x)  = yes x

_⊃_ : Bool → Bool → Bool
_     ⊃ true  = true
true  ⊃ false = false
false ⊃ _     = true

_→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
_     →-dec yes y = yes λ _ → y
yes x →-dec no ¬y = no (λ a→b → ¬y (a→b x))
no ¬x →-dec _     = yes (λ x → ⊥-elim (¬x x))

∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌞ x ⌟ ∧ ⌞ y ⌟ ≡ ⌞ x ×-dec y ⌟
∨-⊎ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌞ x ⌟ ∨ ⌞ y ⌟ ≡ ⌞ x ⊎-dec y ⌟
not-¬ : ∀ {A : Set} (x : Dec A) → not ⌞ x ⌟ ≡ ⌞ ¬? x ⌟

∧-× (yes _) (yes _) = refl
∧-× (no x)  _       = refl
∧-× (yes x) (no y)  = refl

∨-⊎ (yes x) _       = refl
∨-⊎ (no x)  (yes y) = refl
∨-⊎ (no ¬x) (no ¬y) = refl

not-¬ (yes x) = refl
not-¬ (no x) = refl

_↔_ : Bool → Bool → Bool
true  ↔ true  = true
true  ↔ fasle = false
false ↔ true  = false
false ↔ false = true

_⇔-dec_  : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
(yes x) ⇔-dec (yes y) = yes (record { to = \_ → y ; from = \_ → x })
(yes x) ⇔-dec (no ¬y) = no (λ { record { to = a→b ; from = _ } → ¬y (a→b x)})
(no ¬x) ⇔-dec (yes y) = no (λ { record { to = _; from = b→a } → ¬x (b→a y)})
(no ¬x) ⇔-dec (no ¬y) = yes (record { to = λ x → ⊥-elim (¬x x)
                                    ; from = λ y → ⊥-elim (¬y y) })

↔-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌞ x ⌟ ↔ ⌞ y ⌟ ≡ ⌞ x ⇔-dec y ⌟
↔-⇔ (yes x) (yes y) = refl
↔-⇔ (yes x) (no ¬y) = refl
↔-⇔ (no ¬x) (yes y) = refl
↔-⇔ (no ¬x) (no ¬y) = refl

--
