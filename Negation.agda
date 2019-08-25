module plfa.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import plfa.Isomorphism using (_≃_; extensionality)

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro x ¬x = ¬x x

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A
¬¬¬-elim ¬¬¬x = ¬¬¬x ∘ ¬¬-intro  

contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)
contraposition f ¬y = ¬y ∘ f

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ x ≡ y

_ : 1 ≢ 2
_ = λ ()

peano : ∀ {n : ℕ} → zero ≢ suc n
peano = λ ()

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′ 
id≡id′ = extensionality λ ()

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))

----------------------------------------------------------------------

infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n

<-irreflexive : ∀ (n : ℕ) → ¬ n < n
<-irreflexive zero ()
<-irreflexive (suc n) (s<s n<n) = ¬-elim (<-irreflexive n) n<n

_>_ : ℕ → ℕ → Set
x > y = y < x

<-weak-trichotomy : ∀ (m n : ℕ) → (m < n ⊎ m ≡ n) ⊎ m > n
<-weak-trichotomy zero zero = inj₁(inj₂ refl)
<-weak-trichotomy zero (suc n) = inj₁(inj₁ z<s)
<-weak-trichotomy (suc m) zero = inj₂ z<s
<-weak-trichotomy (suc m) (suc n) with (<-weak-trichotomy  m n) 
...                               | inj₁ (inj₁ m<n) = inj₁(inj₁ (s<s m<n))
...                               | inj₁ (inj₂ refl) = inj₁(inj₂ refl)
...                               | inj₂ m>n = inj₂ (s<s m>n)

<-trichotomy-exclusive₁ : ∀ (m n : ℕ) → m < n → m ≢ n
<-trichotomy-exclusive₁ zero .(suc _) z<s = peano
<-trichotomy-exclusive₁ (suc m) (suc n) (s<s m<n) = m≢n→sm≢sn (<-trichotomy-exclusive₁ m n m<n) where
  m≢n→sm≢sn : m ≢ n → suc m ≢ suc n
  m≢n→sm≢sn m≢n refl = m≢n refl

<-trichotomy-exclusive₁′ : ∀ (m n : ℕ) → m > n → m ≢ n
<-trichotomy-exclusive₁′ m n m>n m≡n = <-trichotomy-exclusive₁ n m m>n (sym m≡n)

<-trichotomy-exclusive₂ : ∀ (m n : ℕ) → m < n → ¬ m > n
<-trichotomy-exclusive₂ (suc m) (suc n) (s<s m<n) (s<s m>n) = <-trichotomy-exclusive₂ m n m<n m>n

<-trichotomy-exclusive₂′ : ∀ (m n : ℕ) → m > n → ¬ m < n
<-trichotomy-exclusive₂′ m n m>n m<n = <-trichotomy-exclusive₂ n m m>n m<n

<-trichotomy-exclusive₃ : ∀ (m n : ℕ) → m ≡ n → ¬ m < n
<-trichotomy-exclusive₃ m n refl = <-irreflexive m

<-trichotomy-exclusive₃′ : ∀ (m n : ℕ) → m ≡ n → ¬ m > n
<-trichotomy-exclusive₃′ m n  m≡n m>n = <-trichotomy-exclusive₃ n m (sym m≡n) m>n

<-trichotomy : ∀ (m n : ℕ)
  → ((m < n) × (m ≢ n) × (¬ m > n)
  ⊎ (¬ m < n) × (m ≡ n) × (¬ m > n))
  ⊎ (¬ m < n) × (m ≢ n) × (m > n)
<-trichotomy m n with <-weak-trichotomy m n
...              | inj₁ (inj₁ m<n) = inj₁(inj₁ ⟨ m<n , ⟨ <-trichotomy-exclusive₁ m n m<n
                                                       , <-trichotomy-exclusive₂ m n m<n ⟩ ⟩)
...              | inj₁ (inj₂ m≡n) = inj₁(inj₂ ⟨ <-trichotomy-exclusive₃ m n m≡n
                                               , ⟨ m≡n , <-trichotomy-exclusive₃′ m n m≡n ⟩ ⟩)
...              | inj₂ m>n = inj₂ ⟨ <-trichotomy-exclusive₂′ m n m>n
                                   , ⟨ <-trichotomy-exclusive₁′ m n m>n , m>n ⟩ ⟩

----------------------------------------------------------------------

assimilation′ : ∀ {A : Set} {¬x ¬x′ : ¬ A} → ¬x ≡ ¬x′
assimilation′ {A} {¬x} {¬x′} = assimilation ¬x ¬x′

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× {A} {B} = record
  { to      = λ { ¬⊎ → ⟨ ¬⊎ ∘ inj₁ , ¬⊎ ∘ inj₂ ⟩ }
  ; from    = λ { ¬×¬ → λ A⊎B → [ proj₁ ¬×¬ , proj₂ ¬×¬ ] A⊎B }
  ; from∘to = λ {¬⊎ → assimilation′}
  ; to∘from = λ{ ¬×¬ → refl }
  }

----------------------------------------------------------------------

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable = λ k → k (inj₂ λ a → k (inj₁ a))

-- Classical Rules
-- ===============
-- Excluded Middle: A ⊎ ¬ A, for all A
-- Double Negation Elimination: ¬ ¬ A → A, for all A
-- Peirce’s Law: ((A → B) → A) → A, for all A and B.
-- Implication as disjunction: (A → B) → ¬ A ⊎ B, for all A and B.
-- De Morgan: ¬ (¬ A × ¬ B) → A ⊎ B, for all A and B.
--
-- To show that they are all equivalent, i.e. they all imply each other,
-- it suffices to show circular implication:

em→dne : ∀ {A : Set} → A ⊎ ¬ A → ¬ ¬ A → A
em→dne a⊎¬a ¬¬a = [ (λ x → x) , (λ ¬a → ⊥-elim (¬¬a ¬a)) ] a⊎¬a

dne→pl : (∀ {A : Set} → ¬ ¬ A → A) → (∀ {A B : Set} → ((A → B) → A) → A)
dne→pl dne f = {!!}
