module plfa.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.Isomorphism using (_≃_; _≲_; extensionality)
open plfa.Isomorphism.≃-Reasoning

data _×_  (A B : Set) : Set where
  ⟨_,_⟩ :
      A
    → B
      -----
    → A × B

proj₁ : ∀ {A B : Set}
  → A × B
    -----
  → A
proj₁ ⟨ x , y ⟩ = x  
   
proj₂ : ∀ {A B : Set}
  → A × B
    -----
  → B
proj₂ ⟨ x , y ⟩ = y

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

infixr 2 _×_

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm = record
  { to      = λ{⟨ x , y ⟩ → ⟨ y , x ⟩}
  ; from    = λ{⟨ y , x ⟩ → ⟨ x , y ⟩}
  ; from∘to = λ{⟨ x , y ⟩ → refl}
  ; to∘from = λ{⟨ y , x ⟩ → refl}
  }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc = record
  { to      = λ{⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩}
  ; from    = λ{⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩}
  ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl}
  ; to∘from = λ{⟨ x , ⟨ y , z ⟩ ⟩ → refl}
  }

record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× = record
  { to      = λ{ record { to = to ; from = from } → ⟨ to , from ⟩}
  ; from    = λ{⟨ to , from ⟩ → record { to = to ; from = from }}
  ; from∘to = λ{ record { to = to ; from = from } → refl}
  ; to∘from = λ{⟨ to , from ⟩ → refl}
  }


data ⊤ : Set where
  tt :
    --
    ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ = record
  { to      = λ{ ⟨ tt , x ⟩ → x}
  ; from    = λ{ x → ⟨ tt , x ⟩}
  ; from∘to = λ{ ⟨ tt , x ⟩ → refl}
  ; to∘from = λ{ x → refl}
  }

⊤-identityʳ : ∀ {A : Set} → A × ⊤ ≃ A
⊤-identityʳ{ A }  =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎


data _⊎_ (A B : Set) : Set where

  inj₁ :
      A
      -----
    → A ⊎ B

  inj₂ :
      B
      -----
    → A ⊎ B

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
    ---------
  → A ⊎ B → C
case-⊎ f g (inj₁ a) = f a
case-⊎ f g (inj₂ b) = g b

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ a) = refl
η-⊎ (inj₂ b) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ x) = refl

infix 1 _⊎_

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm = record
  { to      = λ{ (inj₁ a) → inj₂ a ; (inj₂ b) → inj₁ b}
  ; from    = λ{ (inj₁ b) → inj₂ b ; (inj₂ a) → inj₁ a}
  ; from∘to = λ{ (inj₁ a) → refl ; (inj₂ b) → refl}
  ; to∘from = λ{ (inj₁ b) → refl ; (inj₂ a) → refl}
  }

⊎-trans : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-trans = record
  { to      = λ { (inj₁ (inj₁ a)) → inj₁ a ;
                  (inj₁ (inj₂ b)) → inj₂ (inj₁ b) ;
                  (inj₂ c) → inj₂ (inj₂ c)}
  ; from    = λ { (inj₁ a) → inj₁ (inj₁ a) ;
                  (inj₂ (inj₁ b)) → (inj₁ (inj₂ b)) ;
                  (inj₂ (inj₂ c)) → inj₂ c }
  ; from∘to = λ { (inj₁ (inj₁ a)) → refl ; (inj₁ (inj₂ v)) → refl ; (inj₂ c) → refl}
  ; to∘from = λ { (inj₁ a) → refl ; (inj₂ (inj₁ b)) → refl ; (inj₂ (inj₂ c)) → refl}
  }


data ⊥ : Set where
  -- no clauses

⊥-elim : ∀ {A : Set}
  → ⊥
    --
  → A
⊥-elim ()

uniq-⊥ : ∀ {A : Set} (h : ⊥ → A) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ = record
  { to      = λ{ (inj₂ a) → a }
  ; from    = λ{ a → inj₂ a }
  ; from∘to = λ{ (inj₂ a) → refl }
  ; to∘from = λ{ a → refl }
  }

⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityʳ {A} =
  ≃-begin
    (A ⊎ ⊥)
  ≃⟨ ⊎-comm ⟩
    (⊥ ⊎ A)
  ≃⟨ ⊥-identityˡ ⟩
    A
  ≃-∎


→-elim : ∀ {A B : Set} -- Modus Ponens
  → (A → B)
  → A
    -------
  → B
→-elim L M = L M

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying = record
  { to      = λ{ f → λ { ⟨ x , y ⟩ → f x y} }
  ; from    = λ{ g → λ x → λ y → g ⟨ x , y ⟩ }
  ; from∘to = λ{ f → refl}
  ; to∘from = λ{ g → extensionality (λ { ⟨ a , b ⟩ → refl})}
  }

→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× = record
  { to      = λ{ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ }
  ; from    = λ{ ⟨ g , h ⟩ → λ x → ⟨ g x , h x ⟩ }
  ; from∘to = λ{ f → extensionality λ x → η-× (f x) }
  ; to∘from = λ{ ⟨ g , h ⟩ → refl }
  }

→-⊎-× : ∀ {A B C : Set} → (A ⊎ B → C) ≃ (A → C) × (B → C)
→-⊎-× = record
  { to      = λ{ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩ }
  ; from    = λ{ ⟨ g , h ⟩ → λ { (inj₁ a) → g a ; (inj₂ b) → h b} }
  ; from∘to = λ{ f → extensionality (λ { (inj₁ a) → refl ; (inj₂ b) → refl }) }
  ; to∘from = λ{ ⟨ g , h ⟩ → refl }
  }

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ = record
  { to      = λ{ ⟨ inj₁ a , c ⟩ → inj₁ ⟨ a , c ⟩ ; ⟨ inj₂ b , c ⟩ → inj₂ ⟨ b , c ⟩ }
  ; from    = λ{ (inj₁ ⟨ a , c ⟩) → ⟨ inj₁ a , c ⟩ ; (inj₂ ⟨ b , c ⟩) → ⟨ inj₂ b , c ⟩ }
  ; from∘to = λ{ ⟨ inj₁ a , c ⟩ → refl ; ⟨ inj₂ b , c ⟩ → refl }
  ; to∘from = λ{ (inj₁ ⟨ a , c ⟩) → refl ; (inj₂ ⟨ b , c ⟩) → refl }
  }

⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× = record
  { to      = λ{ (inj₁ ⟨ a , b ⟩) → ⟨ inj₁ a , inj₁ b ⟩ ; (inj₂ c) → ⟨ inj₂ c , inj₂ c ⟩ }
  ; from    = λ{ ⟨ inj₁ a , inj₁ b ⟩ → inj₁ ⟨ a , b ⟩
               ; ⟨ inj₁ a , inj₂ c ⟩ → inj₂ c
               ; ⟨ inj₂ c , inj₁ b ⟩ → inj₂ c
               ; ⟨ inj₂ c , _  ⟩ → inj₂ c     -- here we have a choice what to throw away => not iso
              }
  ; from∘to = λ{ (inj₁ ⟨ a , b ⟩) → refl ; (inj₂ c) → refl }
  }

⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ a , c ⟩ = inj₁ a
⊎-weak-× ⟨ inj₂ b , c ⟩ = inj₂ ⟨ b , c ⟩

-- this follows from
-- (A ⊎ B) × C ≃ (A × C) ⊎ (B × C) and
-- (A × C) ⊎ (B × C) → A ⊎ (B × C) ∋ p₁ ⊎ id

⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ a , b ⟩) = ⟨ inj₁ a , inj₁ b ⟩
⊎×-implies-×⊎ (inj₂ ⟨ c , d ⟩) = ⟨ inj₂ c , inj₂ d ⟩

-- the converse is false, e.g. A = D = ⊤ and B = C = ⊥
