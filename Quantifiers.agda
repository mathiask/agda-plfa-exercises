module plfa.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Function using (_∘_)

open import plfa.Isomorphism using (_≃_; extensionality)

∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    -------
  → B M
∀-elim L M = L M

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× = record
  { to      = λ { f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ }
  ; from    = λ { ⟨ f , g ⟩ → λ x → ⟨ f x , g x ⟩ }
  ; from∘to = λ { f → refl }
  ; to∘from = λ { ⟨ f , g ⟩ → refl }
  }

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → (∀ (x : A) → B x ⊎ C x) 
⊎∀-implies-∀⊎ (_⊎_.inj₁ f) x = inj₁ (f x)
⊎∀-implies-∀⊎ (_⊎_.inj₂ g) x = inj₂ (g x) 

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Level using (Level; 0ℓ)

postulate Ext : Extensionality 0ℓ 0ℓ

∀-× : ∀ {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc
∀-× = record
  { to      = λ { f → ⟨ f aa , ⟨ f bb , f cc ⟩ ⟩ }
  ; from    = λ { ⟨ a , ⟨ b , c ⟩ ⟩ → λ { aa → a ; bb → b ; cc → c} }
  ; from∘to = λ { f  → Ext λ { aa → refl ; bb → refl ; cc → refl} }
  ; to∘from = λ { ⟨ a , ⟨ b , c ⟩ ⟩ → refl }
  }


----------------------------------------------------------------------

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    -------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying = record
  { to      = λ { f → λ { ⟨ x , y ⟩ → f x y} }
  ; from    = λ { g → λ { x y → g ⟨ x , y ⟩} }
  ; from∘to = λ { f → refl }
  ; to∘from = λ { f → extensionality (λ {⟨ x , y ⟩ → refl}) }
  }

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ = record
  { to      = λ { ⟨ x , y ⟩ → [ (λ b → inj₁ ⟨ x , b ⟩) , ((λ c → inj₂ ⟨ x , c ⟩)) ] y }
  ; from    = λ { (inj₁ ⟨ x , b ⟩) → ⟨ x , inj₁ b ⟩
                ; (inj₂ ⟨ x , c ⟩) → ⟨ x , inj₂ c ⟩ }
  ; from∘to = λ { ⟨ x , inj₁ b ⟩ → refl ; ⟨ x , inj₂ c ⟩ → refl }
  ; to∘from = λ { (inj₁ ⟨ x , b ⟩) → refl
                ; (inj₂ ⟨ x , c ⟩) → refl }
  }

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ x , ⟨ b , c ⟩ ⟩ = ⟨ ⟨ x , b ⟩ , ⟨ x , c ⟩ ⟩

----------------------------------------------------------------------

∀-⊎ : ∀ {B : Tri → Set} → ∃[ x ] B x  ≃ (B aa ⊎ B bb) ⊎ B cc
∀-⊎ = record
  { to      = λ { ⟨ aa , b ⟩ → inj₁ (inj₁ b)
                ; ⟨ bb , b ⟩ → inj₁ (inj₂ b)
                ; ⟨ cc , b ⟩ → inj₂ b }
  ; from    = λ { (inj₁ (inj₁ a)) → ⟨ aa , a ⟩
                ; (inj₁ (inj₂ b)) → ⟨ bb , b ⟩
                ; (inj₂ c) → ⟨ cc , c ⟩ }
  ; from∘to = λ { ⟨ aa , b ⟩ → refl ; ⟨ bb , b ⟩ → refl ; ⟨ cc , b ⟩ → refl}
  ; to∘from = λ { (inj₁ (inj₁ a)) → refl ; (inj₁ (inj₂ b)) → refl ; (inj₂ c) → refl}
  }
