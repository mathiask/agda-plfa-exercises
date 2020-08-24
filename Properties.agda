module plfa.Properties where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)
open import plfa.Isomorphism
open import plfa.Lambda

V¬—→ : ∀ {M N}
  → Value M
    ---------
  → ¬(M —→ N)
V¬—→ V-ƛ ()
V¬—→ V-zero ()
V¬—→ (V-suc VM) (ξ-suc M—→N) = V¬—→ VM M—→N

—→¬V : ∀ {M N}
  → M —→ N
    ---------
  → ¬ Value M
—→¬V MN VM = V¬—→ VM MN

infix  4 Canonical_⦂_

data Canonical_⦂_ : Term → Type → Set where
  C-ƛ : ∀ {x A N B}
    → ∅ , x ⦂ A ⊢ N ⦂ B
      -----------------------------
    → Canonical (ƛ x ⇒ N) ⦂ (A ⇒ B)

  C-zero :
      --------------------
      Canonical `zero ⦂ `ℕ

  C-suc : ∀ {V}
    → Canonical V ⦂ `ℕ
      ---------------------
    → Canonical `suc V ⦂ `ℕ


canonical : ∀ {V A}
  → ∅ ⊢ V ⦂ A
  → Value V
    -----------
  → Canonical V ⦂ A
canonical (⊢ƛ ⊢N) V-ƛ = C-ƛ ⊢N
canonical (⊢L · ⊢M) ()
canonical ⊢zero V-zero = C-zero
canonical (⊢suc ⊢V) (V-suc VV) = C-suc (canonical ⊢V VV)
canonical (⊢-case ⊢L ⊢M ⊢N) ()
canonical (⊢μ ⊢M) ()

value : ∀ {M A}
  → Canonical M ⦂ A
    ----------------
  → Value M
value (C-ƛ _) = V-ƛ
value C-zero = V-zero
value (C-suc CM) = V-suc (value CM)

typed : ∀ {M A}
  → Canonical M ⦂ A
    ---------------
  → ∅ ⊢ M ⦂ A
typed (C-ƛ ⊢N) = ⊢ƛ ⊢N
typed C-zero = ⊢zero
typed (C-suc CM) = ⊢suc (typed CM)


data Progress (M : Term) : Set where
  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M


progress : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Progress M
progress (⊢ƛ _) = done V-ƛ
progress (⊢L · ⊢M) with progress ⊢L
... | step L→L′ = step (ξ-·₁ L→L′)
... | done VL with progress ⊢M
...   | step M→M′ = step (ξ-·₂ VL M→M′)
...   | done VM with canonical ⊢L VL
...     | C-ƛ x = step (β-ƛ VM)
progress ⊢zero = done V-zero
progress (⊢suc ⊢M) with progress ⊢M
... | step M→M′ = step (ξ-suc M→M′)
... | done VM = done (V-suc VM)
progress (⊢-case ⊢L ⊢M ⊢N) with progress ⊢L
... | step L→L′ = step (ξ-case L→L′)
... | done VL with canonical ⊢L VL
...   | C-zero = step β-zero
...   | C-suc CL = step (β-suc (value CL))
progress (⊢μ ⊢M) = step β-μ

postulate
  progress′ : ∀ M {A} → ∅ ⊢ M ⦂ A → Value M ⊎ ∃[ N ](M —→ N)

-- Helper function to extract the term on the right hand side of a single step:
-- NOT REALLY NEEDED
-- —→result : ∀ {M N} →  (M —→ N) → Term
-- —→result (ξ-·₁ {_} {L′} _) = L′
-- —→result (ξ-·₂ {_} {_} {M′} _ _) = M′
-- —→result (β-ƛ {x} {N} {V} _) = N [ x := V ]
-- —→result (ξ-suc {_} {M′} _) = M′
-- —→result (ξ-case {_} {_} {L′} _) = L′
-- —→result (β-zero {_} {M}) = M
-- —→result (β-suc {x} {V} {_} {N} _) = N [ x := V ]
-- —→result (β-μ {x} {M}) = M [ x := μ x ⇒ M ]

Progress-≃ : ∀ M  → Progress M ≃ Value M ⊎ ∃[ N ](M —→ N)
Progress-≃ M = record
  { to = to
  ; from = from
  ; from∘to = from∘to
  ; to∘from = to∘from
  }
  where
  to : Progress M → Value M ⊎ ∃[ N ](M —→ N)
  to (step {N} s) = inj₂ ⟨ N , s ⟩
  to (done V) = inj₁ V
  from : Value M ⊎ ∃[ N ](M —→ N) → Progress M
  from (inj₁ V) = done V
  from (inj₂ ⟨ M′ , s ⟩) = step s
  from∘to : (p : Progress M) → from (to p) ≡ p
  from∘to (step s) = refl
  from∘to (done V) = refl
  to∘from : (vs : Value M ⊎ ∃[ N ](M —→ N)) → to (from vs) ≡ vs
  to∘from (inj₁ V) = refl
  to∘from (inj₂ s) = refl

progress₂ : ∀ M {A} → ∅ ⊢ M ⦂ A → Value M ⊎ ∃[ N ](M —→ N)
progress₂ N (⊢ƛ ⊢N) = inj₁ V-ƛ
progress₂ `zero ⊢zero = inj₁ V-zero
progress₂ (`suc M) (⊢suc ⊢M) with progress₂ M ⊢M
... | inj₁ VM = inj₁ (V-suc VM)
... | inj₂ ⟨ M′ , M→M′ ⟩ = inj₂ ⟨ `suc M′ , ξ-suc M→M′ ⟩
progress₂ (case L [zero⇒ M |suc x ⇒ N ]) (⊢-case ⊢L ⊢M ⊢N) with progress₂ L ⊢L
... | inj₂ ⟨ L′ , L→L′ ⟩ = inj₂ ⟨ case L′ [zero⇒ M |suc x ⇒ N ] , ξ-case L→L′ ⟩
... | inj₁ VL with canonical ⊢L VL
...   | C-zero = inj₂ ⟨ M , β-zero ⟩
...   | C-suc {V} CV = inj₂ ⟨ N [ x := V ] , β-suc (value CV) ⟩
progress₂ (μ x ⇒ M) (⊢μ ⊢M) = inj₂ ⟨ M [ x := μ x ⇒ M ] , β-μ ⟩
progress₂ (L · M) (⊢L · ⊢M) with progress₂ L ⊢L
... | inj₂ ⟨ L′ , L→L′ ⟩ = inj₂ ⟨ L′ · M , ξ-·₁ L→L′ ⟩
... | inj₁ VL with progress₂ M ⊢M
...   | inj₂ ⟨ M′ , M→M′ ⟩ = inj₂ ⟨ L · M′ , ξ-·₂ VL M→M′ ⟩
...   | inj₁ VM with canonical  ⊢L VL
...     | C-ƛ {x} {_} {N} ⊢N  = inj₂ ⟨ N [ x := M ] , β-ƛ VM ⟩
