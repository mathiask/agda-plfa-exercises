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

-- postulate (see below)
--   progress′ : ∀ M {A} → ∅ ⊢ M ⦂ A → Value M ⊎ ∃[ N ](M —→ N)
--
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

progress′ : ∀ M {A} → ∅ ⊢ M ⦂ A → Value M ⊎ ∃[ N ](M —→ N)
progress′ N (⊢ƛ ⊢N) = inj₁ V-ƛ
progress′ `zero ⊢zero = inj₁ V-zero
progress′ (`suc M) (⊢suc ⊢M) with progress′ M ⊢M
... | inj₁ VM = inj₁ (V-suc VM)
... | inj₂ ⟨ M′ , M→M′ ⟩ = inj₂ ⟨ `suc M′ , ξ-suc M→M′ ⟩
progress′ (case L [zero⇒ M |suc x ⇒ N ]) (⊢-case ⊢L ⊢M ⊢N) with progress′ L ⊢L
... | inj₂ ⟨ L′ , L→L′ ⟩ = inj₂ ⟨ case L′ [zero⇒ M |suc x ⇒ N ] , ξ-case L→L′ ⟩
... | inj₁ VL with canonical ⊢L VL
...   | C-zero = inj₂ ⟨ M , β-zero ⟩
...   | C-suc {V} CV = inj₂ ⟨ N [ x := V ] , β-suc (value CV) ⟩
progress′ (μ x ⇒ M) (⊢μ ⊢M) = inj₂ ⟨ M [ x := μ x ⇒ M ] , β-μ ⟩
progress′ (L · M) (⊢L · ⊢M) with progress′ L ⊢L
... | inj₂ ⟨ L′ , L→L′ ⟩ = inj₂ ⟨ L′ · M , ξ-·₁ L→L′ ⟩
... | inj₁ VL with progress′ M ⊢M
...   | inj₂ ⟨ M′ , M→M′ ⟩ = inj₂ ⟨ L · M′ , ξ-·₂ VL M→M′ ⟩
...   | inj₁ VM with canonical  ⊢L VL
...     | C-ƛ {x} {_} {N} ⊢N  = inj₂ ⟨ N [ x := M ] , β-ƛ VM ⟩

value? : ∀ { A M } → ∅ ⊢ M ⦂ A → Dec (Value M)
value? M with progress M
... | done VM = yes VM
... | step s = no (—→¬V s)

------------------------------------------------------------------

ext : ∀ {Γ Δ}
  → (∀ {x A}     →         Γ ∋ x ⦂ A →         Δ ∋ x ⦂ A)
    -----------------------------------------------------
  → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)
ext ρ Z = Z
ext ρ (S x≢y ∋x) = S x≢y (ρ ∋x)

rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
    ----------------------------------
  → (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ M ⦂ A)
rename ρ (⊢` ∋w) = ⊢` (ρ ∋w)
rename ρ (⊢ƛ ⊢N) = ⊢ƛ (rename (ext ρ) ⊢N)
rename ρ (⊢L · ⊢M) = (rename ρ ⊢L) · (rename ρ ⊢M)
rename ρ ⊢zero = ⊢zero
rename ρ (⊢suc ⊢M) = ⊢suc (rename ρ ⊢M)
rename ρ (⊢-case ⊢L ⊢M ⊢N) = ⊢-case (rename ρ ⊢L) (rename ρ ⊢M) (rename (ext ρ) ⊢N)
rename ρ (⊢μ ⊢M) = ⊢μ (rename (ext ρ) ⊢M)

weaken : ∀ {Γ M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Γ ⊢ M ⦂ A
weaken {Γ} ⊢M = rename (λ ()) ⊢M

drop : ∀ {Γ x M A B C}
  → Γ , x ⦂ A , x ⦂ B ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ B ⊢ M ⦂ C
drop {Γ} {x} {M} {A} {B} {C} ⊢M = rename ρ ⊢M
  where
   ρ : ∀ {z C}
     → Γ , x ⦂ A , x ⦂ B ∋ z ⦂ C
       -------------------------
     → Γ , x ⦂ B ∋ z ⦂ C
   ρ Z = Z
   ρ (S x≢x Z) = ⊥-elim (x≢x refl)
   ρ (S z≢x (S _ ∋z)) = S z≢x ∋z

swap : ∀ {Γ x y M A B C}
  → x ≢ y
  → Γ , y ⦂ B , x ⦂ A ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ A , y ⦂ B ⊢ M ⦂ C
swap {Γ} {x} {y} {M} {A} {B} {C} x≢y ⊢M = rename ρ ⊢M
  where
   ρ : ∀ {z C}
     → Γ , y ⦂ B , x ⦂ A ∋ z ⦂ C
       --------------------------
     → Γ , x ⦂ A , y ⦂ B ∋ z ⦂ C
   ρ Z = S x≢y Z
   ρ (S z≢x Z) = Z
   ρ (S z≢x (S z≢y ∋z)) = S z≢y (S z≢x ∋z)

subst : ∀ {Γ x N V A B}
  → ∅ ⊢ V ⦂ A
  → Γ , x ⦂ A ⊢ N ⦂ B
    --------------------
  → Γ ⊢ N [ x := V ] ⦂ B
subst {x = y}  ⊢V (⊢` {x = x} Z) with x ≟ y
... | yes _ = weaken ⊢V
... | no x≢y = ⊥-elim (x≢y refl) 
subst {x = y} ⊢V (⊢`  {x = x} (S x≢y ∋x)) with x ≟ y
... | yes refl = ⊥-elim (x≢y refl)
... | no _ = ⊢` ∋x
subst {x = y} ⊢V (⊢ƛ {x = x} ⊢N) with x ≟ y
... | yes refl = ⊢ƛ (drop ⊢N)
... | no x≢y = ⊢ƛ (subst ⊢V (swap x≢y ⊢N))
subst ⊢V (⊢L · ⊢M) = (subst ⊢V ⊢L) · (subst ⊢V ⊢M)
subst ⊢V ⊢zero = ⊢zero
subst ⊢V (⊢suc ⊢M) = ⊢suc (subst ⊢V ⊢M)
subst {x = y} ⊢V (⊢-case {x = x} ⊢L ⊢M ⊢N) with x ≟ y
... | yes refl = ⊢-case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (drop ⊢N)
... | no x≢y = ⊢-case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (subst ⊢V (swap x≢y ⊢N))
subst {x = y} ⊢V (⊢μ {x = x} ⊢M) with x ≟ y
... | yes refl = ⊢μ (drop ⊢M)
... | no x≢y = ⊢μ (subst ⊢V (swap x≢y ⊢M))

-- stretch skipped 
-- subst′ : ∀ {Γ x N V A B}
--   → ∅ ⊢ V ⦂ A
--   → Γ , x ⦂ A ⊢ N ⦂ B
--     --------------------
--   → Γ ⊢ N [ x := V ]′ ⦂ B

preserve : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —→ N
    ----------
  → ∅ ⊢ N ⦂ A
preserve (⊢L · ⊢M) (ξ-·₁ L→L′) = (preserve ⊢L L→L′) · ⊢M
preserve (⊢L · ⊢M) (ξ-·₂ VL M→′) = ⊢L · preserve ⊢M M→′
preserve (⊢ƛ ⊢N · ⊢V) (β-ƛ VV) = subst ⊢V ⊢N
preserve (⊢suc ⊢M) (ξ-suc M→M′) = ⊢suc (preserve ⊢M M→M′)
preserve (⊢-case ⊢L ⊢M ⊢N) (ξ-case L→L′) = ⊢-case (preserve ⊢L L→L′) ⊢M ⊢N
preserve (⊢-case ⊢zero ⊢M ⊢N) β-zero = ⊢M
preserve (⊢-case (⊢suc ⊢V) ⊢M ⊢N) (β-suc VV) = subst ⊢V ⊢N
preserve (⊢μ ⊢M) β-μ = subst (⊢μ ⊢M) ⊢M
