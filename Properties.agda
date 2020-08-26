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

----------------------------------------------------------------------

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

------------------------------ Evaluation ------------------------------

record Gas : Set where
  constructor gas
  field
    amount : ℕ

-- C-cC-n or C-cC-d: "gas 42" "Gas.amount (gas 42)"

data Finished (N : Term) : Set where
  done :
      Value N
      ----------
    → Finished N

  out-of-gas :
      ----------
      Finished N


data Steps (L  : Term) : Set where
  steps : ∀ {N}
    → L —↠ N
    → Finished N
      ----------
    → Steps L

eval : ∀ {L A}
  → Gas
  → ∅ ⊢ L ⦂ A
    ---------
  → Steps L
eval {L} (gas zero) ⊢L = steps (L ∎) out-of-gas
eval {L} (gas (suc m)) ⊢L with progress ⊢L
... | done VL = steps (L ∎) (done VL)
... | step {M} L→M with eval (gas m) (preserve ⊢L L→M)
...   | steps M↠N fin = steps (L —→⟨ L→M ⟩ M↠N) fin

⊢sucμ : ∅ ⊢ μ "x" ⇒ `suc ` "x" ⦂ `ℕ
⊢sucμ = ⊢μ (⊢suc (⊢` Z))

-- C-cC-n: eval (gas 3) ⊢sucμ
--         eval (gas 100) (⊢twoᶜ · ⊢sucᶜ · ⊢zero)
--         eval (gas 5) (⊢twoᶜ · ⊢sucᶜ · ⊢zero)
--         eval (gas 100) ⊢2+2
--           actually gas 14 suffices
--         eval (gas 100) ⊢2+2ᶜ

⊢2*2 : ∅ ⊢ mul · two · two ⦂ `ℕ
⊢2*2 = mul-type · ⊢two · ⊢two

-- _ : eval (gas 50) ⊢2*2 ≡
-- -- C-cC-n and paste result here:
-- _ = refl

-- Progress-preservation
postulate
  _ : ∀ M {A} → ∅ ⊢ M ⦂ A → Value M ⊎ ∃[ N ](M —→ N)
  _ : ∀ M N {A} → ∅ ⊢ M ⦂ A → M —→ N → ∅ ⊢ N ⦂ A
  
⊢Xcase1 : (∅ , "x" ⦂ `ℕ) ⊢ case `zero [zero⇒ `zero |suc "a" ⇒ ` "x" ] ⦂ `ℕ
⊢Xcase1 = ⊢-case ⊢zero ⊢zero (⊢` (S ("x" ≠ "a") Z))
⊢Xcase2 : ∅ ⊢ `zero ⦂ `ℕ
⊢Xcase2 = ⊢zero
⊢Xcase3 : case `zero [zero⇒ `zero |suc "a" ⇒ ` "x" ] —→ `zero
⊢Xcase3 = β-zero

⊢Xnocase1 : (∅ , "x" ⦂ `ℕ) ⊢ (ƛ "a" ⇒ (ƛ "b" ⇒ ` "b")) · (ƛ "c" ⇒ ` "x") ⦂ `ℕ ⇒ `ℕ
⊢Xnocase1 = (⊢ƛ (⊢ƛ (⊢` Z))) · (⊢ƛ {A = `ℕ} (⊢` (S ("x" ≠ "c") Z)))
⊢Xnocase2 : ∅ ⊢ (ƛ "b" ⇒ ` "b") ⦂ `ℕ ⇒ `ℕ
⊢Xnocase2 = ⊢ƛ (⊢` Z)
⊢Xnocase3 : (ƛ "a" ⇒ (ƛ "b" ⇒ ` "b")) · (ƛ "c" ⇒ ` "x") —→ ƛ "b" ⇒ ` "b"
⊢Xnocase3 = β-ƛ V-ƛ

----------------------------------------------------------------------

Normal : Term → Set
Normal M = ∀ {N} → ¬ (M —→ N)

Stuck : Term → Set
Stuck M = Normal M × ¬ Value M

Xstuck1 : Stuck (`zero · `zero)
Xstuck1 = ⟨ n , nv ⟩ where
  n : ∀ {N} →  `zero · `zero —→ N → ⊥
  n (ξ-·₁ ())
  n (ξ-·₂ _ ())
  nv : ¬ Value  (`zero · `zero)
  nv ()
Xstuck1b : ∀ {Γ A} → Γ ⊢ `zero · `zero ⦂ A → ⊥
Xstuck1b {Γ} {A} (() · ⊢z₂)

Xstuck2a : Stuck (` "x")
Xstuck2a = ⟨ n , nv ⟩ where
  n : ∀ {N : Term} →  ` "x" —→ N → ⊥
  n ()
  nv : ¬ Value  (` "x")
  nv ()
Xstuck2b : ∅ , "x" ⦂ `ℕ ⊢ ` "x" ⦂ `ℕ
Xstuck2b = ⊢` Z

unstuck : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    -----------
  → ¬ (Stuck M)
unstuck ⊢M s with progress ⊢M
unstuck ⊢M ⟨ nostep , _ ⟩ | step M→N = nostep M→N
unstuck ⊢M ⟨ _ , noval ⟩ | done VM = noval VM

preserves : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —↠ N
    ---------
  → ∅ ⊢ N ⦂ A
preserves ⊢M (M ∎) = ⊢M
preserves ⊢M (M —→⟨ M→N ⟩ s) = preserves (preserve ⊢M M→N) s

wttdgs : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —↠ N
    -----------
  → ¬ (Stuck N)
wttdgs ⊢M M↠N s = unstuck (preserves ⊢M M↠N) s

----------------------------------------------------------------------

cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E)
  {s w : A} {t x : B} {u y : C} {v z : D}
  → s ≡ w → t ≡ x → u ≡ y → v ≡ z → f s t u v ≡ f w x y z
cong₄ f refl refl refl refl = refl

det : ∀ {M M′ M″}
  → (M —→ M′)
  → (M —→ M″)
    --------
  → M′ ≡ M″
det (ξ-·₁ s₁) (ξ-·₁ s₂) = cong₂ _·_ (det s₁ s₂) refl
det (ξ-·₁ s) (ξ-·₂ VL _) = ⊥-elim (V¬—→ VL s)
det (ξ-·₂ VL _) (ξ-·₁ s) = ⊥-elim (V¬—→ VL s)
det (ξ-·₂ _ s₁) (ξ-·₂ _ s₂) = cong₂ _·_ refl (det s₁ s₂) 
det (ξ-·₂ _ s) (β-ƛ VM) = ⊥-elim (V¬—→ VM s)
det (β-ƛ VV) (ξ-·₂ _ s) = ⊥-elim (V¬—→ VV s)
det (β-ƛ _) (β-ƛ _) = refl
det (ξ-suc s₁) (ξ-suc s₂) = cong `suc_ (det s₁ s₂)
det (ξ-case s₁) (ξ-case s₂) = cong₄ case_[zero⇒_|suc_⇒_] (det s₁ s₂) refl refl refl
det (ξ-case s) (β-suc VV) = ⊥-elim (V¬—→ (V-suc VV) s)
det β-zero β-zero = refl
det (β-suc VV) (ξ-case s) = ⊥-elim (V¬—→ (V-suc VV) s)
det (β-suc _) (β-suc _) = refl
det β-μ β-μ = refl

-- Quizzes
-- =======
--
-- -------- β-zap
-- M —→ zap
--
-- ----------- ⊢zap
-- Γ ⊢ zap ⦂ A
--
-- Determinism of step becomes false, for any M that allows a "normal" step.
-- Progress remains true.
-- Preservation remains true (though types are no longer unique, wich we
--   haven't proved anyway).
--
--
-- ------------------ β-foo₁
-- (λ x ⇒ ` x) —→ foo

-- ----------- β-foo₂
-- foo —→ zero
-- Determinism of step becomes false, as we can now reduce λ on the left of _·_.
-- Progress remains true.
-- Preservation is unclear as the is no typing rule for foo.
--
--
-- If we remove ξ-·₁:
-- Determinism remains true.
-- Progress becomes false: ((λ x . suc) zero) zero
-- Preservation remains true.
--
--
-- If we add "Kleene application":
-- Determinism remains true.
-- Progress remains true.
-- Preservation remains true (as none of the relevant terms can be typed).
