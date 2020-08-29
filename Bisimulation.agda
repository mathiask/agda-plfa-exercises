-- IMPLEMENTATION OF SIMULATION FOR THE ALTERNATIVE PRODUCT IS *NOT* FINISHED!

module plfa.Bisimulation where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl ; sym; cong; cong₂)
open import plfa.More

infix  4 _~_
infix  5 ~ƛ_
infix  7 _~·_

-- Auxiliary function needed for the simulation of the alternative product:

fresh₃ : ∀ {Γ A B C F} → Γ , A , B ∋ C → Γ , F , A , B ∋ C
fresh₃ Z = Z
fresh₃ (S Z) = S Z
fresh₃ (S (S x)) = (S (S (S x)))

ρ-ext₃ : ∀ {Γ Δ A B F}
         → (∀ {T} → Γ , A , B ∋ T → Δ , A , B ∋ T)
         → (∀ {T} → Γ , F , A , B ∋ T → Δ , F , A , B ∋ T)
ρ-ext₃ ρ Z = fresh₃ (ρ Z)
ρ-ext₃ ρ (S Z) = fresh₃ (ρ (S Z))
ρ-ext₃ ρ (S (S Z)) = S (S Z)
ρ-ext₃ ρ (S (S (S x))) = fresh₃ (ρ (S (S x)))

postulate 
  rename-fresh₃ : ∀ {Γ A B C F}
    → (ρ : ∀ {T} → Γ , A , B ∋ T → Γ , A , B ∋ T)
    → (N : Γ , A , B ⊢ C)
    → rename (ρ-ext₃ {F = F} ρ) (rename fresh₃ N) ≡ (rename fresh₃ (rename ρ N))

postulate
  ρ-fresh₃ : ∀ {Γ Δ A B N F} 
      → (ρ : ∀ {T} → Γ ∋ T → Δ ∋ T)
      → (⊢N : Γ , A , B ⊢ N)
      → rename (ext (ext (ext ρ))) (rename (fresh₃ {F = F}) ⊢N)
        ≡ rename (fresh₃ {F = F}) (rename (ext (ext ρ)) ⊢N)


data _~_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ~` : ∀ {Γ A} {x : Γ ∋ A}
     ---------
   → ` x ~ ` x

  ~ƛ_ : ∀ {Γ A B} {N N† : Γ , A ⊢ B}
    → N ~ N†
      ----------
    → ƛ N ~ ƛ N†

  _~·_ : ∀ {Γ A B} {L L† : Γ ⊢ A ⇒ B} {M M† : Γ ⊢ A}
    → L ~ L†
    → M ~ M†
      ---------------
    → L · M ~ L† · M†

  ~let : ∀ {Γ A B} {M M† : Γ ⊢ A} {N N† : Γ , A ⊢ B}
    → M ~ M†
    → N ~ N†
      ----------------------
    → `let M N ~ (ƛ N†) · M†

  ~casex : ∀ {Γ A B C} {L L† : Γ ⊢ A `× B} {N N† : Γ , A , B ⊢ C}
    → L ~ L†
    → N ~ N†
      ------------------------------------------------------------------------------------
    → case× L N ~
      `let (L†) (`let (`proj₁ (# 0)) (`let (`proj₂ (# 1)) (rename (fresh₃ {F = A `× B}) N†)))


-- BEGIN Commented out to speed up the rest
--
-- -- To show the equivalence of _~_ and † we need to define the relevant
-- -- fragment of the language:

-- data †relevant : ∀ {Γ A} → Γ ⊢ A → Set where

--   relevant~ : ∀ {Γ A} {x : Γ ∋ A}
--       ---------------
--     → †relevant (` x)

--   relevantƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
--     → †relevant N
--       ---------------
--     → †relevant (ƛ N)

--   relevant· : ∀ {Γ A B} {L : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
--     → †relevant L
--     → †relevant M
--       -----------------
--     → †relevant (L · M)

--   relevant-let : ∀ {Γ A B} {M : Γ ⊢ A} {N : Γ , A ⊢ B}
--     → †relevant M
--     → †relevant N
--       --------------------
--     → †relevant (`let M N)


-- † : ∀ {Γ A} → (M : Γ ⊢ A) → {†relevant M} → (Γ ⊢ A)
-- † (` x) {relevant~} = ` x
-- † (ƛ M) {relevantƛ RM} = ƛ † M {RM}
-- † (M · N) {relevant· RM RN} = († M {RM}) · † N {RN}
-- † (`let M N) {relevant-let RM RN} = (ƛ † N {RN}) · † M {RM}

-- ≡⇒~ : ∀ {Γ A} (M N : Γ ⊢ A) → {RM : †relevant M} → († M {RM} ≡ N) → (M ~ N)
-- ≡⇒~ (` x) (` .x) {relevant~} refl = ~`
-- ≡⇒~ (ƛ M) (ƛ .(† M)) {relevantƛ RM} refl = ~ƛ (≡⇒~ M († M) refl)
-- ≡⇒~ (M · N) (.(† M) · .(† N)) {relevant· RM RM₁} refl =
--     (≡⇒~ M († M) refl) ~· (≡⇒~ N († N) refl)
-- ≡⇒~ (`let M N) (.(ƛ † N) · .(† M)) {relevant-let RM RN} refl =
--     ~let (≡⇒~ M († M) refl) (≡⇒~ N († N) refl)

-- ~⇒≡ : ∀ {Γ A} (M N : Γ ⊢ A) → {RM : †relevant M} → (M ~ N) → († M {RM} ≡ N)
-- ~⇒≡ (` x) (` .x) {relevant~} ~` = refl
-- ~⇒≡ (ƛ M) (ƛ N) {relevantƛ RM} (~ƛ M~N) = cong ƛ_ (~⇒≡ M N M~N)
-- ~⇒≡ (M · N) (O · P) {relevant· RM RN} (M~O ~· N~P) = cong₂ _·_ (~⇒≡ M O M~O) ((~⇒≡ N P N~P))
-- ~⇒≡ (`let M N) ((ƛ N′) · M′) {relevant-let RM RN} (~let M~M′ N~N′)
--     = cong₂ _·_  (cong ƛ_ (~⇒≡ N N′ N~N′)) (~⇒≡ M M′ M~M′)
--
-- END

~val : ∀ {Γ A} {M M† : Γ ⊢ A}
  → M ~ M†
  → Value M
    --------
  → Value M†
~val ~`           ()
~val (~ƛ ~N)      V-ƛ  =  V-ƛ
~val (~L ~· ~M)   ()
~val (~let ~M ~N) ()

~val⁻¹ : ∀ {Γ A} {M M† : Γ ⊢ A}
  → M ~ M†
  → Value M†
    --------
  → Value M
~val⁻¹ (~ƛ N~) V-ƛ = V-ƛ

~rename : ∀ {Γ Δ}
  → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
    ----------------------------------------------------------
  → (∀ {A} {M M† : Γ ⊢ A} → M ~ M† → rename ρ M ~ rename ρ M†)
~rename ρ (~`)          =  ~`
~rename ρ (~ƛ ~N)       =  ~ƛ (~rename (ext ρ) ~N)
~rename ρ (~L ~· ~M)    =  (~rename ρ ~L) ~· (~rename ρ ~M)
~rename ρ (~let ~M ~N)  = ~let (~rename ρ ~M) (~rename (ext ρ) ~N)
~rename ρ (~casex {A = A} {B = B} {L† = L†} {N† = N†} ~L ~N)
  with cong
    (λ x → `let (rename ρ L†) (`let (`proj₁ (` Z)) (`let (`proj₂ (` (S Z))) x)))
    (ρ-fresh₃ {F = A `× B} ρ N†)
... | x = {!!}



-- postulate
--   ρ-fresh₃ : ∀ {Γ Δ A B N F} 
--       → (ρ : ∀ {T} → Γ ∋ T → Δ ∋ T)
--       → (⊢N : Γ , A , B ⊢ N)
--       → rename (ext (ext (ext ρ))) (rename (fresh₃ {F = F}) ⊢N)
--         ≡ rename (fresh₃ {F = F}) (rename (ext (ext ρ)) ⊢N)


-- ~exts : ∀ {Γ Δ}
--   → {σ  : ∀ {A} → Γ ∋ A → Δ ⊢ A}
--   → {σ† : ∀ {A} → Γ ∋ A → Δ ⊢ A}
--   → (∀ {A} → (x : Γ ∋ A) → σ x ~ σ† x)
--     --------------------------------------------------
--   → (∀ {A B} → (x : Γ , B ∋ A) → exts σ x ~ exts σ† x)
-- ~exts ~σ Z      =  ~`
-- ~exts ~σ (S x)  =  ~rename S_ (~σ x)

-- ~subst : ∀ {Γ Δ}
--   → {σ  : ∀ {A} → Γ ∋ A → Δ ⊢ A}
--   → {σ† : ∀ {A} → Γ ∋ A → Δ ⊢ A}
--   → (∀ {A} → (x : Γ ∋ A) → σ x ~ σ† x)
--     ---------------------------------------------------------
--   → (∀ {A} {M M† : Γ ⊢ A} → M ~ M† → subst σ M ~ subst σ† M†)
-- ~subst ~σ (~` {x = x})  =  ~σ x
-- ~subst ~σ (~ƛ ~N)       =  ~ƛ (~subst (~exts ~σ) ~N)
-- ~subst ~σ (~L ~· ~M)    =  (~subst ~σ ~L) ~· (~subst ~σ ~M)
-- ~subst ~σ (~let ~M ~N)  =  ~let (~subst ~σ ~M) (~subst (~exts ~σ) ~N)

-- ~sub : ∀ {Γ A B} {N N† : Γ , B ⊢ A} {M M† : Γ ⊢ B}
--   → N ~ N†
--   → M ~ M†
--     -----------------------
--   → (N [ M ]) ~ (N† [ M† ])
-- ~sub {Γ} {A} {B} ~N ~M = ~subst {Γ , B} {Γ} ~σ {A} ~N
--   where
--   ~σ : ∀ {A} → (x : Γ , B ∋ A) → _ ~ _
--   ~σ Z      =  ~M
--   ~σ (S x)  =  ~`


-- data Leg {Γ A} (M† N : Γ ⊢ A) : Set where

--   leg : ∀ {N† : Γ ⊢ A}
--     → N ~ N†
--     → M† —→ N†
--       --------
--     → Leg M† N


-- sim : ∀ {Γ A} {M M† N : Γ ⊢ A}
--   → M ~ M†
--   → M —→ N
--     --------
--   → Leg M† N
-- sim (~L ~· ~M) (ξ-·₁ L→) with sim ~L L→
-- ... | leg ~L′ L†→                          = leg (~L′ ~· ~M) (ξ-·₁ L†→)
-- sim (~V ~· ~M) (ξ-·₂ VV M→) with sim ~M M→
-- ... | leg ~M′ M†→                          = leg (~V ~· ~M′) (ξ-·₂ (~val ~V VV) M†→)
-- sim ((~ƛ ~N) ~· ~V) (β-ƛ VV)               = leg (~sub ~N ~V) (β-ƛ (~val ~V VV))
-- sim (~let ~M ~N) (ξ-let M→) with sim ~M M→
-- ... | leg ~M′ M†→                          = leg (~let ~M′ ~N) (ξ-·₂ V-ƛ M†→)
-- sim (~let ~V ~N) (β-let VV) = leg (~sub ~N ~V) (β-ƛ (~val ~V VV))


-- data ULeg {Γ A} (M N† : Γ ⊢ A) : Set where

--   uleg : ∀ {N : Γ ⊢ A}
--     → N ~ N†
--     → M —→ N
--       ---------
--     → ULeg M N†


-- sim⁻¹ : ∀ {Γ A} {M M† N† : Γ ⊢ A}
--   → M ~ M†
--   → M† —→ N†
--     ---------
--   → ULeg M N†
-- sim⁻¹ (~L ~· ~M) (ξ-·₁ L†→) with sim⁻¹ ~L L†→
-- ... | uleg ~L′ L→ = uleg (~L′ ~· ~M) (ξ-·₁ L→)
-- sim⁻¹ (~V ~· ~M) (ξ-·₂ VL† M†→) with sim⁻¹ ~M M†→
-- ... | uleg ~M′ M→ = uleg (~V ~· ~M′) (ξ-·₂ (~val⁻¹ ~V VL†) M→)
-- sim⁻¹ ((~ƛ ~N) ~· ~V) (β-ƛ VV) = uleg (~sub ~N ~V) (β-ƛ (~val⁻¹ ~V VV))
-- sim⁻¹ (~let ~M ~N) (ξ-·₂ Vƛ M†→) with sim⁻¹ ~M M†→
-- ... | uleg ~M′ M→ = uleg (~let ~M′ ~N) (ξ-let M→)
-- sim⁻¹ (~let ~V ~N) (β-ƛ VV) = uleg (~sub ~N ~V) (β-let (~val⁻¹ ~V VV))

----------------------------------------------------------------------

