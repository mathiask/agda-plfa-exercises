module plfa.Bisimulation where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl ; sym; cong; cong₂)
open import plfa.More

infix  4 _~_
infix  5 ~ƛ_
infix  7 _~·_

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


-- To show the equivalence of _~_ and † we need to define the relevant
-- fragment of the language:

data †relevant : ∀ {Γ A} → Γ ⊢ A → Set where

  relevant~ : ∀ {Γ A} {x : Γ ∋ A}
      ---------------
    → †relevant (` x)

  relevantƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
    → †relevant N
      ---------------
    → †relevant (ƛ N)

  relevant· : ∀ {Γ A B} {L : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → †relevant L
    → †relevant M
      -----------------
    → †relevant (L · M)

  relevant-let : ∀ {Γ A B} {M : Γ ⊢ A} {N : Γ , A ⊢ B}
    → †relevant M
    → †relevant N
      --------------------
    → †relevant (`let M N)


† : ∀ {Γ A} → (M : Γ ⊢ A) → {†relevant M} → (Γ ⊢ A)
† (` x) {relevant~} = ` x
† (ƛ M) {relevantƛ RM} = ƛ † M {RM}
† (M · N) {relevant· RM RN} = († M {RM}) · † N {RN}
† (`let M N) {relevant-let RM RN} = (ƛ † N {RN}) · † M {RM}

≡⇒~ : ∀ {Γ A} (M N : Γ ⊢ A) → {RM : †relevant M} → († M {RM} ≡ N) → (M ~ N)
≡⇒~ (` x) (` .x) {relevant~} refl = ~`
≡⇒~ (ƛ M) (ƛ .(† M)) {relevantƛ RM} refl = ~ƛ (≡⇒~ M († M) refl)
≡⇒~ (M · N) (.(† M) · .(† N)) {relevant· RM RM₁} refl =
    (≡⇒~ M († M) refl) ~· (≡⇒~ N († N) refl)
≡⇒~ (`let M N) (.(ƛ † N) · .(† M)) {relevant-let RM RN} refl =
    ~let (≡⇒~ M († M) refl) (≡⇒~ N († N) refl)

~⇒≡ : ∀ {Γ A} (M N : Γ ⊢ A) → {RM : †relevant M} → (M ~ N) → († M {RM} ≡ N)
~⇒≡ (` x) (` .x) {relevant~} ~` = refl
~⇒≡ (ƛ M) (ƛ N) {relevantƛ RM} (~ƛ M~N) = cong ƛ_ (~⇒≡ M N M~N)
~⇒≡ (M · N) (O · P) {relevant· RM RN} (M~O ~· N~P) = cong₂ _·_ (~⇒≡ M O M~O) ((~⇒≡ N P N~P))
~⇒≡ (`let M N) ((ƛ N′) · M′) {relevant-let RM RN} (~let M~M′ N~N′)
    = cong₂ _·_  (cong ƛ_ (~⇒≡ N N′ N~N′)) (~⇒≡ M M′ M~M′)
