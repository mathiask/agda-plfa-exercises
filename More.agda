module plfa.More where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _*_)
open import Relation.Nullary using (¬_)

infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_
infixr 9 _`×_
infixr 9 _`⊎_

infix  5 ƛ_
infix  5 μ_
infixl 7 _·_
infixl 8 _`*_
infix  8 `suc_
infix  9 `_
infix  9 S_
infix  9 #_
infixr 8 _`∷_

data Type : Set where
  `ℕ    : Type
  _⇒_   : Type → Type → Type
  Nat   : Type
  _`×_  : Type → Type → Type
  _`⊎_  : Type → Type → Type
  `⊥    : Type
  `⊤    : Type
  `List : Type → Type

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

data _∋_ : Context → Type → Set where
  Z : ∀ {Γ A}
      ---------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ B
      ---------
    → Γ , A ∋ B


data _⊢_ : Context → Type → Set where

  -- variables

  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  -- functions

  ƛ_  :  ∀ {Γ A B}
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B

  -- naturals

  `zero : ∀ {Γ}
      ------
    → Γ ⊢ `ℕ

  `suc_ : ∀ {Γ}
    → Γ ⊢ `ℕ
      ------
    → Γ ⊢ `ℕ

  case : ∀ {Γ A}
    → Γ ⊢ `ℕ
    → Γ ⊢ A
    → Γ , `ℕ ⊢ A
      -----------
    → Γ ⊢ A

  -- fixpoint

  μ_ : ∀ {Γ A}
    → Γ , A ⊢ A
      ----------
    → Γ ⊢ A

  -- primitive numbers

  con : ∀ {Γ}
    → ℕ
      -------
    → Γ ⊢ Nat

  _`*_ : ∀ {Γ}
    → Γ ⊢ Nat
    → Γ ⊢ Nat
      -------
    → Γ ⊢ Nat

  -- let

  `let : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ , A ⊢ B
      ----------
    → Γ ⊢ B

  -- products

  `⟨_,_⟩ : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ ⊢ B
      -----------
    → Γ ⊢ A `× B

  `proj₁ : ∀ {Γ A B}
    → Γ ⊢ A `× B
      -----------
    → Γ ⊢ A

  `proj₂ : ∀ {Γ A B}
    → Γ ⊢ A `× B
      -----------
    → Γ ⊢ B

  -- alternative formulation of products

  case× : ∀ {Γ A B C}
    → Γ ⊢ A `× B
    → Γ , A , B ⊢ C
      --------------
    → Γ ⊢ C

  -- sums
  
  `inj₁ : ∀ {Γ A B}
    → Γ ⊢ A
      -----------
    → Γ ⊢ A `⊎ B

  `inj₂ : ∀ {Γ A B}
    → Γ ⊢ B
      -----------
    → Γ ⊢ A `⊎ B

  case⊎ : ∀ {Γ A B C}
    → Γ     ⊢ A `⊎ B
    → Γ , A ⊢ C
    → Γ , B ⊢ C
      --------------
    → Γ ⊢ C

  -- empty type
  
  case⊥ : ∀ {Γ A}
    → Γ ⊢ `⊥
      ------
    → Γ ⊢ A

  -- unit

  `tt : ∀ {Γ}
      -------
    → Γ ⊢ `⊤

  -- lists

  `[] : ∀ {Γ A}
      -----------
    → Γ ⊢ `List A

  _`∷_ : ∀ {Γ A}
    → Γ ⊢ A
    → Γ ⊢ `List A
      ------------
    → Γ ⊢ `List A

  caseL : ∀ {Γ A B}
    → Γ ⊢ `List A
    → Γ ⊢ B
    → Γ , A , `List A ⊢ B
      -------------------
    → Γ ⊢ B


lookup : Context → ℕ → Type
lookup (Γ , A) zero     =  A
lookup (Γ , _) (suc n)  =  lookup Γ n
lookup ∅       _        =  ⊥-elim impossible
  where postulate impossible : ⊥

count : ∀ {Γ} → (n : ℕ) → Γ ∋ lookup Γ n
count {Γ , _} zero     =  Z
count {Γ , _} (suc n)  =  S (count n)
count {∅}     _        =  ⊥-elim impossible
  where postulate impossible : ⊥

#_ : ∀ {Γ} → (n : ℕ) → Γ ⊢ lookup Γ n
# n  =  ` count n


ext : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ∋ A) → (∀ {A B} → Γ , A ∋ B → Δ , A ∋ B)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

rename : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ∋ A) → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
rename ρ (`zero)        =  `zero
rename ρ (`suc M)       =  `suc (rename ρ M)
rename ρ (case L M N)   =  case (rename ρ L) (rename ρ M) (rename (ext ρ) N)
rename ρ (μ N)          =  μ (rename (ext ρ) N)
rename ρ (con n)        =  con n
rename ρ (M `* N)       =  rename ρ M `* rename ρ N
rename ρ (`let M N)     = `let (rename ρ M) (rename (ext ρ) N)
rename ρ `⟨ M , N ⟩     = `⟨ rename ρ M , rename ρ N ⟩
rename ρ (`proj₁ L)     = `proj₁ (rename ρ L)
rename ρ (`proj₂ L)     = `proj₂ (rename ρ L)
rename ρ (case× L M)    = case× (rename ρ L) (rename (ext (ext ρ)) M)
rename ρ (`inj₁ M)      = `inj₁ (rename ρ M)
rename ρ (`inj₂ N)      = `inj₂ (rename ρ N)
rename ρ (case⊎ L M N)  = case⊎ (rename ρ L) (rename (ext ρ) M) (rename (ext ρ) N) 
rename ρ (case⊥ L)      = case⊥ (rename ρ L)
rename ρ (`tt)          = `tt
rename ρ (`[])          = `[]
rename ρ (H `∷ T)      = rename ρ H `∷ rename ρ T
rename ρ (caseL L M N) = caseL (rename ρ L) (rename ρ M) (rename (ext (ext ρ)) N)
 

exts : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A) → (∀ {A B} → Γ , A ∋ B → Δ , A ⊢ B)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)

subst : ∀ {Γ Δ} → (∀ {C} → Γ ∋ C → Δ ⊢ C) → (∀ {C} → Γ ⊢ C → Δ ⊢ C)
subst σ (` k)          =  σ k
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)
subst σ (`zero)        =  `zero
subst σ (`suc M)       =  `suc (subst σ M)
subst σ (case L M N)   =  case (subst σ L) (subst σ M) (subst (exts σ) N)
subst σ (μ N)          =  μ (subst (exts σ) N)
subst σ (con n)        =  con n
subst σ (M `* N)       =  subst σ M `* subst σ N
subst σ (`let M N)     =  `let (subst σ M) (subst (exts σ) N)
subst σ `⟨ M , N ⟩     =  `⟨ subst σ M , subst σ N ⟩
subst σ (`proj₁ L)     =  `proj₁ (subst σ L)
subst σ (`proj₂ L)     =  `proj₂ (subst σ L)
subst σ (case× L M)    =  case× (subst σ L) (subst (exts (exts σ)) M)
subst σ (`inj₁ M)      =  `inj₁ (subst σ M)
subst σ (`inj₂ N)      =  `inj₂ (subst σ N)
subst σ (case⊎ L M N)  =  case⊎ (subst σ L) (subst (exts σ) M) (subst (exts σ) N)
subst σ (case⊥ L)      =  case⊥ (subst σ L)
subst σ (`tt)          =  `tt
subst σ (`[])          = `[]
subst σ (H `∷ T)      = subst σ H `∷ subst σ T
subst σ (caseL L M N) = caseL (subst σ L) (subst σ M) (subst (exts (exts σ)) N)

substZero : ∀ {Γ}{A B} → Γ ⊢ A → Γ , A ∋ B → Γ ⊢ B
substZero V Z      =  V
substZero V (S x)  =  ` x

_[_] : ∀ {Γ A B}
  → Γ , A ⊢ B
  → Γ ⊢ A
    ---------
  → Γ ⊢ B
_[_] {Γ} {A} N V =  subst {Γ , A} {Γ} (substZero V) N

_[_][_] : ∀ {Γ A B C}
  → Γ , A , B ⊢ C
  → Γ ⊢ A
  → Γ ⊢ B
    -------------
  → Γ ⊢ C
_[_][_] {Γ} {A} {B} N V W =  subst {Γ , A , B} {Γ} σ N
  where
  σ : ∀ {C} → Γ , A , B ∋ C → Γ ⊢ C
  σ Z          =  W
  σ (S Z)      =  V
  σ (S (S x))  =  ` x


data Value : ∀ {Γ A} → Γ ⊢ A → Set where

  -- functions

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ N)

  -- naturals

  V-zero : ∀ {Γ}
      -----------------
    → Value (`zero {Γ})

  V-suc_ : ∀ {Γ} {V : Γ ⊢ `ℕ}
    → Value V
      --------------
    → Value (`suc V)

  -- primitives

  V-con : ∀ {Γ n}
      -----------------
    → Value (con {Γ} n)

  -- products

  V-⟨_,_⟩ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
    → Value V
    → Value W
      ----------------
    → Value `⟨ V , W ⟩

  -- sums

  V-inj₁ : ∀ {Γ A B} {V : Γ ⊢ A}
    → Value V
      --------------
    → Value (`inj₁ {Γ} {A} {B} V) 

  V-inj₂ : ∀ {Γ A B} {W : Γ ⊢ B}
    → Value W
      --------------
    → Value (`inj₂ {Γ} {A} {B} W) 

  -- unit
  V-⊤ : ∀ {Γ}
      ---------
    → Value {Γ} `tt

  -- list
  
  V-[] : ∀ {Γ A}
      -----------------------
    → Value {Γ} {`List A} `[]

  V-∷ : ∀ {Γ A} {V : Γ ⊢ A} {VS : Γ ⊢ `List A}
    → Value V
    → Value VS
      ---------------
    → Value (V `∷ VS)


infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  -- functions

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      ---------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      ---------------
    → V · M —→ V · M′

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {V : Γ ⊢ A}
    → Value V
      --------------------
    → (ƛ N) · V —→ N [ V ]

  -- naturals

  ξ-suc : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
    → M —→ M′
      -----------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {Γ A} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → L —→ L′
      -------------------------
    → case L M N —→ case L′ M N

  β-zero :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
      -------------------
    → case `zero M N —→ M

  β-suc : ∀ {Γ A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → Value V
      ----------------------------
    → case (`suc V) M N —→ N [ V ]

  -- fixpoint

  β-μ : ∀ {Γ A} {N : Γ , A ⊢ A}
      ----------------
    → μ N —→ N [ μ N ]

  -- primitive numbers

  ξ-*₁ : ∀ {Γ} {L L′ M : Γ ⊢ Nat}
    → L —→ L′
      -----------------
    → L `* M —→ L′ `* M

  ξ-*₂ : ∀ {Γ} {V M M′ : Γ ⊢ Nat}
    → Value V
    → M —→ M′
      -----------------
    → V `* M —→ V `* M′

  δ-* : ∀ {Γ c d}
      ---------------------------------
    → con {Γ} c `* con d —→ con (c * d)

  -- let

  ξ-let : ∀ {Γ A B} {M M′ : Γ ⊢ A} {N : Γ , A ⊢ B}
    → M —→ M′
      ---------------------
    → `let M N —→ `let M′ N

  β-let : ∀ {Γ A B} {V : Γ ⊢ A} {N : Γ , A ⊢ B}
    → Value V
      -------------------
    → `let V N —→ N [ V ]

  -- products

  ξ-⟨,⟩₁ : ∀ {Γ A B} {M M′ : Γ ⊢ A} {N : Γ ⊢ B}
    → M —→ M′
      -------------------------
    → `⟨ M , N ⟩ —→ `⟨ M′ , N ⟩

  ξ-⟨,⟩₂ : ∀ {Γ A B} {V : Γ ⊢ A} {N N′ : Γ ⊢ B}
    → Value V
    → N —→ N′
      -------------------------
    → `⟨ V , N ⟩ —→ `⟨ V , N′ ⟩

  ξ-proj₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A `× B}
    → L —→ L′
      ---------------------
    → `proj₁ L —→ `proj₁ L′

  ξ-proj₂ : ∀ {Γ A B} {L L′ : Γ ⊢ A `× B}
    → L —→ L′
      ---------------------
    → `proj₂ L —→ `proj₂ L′

  β-proj₁ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
    → Value V
    → Value W
      ----------------------
    → `proj₁ `⟨ V , W ⟩ —→ V

  β-proj₂ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
    → Value V
    → Value W
      ----------------------
    → `proj₂ `⟨ V , W ⟩ —→ W

  -- alternative formulation of products

  ξ-case× : ∀ {Γ A B C} {L L′ : Γ ⊢ A `× B} {M : Γ , A , B ⊢ C}
    → L —→ L′
      -----------------------
    → case× L M —→ case× L′ M

  β-case× : ∀ {Γ A B C} {V : Γ ⊢ A} {W : Γ ⊢ B} {M : Γ , A , B ⊢ C}
    → Value V
    → Value W
      ----------------------------------
    → case× `⟨ V , W ⟩ M —→ M [ V ][ W ]

  -- sums

  ξ-inj₁ : ∀ {Γ A B} {M M′ : Γ ⊢ A}
    → M —→ M′
      ---------------------
    → `inj₁ {B = B} M —→ `inj₁ M′

  ξ-inj₂ : ∀ {Γ A B} {N N′ : Γ ⊢ B}
    → N —→ N′
      ---------------------
    → `inj₂ {A = A} N —→ `inj₂ N′

  ξ-case⊎ : ∀ {Γ A B C} {L L′ : Γ ⊢ A `⊎ B} {M : Γ , A ⊢ C} {N : Γ , B ⊢ C}
    → L —→ L′
      ----------------------------
    → case⊎ L M N —→ case⊎ L′ M N

  β-inj₁ : ∀ {Γ A B C} {V : Γ ⊢ A} {M : Γ , A ⊢ C} {N : Γ , B ⊢ C}
    → Value V
      ----------------------
    → case⊎ (`inj₁ V) M N —→ M [ V ]

  β-inj₂ : ∀ {Γ A B C} {W : Γ ⊢ B} {M : Γ , A ⊢ C} {N : Γ , B ⊢ C}
    → Value W
      ----------------------
    → case⊎ (`inj₂ W) M N —→ N [ W ]

  -- empty type

  ξ-case⊥ : ∀ {Γ A } {L L′ : Γ ⊢ `⊥}
    → L —→ L′ 
      -------------------
    → case⊥ {A = A} L —→ case⊥ L′ 

  -- list

  ξ-∷₁ : ∀ {Γ A} {M M′ : Γ ⊢ A} {N : Γ ⊢ `List A}
    → M —→ M′
      ------------------
    → M `∷ N —→ M′ `∷ N

  ξ-∷₂ : ∀ {Γ A} {M : Γ ⊢ A} {N N′ : Γ ⊢ `List A}
    → N —→ N′
      ------------------
    → M `∷ N —→ M `∷ N′

  ξ-caseL : ∀ {Γ A B} {L L′ : Γ ⊢ `List A} {M : Γ ⊢ B} {N : Γ , A , `List A ⊢ B}
    → L —→ L′ 
      ---------------------------
    → caseL L M N —→ caseL L′ M N

  β-[] : ∀ {Γ A B} {M : Γ ⊢ B} {N : Γ , A , `List A ⊢ B}
      ---------------------------------------------------
    → caseL `[] M N —→ M

  β-∷ : ∀ {Γ A B} {V : Γ ⊢ A} {VS : Γ ⊢ `List A} {M : Γ ⊢ B} {N : Γ , A , `List A ⊢ B}
    → Value V
    → Value VS
      ------------------------------------
    → caseL (V `∷ VS) M N —→ N [ V ][ VS ]


infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : ∀ {Γ A} (M : Γ ⊢ A)
      ------
    → M —↠ M

  _—→⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L —→ M
    → M —↠ N
      ------
    → L —↠ N

begin_ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N


V¬—→ : ∀ {Γ A} {M N : Γ ⊢ A}
  → Value M
    ----------
  → ¬ (M —→ N)
V¬—→ (V-suc VM)   (ξ-suc M—→M′)          =  V¬—→ VM M—→M′
V¬—→ V-⟨ VM , _ ⟩ (ξ-⟨,⟩₁ M—→M′)        =  V¬—→ VM M—→M′
V¬—→ V-⟨ _ , VN ⟩ (ξ-⟨,⟩₂ _ N—→N′)      =  V¬—→ VN N—→N′
V¬—→ {A = A `⊎ B} (V-inj₁ VV) (ξ-inj₁ s) = V¬—→ VV s
V¬—→ {A = A `⊎ B} (V-inj₂ VW) (ξ-inj₂ s) = V¬—→ VW s
V¬—→ {A = `List A} (V-∷ VV VVS) (ξ-∷₁ s) = V¬—→ VV s
V¬—→ {A = `List A} (V-∷ VV VVS) (ξ-∷₂ s) = V¬—→ VVS s


data Progress {A} (M : ∅ ⊢ A) : Set where

  step : ∀ {N : ∅ ⊢ A}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

progress : ∀ {A}
  → (M : ∅ ⊢ A)
    -----------
  → Progress M
progress (` ())
progress (ƛ N)                              =  done V-ƛ
progress (L · M) with progress L
...    | step L—→L′                         =  step (ξ-·₁ L—→L′)
...    | done V-ƛ with progress M
...        | step M—→M′                     =  step (ξ-·₂ V-ƛ M—→M′)
...        | done VM                        =  step (β-ƛ VM)
progress (`zero)                            =  done V-zero
progress (`suc M) with progress M
...    | step M—→M′                         =  step (ξ-suc M—→M′)
...    | done VM                            =  done (V-suc VM)
progress (case L M N) with progress L
...    | step L—→L′                         =  step (ξ-case L—→L′)
...    | done V-zero                        =  step β-zero
...    | done (V-suc VL)                    =  step (β-suc VL)
progress (μ N)                              =  step β-μ
progress (con n)                            =  done V-con
progress (L `* M) with progress L
...    | step L—→L′                         =  step (ξ-*₁ L—→L′)
...    | done V-con with progress M
...        | step M—→M′                     =  step (ξ-*₂ V-con M—→M′)
...        | done V-con                     =  step δ-*
progress (`let M N) with progress M
...    | step M—→M′                         =  step (ξ-let M—→M′)
...    | done VM                            =  step (β-let VM)
progress `⟨ M , N ⟩ with progress M
...    | step M—→M′                         =  step (ξ-⟨,⟩₁ M—→M′)
...    | done VM with progress N
...        | step N—→N′                     =  step (ξ-⟨,⟩₂ VM N—→N′)
...        | done VN                        =  done (V-⟨ VM , VN ⟩)
progress (`proj₁ L) with progress L
...    | step L—→L′                         =  step (ξ-proj₁ L—→L′)
...    | done (V-⟨ VM , VN ⟩)               =  step (β-proj₁ VM VN)
progress (`proj₂ L) with progress L
...    | step L—→L′                         =  step (ξ-proj₂ L—→L′)
...    | done (V-⟨ VM , VN ⟩)               =  step (β-proj₂ VM VN)
progress (case× L M) with progress L
...    | step L—→L′                         =  step (ξ-case× L—→L′)
...    | done (V-⟨ VM , VN ⟩)               =  step (β-case× VM VN)
progress (`inj₁ M) with progress M
...    | step s                             = step (ξ-inj₁ s)
...    | done VM                            = done (V-inj₁ VM)
progress (`inj₂ N) with progress N
...    | step s                             = step (ξ-inj₂ s)
...    | done VN                            = done (V-inj₂ VN)
progress (case⊎ L M N) with progress L
...    | step s                             = step (ξ-case⊎ s)
...    | done (V-inj₁ V)                    = step (β-inj₁ V)
...    | done (V-inj₂ W)                    = step (β-inj₂ W)
progress (case⊥ L) with progress L
...    | step s                             = step (ξ-case⊥ s)
progress `tt                                = done V-⊤
progress `[]                                = done V-[]
progress (H `∷ T) with progress H
...    | step s                             = step (ξ-∷₁ s)
...    | done VH with progress T
...       | step s                          = step (ξ-∷₂ s)
...       | done VT                         = done (V-∷ VH VT)
progress (caseL L M N) with progress L
...    | step s                             = step (ξ-caseL s)
...       | done V-[]                       = step β-[]
...       | done (V-∷ VL VVS)               = step (β-∷ VL VVS)


record Gas : Set where
  constructor gas
  field
    amount : ℕ

data Finished {Γ A} (N : Γ ⊢ A) : Set where

   done :
       Value N
       ----------
     → Finished N

   out-of-gas :
       ----------
       Finished N

data Steps : ∀ {A} → ∅ ⊢ A → Set where

  steps : ∀ {A} {L N : ∅ ⊢ A}
    → L —↠ N
    → Finished N
      ----------
    → Steps L

eval : ∀ {A}
  → Gas
  → (L : ∅ ⊢ A)
    -----------
  → Steps L
eval (gas zero)    L                     =  steps (L ∎) out-of-gas
eval (gas (suc m)) L with progress L
... | done VL                            =  steps (L ∎) (done VL)
... | step {M} L—→M with eval (gas m) M
...    | steps M—↠N fin                  =  steps (L —→⟨ L—→M ⟩ M—↠N) fin

----------------------------------------------------------------------

cube : ∅ ⊢ Nat ⇒ Nat
cube = ƛ (# 0 `* # 0 `* # 0)

-- eval (gas 100) (cube · con 2)

exp10 : ∅ ⊢ Nat ⇒ Nat
exp10 = ƛ (`let (# 0 `* # 0)
            (`let (# 0 `* # 0)
              (`let (# 0 `* # 2)
                (# 0 `* # 0))))

-- eval (gas 100) (exp10 · con 2)

swap× : ∀ {A B} → ∅ ⊢ A `× B ⇒ B `× A
swap× = ƛ `⟨ `proj₂ (# 0) , `proj₁ (# 0) ⟩

-- eval (gas 100) (swap× · `⟨ con 42 , `zero ⟩)

swap×-case : ∀ {A B} → ∅ ⊢ A `× B ⇒ B `× A
swap×-case = ƛ case× (# 0) `⟨ # 0 , # 1 ⟩

-- eval (gas 100) (swap×-case · `⟨ con 42 , `zero ⟩)

swap⊎ : {A B : Type} → ∅ ⊢ A `⊎ B ⇒ B `⊎ A
swap⊎ = ƛ case⊎ (# 0) (`inj₂ (# 0)) (`inj₁ (# 0))

-- eval (gas 100) (swap⊎ · (`inj₁ (con 42)))
-- eval (gas 100) (swap⊎ · (`inj₂ (con 42)))

-- We can now "prove" ∅ ⊢ `⊥ ...
non-terminating-absurdity : ∅ ⊢ `⊥
non-terminating-absurdity = μ (` Z)
-- ... but there are no values of this Type:

⊥-consistency : ∀ {M : ∅ ⊢ `⊥} → ¬ Value M
⊥-consistency ()

to⊎⊥ : ∀ {A : Type} → ∅ ⊢ A ⇒ A `⊎ `⊥
to⊎⊥ = ƛ (`inj₁ (# 0))

⊥⊎to : ∀ {A : Type} → ∅ ⊢ A ⇒ `⊥ `⊎ A 
⊥⊎to = ƛ (`inj₂ (# 0))

-- eval (gas 100) (to⊎⊥ · (con 42))
-- eval (gas 100) (⊥⊎to · (con 42))

from⊎⊥ : ∀ {A : Type} → ∅ ⊢ A `⊎ `⊥ ⇒ A
from⊎⊥ = ƛ (case⊎ (# 0) (# 0) (case⊥ (# 0)))

⊥⊎from : ∀ {A : Type} → ∅ ⊢ `⊥ `⊎ A ⇒ A
⊥⊎from = ƛ (case⊎ (# 0) (case⊥ (# 0)) (# 0))

-- eval (gas 100) (from⊎⊥ · `inj₁ (con 42))
-- eval (gas 100) (⊥⊎from · `inj₂ (con 42))
-- eval (gas 100) (from⊎⊥ · (to⊎⊥ · (con 42)))
-- eval (gas 100) (to⊎⊥ · (from⊎⊥ · `inj₁ (con 42)))

to×⊤ : ∀ {A : Type} → ∅ ⊢ A ⇒ A `× `⊤
to×⊤ = ƛ `⟨ # 0 , `tt ⟩

from×⊤ : ∀ {A : Type} → ∅ ⊢ A `× `⊤ ⇒ A
from×⊤ = ƛ (`proj₁ (# 0))

-- eval (gas 100) (from×⊤ · (to×⊤ · (con 42)))

mapL : {A B : Type} → ∅ ⊢ (A ⇒ B) ⇒ `List A ⇒ `List B
mapL = μ ƛ ƛ caseL (# 0) `[] ((# 3 · # 1) `∷ (# 4 · # 3 · # 0))

-- map "square"
-- eval (gas 100) (mapL · (ƛ # 0 `* # 0) · (con 1 `∷ con 2 `∷ con 3 `∷ con 4 `∷ con 5 `∷ `[]))


----------------------------------------------------------------------

-- [X] primitive numbers
-- [X] let bindings
-- [X] products
-- [X] an alternative formulation of products
-- [X] sums
-- [X] unit type
-- [ ] an alternative formulation of unit type
-- [X] empty type
-- [X] lists
