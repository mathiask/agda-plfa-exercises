module plfa.Lambda where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.List using (List; _∷_; [])

open import plfa.Isomorphism using (_≲_; _≃_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst)
open import Data.Product using (_×_; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

Id : Set
Id = String

infix  5 ƛ_⇒_
infix  5 μ_⇒_
infixl 7 _·_
infix  8 `suc_
infix  9 `_

data Term : Set where
  `_                   : Id → Term
  ƛ_⇒_                 : Id → Term → Term
  _·_                  : Term → Term → Term
  `zero                : Term
  `suc_                : Term → Term
  case_[zero⇒_|suc_⇒_] : Term → Term → Id → Term → Term
  μ_⇒_                 : Id → Term → Term

two : Term
two = `suc `suc `zero

three : Term
tree = `suc two

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
         case ` "m"
         [zero⇒ ` "n"
         |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]

twoᶜ : Term
twoᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

threeᶜ : Term
threeᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · (` "s" · ` "z"))


plusᶜ : Term
plusᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
  ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc ` "n"


mul : Term
mul = μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
         case ` "m"
         [zero⇒ `zero
         |suc "m" ⇒ plus · ` "n" · (` "*" · ` "m" · ` "n") ]

mulᶜ : Term
mulᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
  ` "m" · (` "n" · ` "s") · ` "z"

data Value : Term → Set where
  V-ƛ : ∀ {x N}
        ---------------
      → Value (ƛ x ⇒ N)

  V-zero :
    -----------
    Value `zero

  V-suc : ∀ {V}
    → Value V
      --------------
    → Value (`suc V)


infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _ = V
... | no  _ = ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _ = ƛ x ⇒ N
... | no  _ = ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ] = L [ y := V ] · M [ y := V ]
`zero [ y := V ] = `zero
(`suc M) [ y := V ] = `suc (M [ y := V ])
case L [zero⇒ M |suc x ⇒ N ] [ y := V ] with x ≟ y
... | yes _ = case (L [ y := V ]) [zero⇒ (M [ y := V ]) |suc x ⇒ N ]
... | no  _ = case (L [ y := V ]) [zero⇒ (M [ y := V ]) |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _ = μ x ⇒ N
... | no  _ = μ x ⇒ N [ y := V ]


-- Examples
_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] ≡ ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
_ = refl

_ : (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] ≡ sucᶜ · (sucᶜ · `zero)
_ = refl

_ : (ƛ "x" ⇒ ` "y") [ "y" := `zero ] ≡ ƛ "x" ⇒ `zero
_ = refl

_ : (ƛ "x" ⇒ ` "x") [ "x" := `zero ] ≡ ƛ "x" ⇒ ` "x"
_ = refl

_ : (ƛ "y" ⇒ ` "y") [ "x" := `zero ] ≡ ƛ "y" ⇒ ` "y"
_ = refl

_ : (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ ` "x")) [ "x" := `zero ] ≡ (ƛ "y" ⇒ `zero · (ƛ "x" ⇒ ` "x"))
_ = refl


_[_:=_]′ : Term → Id → Term → Term
subst-if-not-bound : Term → Id → Id → Term → Term

(` x) [ y := V ]′ with x ≟ y
... | yes _ = V
... | no  _ = ` x
(ƛ x ⇒ N) [ y := V ]′ = ƛ x ⇒ (subst-if-not-bound N x y V)
(L · M) [ y := V ]′ = L [ y := V ]′ · M [ y := V ]′
`zero [ y := V ]′ = `zero
(`suc M) [ y := V ]′ = `suc (M [ y := V ]′)
case L [zero⇒ M |suc x ⇒ N ] [ y := V ]′
  = case (L [ y := V ]′) [zero⇒ (M [ y := V ]′) |suc x ⇒ (subst-if-not-bound N x y V) ]
(μ x ⇒ N) [ y := V ]′ = μ x ⇒ (subst-if-not-bound N x y V)

subst-if-not-bound N x y V  with x ≟ y
subst-if-not-bound N x y V | yes _ = N
subst-if-not-bound N x y V | no  _ = N [ y := V ]′

_ : (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ ` "x")) [ "x" := `zero ]′ ≡ (ƛ "y" ⇒ `zero · (ƛ "x" ⇒ ` "x"))
_ = refl

----------------------------------------------------------------------

infix 4 _—→_

data _—→_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
      -----------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M —→ M′
      -----------------
    → V · M —→ V · M′

  β-ƛ : ∀ {x N V}
    → Value V
      ------------------------------
    → (ƛ x ⇒ N) · V —→ N [ x := V ]

  ξ-suc : ∀ {M M′}
    → M —→ M′
      ------------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {x L L′ M N}
    → L —→ L′
      -----------------------------------------------------------------
    → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]

  β-zero : ∀ {x M N}
      ----------------------------------------
    → case `zero [zero⇒ M |suc x ⇒ N ] —→ M

  β-suc : ∀ {x V M N}
    → Value V
      ---------------------------------------------------
    → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]

  β-μ : ∀ {x M}
      ------------------------------
    → μ x ⇒ M —→ M [ x := μ x ⇒ M ]


_ : (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")  —→ (ƛ "x" ⇒ ` "x")
_ =  β-ƛ V-ƛ

_ : (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")
  —→ (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")
_ = ξ-·₁ (β-ƛ V-ƛ)

_ : twoᶜ · sucᶜ · `zero —→ (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
_ = ξ-·₁ (β-ƛ V-ƛ)


infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : Term → Term → Set where
  _∎ : ∀ M
       ------
     → M —↠ M

  _—→⟨_⟩_ : ∀ L {M N}
          → L —→ M
          → M —↠ N
            ---------
          → L —↠ N

begin_ : ∀ {M N}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N

—↠-refl : ∀ {M} → M —↠ M
—↠-refl {M} = M ∎

—↠-trans : ∀ {M N P} → M —↠ N → N —↠ P → M —↠ P
—↠-trans (M ∎) N—↠P = N—↠P
—↠-trans (L —→⟨ L—→M ⟩ M—↠N) N—↠P = L —→⟨ L—→M ⟩ —↠-trans M—↠N N—↠P


data _—↠′_ : Term → Term → Set where

  step′ : ∀ {M N}
    → M —→ N
      -------
    → M —↠′ N

  refl′ : ∀ {M}
      -------
    → M —↠′ M

  trans′ : ∀ {L M N}
    → L —↠′ M
    → M —↠′ N
      -------
    → L —↠′ N

—↠≲—↠′ : ∀ {L M} → (L —↠ M) ≲ (L —↠′  M)
—↠≲—↠′ {L} {M} = record
  { to = to
  ; from = from
  ; from∘to = from∘to
  } where
    to : ∀ {L M} → L —↠ M → L —↠′ M
    to (_ ∎) = refl′
    to (_ —→⟨ L—→P ⟩ P—↠M) = trans′ (step′ L—→P) (to P—↠M)

    from : ∀ {L M} → L —↠′ M → L —↠ M
    from {L} {M} (step′ L—→M) = L —→⟨ L—→M ⟩ M ∎
    from {L} refl′ = —↠-refl
    from (trans′ L—↠′P P—↠′M) = —↠-trans (from L—↠′P) (from P—↠′M)

    from∘to : ∀ {L M} → (L—↠M : L —↠ M) → from (to L—↠M) ≡ L—↠M
    from∘to (M ∎) = refl
    from∘to (L —→⟨ L—→M ⟩ M—↠N) rewrite from∘to M—↠N = refl

-- It is not an isomorphism as the derivation in the ' case it not unique.

----------------------------------------------------------------------

—→-¬value : ∀ L {M} → L —→ M → ¬ Value L
—→-¬value (`suc L) (ξ-suc L—→M) (V-suc ValueL)
  = —→-¬value L L—→M ValueL

deterministic : ∀ L {M N}
  → L —→ M
  → L —→ N
    ------
  → M ≡ N
deterministic (L · L₁) (ξ-·₁ L—→M) (ξ-·₁ L—→N) rewrite deterministic L L—→M L—→N
  = refl
deterministic (L · L₁) (ξ-·₁ L—→M) (ξ-·₂ V L—→N)
  = ⊥-elim (—→-¬value L L—→M V)
deterministic (L · L₁) (ξ-·₂ V L—→M) (ξ-·₁ L—→N)
  = ⊥-elim (—→-¬value L L—→N V)
deterministic (M · L) (ξ-·₂ V L—→M) (ξ-·₂ V′ L—→N) rewrite deterministic L L—→M L—→N
  = refl
deterministic (.(ƛ _ ⇒ _) · L) (ξ-·₂ _ L—→M) (β-ƛ ValueL)
  = ⊥-elim (—→-¬value L L—→M ValueL)
deterministic (.(ƛ _ ⇒ _) · L) (β-ƛ ValueL) (ξ-·₂ _ L—→N)
  = ⊥-elim (—→-¬value L L—→N ValueL)
deterministic (.(ƛ _ ⇒ _) · L) (β-ƛ _) (β-ƛ _) = refl
deterministic (`suc L) (ξ-suc L—→M) (ξ-suc L—→N) rewrite deterministic L L—→M L—→N
  = refl
deterministic case L [zero⇒ P |suc x ⇒ Q ] (ξ-case case—→M) (ξ-case case—→N)
  rewrite deterministic L case—→M case—→N
  = refl
deterministic case (`suc V) [zero⇒ P |suc x ⇒ Q ] (ξ-case case—→M) (β-suc ValueV)
  with case—→M
... | ξ-suc V—→M′ = ⊥-elim ((—→-¬value V V—→M′) ValueV)
deterministic case .`zero [zero⇒ P |suc x ⇒ Q ] β-zero β-zero
  = refl
deterministic case (`suc V) [zero⇒ P |suc x ⇒ Q ] (β-suc ValueV) (ξ-case case—→N)
  with case—→N
... | ξ-suc V—→N′ = ⊥-elim ((—→-¬value V V—→N′) ValueV)
deterministic case .(`suc _) [zero⇒ P |suc x ⇒ Q ] (β-suc x₁) (β-suc x₂)
  = refl
deterministic (μ x ⇒ L) β-μ β-μ = refl

-- Deterministic relations trivially satisfy "diamond" ...

diamond : ∀ {L M N} →
    ((L —→ M) × (L —→ N))
    --------------------
  → ∃[ P ] ((M —↠ P) × (N —↠ P))
diamond {L} {M} ⟨ L—→M , L—→N ⟩ with deterministic L L—→M  L—→N
diamond {L} {M} ⟨ L—→M , L—→N ⟩ | refl
  = ⟨ M , ⟨ M ∎ , M ∎ ⟩ ⟩

--- ... and "diamond" implies confluence. But this is not that easy to prove...

-- confluence : ∀ {L M N}
--   → ((L —↠ M) × (L —↠ N))
--     ---------------------------
--   → ∃[ P ]((M —↠ P) × (N —↠ P))

-- confluence {.M} {M} ⟨ M ∎ , .M ∎ ⟩ = ⟨ M , ⟨ (M ∎) , (M ∎) ⟩ ⟩
-- confluence {.M} {M} {N} ⟨ M ∎ , .M —→⟨ M—→P ⟩ P—↠N ⟩
--   = ⟨ N , ⟨ M —→⟨ M—→P ⟩ P—↠N , N ∎ ⟩ ⟩
-- confluence {L} {M} {N} ⟨ L —→⟨ L—→P ⟩ P—↠M , .L ∎ ⟩
--   = ⟨ M , ⟨ (M ∎) , (L —→⟨ L—→P ⟩ P—↠M) ⟩ ⟩
-- confluence {L} {M} {N} ⟨ L —→⟨ L—→P ⟩ P—↠M , L —→⟨ L—→Q ⟩ Q—↠N ⟩
--   = {!!}

----------------------------------------------------------------------

one : Term
one = `suc `zero

_ : plus · one · one —↠ two
_ =
  begin
    plus · one · one
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · one · one
  —→⟨ ξ-·₁ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ "n" ⇒
      case one [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · one
  —→⟨ β-ƛ (V-suc V-zero) ⟩
    case one [zero⇒ one |suc "m" ⇒ `suc (plus · ` "m" · one) ]
  —→⟨ β-suc V-zero ⟩
    `suc (plus · `zero · one)
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc ((ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · `zero · one)
  —→⟨ ξ-suc (ξ-·₁ (β-ƛ V-zero)) ⟩
    `suc ((ƛ "n" ⇒
      case `zero [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
         · one)
  —→⟨ ξ-suc (β-ƛ (V-suc V-zero)) ⟩
    `suc (case `zero [zero⇒ one |suc "m" ⇒ `suc (plus · ` "m" · one) ])
  —→⟨ ξ-suc β-zero ⟩
    `suc one
  ∎

----------------------------------------------------------------------

infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type

infixl 5 _,_∶_

data Context : Set where
  ∅ : Context
  _,_∶_ : Context → Id → Type → Context

Context-≃ : Context ≃ List (Id × Type)
Context-≃ = record
  { to = to
  ; from = from
  ; from∘to = from∘to
  ; to∘from = to∘from
  }
  where
  to : Context → List (Id × Type)
  to ∅ = []
  to (ctx , x ∶ t) = ⟨ x , t ⟩ ∷ (to ctx)

  from : List (Id × Type) → Context
  from [] = ∅
  from (⟨ x , t ⟩ ∷ xs) = from xs , x ∶ t

  from∘to : (ctx : Context) → from (to ctx) ≡ ctx
  from∘to ∅ = refl
  from∘to (ctx , x ∶ t) rewrite from∘to ctx = refl

  to∘from : (xs : List (Id × Type)) → to (from xs) ≡ xs
  to∘from [] = refl
  to∘from (x ∷ xs) rewrite to∘from xs = refl


infix 4 _∋_∶_

data _∋_∶_ : Context → Id → Type → Set where
  Z : ∀ {Γ x A}
      -----------------
    → Γ , x ∶ A ∋ x ∶ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ∶ A
      -----------------
    → Γ , y ∶ B ∋ x ∶ A

infix 4 _⊢_∶_

data _⊢_∶_ : Context → Term → Type → Set where
  -- Axiom
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ∶ A
      -----------
    → Γ ⊢ ` x ∶ A

  -- ⇒-I
  ⊢ƛ : ∀ {Γ x N A B}
     → Γ , x ∶ A ⊢ N ∶ B
       -----------------
     → Γ ⊢ ƛ x ⇒ N ∶ A ⇒ B

  -- ⇒-E
  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ∶ A ⇒ B
    → Γ ⊢ M ∶ A
      -------------
    → Γ ⊢ L · M ∶ B

  -- ℕ-I₁
  ⊢zero : ∀ {Γ}
      --------------
    → Γ ⊢ `zero ∶ `ℕ

  -- ℕ-I₂
  ⊢suc : ∀ {Γ M }
    → Γ ⊢ M ∶ `ℕ
      ---------------
    → Γ ⊢ `suc M ∶ `ℕ

  -- ℕ-E
  ⊢-case : ∀ {Γ L M x N A}
    → Γ ⊢ L ∶ `ℕ
    → Γ ⊢ M ∶ A
    → Γ , x ∶ `ℕ ⊢ N ∶ A
      -------------------------------------
    → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ∶ A

  ⊢μ : ∀ {Γ x M A}
    → Γ , x ∶ A ⊢ M ∶ A
      -----------------
    → Γ ⊢ μ x ⇒ M ∶ A


_≠_ : ∀ (x y : Id) → x ≢ y
x ≠ y with x ≟ y
...        | no x≢y = x≢y
...        | yes _  = ⊥-elim impossible
  where postulate impossible : ⊥


Ch : Type → Type
Ch A = (A ⇒ A) ⇒ A ⇒ A

⊢twoᶜ : ∀ {Γ A} → Γ ⊢ twoᶜ ∶ Ch A
⊢twoᶜ = ⊢ƛ (⊢ƛ (⊢` ∋s · (⊢` ∋s · ⊢` ∋z)))
  where
  ∋s = S ("s" ≠ "z") Z
  ∋z = Z

⊢two : ∀ {Γ} → Γ ⊢ two ∶ `ℕ
⊢two = ⊢suc (⊢suc ⊢zero)

⊢plus : ∀ {Γ} → Γ ⊢ plus ∶ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢plus = ⊢μ (⊢ƛ (⊢ƛ (⊢-case (⊢` (S ("m" ≠ "n") Z))
  (⊢` Z)
  (⊢suc (((⊢` (S ("+" ≠ "m") (S ("+" ≠ "n") (S ("+" ≠ "m") Z))))
    · ⊢` Z) · ⊢` (S ("n" ≠ "m") Z))))))

⊢2+2 : ∅ ⊢ plus · two · two ∶ `ℕ
⊢2+2 = ⊢plus · ⊢two · ⊢two

⊢plusᶜ : ∀ {Γ A} → Γ  ⊢ plusᶜ ∶ Ch A ⇒ Ch A ⇒ Ch A
⊢plusᶜ {Γ} {A} = ⊢ƛ (⊢ƛ (⊢ƛ (⊢ƛ ((⊢` (S ("m" ≠ "z") (S ("m" ≠ "s") (S ("m" ≠ "n") Z)))
 · ⊢` (S ("s" ≠ "z") Z))
 · (((⊢` (S ("n" ≠ "z") (S ("n" ≠ "s") Z))) · ⊢` (S ("s" ≠ "z") Z)) · ⊢` Z)))))

⊢sucᶜ : ∅ ⊢ sucᶜ ∶ `ℕ ⇒ `ℕ
⊢sucᶜ = ⊢ƛ (⊢suc (⊢` Z))

⊢2+2ᶜ : ∅ ⊢ plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero ∶ `ℕ
⊢2+2ᶜ = ⊢plusᶜ · ⊢twoᶜ · ⊢twoᶜ · ⊢sucᶜ · ⊢zero


∋-injective : ∀ {Γ x A B} → Γ ∋ x ∶ A → Γ ∋ x ∶ B → A ≡ B
∋-injective Z Z = refl
∋-injective Z (S x b) = ⊥-elim (x refl)
∋-injective (S x a) Z = ⊥-elim (x refl)
∋-injective (S _ a) (S _ b) = ∋-injective a b

nope₁ : ∀ {A} → ¬ (∅ ⊢ `zero · `suc `zero ∶ A)
nope₁ (() · _)

nope₂ : ∀ {A} → ¬ (∅ ⊢ ƛ "x" ⇒ ` "x" · ` "x" ∶ A)
nope₂ (⊢ƛ (⊢` x · ⊢` x₁)) = contradiction (∋-injective x x₁)
  where
  contradiction : ∀ {A B} → ¬ (A ⇒ B ≡ A)
  contradiction ()

q1 : ∅ , "y" ∶ `ℕ ⇒ `ℕ , "x" ∶ `ℕ ⊢ ` "y" · ` "x" ∶ `ℕ
q1 = (⊢` (S ("y" ≠ "x") Z)) · ⊢` Z

q2 : ∀ {A} → ¬ (∅ , "y" ∶ `ℕ ⇒ `ℕ , "x" ∶ `ℕ ⊢ ` "x" · ` "y" ∶ A)
q2 (⊢` x · ⊢` x₁) = contradiction (∋-injective x xN)
  where
  xN : ∅ , "y" ∶ `ℕ ⇒ `ℕ , "x" ∶ `ℕ ∋ "x" ∶ `ℕ
  xN = Z
  contradiction : ∀ {A B} → ¬ (A ⇒ B ≡ `ℕ)
  contradiction ()

q3 : ∅ , "y" ∶ `ℕ ⇒ `ℕ ⊢ ƛ "x" ⇒ ` "y" · ` "x" ∶ `ℕ ⇒ `ℕ
q3 = ⊢ƛ ((⊢` (S ("y" ≠ "x") Z)) · (⊢` Z))

qq1 : ∀ {A B} → ¬ (∅ , "x" ∶ A ⊢ ` "x" · ` "x" ∶ B)
qq1 (⊢` x · ⊢` x₁) = contradiction (∋-injective x x₁)
  where
  contradiction : ∀ {A B} → ¬ (A ⇒ B ≡ A)
  contradiction ()

qq2 : ∅ , "x" ∶ `ℕ ⇒ `ℕ , "y" ∶ `ℕ ⇒ `ℕ ⊢
  ƛ "z" ⇒ ` "x" · (` "y" · ` "z") ∶ `ℕ ⇒ `ℕ
qq2 = ⊢ƛ ((⊢` (S ("x" ≠ "z") (S ("x" ≠ "y") Z)))
  · (⊢` (S ("y" ≠ "z") Z) · ⊢` Z))

mul-type : ∀ {Γ} → Γ ⊢ mul ∶ `ℕ ⇒ `ℕ ⇒ `ℕ
mul-type = ⊢μ (⊢ƛ (⊢ƛ (⊢-case (⊢` (S ("m" ≠ "n") Z))
 ⊢zero
 ((⊢plus · ⊢` (S ("n" ≠ "m") Z))
 · (((⊢` (S ("*" ≠ "m") (S ("*" ≠ "n") (S ("*" ≠ "m") Z))))
 · (⊢` Z)) · (⊢` (S ("n" ≠ "m") Z)))))))

mulᶜ-type : ∀ {Γ A} → Γ  ⊢ mulᶜ ∶ Ch A ⇒ Ch A ⇒ Ch A
mulᶜ-type = ⊢ƛ (⊢ƛ (⊢ƛ (⊢ƛ (((⊢` (S ("m" ≠ "z") (S ("m" ≠ "s") (S ("m" ≠ "n") Z))))
          · ((⊢` (S ("n" ≠ "z") (S ("n" ≠ "s") Z)))
          · (⊢` (S ("s" ≠ "z") Z))))
  · (⊢` Z)))))

--
