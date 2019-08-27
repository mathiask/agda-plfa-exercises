module plfa.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; subst)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_)
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

----------------------------------------------------------------------

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  even-zero : even zero
  even-suc : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ} → even n → odd (suc n)

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (     m * 2 ≡  n)
odd-∃ :  ∀ {n : ℕ} → odd n  → ∃[ m ] ( 1 + m * 2 ≡  n)

even-∃ even-zero = ⟨ zero , refl ⟩
even-∃ (even-suc o) with odd-∃ o
...                 | ⟨ m , refl ⟩ = ⟨ suc m , refl ⟩

odd-∃ (odd-suc e) with even-∃ e
...               | ⟨ m , refl ⟩ = ⟨ m , refl ⟩

∃-even : ∀ {n : ℕ} → ∃[ m ] (     m * 2 ≡  n) → even n
∃-odd :  ∀ {n : ℕ} → ∃[ m ] ( 1 + m * 2 ≡  n) → odd n

∃-even ⟨ zero , refl ⟩ = even-zero
∃-even ⟨ suc m , refl ⟩ = even-suc (∃-odd ⟨ m , refl ⟩)

∃-odd ⟨ m , refl ⟩ = odd-suc (∃-even ⟨ m , refl ⟩)

∃-even′ : ∀ {n : ℕ} → ∃[ m ] (     2 * m ≡ n) → even n
∃-odd′ :  ∀ {n : ℕ} → ∃[ m ] ( 1 + 2 * m ≡ n) → odd n

-- the harder versions with 2*_ on the left:
postulate +-zero : (n : ℕ) → n + zero ≡ n
postulate +-suc : (m n : ℕ) → m + suc n ≡ suc(m + n)

n*2≡n+n : ∀ (n : ℕ) → n * 2 ≡ n + n
n*2≡n+n zero = refl
n*2≡n+n (suc n) = cong suc e where
  e : suc (n * 2) ≡ n + suc n
  e rewrite +-suc n n = cong suc (n*2≡n+n n)

∃-even′ ⟨ zero , refl ⟩ = even-zero
∃-even′ ⟨ suc m , refl ⟩ = even-suc (∃-odd ⟨ m , e ⟩) where
  e : 1 + m * 2 ≡ m + 1 * suc m
  e rewrite +-zero m | +-suc m m = cong suc (n*2≡n+n m)

∃-odd′ ⟨ m , refl ⟩ = odd-suc (∃-even′ ⟨ m , refl ⟩)

open _≤_

∃+≤ : ∀ (n p : ℕ) → n ≤ p → ∃[ m ] (m + n ≡ p)
∃+≤ zero p z≤n rewrite sym (+-zero p) = ⟨ p , refl ⟩
∃+≤ (suc n) (suc p) (s≤s n≤p) with ∃+≤ n p n≤p
...                           | ⟨ m , m+n≡p ⟩ = ⟨ m , eq ⟩ where
  eq : m + suc n ≡ suc p
  eq rewrite +-suc m n = cong suc m+n≡p

----------------------------------------------------------------------

¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
    { to      =  λ{ ¬∃xy x bx →  ¬∃xy ⟨ x , bx ⟩ }
    ; from    =  λ{ ∀¬xy ⟨ x , Bx ⟩ → ∀¬xy x Bx }
    ; from∘to =  λ{ ¬∃xy → extensionality (λ {⟨ x , y ⟩ → refl}) }
    ; to∘from =  λ{ ∀¬xy → refl }
    }

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    --------------
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ x , ¬Bx ⟩ f = ¬Bx (f x)

-- ======================================================================

data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

inc : Bin → Bin
inc nil = x1 nil
inc (x0 bs) = x1 bs
inc (x1 bs) = x0 inc bs

toBin : ℕ → Bin
toBin zero = x0 nil
toBin (suc m) = inc (toBin m)

fromBin : Bin → ℕ
fromBin nil = zero
fromBin (x0 bs) = 2 * fromBin bs
fromBin (x1 bs) = 1 + 2 * fromBin bs

postulate
  fromToI : ∀ (n : ℕ) → fromBin(toBin n) ≡ n -- s. Induction.agda

data One : Bin → Set where
  leading1 : One (x1 nil)
  binExt0 : ∀ {x : Bin} → One x → One (x0 x)
  binExt1 : ∀ {x : Bin} → One x → One (x1 x)

data Can : Bin → Set where
  can0 : Can (x0 nil)
  can : ∀ {x : Bin} → One x → Can x

oneInc : ∀ {x : Bin} → One x → One (inc x)
oneInc leading1 = binExt0 leading1
oneInc (binExt0 ox) = binExt1 ox
oneInc (binExt1 ox) = binExt0 (oneInc ox)

canIncOne : ∀ {x : Bin} → Can x → One (inc x)
canIncOne can0 = leading1
canIncOne (can ox) = oneInc ox

canInc : ∀ {x : Bin} → Can x → Can (inc x)
canInc cx = can (canIncOne cx)

canTo : ∀ (n : ℕ) → Can (toBin n)
canTo zero = can0
canTo (suc n) = canInc (canTo n)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)

open import Data.Empty using (⊥; ⊥-elim)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

emℕ : ∀ {n : ℕ} → n ≡ zero ⊎ n ≢ zero
emℕ {zero} = inj₁ refl
emℕ {suc n} = inj₂ λ ()

-- this seems a bit too complicated...

toX0 : ∀ {n : ℕ} → (n ≡ zero) ⊎ (toBin (n + n) ≡ x0 (toBin n))
toX0 {zero} = inj₁ refl
toX0 {suc n} rewrite +-suc n n = inj₂ eq where
  eq : inc (inc (toBin (n + n))) ≡ (x0 inc (toBin n))
  eq = h emℕ where
    h : n ≡ zero ⊎ n ≢ zero → inc (inc (toBin (n + n))) ≡ (x0 inc (toBin n))
    h (inj₁ n≡0) rewrite n≡0 = refl
    h (inj₂ n≢0) =
      begin
        inc (inc (toBin (n + n)))
      ≡⟨ cong (inc ∘ inc) (k (toX0 {n})) ⟩
        inc (inc (x0 (toBin n)))
      ≡⟨⟩
        (x0 inc (toBin n))
      ∎ where
        k : (n ≡ zero) ⊎ (toBin (n + n) ≡ x0 (toBin n)) → (toBin (n + n) ≡ x0 (toBin n))
        k (inj₁ n≡0) = ⊥-elim (n≢0 n≡0)
        k (inj₂ ev) = ev

toX0noZero : ∀ {n : ℕ} {x : Bin} → One x → toBin n ≡ x → toBin (n + n) ≡ x0 (toBin n)
toX0noZero {n} {x} OneX toBinX≡x = h (toX0 {n}) where
  h : n ≡ zero ⊎ toBin (n + n) ≡ x0 (toBin n) → toBin (n + n) ≡ x0 (toBin n)
  h (inj₁ n≡0) = ⊥-elim (¬One0 One0) where
    x≡x0nil : x ≡ x0 nil
    x≡x0nil rewrite (sym toBinX≡x) | n≡0  = refl
    One0 : One (toBin 0)
    One0 rewrite (sym x≡x0nil) = OneX
    ¬One0 : ¬ One (toBin 0)
    ¬One0 (binExt0 ())
  h (inj₂ ev) = ev

toX1 : ∀ {n : ℕ} → n ≡ 0 ⊎ toBin (suc(n + n)) ≡ x1 (toBin n)
toX1 {zero} = inj₁ refl
toX1 {suc n} = inj₂ (eqCases emℕ) where
  eqCases : n ≡ zero ⊎ n ≢ zero → toBin (suc (suc n + suc n)) ≡ (x1 toBin (suc n))
  eqCases (inj₁ n≡0) rewrite n≡0 = refl
  eqCases (inj₂ n≢0) =
    begin
      toBin (suc (suc n + suc n))
    ≡⟨⟩
      toBin (suc (suc (n + suc n)))
    ≡⟨ cong (toBin ∘ suc ∘ suc) (+-suc n n) ⟩
      toBin (suc (suc (suc (n + n))))
    ≡⟨⟩
      inc (inc (toBin (suc (n + n))))
    ≡⟨ cong (inc ∘ inc) (k (toX1 {n})) ⟩
      inc (inc (x1 (toBin n)))
    ≡⟨⟩
      x1 (toBin (suc n))
    ∎ where
      k : n ≡ 0 ⊎ toBin (suc(n + n)) ≡ x1 (toBin n) → toBin (suc(n + n)) ≡ x1 (toBin n)
      k (inj₁ n≡0) = ⊥-elim (n≢0 n≡0)
      k (inj₂ ev) = ev

toX1noZero : ∀ {n : ℕ} → One (toBin n) →  toBin (suc(n + n)) ≡ x1 (toBin n)
toX1noZero {n} OneToBinN = h (toX1 {n}) where
  h : n ≡ zero ⊎ toBin (suc(n + n)) ≡ x1 (toBin n) → toBin (suc(n + n)) ≡ x1 (toBin n)
  h (inj₁ n≡0) = ⊥-elim (¬OneToBinN OneToBinN) where
    ¬OneToBinN : ¬ One (toBin n)
    ¬OneToBinN rewrite n≡0 = λ { (binExt0 ())}
  h (inj₂ ev) = ev

one∃to : ∀ {x : Bin} → One x → ∃[ n ] (toBin n ≡ x)
one∃to leading1 = ⟨ 1 , refl ⟩
one∃to {x0 x} (binExt0 oneX) = h (one∃to oneX) where
  h : (∃[ n ] (toBin n ≡ x)) → (∃[ n ] (toBin n ≡ (x0 x)))
  h ⟨ n , toBinN≡X ⟩ = ⟨ (n + n) , eq ⟩ where
    oneToBinN : One (toBin n)
    oneToBinN rewrite toBinN≡X = oneX
    eq : toBin (n + n) ≡ (x0 x)
    eq =
      begin
        toBin (n + n)
      ≡⟨ toX0noZero {n} {x} oneX toBinN≡X ⟩
        x0 (toBin n)
      ≡⟨ cong x0_ toBinN≡X ⟩
        (x0 x)
      ∎
one∃to {x1 x} (binExt1 oneX) = h (one∃to oneX) where
  h : (∃[ n ] (toBin n ≡ x)) → (∃[ n ] (toBin n ≡ (x1 x)))
  h ⟨ n , toBinN≡X ⟩ = ⟨ (suc (n + n)) , eq ⟩ where
    oneToBinN : One (toBin n)
    oneToBinN rewrite toBinN≡X = oneX
    eq : toBin (suc (n + n)) ≡ (x1 x)
    eq =
      begin
        toBin (suc (n + n))
      ≡⟨ toX1noZero {n} oneToBinN ⟩
        x1 (toBin n)
      ≡⟨ cong x1_ toBinN≡X ⟩
        (x1 x)
      ∎

can0orOne : ∀ {x : Bin} → Can x → x ≡ x0 nil ⊎ One x
can0orOne can0 = inj₁ refl
can0orOne (can x) = inj₂ x

can∃to : ∀ {x : Bin} → Can x → ∃[ n ] (toBin n ≡ x)
can∃to canX = [ (λ x≡x0 → ⟨ zero , (sym x≡x0) ⟩)
              , (λ oneX → one∃to oneX)
              ] (can0orOne canX)

oneUniq : ∀ {x : Bin} → (ox ox′ : One x) → ox ≡ ox′
oneUniq {x0 x} (binExt0 ox) (binExt0 ox′) = cong binExt0 (oneUniq {x} ox ox′)
oneUniq {x1 .nil} leading1 leading1 = refl
oneUniq {x1 x} (binExt1 ox) (binExt1 ox′) = cong binExt1 (oneUniq {x} ox ox′)

¬OneX0Nil : ¬ One (x0 nil)
¬OneX0Nil (binExt0 ())

canUniq : ∀ {x : Bin} → (cx cx′ : Can x) → cx ≡ cx′
canUniq {x0 .nil} can0 can0 = refl
canUniq {x0 .nil} can0 (can x) = ⊥-elim (¬OneX0Nil x)
canUniq {x0 .nil} (can x) can0 = ⊥-elim (¬OneX0Nil x)
canUniq {x0 x} (can ox) (can ox′) = cong can (oneUniq ox ox′)
canUniq {x1 x} (can ox) (can ox′) = cong can (oneUniq ox ox′)

∃-witness : ∀ {A : Set} {B : A → Set} → (∃[ x ] B x) → A
∃-witness ⟨ w , _ ⟩ = w

toFromOnCan : ∀ {x : ∃[ x ] Can x}
  → ⟨ toBin (fromBin (∃-witness x)) , canTo (fromBin (∃-witness x)) ⟩ ≡ x
toFromOnCan {⟨ x , CanX ⟩} with can∃to {x} CanX
toFromOnCan {⟨ x , CanX ⟩} | ⟨ n , n→x ⟩
  rewrite sym n→x | fromToI n | canUniq {toBin n} (canTo n) CanX = refl

ℕ≡Bin : ℕ ≃ ∃[ x ] Can x
ℕ≡Bin =
  record
    { to      = λ n → ⟨ toBin n , canTo n ⟩
    ; from    = λ { ⟨ x , CanX ⟩ → fromBin x}
    ; from∘to = λ n → fromToI n
    ; to∘from = λ { ⟨ x , CanX ⟩ → toFromOnCan}
    }

----------------------------------------------------------------------

-- Failed attempt...
--
-- ⟨⟩≡  : ∀ {A : Set} {B : A → Set} (a : A) (p p' : B a)
--       → p ≡ p' → _≡_ {0ℓ} {∃[ x ] B x} ⟨ a , p ⟩  ⟨ a , p' ⟩
-- ⟨⟩≡ x p p' pp' rewrite pp' = refl

-- ∃-evidence : ∀ {A : Set} {B : A → Set} → (f : ∃[ x ] B x) → B (∃-witness f)
-- ∃-evidence ⟨ _ , e ⟩ = e

-- -- The "General Theorem"
-- isoOnto : ∀ {A B : Set} {f : A → B} {g : B → A} {P : B → Set}
--   → (∀ (a : A) → g (f a) ≡ a)
--   → (∀ (a : A) → P (f a))
--   → (∀ (b : B) → P b → (∃[ a ] (f a ≡ b)))
--   → (∀ (b : B) (pb pb′ : P b) → pb ≡ pb′)
--     --------------------------------------
--   → A ≃ ∃[ b ] P b
-- isoOnto {A} {B} {f} {g} {P} gf Pf onto pi = a where
--   a = record
--       { to      = λ a → ⟨ (f a) , (Pf a) ⟩
--       ; from    = λ {⟨ b , Pb ⟩ → g b}
--       ; from∘to = λ a → gf a
--       ; to∘from = λ {⟨ b , Pb ⟩ →  {!!}}
--       }
