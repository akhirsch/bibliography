{-# OPTIONS --safe #-}

open import Level hiding (zero; suc)
open import Data.Nat hiding (_⊔_)
open import Relation.Binary.PropositionalEquality
open import Function

module Common where

-- Extensional function equality
infix 4 _≈_
_≈_ : ∀{a b} {A : Set a} {B : A → Set b} →
      (f g : (x : A) → B x) → Set (a ⊔ b)
f ≈ g = ∀ x → f x ≡ g x

-- Identity renaming
idRen : ℕ → ℕ
idRen n = n

-- `up` construction on variable renamings
↑ : (ξ : ℕ → ℕ) → ℕ → ℕ
↑ ξ zero = zero
↑ ξ (suc n) = suc (ξ n)

-- The `up` construction respects the identity
↑Id : ∀ n → ↑ idRen n ≡ idRen n
↑Id zero = refl
↑Id (suc n) = refl

-- The `up` construction respects extensional equality
↑Ext : ∀{ξ1 ξ2} → ξ1 ≈ ξ2 → ↑ ξ1 ≈ ↑ ξ2
↑Ext ξ1≈ξ2 zero = refl
↑Ext ξ1≈ξ2 (suc n) = cong suc (ξ1≈ξ2 n)

-- The `up` construction enjoys fusion
↑Fuse : ∀ ξ1 ξ2 → ↑ (ξ2 ∘ ξ1) ≈ ↑ ξ2 ∘ ↑ ξ1
↑Fuse ξ1 ξ2 zero = refl
↑Fuse ξ1 ξ2 (suc n) = refl

-- Extended congruence methods as the standard library only goes up to cong₂
cong₃ : ∀{a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {a1 a2 : A} {b1 b2 : B} {c1 c2 : C} →
        a1 ≡ a2 → b1 ≡ b2 → c1 ≡ c2 →
        f a1 b1 c1 ≡ f a2 b2 c2
cong₃ f refl refl refl = refl

cong₄ : ∀{a b c d e} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e}
        (f : A → B → C → D → E) {a1 a2 : A} {b1 b2 : B} {c1 c2 : C} {d1 d2 : D} →
        a1 ≡ a2 → b1 ≡ b2 → c1 ≡ c2 → d1 ≡ d2 →
        f a1 b1 c1 d1 ≡ f a2 b2 c2 d2
cong₄ f refl refl refl refl = refl

cong₅ : ∀{a b c d e f} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e} {F : Set f}
        (α : A → B → C → D → E → F) {a1 a2 : A} {b1 b2 : B} {c1 c2 : C} {d1 d2 : D} {e1 e2 : E} →
        a1 ≡ a2 → b1 ≡ b2 → c1 ≡ c2 → d1 ≡ d2 → e1 ≡ e2 →
        α a1 b1 c1 d1 e1 ≡ α a2 b2 c2 d2 e2
cong₅ α refl refl refl refl refl = refl
