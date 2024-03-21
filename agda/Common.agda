{-# OPTIONS --safe #-}

open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Function

module Common where

-- `up` construction on variable renamings
↑ : (ℕ → ℕ) → ℕ → ℕ
↑ ξ zero = zero
↑ ξ (suc n) = suc (ξ n)

idRen : ℕ → ℕ
idRen n = n

-- `up` construction has no extensional effect on the identity renaming
↑Id : ∀ n → ↑ idRen n ≡ idRen n
↑Id zero = refl
↑Id (suc n) = refl

-- The `up` construction respects extensional equality
↑Ext : ∀{ξ1 ξ2} →
              (∀ n → ξ1 n ≡ ξ2 n) →
              ∀ n → ↑ ξ1 n ≡ ↑ ξ2 n
↑Ext ξ1≈ξ2 zero = refl
↑Ext ξ1≈ξ2 (suc n) = cong suc (ξ1≈ξ2 n)

-- The `up` construction extensionally commutes with composition
↑Fuse : ∀ ξ1 ξ2 n → ↑ (ξ2 ∘ ξ1) n ≡ ↑ ξ2 (↑ ξ1 n)
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
