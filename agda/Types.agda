{-# OPTIONS --safe #-}

open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Nat.Properties
open import Data.List
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function

open import Common
open import Kinds
open import LocalLang
open import TypedLocalLang
open import Locations

module Types
  (L : Location)
  (E : TypedLocalLanguage L)
  where

open Location L
open TypedLocalLanguage E
open ≡-Reasoning

-- Local expression types
data Typₑ : Set where
  VarTypₑ : (x : ℕ) → Typₑ
  LitTypₑ : (t : TypVal) → Typₑ

-- Choreographic types
data Typ : Set where
  VarTyp : (x : ℕ) → Typ
  At : (t : Typₑ) (ℓ : Loc) → Typ
  Arrow : (τ1 τ2 : Typ) → Typ
  All : (κ : Kind) (τ : Typ) → Typ

-- Injectivity of constructors
VarTypₑ-inj : ∀{x x'} → VarTypₑ x ≡ VarTypₑ x' → x ≡ x'
VarTypₑ-inj refl = refl

LitTypₑ-inj : ∀{t t'} → LitTypₑ t ≡ LitTypₑ t' → t ≡ t'
LitTypₑ-inj refl = refl

VarTyp-inj : ∀{x x'} → VarTyp x ≡ VarTyp x' → x ≡ x'
VarTyp-inj refl = refl

At-inj : ∀{t t' ℓ ℓ'} → 
         At t ℓ ≡ At t' ℓ' →
         t ≡ t' × ℓ ≡ ℓ'
At-inj refl = refl , refl

Arrow-inj : ∀{τ1 τ1' τ2 τ2'} →
            Arrow τ1 τ2 ≡ Arrow τ1' τ2' →
            τ1 ≡ τ1' × τ2 ≡ τ2'
Arrow-inj refl = refl , refl

All-inj : ∀{κ κ' τ τ'} →
          All κ τ ≡ All κ' τ' →
          κ ≡ κ' × τ ≡ τ'
All-inj refl = refl , refl

-- Renaming on local expression types
renₑₜ : (ℕ → ℕ) → Typₑ → Typₑ
renₑₜ ξ (VarTypₑ x) = VarTypₑ (ξ x)
renₑₜ ξ (LitTypₑ t) = LitTypₑ t

-- Renaming on types
renₜ : KindRen → Typ → Typ
renₜ ξ (VarTyp x) = VarTyp (ξ ⋆ x)
renₜ ξ (At t ℓ) = At (renₑₜ (ξ ⋆ₑ) t) (renₗ-Loc (ξ ⋆ₗ) ℓ)
renₜ ξ (Arrow τ1 τ2) = Arrow (renₜ ξ τ1) (renₜ ξ τ2)
renₜ ξ (All κ τ) = All κ (renₜ (↑ₖ[ κ ] ξ) τ)


-- Renaming respects extensional equaLitTypₑy
renExtₑₜ : ∀{ξ1 ξ2} → ξ1 ≈ ξ2 → renₑₜ ξ1 ≈ renₑₜ ξ2
renExtₑₜ ξ1≈ξ2 (VarTypₑ x) = cong VarTypₑ (ξ1≈ξ2 x)
renExtₑₜ ξ1≈ξ2 (LitTypₑ t) = refl

renExtₜ : ∀{ξ1 ξ2} → ξ1 ≈₂ ξ2 → renₜ ξ1 ≈ renₜ ξ2
renExtₜ ξ1≈ξ2 (VarTyp x) = cong VarTyp (ξ1≈ξ2 ⋆ x)
renExtₜ ξ1≈ξ2 (At t ℓ) = cong₂ At (renExtₑₜ (ξ1≈ξ2 ⋆ₑ) t) (renExtₗ-Loc (ξ1≈ξ2 ⋆ₗ) ℓ)
renExtₜ ξ1≈ξ2 (Arrow τ1 τ2) =
  cong₂ Arrow (renExtₜ ξ1≈ξ2 τ1) (renExtₜ ξ1≈ξ2 τ2)
renExtₜ ξ1≈ξ2 (All κ τ) = cong (All κ) (renExtₜ (↑Extₖ κ ξ1≈ξ2) τ)

-- Renaming respects the identity
renIdₑₜ : ∀ t → renₑₜ idRen t ≡ t
renIdₑₜ (VarTypₑ x) = refl
renIdₑₜ (LitTypₑ t) = refl

-- Renaming respects the identity
renIdₜ : ∀ τ → renₜ idKindRen τ ≡ τ
renIdₜ (VarTyp x) = refl
renIdₜ (At t ℓ) = cong₂ At (renIdₑₜ t) (renIdₗ-Loc ℓ)
renIdₜ (Arrow τ1 τ2) = cong₂ Arrow (renIdₜ τ1) (renIdₜ τ2)
renIdₜ (All κ τ) = cong (All κ) (renExtₜ (↑Idₖ κ) τ ∙ renIdₜ τ)

-- Renaming enjoys fusion
renFuseₑₜ : ∀ ξ1 ξ2 → renₑₜ (ξ1 ∘ ξ2) ≈ renₑₜ ξ1 ∘ renₑₜ ξ2
renFuseₑₜ ξ1 ξ2 (VarTypₑ x) = refl
renFuseₑₜ ξ1 ξ2 (LitTypₑ t) = refl

renFuseₜ : ∀ ξ1 ξ2 → renₜ (ξ1 ∘ₖ ξ2)  ≈ renₜ ξ1 ∘ renₜ ξ2
renFuseₜ ξ1 ξ2 (VarTyp x) = refl
renFuseₜ ξ1 ξ2 (At t ℓ) = cong₂ At (renFuseₑₜ (ξ1 ⋆ₑ) (ξ2 ⋆ₑ) t) (renFuseₗ-Loc (ξ1 ⋆ₗ) (ξ2 ⋆ₗ) ℓ)
renFuseₜ ξ1 ξ2 (Arrow τ1 τ2) = cong₂ Arrow (renFuseₜ ξ1 ξ2 τ1) (renFuseₜ ξ1 ξ2 τ2)
renFuseₜ ξ1 ξ2 (All κ τ) = cong (All κ) (renExtₜ (↑Fuseₖ ξ1 ξ2 κ) τ ∙ renFuseₜ (↑ₖ[ κ ] ξ1) (↑ₖ[ κ ] ξ2) τ)

-- Renaming preserves injectivity
renInjₑₜ : ∀{ξ} →
                Injective _≡_ _≡_ ξ →
                ∀ t1 t2 →
                renₑₜ ξ t1 ≡ renₑₜ ξ t2 →
                t1 ≡ t2
renInjₑₜ ξ-inj (VarTypₑ x1) (VarTypₑ x2) eq = cong VarTypₑ (ξ-inj (VarTypₑ-inj eq))
renInjₑₜ ξ-inj (LitTypₑ t1) (LitTypₑ .t1) refl = refl

renInjₜ : ∀{ξ} →
          (∀ κ → Injective _≡_ _≡_ (ξ κ)) →
          ∀ τ1 τ2 →
          renₜ ξ τ1 ≡ renₜ ξ τ2 →
          τ1 ≡ τ2
renInjₜ ξ-inj (VarTyp x1) (VarTyp x2) eq =
  cong VarTyp (ξ-inj ⋆ (VarTyp-inj eq))
renInjₜ ξ-inj (At t1 ℓ1) (At t2 ℓ2) eq =
  cong₂ At (renInjₑₜ (ξ-inj ⋆ₑ) t1 t2 (At-inj eq .fst)) (renInjₗ-Loc (ξ-inj ⋆ₗ) (At-inj eq .snd))
renInjₜ ξ-inj (Arrow τ11 τ12) (Arrow τ21 τ22) eq =
  cong₂ Arrow (renInjₜ ξ-inj τ11 τ21 (Arrow-inj eq .fst)) (renInjₜ ξ-inj τ12 τ22 (Arrow-inj eq .snd))
renInjₜ {ξ} ξ-inj (All κ1 τ1) (All κ2 τ2) eq with All-inj eq .fst
... | refl = cong (All κ1) (renInjₜ (↑Injₖ ξ-inj κ1) τ1 τ2 (All-inj eq .snd))

-- Weakening a local expression type by one type variable
↑ₑₜ : Typₑ → Typₑ
↑ₑₜ = renₑₜ suc

-- ↑ₑₜ is injective
↑Injₑₜ : ∀ t1 t2 → ↑ₑₜ t1 ≡ ↑ₑₜ t2 → t1 ≡ t2
↑Injₑₜ = renInjₑₜ suc-injective

-- Weakening a choreography type by one kind variable
↑ₜ[_] : Kind → Typ → Typ
↑ₜ[ κ ] = renₜ (sucₖ[ κ ] idKindRen)

-- ↑ₜ is injective
↑Injₜ : ∀ κ τ1 τ2 → ↑ₜ[ κ ] τ1 ≡ ↑ₜ[ κ ] τ2 → τ1 ≡ τ2
↑Injₜ κ = renInjₜ (sucInjₖ (λ κ' eq → eq) κ)
