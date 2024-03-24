{-# OPTIONS --safe #-}

open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Nat.Properties
open import Data.List
open import Data.Product
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function

open import Common
open import LocalLang
open import TypedLocalLang
open import Locations

module Types
  (L : Location)
  (E : Language L)
  (LE : LawfulLanguage L E)
  (TE : TypedLocalLanguage L E LE)
  where

open import Choreographies L E
open import LocalRenamings L E LE
open import LocationRenamings L E LE
open import Renamings L E LE
open import Substitutions L E LE
open Location L
open Language E
open LawfulLanguage LE
open TypedLocalLanguage TE
open ≡-Reasoning

-- Choreographic types
data Typ : Set where
  At : (t : Typₑ) (ℓ : Loc) → Typ
  Arrow : (τ1 τ2 : Typ) → Typ
  AllLoc : (τ : Typ) → Typ

-- Location renaming on types
renₜ : Typ → (ℕ → ℕ) → Typ
renₜ (At t ℓ) ξ = At t (renₗ-Loc ℓ ξ)
renₜ (Arrow τ1 τ2) ξ = Arrow (renₜ τ1 ξ) (renₜ τ2 ξ)
renₜ (AllLoc τ) ξ = AllLoc (renₜ τ (↑ ξ))

-- Renaming respects extensional equality
renExtₜ : ∀{ξ1 ξ2} → ξ1 ≈ ξ2 → ∀ τ → renₜ τ ξ1 ≡ renₜ τ ξ2
renExtₜ ξ1≈ξ2 (At t ℓ) = cong₂ At refl (renExtₗ-Loc ξ1≈ξ2 ℓ)
renExtₜ ξ1≈ξ2 (Arrow τ1 τ2) =
  cong₂ Arrow (renExtₜ ξ1≈ξ2 τ1) (renExtₜ ξ1≈ξ2 τ2)
renExtₜ ξ1≈ξ2 (AllLoc τ) = cong AllLoc (renExtₜ (↑Ext ξ1≈ξ2) τ)

-- Renaming respects the identity
renIdₜ : ∀ τ → renₜ τ idRen ≡ τ
renIdₜ (At t ℓ) = cong₂ At refl (renIdₗ-Loc ℓ)
renIdₜ (Arrow τ1 τ2) = cong₂ Arrow (renIdₜ τ1) (renIdₜ τ2)
renIdₜ (AllLoc τ) = cong AllLoc τ⟨↑id⟩≡τ
  where

  τ⟨↑id⟩≡τ : renₜ τ (↑ idRen) ≡ τ
  τ⟨↑id⟩≡τ =
    renₜ τ (↑ idRen) ≡⟨ renExtₜ ↑Id τ ⟩
    renₜ τ idRen     ≡⟨ renIdₜ τ ⟩
    τ                ∎

-- Renaming enjoys fusion
renFuseₜ : ∀ ξ1 ξ2 τ → renₜ τ (ξ2 ∘ ξ1) ≡ renₜ (renₜ τ ξ1) ξ2
renFuseₜ ξ1 ξ2 (At t ℓ) = cong₂ At refl (renFuseₗ-Loc ξ1 ξ2 ℓ)
renFuseₜ ξ1 ξ2 (Arrow τ1 τ2) =
  cong₂ Arrow (renFuseₜ ξ1 ξ2 τ1) (renFuseₜ ξ1 ξ2 τ2)
renFuseₜ ξ1 ξ2 (AllLoc τ) = cong AllLoc τ⟨↑[ξ2∘ξ1]⟩≡τ⟨↑ξ1⟩⟨↑ξ2⟩
  where

  τ⟨↑[ξ2∘ξ1]⟩≡τ⟨↑ξ1⟩⟨↑ξ2⟩ : renₜ τ (↑ (ξ2 ∘ ξ1)) ≡ renₜ (renₜ τ (↑ ξ1)) (↑ ξ2)
  τ⟨↑[ξ2∘ξ1]⟩≡τ⟨↑ξ1⟩⟨↑ξ2⟩ = 
    renₜ τ (↑ (ξ2 ∘ ξ1))        ≡⟨ renExtₜ (↑Fuse ξ1 ξ2) τ ⟩
    renₜ τ (↑ ξ2 ∘ ↑ ξ1)        ≡⟨ renFuseₜ (↑ ξ1) (↑ ξ2) τ ⟩
    renₜ (renₜ τ (↑ ξ1)) (↑ ξ2) ∎

-- Weakening a type by one variable
↑ₜ : Typ → Typ
↑ₜ τ = renₜ τ suc

-- Location substitution on types
subₜ : Typ → (ℕ → Loc) → Typ
subₜ (At t ℓ) σ = At t (subₗ-Loc ℓ σ)
subₜ (Arrow τ1 τ2) σ = Arrow (subₜ τ1 σ) (subₜ τ2 σ)
subₜ (AllLoc τ) σ = AllLoc (subₜ τ (↑σₗ σ))

-- Substitution respects extensional equality
subExtₜ : ∀{σ1 σ2} →
          σ1 ≈ σ2 →
          ∀ τ →
          subₜ τ σ1 ≡ subₜ τ σ2
subExtₜ σ1≈σ2 (At t ℓ) = cong₂ At refl (subExtₗ-Loc σ1≈σ2 ℓ)
subExtₜ σ1≈σ2 (Arrow τ1 τ2) = cong₂ Arrow (subExtₜ σ1≈σ2 τ1) (subExtₜ σ1≈σ2 τ2)
subExtₜ σ1≈σ2 (AllLoc τ) = cong AllLoc (subExtₜ (↑σExtₗ σ1≈σ2) τ)

-- Substitution respects the inclusion
subιₜ : ∀ ξ τ → subₜ τ (ιₗ ξ) ≡ renₜ τ ξ
subιₜ ξ (At t ℓ) = cong (At t) (subιₗ-Loc ξ ℓ)
subιₜ ξ (Arrow τ1 τ2) = cong₂ Arrow (subιₜ ξ τ1) (subιₜ ξ τ2)
subιₜ ξ (AllLoc τ) = cong AllLoc τ⟨↑ιξ⟩≡τ⟨↑ξ⟩
  where

  τ⟨↑ιξ⟩≡τ⟨↑ξ⟩ : subₜ τ (↑σₗ (ιₗ ξ)) ≡ renₜ τ (↑ ξ)
  τ⟨↑ιξ⟩≡τ⟨↑ξ⟩ =
    subₜ τ (↑σₗ (ιₗ ξ)) ≡⟨ subExtₜ (↑σιₗ ξ) τ ⟩
    subₜ τ (ιₗ (↑ ξ))   ≡⟨ subιₜ (↑ ξ) τ ⟩
    renₜ τ (↑ ξ)        ∎

-- Substitution respects the identity
subIdₜ : ∀ τ → subₜ τ idSubₗ ≡ τ
subIdₜ (At t ℓ) = cong₂ At refl (subIdₗ-Loc ℓ)
subIdₜ (Arrow τ1 τ2) = cong₂ Arrow (subIdₜ τ1) (subIdₜ τ2)
subIdₜ (AllLoc τ) = cong AllLoc τ⟨↑id⟩≡τ
  where

  τ⟨↑id⟩≡τ : subₜ τ (↑σₗ idSubₗ) ≡ τ
  τ⟨↑id⟩≡τ =
    subₜ τ (↑σₗ idSubₗ) ≡⟨ subExtₜ ↑σIdₗ τ ⟩
    subₜ τ idSubₗ       ≡⟨ subIdₜ τ ⟩
    τ                   ∎

-- Substitution enjoys fusion
subFuseₜ : ∀ σ1 σ2 τ → subₜ τ (σ1 •ₗ σ2) ≡ subₜ (subₜ τ σ2) σ1
subFuseₜ σ1 σ2 (At t ℓ) = cong₂ At refl (subFuseₗ-Loc σ1 σ2 ℓ)
subFuseₜ σ1 σ2 (Arrow τ1 τ2) = cong₂ Arrow (subFuseₜ σ1 σ2 τ1) (subFuseₜ σ1 σ2 τ2)
subFuseₜ σ1 σ2 (AllLoc τ) = cong AllLoc τ⟨↑[σ1•σ2]⟩≡τ⟨↑σ2⟩⟨↑σ1⟩
  where

  τ⟨↑[σ1•σ2]⟩≡τ⟨↑σ2⟩⟨↑σ1⟩ : subₜ τ (↑σₗ (σ1 •ₗ σ2)) ≡ subₜ (subₜ τ (↑σₗ σ2)) (↑σₗ σ1)
  τ⟨↑[σ1•σ2]⟩≡τ⟨↑σ2⟩⟨↑σ1⟩ =
    subₜ τ (↑σₗ (σ1 •ₗ σ2))         ≡⟨ subExtₜ (↑σ•ₗ σ1 σ2) τ ⟩
    subₜ τ (↑σₗ σ1 •ₗ ↑σₗ σ2)       ≡⟨ subFuseₜ (↑σₗ σ1) (↑σₗ σ2) τ ⟩
    subₜ (subₜ τ (↑σₗ σ2)) (↑σₗ σ1) ∎