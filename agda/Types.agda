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

-- Choreographic types
data Typ : Set where
  At : (t : Typₑ) (ℓ : Loc) → Typ
  Arrow : (τ1 τ2 : Typ) → Typ
  AllLoc : (τ : Typ) → Typ

-- Injectivity of constructors
At-inj : ∀{t t' ℓ ℓ'} → 
         At t ℓ ≡ At t' ℓ' →
         t ≡ t' × ℓ ≡ ℓ'
At-inj refl = refl , refl

Arrow-inj : ∀{τ1 τ1' τ2 τ2'} →
            Arrow τ1 τ2 ≡ Arrow τ1' τ2' →
            τ1 ≡ τ1' × τ2 ≡ τ2'
Arrow-inj refl = refl , refl

AllLoc-inj : ∀{τ τ'} →
             AllLoc τ ≡ AllLoc τ' →
             τ ≡ τ'
AllLoc-inj refl = refl

-- Location renaming on types
renₜ : (ℕ → ℕ) → Typ → Typ
renₜ ξ (At t ℓ) = At t (renₗ-Loc ξ ℓ)
renₜ ξ (Arrow τ1 τ2) = Arrow (renₜ ξ τ1) (renₜ ξ τ2)
renₜ ξ (AllLoc τ) = AllLoc (renₜ (↑ ξ) τ)

-- Renaming respects extensional equality
renExtₜ : ∀{ξ1 ξ2} → ξ1 ≈ ξ2 → ∀ τ → renₜ ξ1 τ ≡ renₜ ξ2 τ
renExtₜ ξ1≈ξ2 (At t ℓ) = cong₂ At refl (renExtₗ-Loc ξ1≈ξ2 ℓ)
renExtₜ ξ1≈ξ2 (Arrow τ1 τ2) =
  cong₂ Arrow (renExtₜ ξ1≈ξ2 τ1) (renExtₜ ξ1≈ξ2 τ2)
renExtₜ ξ1≈ξ2 (AllLoc τ) = cong AllLoc (renExtₜ (↑Ext ξ1≈ξ2) τ)

-- Renaming respects the identity
renIdₜ : ∀ τ → renₜ idRen τ ≡ τ
renIdₜ (At t ℓ) = cong₂ At refl (renIdₗ-Loc ℓ)
renIdₜ (Arrow τ1 τ2) = cong₂ Arrow (renIdₜ τ1) (renIdₜ τ2)
renIdₜ (AllLoc τ) = cong AllLoc τ⟨↑id⟩≡τ
  where

  τ⟨↑id⟩≡τ : renₜ (↑ idRen) τ ≡ τ
  τ⟨↑id⟩≡τ =
    renₜ (↑ idRen) τ ≡⟨ renExtₜ ↑Id τ ⟩
    renₜ idRen τ     ≡⟨ renIdₜ τ ⟩
    τ                ∎

-- Renaming enjoys fusion
renFuseₜ : ∀ ξ1 ξ2 → renₜ (ξ1 ∘ ξ2) ≈ renₜ ξ1 ∘ renₜ ξ2
renFuseₜ ξ1 ξ2 (At t ℓ) = cong₂ At refl (renFuseₗ-Loc ξ1 ξ2 ℓ)
renFuseₜ ξ1 ξ2 (Arrow τ1 τ2) =
  cong₂ Arrow (renFuseₜ ξ1 ξ2 τ1) (renFuseₜ ξ1 ξ2 τ2)
renFuseₜ ξ1 ξ2 (AllLoc τ) = cong AllLoc τ⟨↑[ξ1∘ξ2]⟩≡τ⟨↑ξ2⟩⟨↑ξ1⟩
  where

  τ⟨↑[ξ1∘ξ2]⟩≡τ⟨↑ξ2⟩⟨↑ξ1⟩ : renₜ (↑ (ξ1 ∘ ξ2)) τ ≡ renₜ (↑ ξ1) (renₜ (↑ ξ2) τ)
  τ⟨↑[ξ1∘ξ2]⟩≡τ⟨↑ξ2⟩⟨↑ξ1⟩ = 
    renₜ (↑ (ξ1 ∘ ξ2)) τ        ≡⟨ renExtₜ (↑Fuse ξ1 ξ2) τ ⟩
    renₜ (↑ ξ1 ∘ ↑ ξ2) τ        ≡⟨ renFuseₜ (↑ ξ1) (↑ ξ2) τ ⟩
    renₜ (↑ ξ1) (renₜ (↑ ξ2) τ) ∎

-- Renaming preserves injectivity
renₜ-pres-inj : ∀{ξ} →
                Injective _≡_ _≡_ ξ →
                ∀ τ1 τ2 →
                renₜ ξ τ1 ≡ renₜ ξ τ2 →
                τ1 ≡ τ2
renₜ-pres-inj ξ-inj (At t ℓ) (At t' ℓ') eq =
  cong₂ At (At-inj eq .fst) (renInjₗ-Loc ξ-inj (At-inj eq .snd))
renₜ-pres-inj ξ-inj (Arrow τ1 τ2) (Arrow τ1' τ2') eq =
  cong₂ Arrow (renₜ-pres-inj ξ-inj τ1 τ1' (Arrow-inj eq .fst))
    (renₜ-pres-inj ξ-inj τ2 τ2' (Arrow-inj eq .snd))
renₜ-pres-inj ξ-inj (AllLoc τ) (AllLoc τ') eq =
  cong AllLoc (renₜ-pres-inj (↑-pres-inj ξ-inj) τ τ' (AllLoc-inj eq))

-- Weakening a type by one variable
↑ₜ : Typ → Typ
↑ₜ τ = renₜ suc τ

-- ↑ preserves injectivity
↑ₜ-pres-inj : ∀ τ1 τ2 → ↑ₜ τ1 ≡ ↑ₜ τ2 → τ1 ≡ τ2
↑ₜ-pres-inj = renₜ-pres-inj suc-injective

-- Location substitution on types
subₜ : (ℕ → Loc) → Typ → Typ
subₜ σ (At t ℓ) = At t (subₗ-Loc σ ℓ)
subₜ σ (Arrow τ1 τ2) = Arrow (subₜ σ τ1) (subₜ σ τ2)
subₜ σ (AllLoc τ) = AllLoc (subₜ (↑σₗ σ) τ)

-- Substitution respects extensional equality
subExtₜ : ∀{σ1 σ2} →
          σ1 ≈ σ2 →
          ∀ τ →
          subₜ σ1 τ ≡ subₜ σ2 τ
subExtₜ σ1≈σ2 (At t ℓ) = cong₂ At refl (subExtₗ-Loc σ1≈σ2 ℓ)
subExtₜ σ1≈σ2 (Arrow τ1 τ2) = cong₂ Arrow (subExtₜ σ1≈σ2 τ1) (subExtₜ σ1≈σ2 τ2)
subExtₜ σ1≈σ2 (AllLoc τ) = cong AllLoc (subExtₜ (↑σExtₗ σ1≈σ2) τ)

-- Substitution respects the inclusion
subιₜ : ∀ ξ τ → subₜ (ιₗ ξ) τ ≡ renₜ ξ τ
subιₜ ξ (At t ℓ) = cong (At t) (subιₗ-Loc ξ ℓ)
subιₜ ξ (Arrow τ1 τ2) = cong₂ Arrow (subιₜ ξ τ1) (subιₜ ξ τ2)
subιₜ ξ (AllLoc τ) = cong AllLoc τ⟨↑ιξ⟩≡τ⟨↑ξ⟩
  where

  τ⟨↑ιξ⟩≡τ⟨↑ξ⟩ : subₜ (↑σₗ (ιₗ ξ)) τ ≡ renₜ (↑ ξ) τ
  τ⟨↑ιξ⟩≡τ⟨↑ξ⟩ =
    subₜ (↑σₗ (ιₗ ξ)) τ ≡⟨ subExtₜ (↑σιₗ ξ) τ ⟩
    subₜ (ιₗ (↑ ξ)) τ   ≡⟨ subιₜ (↑ ξ) τ ⟩
    renₜ (↑ ξ) τ        ∎

-- Substitution respects the identity
subIdₜ : ∀ τ → subₜ idSubₗ τ ≡ τ
subIdₜ (At t ℓ) = cong₂ At refl (subIdₗ-Loc ℓ)
subIdₜ (Arrow τ1 τ2) = cong₂ Arrow (subIdₜ τ1) (subIdₜ τ2)
subIdₜ (AllLoc τ) = cong AllLoc τ⟨↑id⟩≡τ
  where

  τ⟨↑id⟩≡τ : subₜ (↑σₗ idSubₗ) τ ≡ τ
  τ⟨↑id⟩≡τ =
    subₜ (↑σₗ idSubₗ) τ ≡⟨ subExtₜ ↑σIdₗ τ ⟩
    subₜ idSubₗ τ       ≡⟨ subIdₜ τ ⟩
    τ                   ∎

-- Substitution enjoys fusion
subFuseₜ : ∀ σ1 σ2 → subₜ (σ1 •ₗ σ2) ≈ subₜ σ1 ∘ subₜ σ2
subFuseₜ σ1 σ2 (At t ℓ) = cong₂ At refl (subFuseₗ-Loc σ1 σ2 ℓ)
subFuseₜ σ1 σ2 (Arrow τ1 τ2) = cong₂ Arrow (subFuseₜ σ1 σ2 τ1) (subFuseₜ σ1 σ2 τ2)
subFuseₜ σ1 σ2 (AllLoc τ) = cong AllLoc τ⟨↑[σ1•σ2]⟩≡τ⟨↑σ2⟩⟨↑σ1⟩
  where

  τ⟨↑[σ1•σ2]⟩≡τ⟨↑σ2⟩⟨↑σ1⟩ : subₜ (↑σₗ (σ1 •ₗ σ2)) τ ≡ subₜ (↑σₗ σ1) (subₜ (↑σₗ σ2) τ)
  τ⟨↑[σ1•σ2]⟩≡τ⟨↑σ2⟩⟨↑σ1⟩ =
    subₜ (↑σₗ (σ1 •ₗ σ2)) τ         ≡⟨ subExtₜ (↑σ•ₗ σ1 σ2) τ ⟩
    subₜ (↑σₗ σ1 •ₗ ↑σₗ σ2) τ       ≡⟨ subFuseₜ (↑σₗ σ1) (↑σₗ σ2) τ ⟩
    subₜ (↑σₗ σ1) (subₜ (↑σₗ σ2) τ) ∎ 