{-# OPTIONS --safe #-}

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Function

open import Common

module Kinds where

data Kind : Set where
  ⋆ : Kind -- Kind of choreographic types
  ⋆ₑ : Kind -- Kind of local language types
  ⋆ₗ : Kind -- Kind of locations

-- Kind renamings
KindRen : Set
KindRen = Kind → ℕ → ℕ

idKindRen : KindRen
idKindRen κ = idRen

_∘ₖ_ : KindRen → KindRen → KindRen
(ξ1 ∘ₖ ξ2) κ = ξ1 κ ∘ ξ2 κ

↑ₖ[_] : Kind → KindRen → KindRen
↑ₖ[ ⋆ ] ξ ⋆ = ↑ (ξ ⋆)
↑ₖ[ ⋆ ] ξ ⋆ₑ = ξ ⋆ₑ
↑ₖ[ ⋆ ] ξ ⋆ₗ = ξ ⋆ₗ  
↑ₖ[ ⋆ₑ ] ξ ⋆ = ξ ⋆
↑ₖ[ ⋆ₑ ] ξ ⋆ₑ = ↑ (ξ ⋆ₑ) 
↑ₖ[ ⋆ₑ ] ξ ⋆ₗ = ξ ⋆ₗ
↑ₖ[ ⋆ₗ ] ξ ⋆ = ξ ⋆ 
↑ₖ[ ⋆ₗ ] ξ ⋆ₑ = ξ ⋆ₑ
↑ₖ[ ⋆ₗ ] ξ ⋆ₗ = ↑ (ξ ⋆ₗ)

sucₖ[_] : Kind → KindRen → KindRen
sucₖ[ ⋆ ] ξ ⋆ = suc ∘ (ξ ⋆)
sucₖ[ ⋆ ] ξ ⋆ₑ = ξ ⋆ₑ
sucₖ[ ⋆ ] ξ ⋆ₗ = ξ ⋆ₗ
sucₖ[ ⋆ₑ ] ξ ⋆ = ξ ⋆
sucₖ[ ⋆ₑ ] ξ ⋆ₑ = suc ∘ (ξ ⋆ₑ)
sucₖ[ ⋆ₑ ] ξ ⋆ₗ = ξ ⋆ₗ
sucₖ[ ⋆ₗ ] ξ ⋆ = ξ ⋆
sucₖ[ ⋆ₗ ] ξ ⋆ₑ = ξ ⋆ₑ
sucₖ[ ⋆ₗ ] ξ ⋆ₗ = suc ∘ (ξ ⋆ₗ)

↑Extₖ : ∀{ξ1 ξ2} κ → ξ1 ≈₂ ξ2 → ↑ₖ[ κ ] ξ1 ≈₂ ↑ₖ[ κ ] ξ2
↑Extₖ ⋆ ξ1≈ξ2 ⋆ = ↑Ext (ξ1≈ξ2 ⋆)
↑Extₖ ⋆ ξ1≈ξ2 ⋆ₑ = ξ1≈ξ2 ⋆ₑ
↑Extₖ ⋆ ξ1≈ξ2 ⋆ₗ = ξ1≈ξ2 ⋆ₗ  
↑Extₖ ⋆ₑ ξ1≈ξ2 ⋆ = ξ1≈ξ2 ⋆
↑Extₖ ⋆ₑ ξ1≈ξ2 ⋆ₑ = ↑Ext (ξ1≈ξ2 ⋆ₑ) 
↑Extₖ ⋆ₑ ξ1≈ξ2 ⋆ₗ = ξ1≈ξ2 ⋆ₗ
↑Extₖ ⋆ₗ ξ1≈ξ2 ⋆ = ξ1≈ξ2 ⋆ 
↑Extₖ ⋆ₗ ξ1≈ξ2 ⋆ₑ = ξ1≈ξ2 ⋆ₑ
↑Extₖ ⋆ₗ ξ1≈ξ2 ⋆ₗ = ↑Ext (ξ1≈ξ2 ⋆ₗ)

↑Idₖ : ∀ κ → ↑ₖ[ κ ] idKindRen ≈₂ idKindRen
↑Idₖ ⋆ ⋆ = ↑Id
↑Idₖ ⋆ ⋆ₑ = λ _ → refl
↑Idₖ ⋆ ⋆ₗ = λ _ → refl  
↑Idₖ ⋆ₑ ⋆ = λ _ → refl
↑Idₖ ⋆ₑ ⋆ₑ = ↑Id 
↑Idₖ ⋆ₑ ⋆ₗ = λ _ → refl
↑Idₖ ⋆ₗ ⋆ = λ _ → refl 
↑Idₖ ⋆ₗ ⋆ₑ = λ _ → refl
↑Idₖ ⋆ₗ ⋆ₗ = ↑Id

↑Fuseₖ : ∀ ξ1 ξ2 κ → ↑ₖ[ κ ] (ξ1 ∘ₖ ξ2) ≈₂ (↑ₖ[ κ ] ξ1) ∘ₖ (↑ₖ[ κ ] ξ2)
↑Fuseₖ ξ1 ξ2 ⋆ ⋆ = ↑Fuse (ξ1 ⋆) (ξ2 ⋆)
↑Fuseₖ ξ1 ξ2 ⋆ ⋆ₑ x = refl
↑Fuseₖ ξ1 ξ2 ⋆ ⋆ₗ x = refl  
↑Fuseₖ ξ1 ξ2 ⋆ₑ ⋆ x = refl
↑Fuseₖ ξ1 ξ2 ⋆ₑ ⋆ₑ = ↑Fuse (ξ1 ⋆ₑ) (ξ2 ⋆ₑ) 
↑Fuseₖ ξ1 ξ2 ⋆ₑ ⋆ₗ x = refl
↑Fuseₖ ξ1 ξ2 ⋆ₗ ⋆ x = refl 
↑Fuseₖ ξ1 ξ2 ⋆ₗ ⋆ₑ x = refl
↑Fuseₖ ξ1 ξ2 ⋆ₗ ⋆ₗ = ↑Fuse (ξ1 ⋆ₗ) (ξ2 ⋆ₗ)

↑Injₖ : ∀{ξ} → (∀ κ → Injective _≡_ _≡_ (ξ κ)) →
        ∀ κ →
        ∀ κ' → Injective _≡_ _≡_ ((↑ₖ[ κ ] ξ) κ')
↑Injₖ ξ-inj ⋆ ⋆ = ↑Inj (ξ-inj ⋆)
↑Injₖ ξ-inj ⋆ ⋆ₑ = ξ-inj ⋆ₑ
↑Injₖ ξ-inj ⋆ ⋆ₗ = ξ-inj ⋆ₗ
↑Injₖ ξ-inj ⋆ₑ ⋆ = ξ-inj ⋆
↑Injₖ ξ-inj ⋆ₑ ⋆ₑ = ↑Inj (ξ-inj ⋆ₑ) 
↑Injₖ ξ-inj ⋆ₑ ⋆ₗ = ξ-inj ⋆ₗ
↑Injₖ ξ-inj ⋆ₗ ⋆ = ξ-inj ⋆     
↑Injₖ ξ-inj ⋆ₗ ⋆ₑ = ξ-inj ⋆ₑ
↑Injₖ ξ-inj ⋆ₗ ⋆ₗ = ↑Inj (ξ-inj ⋆ₗ)

sucInjₖ : ∀{ξ} → (∀ κ → Injective _≡_ _≡_ (ξ κ)) →
        ∀ κ →
        ∀ κ' → Injective _≡_ _≡_ ((sucₖ[ κ ] ξ) κ')
sucInjₖ ξ-inj ⋆ ⋆ = ξ-inj ⋆ ∘ suc-injective
sucInjₖ ξ-inj ⋆ ⋆ₑ = ξ-inj ⋆ₑ
sucInjₖ ξ-inj ⋆ ⋆ₗ = ξ-inj ⋆ₗ
sucInjₖ ξ-inj ⋆ₑ ⋆ = ξ-inj ⋆
sucInjₖ ξ-inj ⋆ₑ ⋆ₑ = ξ-inj ⋆ₑ ∘ suc-injective
sucInjₖ ξ-inj ⋆ₑ ⋆ₗ = ξ-inj ⋆ₗ
sucInjₖ ξ-inj ⋆ₗ ⋆ = ξ-inj ⋆     
sucInjₖ ξ-inj ⋆ₗ ⋆ₑ = ξ-inj ⋆ₑ
sucInjₖ ξ-inj ⋆ₗ ⋆ₗ = ξ-inj ⋆ₗ ∘ suc-injective