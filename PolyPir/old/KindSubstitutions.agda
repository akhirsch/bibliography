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

module KindSubstitutions
  (L : Location)
  (E : TypedLocalLanguage L)
  where

open import Types L E

open Location L
open TypedLocalLanguage E
open ≡-Reasoning

record KindSub : Set where
  field
    typSub  : ℕ → Typ
    typSubₑ : ℕ → Typₑ
    locSub  : ℕ → Loc

open KindSub public

idSubₑₜ : ℕ → Typₑ
idSubₑₜ = VarTypₑ

idKindSub : KindSub
typSub idKindSub = VarTyp
typSubₑ idKindSub = idSubₑₜ
locSub idKindSub = idSubₗ

renKindSub : KindRen → KindSub → KindSub
typSub  (renKindSub ξ σ) = renₜ ξ ∘ σ .typSub
typSubₑ (renKindSub ξ σ) = renₑₜ (ξ ⋆ₑ) ∘ σ .typSubₑ
locSub  (renKindSub ξ σ) = renₗ-Loc (ξ ⋆ₗ) ∘ σ .locSub

KindSubRange : Kind → Set
KindSubRange ⋆ = Typ
KindSubRange ⋆ₑ = Typₑ
KindSubRange ⋆ₗ = Loc

Varₖ : (κ : Kind) → ℕ → KindSubRange κ
Varₖ ⋆ = VarTyp
Varₖ ⋆ₑ = VarTypₑ
Varₖ ⋆ₗ = VarLoc

_▸ₖ[_]_ : KindSub → (κ : Kind) → KindSubRange κ → KindSub
σ ▸ₖ[ ⋆  ] τ = record σ { typSub  = σ .typSub ▸ τ }
σ ▸ₖ[ ⋆ₑ ] t = record σ { typSubₑ = σ .typSubₑ ▸ t }
σ ▸ₖ[ ⋆ₗ ] ℓ = record σ { locSub  = σ .locSub ▸ ℓ }

↑σₖ[_] : Kind → KindSub → KindSub
↑σₖ[ κ ] σ = renKindSub (sucₖ[ κ ] idKindRen) σ ▸ₖ[ κ ] Varₖ κ zero

record _≈ₖ_ (σ1 σ2 : KindSub) : Set where
  field
    typSub≈  : σ1 .typSub  ≈ σ2 .typSub
    typSubₑ≈ : σ1 .typSubₑ ≈ σ2 .typSubₑ
    locSub≈  : σ1 .locSub  ≈ σ2 .locSub

open _≈ₖ_ public

▸Extₖ : ∀{σ1 σ2} →
         σ1 ≈ₖ σ2 →
         ∀ κ x → (σ1 ▸ₖ[ κ ] x) ≈ₖ (σ2 ▸ₖ[ κ ] x)
typSub≈  (▸Extₖ eq ⋆ τ)  = ▸Ext (eq .typSub≈) τ
typSubₑ≈ (▸Extₖ eq ⋆ τ)  = eq .typSubₑ≈
locSub≈  (▸Extₖ eq ⋆ τ)  = eq .locSub≈
typSub≈  (▸Extₖ eq ⋆ₑ t) = eq .typSub≈
typSubₑ≈ (▸Extₖ eq ⋆ₑ t) = ▸Ext (eq .typSubₑ≈) t
locSub≈  (▸Extₖ eq ⋆ₑ t) = eq .locSub≈
typSub≈  (▸Extₖ eq ⋆ₗ ℓ) = eq .typSub≈
typSubₑ≈ (▸Extₖ eq ⋆ₗ ℓ) = eq .typSubₑ≈
locSub≈  (▸Extₖ eq ⋆ₗ ℓ) = ▸Ext (eq .locSub≈) ℓ

renKindSubExt : ∀{ξ1 ξ2 σ1 σ2} →
                ξ1 ≈₂ ξ2 →
                σ1 ≈ₖ σ2 →
                renKindSub ξ1 σ1 ≈ₖ renKindSub ξ2 σ2
typSub≈ (renKindSubExt {ξ1} {ξ2} {σ1} {σ2} eq1 eq2) n = renExtₜ eq1 (σ1 .typSub n) ∙ cong (renₜ ξ2) (eq2 .typSub≈ n)
typSubₑ≈ (renKindSubExt {ξ1} {ξ2} {σ1} {σ2} eq1 eq2) n = renExtₑₜ (eq1 ⋆ₑ) (σ1 .typSubₑ n) ∙ cong (renₑₜ (ξ2 ⋆ₑ)) (eq2 .typSubₑ≈ n)
locSub≈  (renKindSubExt {ξ1} {ξ2} {σ1} {σ2} eq1 eq2) n = renExtₗ-Loc (eq1 ⋆ₗ) (σ1 .locSub n) ∙ cong (renₗ-Loc (ξ2 ⋆ₗ)) (eq2 .locSub≈ n)

↑σExtₖ : ∀{σ1 σ2} →
         σ1 ≈ₖ σ2 →
         ∀ κ → ↑σₖ[ κ ] σ1 ≈ₖ ↑σₖ[ κ ] σ2
↑σExtₖ eq κ = ▸Extₖ (renKindSubExt ≈₂-refl eq) κ (Varₖ κ zero)

↑σIdₖ : ∀ κ → ↑σₖ[ κ ] idKindSub ≈ₖ idKindSub
typSub≈  (↑σIdₖ ⋆)  zero = refl
typSub≈  (↑σIdₖ ⋆)  (suc n) = refl
typSubₑ≈ (↑σIdₖ ⋆)  n = refl
locSub≈  (↑σIdₖ ⋆)  n = refl
typSub≈  (↑σIdₖ ⋆ₑ) n = refl
typSubₑ≈ (↑σIdₖ ⋆ₑ) zero = refl
typSubₑ≈ (↑σIdₖ ⋆ₑ) (suc n) = refl
locSub≈  (↑σIdₖ ⋆ₑ) n = refl
typSub≈  (↑σIdₖ ⋆ₗ) n = refl
typSubₑ≈ (↑σIdₖ ⋆ₗ) n = refl
locSub≈  (↑σIdₖ ⋆ₗ) zero = refl
locSub≈  (↑σIdₖ ⋆ₗ) (suc n) = refl

-- Substitution on local expression types
subₑₜ : (ℕ → Typₑ) → Typₑ → Typₑ
subₑₜ σ (VarTypₑ x) = σ x
subₑₜ σ (LitTypₑ t) = LitTypₑ t

-- Kind substitution on types
subₜ : KindSub → Typ → Typ
subₜ σ (VarTyp x) = σ .typSub x
subₜ σ (At t ℓ) = At (subₑₜ (σ .typSubₑ) t) (subₗ-Loc (σ .locSub) ℓ)
subₜ σ (Arrow τ1 τ2) = Arrow (subₜ σ τ1) (subₜ σ τ2)
subₜ σ (All κ τ) = All κ (subₜ (↑σₖ[ κ ] σ) τ)

-- Substitution respects extensional equality
subExtₑₜ : ∀{σ1 σ2} →
           σ1 ≈ σ2 →
           subₑₜ σ1 ≈ subₑₜ σ2
subExtₑₜ eq (VarTypₑ x) = eq x
subExtₑₜ eq (LitTypₑ t) = refl

subExtₜ : ∀{σ1 σ2} →
          σ1 ≈ₖ σ2 →
          subₜ σ1 ≈ subₜ σ2
subExtₜ eq (VarTyp x) = eq .typSub≈ x
subExtₜ eq (At t ℓ) = cong₂ At (subExtₑₜ (eq .typSubₑ≈) t) (subExtₗ-Loc (eq .locSub≈) ℓ)
subExtₜ eq (Arrow τ1 τ2) = cong₂ Arrow (subExtₜ eq τ1) (subExtₜ eq τ2)
subExtₜ eq (All κ τ) = cong (All κ) (subExtₜ (↑σExtₖ eq κ) τ)

ιₖ : KindRen → KindSub
typSub  (ιₖ ξ) = VarTyp ∘ ξ ⋆
typSubₑ (ιₖ ξ) = VarTypₑ ∘ ξ ⋆ₑ
locSub  (ιₖ ξ) = ιₗ (ξ ⋆ₗ)

↑σιₖ : (ξ : KindRen) (κ : Kind) →  ↑σₖ[ κ ] (ιₖ ξ) ≈ₖ ιₖ (↑ₖ[ κ ] ξ)
typSub≈  (↑σιₖ ξ ⋆) zero = refl
typSub≈  (↑σιₖ ξ ⋆) (suc n) = refl
typSubₑ≈ (↑σιₖ ξ ⋆)  = ≈-refl
locSub≈  (↑σιₖ ξ ⋆)  = ≈-refl
typSub≈  (↑σιₖ ξ ⋆ₑ) = ≈-refl
typSubₑ≈ (↑σιₖ ξ ⋆ₑ) zero = refl
typSubₑ≈ (↑σιₖ ξ ⋆ₑ) (suc n) = refl
locSub≈  (↑σιₖ ξ ⋆ₑ) = ≈-refl
typSub≈  (↑σιₖ ξ ⋆ₗ) = ≈-refl
typSubₑ≈ (↑σιₖ ξ ⋆ₗ) = ≈-refl
locSub≈  (↑σιₖ ξ ⋆ₗ) zero = refl
locSub≈  (↑σιₖ ξ ⋆ₗ) (suc n) = refl

-- Substitution respects the inclusion
subιₑₜ : ∀ ξ t → subₑₜ (VarTypₑ ∘ ξ) t ≡ renₑₜ ξ t
subιₑₜ ξ (VarTypₑ x) = refl
subιₑₜ ξ (LitTypₑ t) = refl

subιₜ : ∀ ξ τ → subₜ (ιₖ ξ) τ ≡ renₜ ξ τ
subιₜ ξ (VarTyp x) = refl
subιₜ ξ (At t ℓ) = cong₂ At (subιₑₜ (ξ ⋆ₑ) t) (subιₗ-Loc (ξ ⋆ₗ) ℓ)
subιₜ ξ (Arrow τ1 τ2) = cong₂ Arrow (subιₜ ξ τ1) (subιₜ ξ τ2)
subιₜ ξ (All κ τ) = cong (All κ) (subExtₜ (↑σιₖ ξ κ) τ ∙ subιₜ (↑ₖ[ κ ] ξ) τ)

-- Substitution respects the identity
subIdₑₜ : ∀ t → subₑₜ idSubₑₜ t ≡ t
subIdₑₜ (VarTypₑ x) = refl
subIdₑₜ (LitTypₑ t) = refl

-- Substitution respects the identity
subIdₜ : ∀ τ → subₜ idKindSub τ ≡ τ
subIdₜ (VarTyp x) = refl
subIdₜ (At t ℓ) = cong₂ At (subIdₑₜ t) (subIdₗ-Loc ℓ)
subIdₜ (Arrow τ1 τ2) = cong₂ Arrow (subIdₜ τ1) (subIdₜ τ2)
subIdₜ (All κ τ) = cong (All κ) (subExtₜ (↑σIdₖ κ) τ ∙ subIdₜ τ)
