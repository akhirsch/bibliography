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

module LocationContexts
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
open import Types L E LE TE
open Location L
open Language E
open LawfulLanguage LE
open TypedLocalLanguage TE

{-
  Location contexts are an infinite map which
  distinguishes the in-scope location variables.
  That is, Θ n is inhabited iff n is in scope.
-}
LocCtx : Set₁
LocCtx = ℕ → Set

-- ↑ adds another variale to the context
↑LocCtx : LocCtx → LocCtx
↑LocCtx Θ zero = ⊤
↑LocCtx Θ (suc n) = Θ n

-- ↑ respects extensional equality
↑LocCtxExt : ∀{Θ1 Θ2} → Θ1 ≈ Θ2 → ↑LocCtx Θ1 ≈ ↑LocCtx Θ2
↑LocCtxExt Θ1≈Θ2 zero = refl
↑LocCtxExt Θ1≈Θ2 (suc n) = Θ1≈Θ2 n

-- ↑ distributes over renaming
↑-distr-∘ : ∀ Θ ξ → ↑LocCtx (Θ ∘ ξ) ≈ ↑LocCtx Θ ∘ ↑ ξ
↑-distr-∘ Θ ξ zero = refl
↑-distr-∘ Θ ξ (suc n) = refl

-- Location well-formedness
data _⊢ₗ_ : LocCtx → Loc → Set where
  wfVar : ∀{Θ x} → Θ x → Θ ⊢ₗ Var x
  wfLit : ∀{Θ} L → Θ ⊢ₗ Lit L

-- Location well-formedness has weakening
wfWkₗ : ∀{Θ Θ' ℓ} ξ →
        Θ ≈ Θ' ∘ ξ →
        Θ ⊢ₗ ℓ →
        Θ' ⊢ₗ renₗ-Loc ℓ ξ
wfWkₗ {Θ' = Θ'} ξ Θ'≈Θ∘ξ (wfVar {x = x} Θx) = wfVar (transport (Θ'≈Θ∘ξ x) Θx)
wfWkₗ ξ Θ'≈Θ∘ξ (wfLit L) = wfLit L

-- Location well-formedness respects extensional equality
wfExtₗ : ∀{Θ1 Θ2 ℓ} →
        Θ1 ≈ Θ2 →
        Θ1 ⊢ₗ ℓ →
        Θ2 ⊢ₗ ℓ
wfExtₗ Θ1≈Θ2 (wfVar {x = x} Θ1x) = wfVar (transport (Θ1≈Θ2 x) Θ1x)
wfExtₗ Θ1≈Θ2 (wfLit L) = wfLit L

-- Location list well-formedness
data _⊢ₗₗ_ : LocCtx → LocList → Set where
  wfNil : ∀{Θ} → Θ ⊢ₗₗ []
  wfCons : ∀{Θ ℓ ρ}
           (Θ⊢ℓ : Θ ⊢ₗ ℓ)
           (Θ⊢ρ : Θ ⊢ₗₗ ρ) →
           Θ ⊢ₗₗ (ℓ ∷ ρ)

-- Location list well-formedness has weakening
wfWkₗₗ : ∀{Θ Θ' ρ} ξ →
        Θ ≈ Θ' ∘ ξ →
        Θ ⊢ₗₗ ρ →
        Θ' ⊢ₗₗ renₗ-List ρ ξ
wfWkₗₗ ξ Θ≈Θ'∘ξ wfNil = wfNil
wfWkₗₗ ξ Θ≈Θ'∘ξ (wfCons Θ⊢ℓ Θ⊢ρ) = wfCons (wfWkₗ ξ Θ≈Θ'∘ξ Θ⊢ℓ) (wfWkₗₗ ξ Θ≈Θ'∘ξ Θ⊢ρ)

-- Location list well-formedness respects extensional equality
wfExtₗₗ : ∀{Θ1 Θ2 ρ} →
        Θ1 ≈ Θ2 →
        Θ1 ⊢ₗₗ ρ →
        Θ2 ⊢ₗₗ ρ
wfExtₗₗ Θ1≈Θ2 wfNil = wfNil
wfExtₗₗ Θ1≈Θ2 (wfCons Θ⊢ℓ Θ⊢ρ) = wfCons (wfExtₗ Θ1≈Θ2 Θ⊢ℓ) (wfExtₗₗ Θ1≈Θ2 Θ⊢ρ)

-- Choreography type well-formedness
data _⊢ₜ_ : LocCtx → Typ → Set where
  wfAt : ∀{Θ t ℓ} (Θ⊢ℓ : Θ ⊢ₗ ℓ) → Θ ⊢ₜ At t ℓ
  wfArrow : ∀{Θ τ1 τ2}
            (Θ⊢τ1 : Θ ⊢ₜ τ1) (Θ⊢τ2 : Θ ⊢ₜ τ2) →
            Θ ⊢ₜ Arrow τ1 τ2
  wfAllLoc : ∀{Θ τ} →
             (↑Θ⊢τ : ↑LocCtx Θ ⊢ₜ τ) →
             Θ ⊢ₜ AllLoc τ

-- Type well-formedness has weakening
wfWkₜ : ∀{Θ Θ' τ} ξ →
        Θ ≈ Θ' ∘ ξ →
        Θ ⊢ₜ τ →
        Θ' ⊢ₜ renₜ τ ξ
wfWkₜ ξ Θ≈Θ'∘ξ (wfAt Θ⊢ℓ) = wfAt (wfWkₗ ξ Θ≈Θ'∘ξ Θ⊢ℓ)
wfWkₜ ξ Θ≈Θ'∘ξ (wfArrow Θ⊢τ1 Θ⊢τ2) = wfArrow (wfWkₜ ξ Θ≈Θ'∘ξ Θ⊢τ1) (wfWkₜ ξ Θ≈Θ'∘ξ Θ⊢τ2)
wfWkₜ {Θ} {Θ'} ξ Θ≈Θ'∘ξ (wfAllLoc ↑Θ⊢τ) = wfAllLoc (wfWkₜ (↑ ξ) ↑Θ≈↑Θ'∘↑ξ ↑Θ⊢τ)
  where
  ↑Θ≈↑Θ'∘↑ξ : ↑LocCtx Θ ≈ ↑LocCtx Θ' ∘ ↑ ξ
  ↑Θ≈↑Θ'∘↑ξ = ≈-trans (↑LocCtxExt Θ≈Θ'∘ξ) (↑-distr-∘ Θ' ξ)

-- Type well-formedness respects extensional equality
wfExtₜ : ∀{Θ1 Θ2 τ} →
        Θ1 ≈ Θ2 →
        Θ1 ⊢ₜ τ →
        Θ2 ⊢ₜ τ
wfExtₜ Θ1≈Θ2 (wfAt Θ⊢ℓ) = wfAt (wfExtₗ Θ1≈Θ2 Θ⊢ℓ)
wfExtₜ Θ1≈Θ2 (wfArrow Θ⊢τ1 Θ⊢τ2) = wfArrow (wfExtₜ Θ1≈Θ2 Θ⊢τ1) (wfExtₜ Θ1≈Θ2 Θ⊢τ2)
wfExtₜ Θ1≈Θ2 (wfAllLoc ↑Θ⊢τ) = wfAllLoc (wfExtₜ (↑LocCtxExt Θ1≈Θ2) ↑Θ⊢τ)
