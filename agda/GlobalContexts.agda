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

module GlobalContexts
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
open import LocationContexts L E LE TE
open import LocalContexts L E LE TE
open Location L
open Language E
open LawfulLanguage LE
open TypedLocalLanguage TE


-- Choreographic/global contexts
Ctx : Set
Ctx = ℕ → Typ

-- Add a type to the context
_,,_ : Ctx → Typ → Ctx
(Γ ,, τ) zero = τ
(Γ ,, τ) (suc n) = Γ n

-- Adding types respects extensional equality
addCtxExt : ∀{Γ Γ' τ} →
            Γ ≈ Γ' → Γ ,, τ ≈ Γ' ,, τ
addCtxExt Γ≈Γ' zero = refl
addCtxExt Γ≈Γ' (suc n) = Γ≈Γ' n

-- Renaming on global contexts
renCtx : Ctx → (ℕ → ℕ) → Ctx
renCtx Γ ξ n = renₜ (Γ n) ξ

-- Renaming distributes over adding a type
renCtx,, : ∀ Γ τ ξ →
           renCtx (Γ ,, τ) ξ ≈ renCtx Γ ξ ,, renₜ τ ξ
renCtx,, Γ τ ξ zero = refl
renCtx,, Γ τ ξ (suc n) = refl

-- ↑ on global contexts
↑Ctx : Ctx → Ctx
↑Ctx Γ = renCtx Γ suc

-- ↑ respects extensional equality
↑CtxExt : ∀{Γ1 Γ2} → Γ1 ≈ Γ2 → ↑Ctx Γ1 ≈ ↑Ctx Γ2
↑CtxExt Γ1≈Γ2 n = cong₂ renₜ (Γ1≈Γ2 n) refl

-- ↑ distributes over renaming contexts
renCtx↑ : ∀ Γ ξ → renCtx (↑Ctx Γ) (↑ ξ) ≈ ↑Ctx (renCtx Γ ξ)
renCtx↑ Γ ξ n = eq
  where
  open ≡-Reasoning

  eq : renₜ (renₜ (Γ n) suc) (↑ ξ) ≡ renₜ (renₜ (Γ n) ξ) suc
  eq = 
    renₜ (renₜ (Γ n) suc) (↑ ξ) ≡⟨ sym (renFuseₜ suc (↑ ξ) (Γ n)) ⟩
    renₜ (Γ n) (↑ ξ ∘ suc)      ≡⟨ renExtₜ (↑∘suc ξ) (Γ n) ⟩
    renₜ (Γ n) (suc ∘ ξ)        ≡⟨ renFuseₜ ξ suc (Γ n) ⟩
    renₜ (renₜ (Γ n) ξ) suc     ∎

{-
  A global context is well-formed if
  each type that it maps to is well-formed
-}
_⊢_ : LocCtx → Ctx → Set
Θ ⊢ Γ = ∀ n → Θ ⊢ₜ Γ n

-- Context well-formedness has weakening
wfCtxWk : ∀{Θ Θ' Γ} ξ →
          Θ ≈ Θ' ∘ ξ →
          Θ ⊢ Γ →
          Θ' ⊢ renCtx Γ ξ
wfCtxWk ξ Θ≈Θ'∘ξ Θ⊢Γ n = wfWkₜ ξ Θ≈Θ'∘ξ (Θ⊢Γ n)

-- Context well-formedness respects extensional equality
wfCtxExt : ∀{Θ1 Θ2 Γ1 Γ2} →
           Θ1 ≈ Θ2 →
           Γ1 ≈ Γ2 →
           Θ1 ⊢ Γ1 →
           Θ2 ⊢ Γ2
wfCtxExt Θ1≈Θ2 Γ1≈Γ2 Θ1⊢Γ1 n = subst (λ x → _ ⊢ₜ x) (Γ1≈Γ2 n) (wfExtₜ Θ1≈Θ2 (Θ1⊢Γ1 n))
