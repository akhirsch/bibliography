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
open import LocationRenamings L E LE
open import LocationSubstitutions L E LE
open import Types L E LE TE
open import LocationContexts L E LE TE
open import LocalContexts L E LE TE


open Location L
open Language E
open LawfulLanguage LE
open TypedLocalLanguage TE
open ≡-Reasoning


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

-- Renaming locations on global contexts
renCtx : Ctx → (ℕ → ℕ) → Ctx
renCtx Γ ξ n = renₜ (Γ n) ξ

-- Renaming distributes over adding a type
renCtx,, : ∀ Γ τ ξ →
           renCtx (Γ ,, τ) ξ ≈ renCtx Γ ξ ,, renₜ τ ξ
renCtx,, Γ τ ξ zero = refl
renCtx,, Γ τ ξ (suc n) = refl

-- Renaming distributes over composition
renCtx∘ : ∀ Γ ξ1 ξ2 →
          renCtx (Γ ∘ ξ1) ξ2 ≈ renCtx Γ ξ2 ∘ ξ1
renCtx∘ Γ ξ1 ξ2 n = refl

-- ↑ for location variables on global contexts
↑Ctx : Ctx → Ctx
↑Ctx Γ = renCtx Γ suc

-- ↑ respects extensional equality
↑CtxExt : ∀{Γ1 Γ2} → Γ1 ≈ Γ2 → ↑Ctx Γ1 ≈ ↑Ctx Γ2
↑CtxExt Γ1≈Γ2 n = cong₂ renₜ (Γ1≈Γ2 n) refl

-- ↑ distributes over composition
↑Ctx∘ : ∀ Γ ξ →
        ↑Ctx (Γ ∘ ξ) ≈ ↑Ctx Γ ∘ ξ
↑Ctx∘ Γ ξ = renCtx∘ Γ ξ suc

-- ↑ distributes over renaming contexts
renCtx↑ : ∀ Γ ξ → renCtx (↑Ctx Γ) (↑ ξ) ≈ ↑Ctx (renCtx Γ ξ)
renCtx↑ Γ ξ n = eq
  where
  
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

-- Context well-formedness is monotone
wfMono : ∀{Θ1 Θ2 Γ} →
          Θ1 ⊆ Θ2 →
          Θ1 ⊢ Γ →
          Θ2 ⊢ Γ
wfMono Θ1⊆Θ2 Θ1⊢Γ n = wfMonoₜ Θ1⊆Θ2 (Θ1⊢Γ n)

-- Adding a well-formed type to a well-formed context retains its well-formedness
wfCtx,, : ∀{Θ Γ τ} →
          Θ ⊢ Γ →
          Θ ⊢ₜ τ →
          Θ ⊢ (Γ ,, τ)
wfCtx,, Θ⊢Γ Θ⊢τ zero = Θ⊢τ
wfCtx,, Θ⊢Γ Θ⊢τ (suc n) = Θ⊢Γ n

-- Removing the top-most type from a well-formed context retains its well-formedness
wfCtxTail : ∀{Θ Γ τ} →
            Θ ⊢ (Γ ,, τ) →
            Θ ⊢ Γ
wfCtxTail Θ⊢Γ,,τ n = Θ⊢Γ,,τ (suc n)

-- If Γ is well-formed in Θ, then ↑Γ is well-formed in ↑Γ
wfCtx↑ : ∀{Θ Γ} → Θ ⊢ Γ → ↑LocCtx Θ ⊢ ↑Ctx Γ
wfCtx↑ Θ⊢Γ n = wfTy↑ (Θ⊢Γ n)

-- Substitution of locations in global contexts
subₗ-Ctx : Ctx → (ℕ → Loc) → Ctx
subₗ-Ctx Γ σ n = subₜ (Γ n) σ

-- Context well-formedness is closed under change of context
wfCtxSub : ∀{Θ1 Θ2 Γ σ} →
           σ ∶ Θ1 ⇒ₗ Θ2 →
           Θ1 ⊢ Γ →
           Θ2 ⊢ subₗ-Ctx Γ σ
wfCtxSub σ⇒ Θ1⊢Γ n = wfSubₜ σ⇒ (Θ1⊢Γ n)
