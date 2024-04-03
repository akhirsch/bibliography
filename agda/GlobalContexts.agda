{-# OPTIONS --safe #-}

open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Nat.Properties
open import Data.List hiding (map)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map)
open import Data.Maybe
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
Ctx = ℕ → Maybe Typ

-- Add a type to the context
_,,_ : Ctx → Typ → Ctx
(Γ ,, τ) zero = just τ
(Γ ,, τ) (suc n) = Γ n

-- Adding types respects extensional equality
addCtxExt : ∀{Γ Γ' τ} →
            Γ ≈ Γ' → Γ ,, τ ≈ Γ' ,, τ
addCtxExt Γ≈Γ' zero = refl
addCtxExt Γ≈Γ' (suc n) = Γ≈Γ' n

-- Renaming locations on global contexts
renCtx : (ℕ → ℕ) → Ctx → Ctx
renCtx ξ Γ n = map (renₜ ξ) (Γ n)

-- Renaming distributes over adding a type
renCtx,, : ∀ Γ τ ξ →
           renCtx ξ (Γ ,, τ) ≈ renCtx ξ Γ ,, renₜ ξ τ
renCtx,, Γ τ ξ zero = refl
renCtx,, Γ τ ξ (suc n) = refl

-- Renaming distributes over composition
renCtx∘ : ∀ Γ ξ1 ξ2 →
          renCtx ξ2 (Γ ∘ ξ1) ≈ renCtx ξ2 Γ ∘ ξ1
renCtx∘ Γ ξ1 ξ2 n = refl

-- ↑ for location variables on global contexts
↑Ctx : Ctx → Ctx
↑Ctx Γ = renCtx suc Γ

-- ↑ respects extensional equality
↑CtxExt : ∀{Γ1 Γ2} → Γ1 ≈ Γ2 → ↑Ctx Γ1 ≈ ↑Ctx Γ2
↑CtxExt {Γ1} {Γ2} Γ1≈Γ2 n = cong (map (renₜ suc)) (Γ1≈Γ2 n)

-- ↑ distributes over composition
↑Ctx∘ : ∀ Γ ξ →
        ↑Ctx (Γ ∘ ξ) ≈ ↑Ctx Γ ∘ ξ
↑Ctx∘ Γ ξ = renCtx∘ Γ ξ suc

-- ↑ distributes over renaming contexts
renCtx↑ : ∀ Γ ξ → renCtx (↑ ξ) (↑Ctx Γ) ≈ ↑Ctx (renCtx ξ Γ)
renCtx↑ Γ ξ n =
  map (renₜ (↑ ξ)) (map (renₜ suc) (Γ n)) ≡⟨ sym (map∘ (renₜ (↑ ξ)) (renₜ suc) (Γ n)) ⟩
  map (renₜ (↑ ξ) ∘ renₜ suc) (Γ n)       ≡⟨ sym (mapExt (renFuseₜ (↑ ξ) suc) (Γ n)) ⟩
  map (renₜ (↑ ξ ∘ suc)) (Γ n)            ≡⟨ mapExt (renExtₜ (↑∘suc ξ)) (Γ n) ⟩
  map (renₜ (suc ∘ ξ)) (Γ n)              ≡⟨ mapExt (renFuseₜ suc ξ) (Γ n) ⟩
  map (renₜ suc ∘ renₜ ξ) (Γ n)           ≡⟨ map∘ (renₜ suc) (renₜ ξ) (Γ n) ⟩
  map (renₜ suc) (map (renₜ ξ) (Γ n)) ∎

{-
  A global context is well-formed if
  each type that it maps to is well-formed
-}
_⊢_ : LocCtx → Ctx → Set
Θ ⊢ Γ = ∀ n τ → Γ n ≡ just τ → Θ ⊢ₜ τ

-- Context well-formedness has weakening
wfCtxWk : ∀{Θ Θ' Γ} ξ →
          Θ ≈ Θ' ∘ ξ →
          Θ ⊢ Γ →
          Θ' ⊢ renCtx ξ Γ
wfCtxWk {Θ} {Θ'} {Γ} ξ Θ≈Θ'∘ξ Θ⊢Γ n τ p with Γ n | inspect Γ n
wfCtxWk {Θ} {Θ'} {Γ} ξ Θ≈Θ'∘ξ Θ⊢Γ n .(renₜ ξ τ') refl | just τ' | [ Γ[n]≡τ' ] =
  wfWkₜ ξ Θ≈Θ'∘ξ (Θ⊢Γ n τ' Γ[n]≡τ')
wfCtxWk {Θ} {Θ'} {Γ} ξ Θ≈Θ'∘ξ Θ⊢Γ n τ () | nothing | [ Γ[n]≡⊥ ]

-- Context well-formedness respects extensional equality
wfCtxExt : ∀{Θ1 Θ2 Γ1 Γ2} →
           Θ1 ≈ Θ2 →
           Γ1 ≈ Γ2 →
           Θ1 ⊢ Γ1 →
           Θ2 ⊢ Γ2
wfCtxExt {Γ1 = Γ1} {Γ2} Θ1≈Θ2 Γ1≈Γ2 Θ1⊢Γ1 n τ Γ[n]≡τ with Γ2 n | inspect Γ2 n
wfCtxExt {Γ1 = Γ1} {Γ2} Θ1≈Θ2 Γ1≈Γ2 Θ1⊢Γ1 n .τ' refl | just τ' | [ Γ2[n]≡τ' ] =
  wfExtₜ Θ1≈Θ2 (Θ1⊢Γ1 n τ' (Γ1≈Γ2 n ∙ Γ2[n]≡τ'))

-- Context well-formedness is monotone
wfMono : ∀{Θ1 Θ2 Γ} →
          Θ1 ⊆ Θ2 →
          Θ1 ⊢ Γ →
          Θ2 ⊢ Γ
wfMono {Γ = Γ} Θ1⊆Θ2 Θ1⊢Γ n τ Γ[n]≡τ with Γ n | inspect Γ n
wfMono {Γ = Γ} Θ1⊆Θ2 Θ1⊢Γ n .τ' refl | just τ' | [ Γ[n]≡τ' ] =
  wfMonoₜ Θ1⊆Θ2 (Θ1⊢Γ n τ' Γ[n]≡τ')

-- Adding a well-formed type to a well-formed context retains its well-formedness
wfCtx,, : ∀{Θ Γ τ} →
          Θ ⊢ Γ →
          Θ ⊢ₜ τ →
          Θ ⊢ (Γ ,, τ)
wfCtx,, Θ⊢Γ Θ⊢τ zero τ' refl = Θ⊢τ
wfCtx,, Θ⊢Γ Θ⊢τ (suc n) τ' Γ[n]≡τ' = Θ⊢Γ n τ' Γ[n]≡τ'

-- Removing the top-most type from a well-formed context retains its well-formedness
wfCtxTail : ∀{Θ Γ τ} →
            Θ ⊢ (Γ ,, τ) →
            Θ ⊢ Γ
wfCtxTail Θ⊢Γ,,τ n = Θ⊢Γ,,τ (suc n)

-- If Γ is well-formed in Θ, then ↑Γ is well-formed in ↑Γ
wfCtx↑ : ∀{Θ Γ} → Θ ⊢ Γ → ↑LocCtx Θ ⊢ ↑Ctx Γ
wfCtx↑ {Γ = Γ} Θ⊢Γ n τ ↑Γ[n]≡τ with Γ n | inspect Γ n
wfCtx↑ {Γ = Γ} Θ⊢Γ n .(renₜ suc τ) refl | just τ | [ eq ] =
  wfTy↑ (Θ⊢Γ n τ eq)

-- Substitution of locations in global contexts
subₗ-Ctx : (ℕ → Loc) → Ctx → Ctx
subₗ-Ctx σ Γ n = map (subₜ σ) (Γ n)

-- Context well-formedness is closed under change of context
wfCtxSub : ∀{Θ1 Θ2 Γ σ} →
           σ ∶ Θ1 ⇒ₗ Θ2 →
           Θ1 ⊢ Γ →
           Θ2 ⊢ subₗ-Ctx σ Γ
wfCtxSub {Γ = Γ} σ⇒ Θ1⊢Γ n τ Γ⟨σ⟩[n]≡τ with Γ n | inspect Γ n
wfCtxSub {Γ = Γ} {σ} σ⇒ Θ1⊢Γ n .(subₜ σ τ) refl | just τ | [ eq ] =
  wfSubₜ σ⇒ (Θ1⊢Γ n τ eq)