{-# OPTIONS --safe #-}

open import Data.Unit
open import Data.Nat
open import Data.List
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

open import Choreographies L E LE TE
open import LocalRenamings L E LE
open import LocationRenamings L E LE
open import Renamings L E LE
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

-- ↑ adds another variable to the context
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

-- Context inclusion
_⊆_ : LocCtx → LocCtx → Set
Θ1 ⊆ Θ2 = ∀ x → Θ1 x → Θ2 x

-- ↑ respects inclusions
↑LocCtx⊆ : ∀{Θ1 Θ2} →
           Θ1 ⊆ Θ2 →
           ↑LocCtx Θ1 ⊆ ↑LocCtx Θ2
↑LocCtx⊆ Θ1⊆Θ2 zero tt = tt
↑LocCtx⊆ Θ1⊆Θ2 (suc n) ↑Θ1n = Θ1⊆Θ2 n ↑Θ1n

-- Location well-formedness
data _⊢ₗ_ : LocCtx → Loc → Set where
  wfVar : ∀{Θ x} → Θ x → Θ ⊢ₗ Var x
  wfLit : ∀{Θ} L → Θ ⊢ₗ Lit L

-- Location well-formedness has weakening
wfWkₗ : ∀{Θ Θ' ℓ} ξ →
        Θ ≈ Θ' ∘ ξ →
        Θ ⊢ₗ ℓ →
        Θ' ⊢ₗ renₗ-Loc ξ ℓ
wfWkₗ {Θ' = Θ'} ξ Θ'≈Θ∘ξ (wfVar {x = x} Θx) = wfVar (transport (Θ'≈Θ∘ξ x) Θx)
wfWkₗ ξ Θ'≈Θ∘ξ (wfLit L) = wfLit L

-- Location well-formedness respects extensional equality
wfExtₗ : ∀{Θ1 Θ2 ℓ} →
        Θ1 ≈ Θ2 →
        Θ1 ⊢ₗ ℓ →
        Θ2 ⊢ₗ ℓ
wfExtₗ Θ1≈Θ2 (wfVar {x = x} Θ1x) = wfVar (transport (Θ1≈Θ2 x) Θ1x)
wfExtₗ Θ1≈Θ2 (wfLit L) = wfLit L

-- Location well-formedness is monotone
wfMonoₗ : ∀{Θ1 Θ2 ℓ} →
          Θ1 ⊆ Θ2 →
          Θ1 ⊢ₗ ℓ →
          Θ2 ⊢ₗ ℓ
wfMonoₗ Θ1⊆Θ2 (wfVar {x = x} Θ1x) = wfVar (Θ1⊆Θ2 x Θ1x)
wfMonoₗ Θ1⊆Θ2 (wfLit L) = wfLit L

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
        Θ' ⊢ₗₗ renₗ-List ξ ρ
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

wfArrow₁ : ∀{Θ τ1 τ2} → Θ ⊢ₜ Arrow τ1 τ2 → Θ ⊢ₜ τ1
wfArrow₁ (wfArrow τ1 τ2) = τ1

wfArrow₂ : ∀{Θ τ1 τ2} → Θ ⊢ₜ Arrow τ1 τ2 → Θ ⊢ₜ τ2
wfArrow₂ (wfArrow τ1 τ2) = τ2

wfAllLocArg : ∀{Θ τ} → Θ ⊢ₜ AllLoc τ → ↑LocCtx Θ ⊢ₜ τ
wfAllLocArg (wfAllLoc τ) = τ


-- Type well-formedness has weakening
wfWkₜ : ∀{Θ Θ' τ} ξ →
        Θ ≈ Θ' ∘ ξ →
        Θ ⊢ₜ τ →
        Θ' ⊢ₜ renₜ ξ τ
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

-- Type well-formedness is monotone
wfMonoₜ : ∀{Θ1 Θ2 τ} →
          Θ1 ⊆ Θ2 →
          Θ1 ⊢ₜ τ →
          Θ2 ⊢ₜ τ
wfMonoₜ Θ1⊆Θ2 (wfAt Θ⊢ℓ) = wfAt (wfMonoₗ Θ1⊆Θ2 Θ⊢ℓ) 
wfMonoₜ Θ1⊆Θ2 (wfArrow Θ1⊢τ1 Θ1⊢τ2) = wfArrow (wfMonoₜ Θ1⊆Θ2 Θ1⊢τ1) (wfMonoₜ Θ1⊆Θ2 Θ1⊢τ2)
wfMonoₜ Θ1⊆Θ2 (wfAllLoc ↑Θ1⊢τ) = wfAllLoc (wfMonoₜ (↑LocCtx⊆ Θ1⊆Θ2) ↑Θ1⊢τ)

-- If τ is well-formed in Θ, then ↑τ is well-formed in ↑Θ
wfTy↑ : ∀{Θ τ} → Θ ⊢ₜ τ → ↑LocCtx Θ ⊢ₜ ↑ₜ τ
wfTy↑ {Θ} Θ⊢τ = wfWkₜ suc Θ≈↑Θ∘suc Θ⊢τ
  where
  Θ≈↑Θ∘suc : Θ ≈ ↑LocCtx Θ ∘ suc
  Θ≈↑Θ∘suc n = refl


{-
  A location substitution σ changes context Θ1 to context Θ2
  if for every variable n in the scope of Θ1, σ assigns n
  to a location which is well-formed under Θ2
-}
_∶_⇒ₗ_ : (σ : ℕ → Loc) (Θ1 Θ2 : ℕ → Set) → Set
σ ∶ Θ1 ⇒ₗ Θ2 = ∀ n → Θ1 n → Θ2 ⊢ₗ σ n

-- The identity location substitution changes any context to itself
idSubₗ⇒ : ∀ Θ → idSubₗ ∶ Θ ⇒ₗ Θ
idSubₗ⇒ Θ n Θn = wfVar Θn

-- Instantiating a well-formed location preserves change in context
▸ₗ⇒ : ∀{Θ1 Θ2 σ ℓ} →
      σ ∶ Θ1 ⇒ₗ Θ2 →
      Θ2 ⊢ₗ ℓ →
      (σ ▸ₗ ℓ) ∶ ↑LocCtx Θ1 ⇒ₗ Θ2
▸ₗ⇒ σ⇒ Θ2⊢ℓ zero tt = Θ2⊢ℓ
▸ₗ⇒ σ⇒ Θ2⊢ℓ (suc n) Θ1n = σ⇒ n Θ1n

-- ↑ preserves change in context
↑σₗ⇒ : ∀{σ Θ1 Θ2} →
       σ ∶ Θ1 ⇒ₗ Θ2 →
       ↑σₗ σ ∶ ↑LocCtx Θ1 ⇒ₗ ↑LocCtx Θ2
↑σₗ⇒ σ⇒ zero tt = wfVar tt
↑σₗ⇒ {σ} {Θ1} {Θ2} σ⇒ (suc n) Θ1n =
  subst (λ x → ↑LocCtx Θ2 ⊢ₗ x) (sym (subιₗ-Loc suc (σ n))) ↑Θ2⊢σn⟨suc⟩
  where
  Θ2≈↑Θ2∘suc : Θ2 ≈ ↑LocCtx Θ2 ∘ suc
  Θ2≈↑Θ2∘suc zero = refl
  Θ2≈↑Θ2∘suc (suc n) = refl

  ↑Θ2⊢σn⟨suc⟩ : ↑LocCtx Θ2 ⊢ₗ renₗ-Loc suc (σ n)
  ↑Θ2⊢σn⟨suc⟩ = wfWkₗ suc Θ2≈↑Θ2∘suc (σ⇒ n Θ1n)

-- Location well-formedness is closed under context-changing substitutions
wfSubₗ : ∀{σ Θ1 Θ2 ℓ} →
         σ ∶ Θ1 ⇒ₗ Θ2 →
         Θ1 ⊢ₗ ℓ →
         Θ2 ⊢ₗ subₗ-Loc σ ℓ
wfSubₗ σ⇒ (wfVar Θ1x) = σ⇒ _ Θ1x
wfSubₗ σ⇒ (wfLit L) = wfLit L

-- Location list well-formedness is closed under context-changing substitutions
wfSubₗₗ : ∀{σ Θ1 Θ2 ρ} →
         σ ∶ Θ1 ⇒ₗ Θ2 →
         Θ1 ⊢ₗₗ ρ →
         Θ2 ⊢ₗₗ subₗ-List σ ρ
wfSubₗₗ σ⇒ wfNil = wfNil
wfSubₗₗ σ⇒ (wfCons Θ⊢ℓ Θ⊢ρ) = wfCons (wfSubₗ σ⇒ Θ⊢ℓ) (wfSubₗₗ σ⇒ Θ⊢ρ)

-- Type well-formedness is closed under context-changing substitutions
wfSubₜ : ∀{σ Θ1 Θ2 τ} →
         σ ∶ Θ1 ⇒ₗ Θ2 →
         Θ1 ⊢ₜ τ →
         Θ2 ⊢ₜ subₜ σ τ
wfSubₜ σ⇒ (wfAt Θ⊢ℓ) = wfAt (wfSubₗ σ⇒ Θ⊢ℓ)
wfSubₜ σ⇒ (wfArrow τ1 τ2) = wfArrow (wfSubₜ σ⇒ τ1) (wfSubₜ σ⇒ τ2)
wfSubₜ σ⇒ (wfAllLoc τ) = wfAllLoc (wfSubₜ (↑σₗ⇒ σ⇒) τ)
