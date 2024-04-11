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

module KindContexts
  (L : Location)
  (E : TypedLocalLanguage L)
  where

open import Types L E
open import KindSubstitutions L E

open Location L
open TypedLocalLanguage E
open ≡-Reasoning

{-
  Kind contexts are for each kind an infinite map which
  distinguishes the in-scope variables of that kind.
  That is, Θ κ n is inhabited iff n : κ is in scope.
-}
KindCtx : Set₁
KindCtx = Kind → ℕ → Set

-- ↑ adds another variable to the context
↑KindCtx[_] : Kind → KindCtx → KindCtx
↑KindCtx[ ⋆ ] Θ ⋆ zero = ⊤
↑KindCtx[ ⋆ ] Θ ⋆ (suc n) = Θ ⋆ n
↑KindCtx[ ⋆ ] Θ ⋆ₑ = Θ ⋆ₑ
↑KindCtx[ ⋆ ] Θ ⋆ₗ = Θ ⋆ₗ
↑KindCtx[ ⋆ₑ ] Θ ⋆ = Θ ⋆
↑KindCtx[ ⋆ₑ ] Θ ⋆ₑ zero = ⊤
↑KindCtx[ ⋆ₑ ] Θ ⋆ₑ (suc n) = Θ ⋆ₑ n
↑KindCtx[ ⋆ₑ ] Θ ⋆ₗ = Θ ⋆ₗ
↑KindCtx[ ⋆ₗ ] Θ ⋆ = Θ ⋆
↑KindCtx[ ⋆ₗ ] Θ ⋆ₑ = Θ ⋆ₑ
↑KindCtx[ ⋆ₗ ] Θ ⋆ₗ zero = ⊤
↑KindCtx[ ⋆ₗ ] Θ ⋆ₗ (suc n) = Θ ⋆ₗ n

-- ↑ respects extensional equality
↑KindCtxExt : ∀{Θ1 Θ2} → Θ1 ≈₂ Θ2 → ∀ κ → ↑KindCtx[ κ ] Θ1 ≈₂ ↑KindCtx[ κ ] Θ2
↑KindCtxExt eq ⋆ ⋆ zero = refl
↑KindCtxExt eq ⋆ ⋆ (suc n) = eq ⋆ n
↑KindCtxExt eq ⋆ ⋆ₑ = eq ⋆ₑ
↑KindCtxExt eq ⋆ ⋆ₗ = eq ⋆ₗ
↑KindCtxExt eq ⋆ₑ ⋆ = eq ⋆
↑KindCtxExt eq ⋆ₑ ⋆ₑ zero = refl
↑KindCtxExt eq ⋆ₑ ⋆ₑ (suc n) = eq ⋆ₑ n
↑KindCtxExt eq ⋆ₑ ⋆ₗ = eq ⋆ₗ
↑KindCtxExt eq ⋆ₗ ⋆ = eq ⋆
↑KindCtxExt eq ⋆ₗ ⋆ₑ = eq ⋆ₑ
↑KindCtxExt eq ⋆ₗ ⋆ₗ zero = refl
↑KindCtxExt eq ⋆ₗ ⋆ₗ (suc n) = eq ⋆ₗ n

renKindCxt : KindRen → KindCtx → KindCtx
renKindCxt ξ Θ κ n = Θ κ (ξ κ n)

-- ↑ distributes over renaming
↑KindCtx-distr-renKindCxt : ∀ Θ ξ κ → ↑KindCtx[ κ ] (renKindCxt ξ Θ) ≈₂ renKindCxt (↑ₖ[ κ ] ξ) (↑KindCtx[ κ ] Θ)
↑KindCtx-distr-renKindCxt Θ ξ ⋆ ⋆ zero = refl
↑KindCtx-distr-renKindCxt Θ ξ ⋆ ⋆ (suc n) = refl
↑KindCtx-distr-renKindCxt Θ ξ ⋆ ⋆ₑ = ≈-refl
↑KindCtx-distr-renKindCxt Θ ξ ⋆ ⋆ₗ = ≈-refl
↑KindCtx-distr-renKindCxt Θ ξ ⋆ₑ ⋆ = ≈-refl
↑KindCtx-distr-renKindCxt Θ ξ ⋆ₑ ⋆ₑ zero = refl
↑KindCtx-distr-renKindCxt Θ ξ ⋆ₑ ⋆ₑ (suc n) = refl
↑KindCtx-distr-renKindCxt Θ ξ ⋆ₑ ⋆ₗ = ≈-refl
↑KindCtx-distr-renKindCxt Θ ξ ⋆ₗ ⋆ = ≈-refl
↑KindCtx-distr-renKindCxt Θ ξ ⋆ₗ ⋆ₑ = ≈-refl
↑KindCtx-distr-renKindCxt Θ ξ ⋆ₗ ⋆ₗ zero = refl
↑KindCtx-distr-renKindCxt Θ ξ ⋆ₗ ⋆ₗ (suc n) = refl

-- Context inclusion
_⊆_ : KindCtx → KindCtx → Set
Θ1 ⊆ Θ2 = ∀ κ x → Θ1 κ x → Θ2 κ x

-- ↑ respects inclusions
↑KindCtx⊆ : ∀{Θ1 Θ2} →
            Θ1 ⊆ Θ2 →
            ∀ κ → ↑KindCtx[ κ ] Θ1 ⊆ ↑KindCtx[ κ ] Θ2
↑KindCtx⊆ Θ1⊆Θ2 ⋆ ⋆ zero = λ _ → tt
↑KindCtx⊆ Θ1⊆Θ2 ⋆ ⋆ (suc n) = Θ1⊆Θ2 ⋆ n
↑KindCtx⊆ Θ1⊆Θ2 ⋆ ⋆ₑ = Θ1⊆Θ2 ⋆ₑ
↑KindCtx⊆ Θ1⊆Θ2 ⋆ ⋆ₗ = Θ1⊆Θ2 ⋆ₗ
↑KindCtx⊆ Θ1⊆Θ2 ⋆ₑ ⋆ = Θ1⊆Θ2 ⋆
↑KindCtx⊆ Θ1⊆Θ2 ⋆ₑ ⋆ₑ zero = λ _ → tt
↑KindCtx⊆ Θ1⊆Θ2 ⋆ₑ ⋆ₑ (suc n) = Θ1⊆Θ2 ⋆ₑ n
↑KindCtx⊆ Θ1⊆Θ2 ⋆ₑ ⋆ₗ = Θ1⊆Θ2 ⋆ₗ
↑KindCtx⊆ Θ1⊆Θ2 ⋆ₗ ⋆ = Θ1⊆Θ2 ⋆
↑KindCtx⊆ Θ1⊆Θ2 ⋆ₗ ⋆ₑ = Θ1⊆Θ2 ⋆ₑ
↑KindCtx⊆ Θ1⊆Θ2 ⋆ₗ ⋆ₗ zero = λ _ → tt
↑KindCtx⊆ Θ1⊆Θ2 ⋆ₗ ⋆ₗ (suc n) = Θ1⊆Θ2 ⋆ₗ n

-- Location well-formedness
data _⊢ₗ_ (Θ : KindCtx) : Loc → Set where
  wfVarLoc : ∀ x → Θ ⋆ₗ x → Θ ⊢ₗ VarLoc x
  wfLitLoc : ∀ L → Θ ⊢ₗ LitLoc L

-- Well-formed renamings between kind contexts
KindREN : (ξ : KindRen) (Θ1 Θ2 : KindCtx) → Set₁
KindREN ξ Θ1 Θ2 = Θ1 ≈₂ renKindCxt ξ Θ2

idKindREN : ∀{Θ} → KindREN idKindRen Θ Θ
idKindREN κ n = refl

↑KindREN : ∀{Θ1 Θ2 ξ} →
           KindREN ξ Θ1 Θ2 →
           ∀ κ → KindREN (↑ₖ[ κ ] ξ) (↑KindCtx[ κ ] Θ1) (↑KindCtx[ κ ] Θ2)
↑KindREN {ξ = ξ} ξ⇒ ⋆ ⋆ zero = refl
↑KindREN {ξ = ξ} ξ⇒ ⋆ ⋆ (suc n) = ξ⇒ ⋆ n
↑KindREN {ξ = ξ} ξ⇒ ⋆ ⋆ₑ = ξ⇒ ⋆ₑ
↑KindREN {ξ = ξ} ξ⇒ ⋆ ⋆ₗ = ξ⇒ ⋆ₗ
↑KindREN {ξ = ξ} ξ⇒ ⋆ₑ ⋆ = ξ⇒ ⋆
↑KindREN {ξ = ξ} ξ⇒ ⋆ₑ ⋆ₑ zero = refl
↑KindREN {ξ = ξ} ξ⇒ ⋆ₑ ⋆ₑ (suc n) = ξ⇒ ⋆ₑ n
↑KindREN {ξ = ξ} ξ⇒ ⋆ₑ ⋆ₗ = ξ⇒ ⋆ₗ
↑KindREN {ξ = ξ} ξ⇒ ⋆ₗ ⋆ = ξ⇒ ⋆
↑KindREN {ξ = ξ} ξ⇒ ⋆ₗ ⋆ₑ = ξ⇒ ⋆ₑ
↑KindREN {ξ = ξ} ξ⇒ ⋆ₗ ⋆ₗ zero = refl
↑KindREN {ξ = ξ} ξ⇒ ⋆ₗ ⋆ₗ (suc n) = ξ⇒ ⋆ₗ n

sucKindREN : ∀{Θ1 Θ2 ξ} →
             KindREN ξ Θ1 Θ2 →
             ∀ κ → KindREN (sucₖ[ κ ] ξ) Θ1 (↑KindCtx[ κ ] Θ2)
sucKindREN {Θ1} {Θ2} {ξ = ξ} Θ⇒ ⋆ ⋆ = Θ⇒ ⋆
sucKindREN {ξ = ξ} Θ⇒ ⋆ ⋆ₑ = Θ⇒ ⋆ₑ
sucKindREN {ξ = ξ} Θ⇒ ⋆ ⋆ₗ = Θ⇒ ⋆ₗ
sucKindREN {ξ = ξ} Θ⇒ ⋆ₑ ⋆ = Θ⇒ ⋆
sucKindREN {ξ = ξ} Θ⇒ ⋆ₑ ⋆ₑ = Θ⇒ ⋆ₑ
sucKindREN {ξ = ξ} Θ⇒ ⋆ₑ ⋆ₗ = Θ⇒ ⋆ₗ
sucKindREN {ξ = ξ} Θ⇒ ⋆ₗ ⋆ = Θ⇒ ⋆
sucKindREN {ξ = ξ} Θ⇒ ⋆ₗ ⋆ₑ = Θ⇒ ⋆ₑ
sucKindREN {ξ = ξ} Θ⇒ ⋆ₗ ⋆ₗ = Θ⇒ ⋆ₗ

-- Location well-formedness has weakening
wfWkₗ : ∀{Θ1 Θ2 ℓ ξ} →
        KindREN ξ Θ1 Θ2 →
        Θ1 ⊢ₗ ℓ →
        Θ2 ⊢ₗ renₗ-Loc (ξ ⋆ₗ) ℓ
wfWkₗ {ξ = ξ} ξ⇒ (wfVarLoc x Θ1[x]) = wfVarLoc (ξ ⋆ₗ x) (transport (ξ⇒ ⋆ₗ x) Θ1[x])
wfWkₗ ξ (wfLitLoc L) = wfLitLoc L

-- Location well-formedness respects extensional equality
wfExtₗ : ∀{Θ1 Θ2 ℓ} →
         Θ1 ≈₂ Θ2 →
         Θ1 ⊢ₗ ℓ →
         Θ2 ⊢ₗ ℓ
wfExtₗ Θ1≈Θ2 (wfVarLoc x Θ1[x]) = wfVarLoc x (transport (Θ1≈Θ2 ⋆ₗ x) Θ1[x])
wfExtₗ Θ1≈Θ2 (wfLitLoc L) = wfLitLoc L

-- Location well-formedness is monotone
wfMonoₗ : ∀{Θ1 Θ2 ℓ} →
          Θ1 ⊆ Θ2 →
          Θ1 ⊢ₗ ℓ →
          Θ2 ⊢ₗ ℓ
wfMonoₗ Θ1⊆Θ2 (wfVarLoc x Θ1[x]) = wfVarLoc x (Θ1⊆Θ2 ⋆ₗ x Θ1[x])
wfMonoₗ Θ1⊆Θ2 (wfLitLoc L) = wfLitLoc L

-- Location list well-formedness
data _⊢ₗₗ_ : KindCtx → LocList → Set where
  wfNil : ∀{Θ} → Θ ⊢ₗₗ []
  wfCons : ∀{Θ ℓ ρ}
           (Θ⊢ℓ : Θ ⊢ₗ ℓ)
           (Θ⊢ρ : Θ ⊢ₗₗ ρ) →
           Θ ⊢ₗₗ (ℓ ∷ ρ)

-- Location list well-formedness has weakening
wfWkₗₗ : ∀{Θ1 Θ2 ρ ξ} →
         KindREN ξ Θ1 Θ2 →
         Θ1 ⊢ₗₗ ρ →
         Θ2 ⊢ₗₗ renₗ-List (ξ ⋆ₗ) ρ
wfWkₗₗ ξ⇒ wfNil = wfNil
wfWkₗₗ ξ⇒ (wfCons Θ⊢ℓ Θ⊢ρ) = wfCons (wfWkₗ ξ⇒ Θ⊢ℓ) (wfWkₗₗ ξ⇒ Θ⊢ρ)

-- Location list well-formedness respects extensional equality
wfExtₗₗ : ∀{Θ1 Θ2 ρ} →
          Θ1 ≈₂ Θ2 →
          Θ1 ⊢ₗₗ ρ →
          Θ2 ⊢ₗₗ ρ
wfExtₗₗ Θ1≈Θ2 wfNil = wfNil
wfExtₗₗ Θ1≈Θ2 (wfCons Θ⊢ℓ Θ⊢ρ) = wfCons (wfExtₗ Θ1≈Θ2 Θ⊢ℓ) (wfExtₗₗ Θ1≈Θ2 Θ⊢ρ)

-- Local expression type well-formedness
data _⊢ₑₜ_ : KindCtx → Typₑ → Set where
  wfVarTypₑ : ∀{Θ} x → (Θ⊢x : Θ ⋆ₑ x) → Θ ⊢ₑₜ VarTypₑ x
  wfLitTypₑ : ∀{Θ} t → Θ ⊢ₑₜ LitTypₑ t

-- Choreography type well-formedness
data _⊢ₜ_ : KindCtx → Typ → Set where
  wfVarTyp : ∀{Θ} x → (Θ⊢x : Θ ⋆ x) → Θ ⊢ₜ VarTyp x
  wfAt : ∀{Θ t ℓ} (Θ⊢t : Θ ⊢ₑₜ t) (Θ⊢ℓ : Θ ⊢ₗ ℓ) → Θ ⊢ₜ At t ℓ
  wfArrow : ∀{Θ τ1 τ2}
            (Θ⊢τ1 : Θ ⊢ₜ τ1) (Θ⊢τ2 : Θ ⊢ₜ τ2) →
            Θ ⊢ₜ Arrow τ1 τ2
  wfAll : ∀{Θ τ} κ →
          (↑[κ]Θ⊢τ : ↑KindCtx[ κ ] Θ ⊢ₜ τ) →
          Θ ⊢ₜ All κ τ

wfArrow₁ : ∀{Θ τ1 τ2} → Θ ⊢ₜ Arrow τ1 τ2 → Θ ⊢ₜ τ1
wfArrow₁ (wfArrow τ1 τ2) = τ1

wfArrow₂ : ∀{Θ τ1 τ2} → Θ ⊢ₜ Arrow τ1 τ2 → Θ ⊢ₜ τ2
wfArrow₂ (wfArrow τ1 τ2) = τ2

wfAllArg : ∀{Θ κ τ} → Θ ⊢ₜ All κ τ → ↑KindCtx[ κ ] Θ ⊢ₜ τ
wfAllArg (wfAll κ τ) = τ


-- Local expression type well-formedness has weakening
wfWkₑₜ : ∀{Θ1 Θ2 t ξ} →
        KindREN ξ Θ1 Θ2 →
        Θ1 ⊢ₑₜ t →
        Θ2 ⊢ₑₜ renₑₜ (ξ ⋆ₑ) t
wfWkₑₜ {ξ = ξ} ξ⇒ (wfVarTypₑ x Θ⊢x) = wfVarTypₑ (ξ ⋆ₑ x) (transport (ξ⇒ ⋆ₑ x) Θ⊢x)
wfWkₑₜ ξ⇒ (wfLitTypₑ t) = wfLitTypₑ t

-- Choreography type well-formedness has weakening
wfWkₜ : ∀{Θ1 Θ2 τ ξ} →
        KindREN ξ Θ1 Θ2 →
        Θ1 ⊢ₜ τ →
        Θ2 ⊢ₜ renₜ ξ τ
wfWkₜ {ξ = ξ} ξ⇒ (wfVarTyp x Θ⊢x) = wfVarTyp (ξ ⋆ x) (transport (ξ⇒ ⋆ x) Θ⊢x)
wfWkₜ ξ⇒ (wfAt t ℓ) = wfAt (wfWkₑₜ ξ⇒ t) (wfWkₗ ξ⇒ ℓ)
wfWkₜ ξ⇒ (wfArrow τ1 τ2) = wfArrow (wfWkₜ ξ⇒ τ1) (wfWkₜ ξ⇒ τ2)
wfWkₜ ξ⇒ (wfAll κ τ) = wfAll κ (wfWkₜ (↑KindREN ξ⇒ κ) τ)

-- Local expression type well-formedness respects extensional equality
wfExtₑₜ : ∀{Θ1 Θ2 t} →
          Θ1 ≈₂ Θ2 →
          Θ1 ⊢ₑₜ t →
          Θ2 ⊢ₑₜ t
wfExtₑₜ Θ1≈Θ2 (wfVarTypₑ x Θ1⊢x) = wfVarTypₑ x (transport (Θ1≈Θ2 ⋆ₑ x) Θ1⊢x)
wfExtₑₜ Θ1≈Θ2 (wfLitTypₑ t) = wfLitTypₑ t

-- Choreography type well-formedness respects extensional equality
wfExtₜ : ∀{Θ1 Θ2 τ} →
         Θ1 ≈₂ Θ2 →
         Θ1 ⊢ₜ τ →
         Θ2 ⊢ₜ τ
wfExtₜ Θ1≈Θ2 (wfVarTyp x Θ1⊢x) = wfVarTyp x (transport (Θ1≈Θ2 ⋆ x) Θ1⊢x)
wfExtₜ Θ1≈Θ2 (wfAt t ℓ) = wfAt (wfExtₑₜ Θ1≈Θ2 t) (wfExtₗ Θ1≈Θ2 ℓ)
wfExtₜ Θ1≈Θ2 (wfArrow τ1 τ2) = wfArrow (wfExtₜ Θ1≈Θ2 τ1) (wfExtₜ Θ1≈Θ2 τ2)
wfExtₜ Θ1≈Θ2 (wfAll κ τ) = wfAll κ (wfExtₜ (↑KindCtxExt Θ1≈Θ2 κ) τ)

-- Local expression type well-formedness is monotone
wfMonoₑₜ : ∀{Θ1 Θ2 t} →
           Θ1 ⊆ Θ2 →
           Θ1 ⊢ₑₜ t →
           Θ2 ⊢ₑₜ t
wfMonoₑₜ Θ1⊆Θ2 (wfVarTypₑ x Θ1⊢x) = wfVarTypₑ x (Θ1⊆Θ2 ⋆ₑ x Θ1⊢x)
wfMonoₑₜ Θ1⊆Θ2 (wfLitTypₑ t) = wfLitTypₑ t

-- Choreography type well-formedness is monotone
wfMonoₜ : ∀{Θ1 Θ2 τ} →
          Θ1 ⊆ Θ2 →
          Θ1 ⊢ₜ τ →
          Θ2 ⊢ₜ τ
wfMonoₜ Θ1⊆Θ2 (wfVarTyp x Θ1⊢x) = wfVarTyp x (Θ1⊆Θ2 ⋆ x Θ1⊢x)
wfMonoₜ Θ1⊆Θ2 (wfAt t ℓ) = wfAt (wfMonoₑₜ Θ1⊆Θ2 t) (wfMonoₗ Θ1⊆Θ2 ℓ)
wfMonoₜ Θ1⊆Θ2 (wfArrow τ1 τ2) = wfArrow (wfMonoₜ Θ1⊆Θ2 τ1) (wfMonoₜ Θ1⊆Θ2 τ2)
wfMonoₜ Θ1⊆Θ2 (wfAll κ τ) = wfAll κ (wfMonoₜ (↑KindCtx⊆ Θ1⊆Θ2 κ) τ)

-- If t is well-formed in Θ, then ↑t is well-formed in ↑[⋆ₑ]Θ
wf↑ₑₜ : ∀{Θ t} → Θ ⊢ₑₜ t → ↑KindCtx[ ⋆ₑ ] Θ ⊢ₑₜ ↑ₑₜ t
wf↑ₑₜ {Θ} Θ⊢t = wfWkₑₜ {ξ = sucₖ[ ⋆ₑ ] idKindRen} (sucKindREN idKindREN ⋆ₑ) Θ⊢t

-- If τ is well-formed in Θ, then ↑[κ]τ is well-formed in ↑[κ]Θ
wf↑ₜ : ∀{Θ τ} → Θ ⊢ₜ τ → ∀ κ → ↑KindCtx[ κ ] Θ ⊢ₜ ↑ₜ[ κ ] τ
wf↑ₜ {Θ} Θ⊢τ κ = wfWkₜ {ξ = sucₖ[ κ ] idKindRen} (sucKindREN idKindREN κ) Θ⊢τ

-- Well-formed substitutions between kind contexts
record KindSUB (σ : KindSub) (Θ1 Θ2 : KindCtx) : Set where
  field
    typSUB  : ∀ n → Θ1 ⋆ n → Θ2 ⊢ₜ σ .typSub n
    typSUBₑ : ∀ n → Θ1 ⋆ₑ n → Θ2 ⊢ₑₜ σ .typSubₑ n
    locSUB  : ∀ n → Θ1 ⋆ₗ n → Θ2 ⊢ₗ σ .locSub n

open KindSUB public

-- The identity location substitution is well-formed
idKindSUB : ∀{Θ} → KindSUB idKindSub Θ Θ
typSUB idKindSUB = wfVarTyp
typSUBₑ idKindSUB = wfVarTypₑ
locSUB idKindSUB = wfVarLoc 

-- Applying a well-formed renaming after a well-formed substitution is well-formed
renKindSUB : ∀{Θ1 Θ2 Θ3 ξ σ} →
             KindREN ξ Θ2 Θ3 →
             KindSUB σ Θ1 Θ2 →
             KindSUB (renKindSub ξ σ) Θ1 Θ3
typSUB (renKindSUB ξ σ) n p = wfWkₜ ξ (σ .typSUB n p)
typSUBₑ (renKindSUB ξ σ) n p = wfWkₑₜ ξ (σ .typSUBₑ n p)
locSUB (renKindSUB ξ σ) n p = wfWkₗ ξ (σ .locSUB n p)

-- Kind-generic well-formedness
_⊢[_]_ : KindCtx → (κ : Kind) → KindSubRange κ → Set
Θ ⊢[ ⋆  ] τ = Θ ⊢ₜ τ
Θ ⊢[ ⋆ₑ ] t = Θ ⊢ₑₜ t
Θ ⊢[ ⋆ₗ ] ℓ = Θ ⊢ₗ ℓ

-- Instantiating a well-formed value in a substitution preserves well-formedness
▸ₖ⇒ : ∀{Θ1 Θ2 σ} →
      KindSUB σ Θ1 Θ2 →
      (κ : Kind) →
      (x : KindSubRange κ) →
      Θ2 ⊢[ κ ] x →
      KindSUB (σ ▸ₖ[ κ ] x) (↑KindCtx[ κ ] Θ1) Θ2
typSUB  (▸ₖ⇒ σ⇒ ⋆ τ p) zero tt = p
typSUB  (▸ₖ⇒ σ⇒ ⋆ τ p) (suc n) = σ⇒ .typSUB n
typSUBₑ (▸ₖ⇒ σ⇒ ⋆ τ p) = σ⇒ .typSUBₑ
locSUB  (▸ₖ⇒ σ⇒ ⋆ τ p) = σ⇒ .locSUB
typSUB  (▸ₖ⇒ σ⇒ ⋆ₑ t p) = σ⇒ .typSUB
typSUBₑ (▸ₖ⇒ σ⇒ ⋆ₑ t p) zero tt = p
typSUBₑ (▸ₖ⇒ σ⇒ ⋆ₑ t p) (suc n) = σ⇒ .typSUBₑ n
locSUB  (▸ₖ⇒ σ⇒ ⋆ₑ t p) = σ⇒ .locSUB
typSUB  (▸ₖ⇒ σ⇒ ⋆ₗ ℓ p) = σ⇒ .typSUB
typSUBₑ (▸ₖ⇒ σ⇒ ⋆ₗ ℓ p) = σ⇒ .typSUBₑ
locSUB  (▸ₖ⇒ σ⇒ ⋆ₗ ℓ p) zero tt = p
locSUB  (▸ₖ⇒ σ⇒ ⋆ₗ ℓ p) (suc n) = σ⇒ .locSUB n

Var0ₖ : ∀{Θ} (κ : Kind) → (↑KindCtx[ κ ] Θ) ⊢[ κ ] Varₖ κ zero
Var0ₖ ⋆  = wfVarTyp  zero tt
Var0ₖ ⋆ₑ = wfVarTypₑ zero tt
Var0ₖ ⋆ₗ = wfVarLoc  zero tt

-- ↑σₖ preserves well-formedness
↑σₖ⇒ : ∀{σ Θ1 Θ2} →
       KindSUB σ Θ1 Θ2 →
       ∀ κ →
       KindSUB (↑σₖ[ κ ] σ) (↑KindCtx[ κ ] Θ1) (↑KindCtx[ κ ] Θ2)
↑σₖ⇒ σ κ = ▸ₖ⇒ (renKindSUB (sucKindREN idKindREN κ) σ) κ (Varₖ κ zero) (Var0ₖ κ)

-- Location well-formedness is closed under well-formed substitutions
wfSubₗ : ∀{σ Θ1 Θ2 ℓ} →
         KindSUB σ Θ1 Θ2 →
         Θ1 ⊢ₗ ℓ →
         Θ2 ⊢ₗ subₗ-Loc (σ .locSub) ℓ
wfSubₗ σ (wfVarLoc x Θ1[x]) = σ .locSUB x Θ1[x]
wfSubₗ σ (wfLitLoc L) = wfLitLoc L

-- Location list well-formedness is closed under well-formed substitutions
wfSubₗₗ : ∀{σ Θ1 Θ2 ρ} →
          KindSUB σ Θ1 Θ2 →
         Θ1 ⊢ₗₗ ρ →
         Θ2 ⊢ₗₗ subₗ-List (σ .locSub) ρ
wfSubₗₗ σ⇒ wfNil = wfNil
wfSubₗₗ σ⇒ (wfCons Θ⊢ℓ Θ⊢ρ) = wfCons (wfSubₗ σ⇒ Θ⊢ℓ) (wfSubₗₗ σ⇒ Θ⊢ρ)

-- Local expression type well-formedness is closed under well-formed substitutions
wfSubₑₜ : ∀{σ Θ1 Θ2 t} →
         KindSUB σ Θ1 Θ2 →
         Θ1 ⊢ₑₜ t →
         Θ2 ⊢ₑₜ subₑₜ (σ .typSubₑ) t
wfSubₑₜ σ (wfVarTypₑ x Θ⊢x) = σ .typSUBₑ x Θ⊢x
wfSubₑₜ σ (wfLitTypₑ t) = wfLitTypₑ t

-- Choreography type well-formedness is closed under well-formed substitutions
wfSubₜ : ∀{σ Θ1 Θ2 τ} →
         KindSUB σ Θ1 Θ2 →
         Θ1 ⊢ₜ τ →
         Θ2 ⊢ₜ subₜ σ τ
wfSubₜ σ (wfVarTyp x Θ⊢x) = σ .typSUB x Θ⊢x
wfSubₜ σ (wfAt t ℓ) = wfAt (wfSubₑₜ σ t) (wfSubₗ σ ℓ)
wfSubₜ σ (wfArrow τ1 τ2) = wfArrow (wfSubₜ σ τ1) (wfSubₜ σ τ2)
wfSubₜ σ (wfAll κ τ) = wfAll κ (wfSubₜ (↑σₖ⇒ σ κ) τ)
