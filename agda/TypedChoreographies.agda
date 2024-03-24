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

module TypedChoreographies
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

-- Renaming types respects extensional equality
renExtₜ : ∀{ξ1 ξ2} → ξ1 ≈ ξ2 → ∀ τ → renₜ τ ξ1 ≡ renₜ τ ξ2
renExtₜ ξ1≈ξ2 (At t ℓ) = cong₂ At refl (renExtₗ-Loc ξ1≈ξ2 ℓ)
renExtₜ ξ1≈ξ2 (Arrow τ1 τ2) =
  cong₂ Arrow (renExtₜ ξ1≈ξ2 τ1) (renExtₜ ξ1≈ξ2 τ2)
renExtₜ ξ1≈ξ2 (AllLoc τ) = cong AllLoc (renExtₜ (↑Ext ξ1≈ξ2) τ)

-- Renaming locations on types enjoys fusion
renFuseₜ : ∀ ξ1 ξ2 τ → renₜ τ (ξ2 ∘ ξ1) ≡ renₜ (renₜ τ ξ1) ξ2
renFuseₜ ξ1 ξ2 (At t ℓ) = cong₂ At refl (renFuseₗ-Loc ξ1 ξ2 ℓ)
renFuseₜ ξ1 ξ2 (Arrow τ1 τ2) =
  cong₂ Arrow (renFuseₜ ξ1 ξ2 τ1) (renFuseₜ ξ1 ξ2 τ2)
renFuseₜ ξ1 ξ2 (AllLoc τ) = cong AllLoc τ⟨↑[ξ2∘ξ1]⟩≡τ⟨↑ξ1⟩⟨↑ξ2⟩
  where
  open ≡-Reasoning
  
  τ⟨↑[ξ2∘ξ1]⟩≡τ⟨↑ξ1⟩⟨↑ξ2⟩ : renₜ τ (↑ (ξ2 ∘ ξ1)) ≡ renₜ (renₜ τ (↑ ξ1)) (↑ ξ2)
  τ⟨↑[ξ2∘ξ1]⟩≡τ⟨↑ξ1⟩⟨↑ξ2⟩ = 
    renₜ τ (↑ (ξ2 ∘ ξ1))        ≡⟨ renExtₜ (↑Fuse ξ1 ξ2) τ ⟩
    renₜ τ (↑ ξ2 ∘ ↑ ξ1)        ≡⟨ renFuseₜ (↑ ξ1) (↑ ξ2) τ ⟩
    renₜ (renₜ τ (↑ ξ1)) (↑ ξ2) ∎

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
  open ≡-Reasoning

  τ⟨↑ιξ⟩≡τ⟨↑ξ⟩ : subₜ τ (↑σₗ (ιₗ ξ)) ≡ renₜ τ (↑ ξ)
  τ⟨↑ιξ⟩≡τ⟨↑ξ⟩ =
    subₜ τ (↑σₗ (ιₗ ξ)) ≡⟨ subExtₜ (↑σιₗ ξ) τ ⟩
    subₜ τ (ιₗ (↑ ξ))   ≡⟨ subιₜ (↑ ξ) τ ⟩
    renₜ τ (↑ ξ)        ∎

-- Substitution enjoys fusion
subFuseₜ : ∀ σ1 σ2 τ → subₜ τ (σ1 •ₗ σ2) ≡ subₜ (subₜ τ σ2) σ1
subFuseₜ σ1 σ2 (At t ℓ) = cong₂ At refl (subFuseₗ-Loc σ1 σ2 ℓ)
subFuseₜ σ1 σ2 (Arrow τ1 τ2) = cong₂ Arrow (subFuseₜ σ1 σ2 τ1) (subFuseₜ σ1 σ2 τ2)
subFuseₜ σ1 σ2 (AllLoc τ) = cong AllLoc τ⟨↑[σ1•σ2]⟩≡τ⟨↑σ2⟩⟨↑σ1⟩
  where
  open ≡-Reasoning

  τ⟨↑[σ1•σ2]⟩≡τ⟨↑σ2⟩⟨↑σ1⟩ : subₜ τ (↑σₗ (σ1 •ₗ σ2)) ≡ subₜ (subₜ τ (↑σₗ σ2)) (↑σₗ σ1)
  τ⟨↑[σ1•σ2]⟩≡τ⟨↑σ2⟩⟨↑σ1⟩ =
    subₜ τ (↑σₗ (σ1 •ₗ σ2))         ≡⟨ subExtₜ (↑σ•ₗ σ1 σ2) τ ⟩
    subₜ τ (↑σₗ σ1 •ₗ ↑σₗ σ2)       ≡⟨ subFuseₜ (↑σₗ σ1) (↑σₗ σ2) τ ⟩
    subₜ (subₜ τ (↑σₗ σ2)) (↑σₗ σ1) ∎


{-
  Location contexts are an infinite map which
  distinguishes the in-scope location variables
-}
LocCtx : Set₁
LocCtx = ℕ → Set

-- `up` construction on location contexts
↑LocCtx : LocCtx → LocCtx
↑LocCtx Θ zero = ⊤
↑LocCtx Θ (suc n) = Θ n

-- `up` construction respects extensional equality
↑LocCtxExt : ∀{Θ1 Θ2} → Θ1 ≈ Θ2 → ↑LocCtx Θ1 ≈ ↑LocCtx Θ2
↑LocCtxExt Θ1≈Θ2 zero = refl
↑LocCtxExt Θ1≈Θ2 (suc n) = Θ1≈Θ2 n

{-
  Local contexts are an infinite map from
  locations and variables to local types
-}
LocalCtx : Set
LocalCtx = Loc → ℕ → Typₑ

-- Add a local type to specified local context
_,,[_]_ : LocalCtx → Loc → Typₑ → LocalCtx
(Δ ,,[ ℓ ] t) ℓ' with ≡-dec-Loc ℓ ℓ'
... | yes _ = λ{ zero → t ; (suc n) → Δ ℓ n }
... | no  _ = Δ ℓ'

addLocCtxExt : ∀{Δ Δ'} →
               Δ ≈₂ Δ' →
               ∀ ℓ t →
               Δ ,,[ ℓ ] t ≈₂ Δ' ,,[ ℓ ] t
addLocCtxExt Δ≈Δ' ℓ t ℓ' with ≡-dec-Loc ℓ ℓ'
... | yes _ = λ{ zero → refl ; (suc n) → Δ≈Δ' ℓ n }
... | no  _ = Δ≈Δ' ℓ'              

-- Composing a local context with a location renaming
_∘ₗ_ : LocalCtx → (ℕ → ℕ) → LocalCtx
(Δ ∘ₗ ξ) ℓ = Δ (renₗ-Loc ℓ ξ)

-- Injectivity of constructor
Varₗ-inj : ∀{ℓ ℓ'} → Location.Var ℓ ≡ Var ℓ' → ℓ ≡ ℓ'
Varₗ-inj refl = refl

-- Injectivity of renaming
renₗ-Loc-inj : ∀{ℓ ℓ' ξ} →
               Injective _≡_ _≡_ ξ →
               renₗ-Loc ℓ ξ ≡ renₗ-Loc ℓ' ξ → ℓ ≡ ℓ'
renₗ-Loc-inj {ℓ = Var x} {Var x'} ξ-inj Vξx≡Vξx' = cong Var (ξ-inj (Varₗ-inj Vξx≡Vξx'))
renₗ-Loc-inj {ℓ = Var x} {Lit L'} ξ-inj ()
renₗ-Loc-inj {ℓ = Lit L} {Var x'} ξ-inj ()
renₗ-Loc-inj {ℓ = Lit L} {Lit .L} ξ-inj refl = refl

{-
  Composing a local context with a location renaming
  commutes with adding to the context
-}
∘ₗ,, : ∀ Δ ξ ℓ t →
     Injective _≡_ _≡_ ξ →
     (Δ ∘ₗ ξ) ,,[ ℓ ] t ≈₂ (Δ ,,[ renₗ-Loc ℓ ξ ] t) ∘ₗ ξ
∘ₗ,, Δ ξ ℓ t ξ-inj ℓ' with ≡-dec-Loc ℓ ℓ' | ≡-dec-Loc (renₗ-Loc ℓ ξ) (renₗ-Loc ℓ' ξ)
... | yes _    | yes _        = λ{ zero → refl ; (suc n) → refl }
... | yes refl | no  ℓ⟨ξ⟩≠ℓ⟨ξ⟩ = ⊥-elim (ℓ⟨ξ⟩≠ℓ⟨ξ⟩ refl)
... | no ℓ≠ℓ'  | yes ℓ⟨ξ⟩≡ℓ⟨ξ⟩ = ⊥-elim (ℓ≠ℓ' (renₗ-Loc-inj ξ-inj ℓ⟨ξ⟩≡ℓ⟨ξ⟩))
... | no _     | no  _        = λ _ → refl

{-
  `up` construction on local contexts.
  Arbitrarily assigns the boolean type to all variables
  of the newly introduced location variable. This should
  be OK because the local type system only cares about
  the variables which are in context.
-}
↑LocalCtx : LocalCtx → LocalCtx
↑LocalCtx Δ (Var zero) = λ _ → Boolₑ
↑LocalCtx Δ (Var (suc x)) = Δ (Var x)
↑LocalCtx Δ (Lit L) = Δ (Lit L)

-- `up` construction respects extensional equality
↑LocalCtxExt : ∀{Δ1 Δ2} → Δ1 ≈₂ Δ2 → ↑LocalCtx Δ1 ≈₂ ↑LocalCtx Δ2
↑LocalCtxExt Δ1≈Δ2 (Var zero) n = refl
↑LocalCtxExt Δ1≈Δ2 (Var (suc x)) n = Δ1≈Δ2 (Var x) n
↑LocalCtxExt Δ1≈Δ2 (Lit L) n = Δ1≈Δ2 (Lit L) n

-- Choreographic/global contexts
Ctx : Set
Ctx = ℕ → Typ

-- Add a global type to the context
_,,_ : Ctx → Typ → Ctx
(Γ ,, τ) zero = τ
(Γ ,, τ) (suc n) = Γ n

addCtxExt : ∀{Γ Γ' τ} →
            Γ ≈ Γ' → Γ ,, τ ≈ Γ' ,, τ
addCtxExt Γ≈Γ' zero = refl
addCtxExt Γ≈Γ' (suc n) = Γ≈Γ' n

-- Location renaming on global contexts.
renCtx : Ctx → (ℕ → ℕ) → Ctx
renCtx Γ ξ n = renₜ (Γ n) ξ

-- Renaming and adding to a context commute
renCtx,, : ∀ Γ τ ξ →
           renCtx (Γ ,, τ) ξ ≈ renCtx Γ ξ ,, renₜ τ ξ
renCtx,, Γ τ ξ zero = refl
renCtx,, Γ τ ξ (suc n) = refl

-- `up` construction on global contexts
↑Ctx : Ctx → Ctx
↑Ctx Γ = renCtx Γ suc

-- `up` construction respects extensional equality
↑CtxExt : ∀{Γ1 Γ2} → Γ1 ≈ Γ2 → ↑Ctx Γ1 ≈ ↑Ctx Γ2
↑CtxExt Γ1≈Γ2 n = cong₂ renₜ (Γ1≈Γ2 n) refl

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

↑LocCtxFuse : ∀ Θ ξ → ↑LocCtx (Θ ∘ ξ) ≈ ↑LocCtx Θ ∘ ↑ ξ
↑LocCtxFuse Θ ξ zero = refl
↑LocCtxFuse Θ ξ (suc n) = refl

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
  ↑Θ≈↑Θ'∘↑ξ = ≈-trans (↑LocCtxExt Θ≈Θ'∘ξ) (↑LocCtxFuse Θ' ξ)

-- Type well-formedness respects extensional equality
wfExtₜ : ∀{Θ1 Θ2 τ} →
        Θ1 ≈ Θ2 →
        Θ1 ⊢ₜ τ →
        Θ2 ⊢ₜ τ
wfExtₜ Θ1≈Θ2 (wfAt Θ⊢ℓ) = wfAt (wfExtₗ Θ1≈Θ2 Θ⊢ℓ)
wfExtₜ Θ1≈Θ2 (wfArrow Θ⊢τ1 Θ⊢τ2) = wfArrow (wfExtₜ Θ1≈Θ2 Θ⊢τ1) (wfExtₜ Θ1≈Θ2 Θ⊢τ2)
wfExtₜ Θ1≈Θ2 (wfAllLoc ↑Θ⊢τ) = wfAllLoc (wfExtₜ (↑LocCtxExt Θ1≈Θ2) ↑Θ⊢τ)

{-
  A Choreographic context is well-formed if
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

{-
  Choreographic typing relation of the form
  (Θ , Δ , Γ) ⊢ C : τ
  where Θ is the location context,
  Δ is the local context,
  Γ is the global context,
  C is the choreography,
  and τ is the type.
-}
data _⊢_∶_ : LocCtx × LocalCtx × Ctx → Chor → Typ → Set where
  tyVar : ∀{Θ Δ Γ}
          (Θ⊢Γ : Θ ⊢ Γ) →
          ∀ x →
          (Θ , Δ , Γ) ⊢ Var x ∶ Γ x
  tyDone : ∀{Θ Δ Γ e t ℓ}
           (Θ⊢ℓ : Θ ⊢ₗ ℓ) →
           (Δ[ℓ]⊢e∶t : Δ ℓ ⊢ₑ e ∶ t) →
           (Θ , Δ , Γ) ⊢ Done ℓ e ∶ At t ℓ
  tySend : ∀{Θ Δ Γ C t ℓ1 ℓ2}
           (Θ；Δ；Γ⊢C:ℓ1_t : (Θ , Δ , Γ) ⊢ C ∶ At t ℓ1)
           (Θ⊢ℓ2 : Θ ⊢ₗ ℓ2) →
           (Θ , Δ , Γ) ⊢ Send ℓ1 C ℓ2 ∶ At t ℓ2
  tyIf : ∀{Θ Δ Γ C C1 C2 τ ℓ}
          (Θ；Δ；Γ⊢C:ℓ_bool : (Θ , Δ , Γ) ⊢ C ∶ At Boolₑ ℓ)
          (Θ；Δ；Γ⊢C1:τ : (Θ , Δ , Γ) ⊢ C1 ∶ τ)
          (Θ；Δ；Γ⊢C2:τ : (Θ , Δ , Γ) ⊢ C2 ∶ τ) →
          (Θ , Δ , Γ) ⊢ If ℓ C C1 C2 ∶ τ
  tySync : ∀{Θ Δ Γ C τ ℓ1 ℓ2 d}
           (Θ⊢ℓ1 : Θ ⊢ₗ ℓ1) (Θ⊢ℓ2 : Θ ⊢ₗ ℓ2)
           (Θ；Δ；Γ⊢C:τ : (Θ , Δ , Γ) ⊢ C ∶ τ) →
           (Θ , Δ , Γ) ⊢ Sync ℓ1 d ℓ2 C ∶ τ
  tyDefLocal : ∀{Θ Δ Γ C1 C2 t1 ℓ τ2}
               (Θ；Δ；Γ⊢C1:ℓ_t1 : (Θ , Δ , Γ)  ⊢ C1 ∶ At t1 ℓ)
               (Θ；Δ,ℓ_t1；Γ⊢C2:τ2 : (Θ , (Δ ,,[ ℓ ] t1) , Γ) ⊢ C2 ∶ τ2) →
               (Θ , Δ , Γ) ⊢ DefLocal ℓ C1 C2 ∶ τ2
  tyFun : ∀{Θ Δ Γ C τ1 τ2} →
          (Θ；Δ；Γ,τ1⊢C:τ2 : (Θ , Δ , (Γ ,, τ1)) ⊢ C ∶ τ2) →
          (Θ , Δ , Γ) ⊢ Fun C ∶ Arrow τ1 τ2
  tyFix : ∀{Θ Δ Γ C τ} →
          (Θ；Δ；Γ,τ⊢C:τ : (Θ , Δ , (Γ ,, τ)) ⊢ C ∶ τ) →
          (Θ , Δ , Γ) ⊢ Fix C ∶ τ
  tyApp : ∀{Θ Δ Γ C1 C2 τ1 τ2}
          (Θ；Δ；Γ⊢C1:τ1⇒τ2 : (Θ , Δ , Γ)  ⊢ C1 ∶ Arrow τ1 τ2)
          (Θ；Δ；Γ⊢C2:τ1 : (Θ , Δ , Γ) ⊢ C2 ∶ τ1) →
          (Θ , Δ , Γ) ⊢ App C1 C2 ∶ τ2
  tyLocAbs : ∀{Θ Δ Γ C τ}
             (↑Θ；↑Δ；↑Γ⊢C∶τ : (↑LocCtx Θ , ↑LocalCtx Δ , ↑Ctx Γ)  ⊢ C ∶ τ) →
             (Θ , Δ , Γ) ⊢ LocAbs C ∶ AllLoc τ
  tyLocApp : ∀{Θ Δ Γ C τ ℓ}
             (Θ；Δ；Γ⊢C:∀τ : (Θ , Δ , Γ)  ⊢ C ∶ AllLoc τ) →
             (Θ⊢ℓ : Θ ⊢ₗ ℓ) →
             (Θ , Δ , Γ) ⊢ LocApp C ℓ ∶ subₜ τ (idSubₗ ▸ₗ ℓ)
  tyTellLet : ∀{Θ Δ Γ C1 C2 ρ1 ρ2 ℓ τ} →
              (Θ；Δ；Γ⊢C1:ℓ_t : (Θ , Δ , Γ) ⊢ C1 ∶ At Locₑ ℓ)
              (Θ⊢ρ1 : Θ ⊢ₗₗ ρ1) (Θ⊢ρ2 : Θ ⊢ₗₗ ρ2)
              (Θ⊢τ : Θ ⊢ₜ τ)
              (↑Θ；↑Δ；↑Γ⊢C2:↑τ : (↑LocCtx Θ , ↑LocalCtx Δ , ↑Ctx Γ) ⊢ C2 ∶ ↑ₜ τ) →
              (Θ , Δ , Γ) ⊢ TellLet ℓ ρ1 C1 ρ2 C2 ∶ τ

-- The typing relation respects extensional equality
tyExt : ∀{Θ Θ' Δ Δ' Γ Γ' C τ} →
        Θ ≈ Θ' → Δ ≈₂ Δ' → Γ ≈ Γ' →
        (Θ , Δ , Γ) ⊢ C ∶ τ →
        (Θ' , Δ' , Γ') ⊢ C ∶ τ
tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' (tyVar Θ⊢Γ x) =
  subst (λ z → _ ⊢ Var x ∶ z) (sym (Γ≈Γ' x)) (tyVar (wfCtxExt Θ≈Θ' Γ≈Γ' Θ⊢Γ) x)
tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' (tyDone {ℓ = ℓ} Θ⊢ℓ Δ[ℓ]⊢e∶t) =
  tyDone (wfExtₗ Θ≈Θ' Θ⊢ℓ) (tyExtₑ (Δ≈Δ' ℓ) Δ[ℓ]⊢e∶t)
tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' (tySend C∶τ Θ⊢ℓ2) =
  tySend (tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' C∶τ) (wfExtₗ Θ≈Θ' Θ⊢ℓ2)
tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' (tyIf C∶τ C∶τ1 C∶τ2) =
  tyIf (tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' C∶τ) (tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' C∶τ1) (tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' C∶τ2)
tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' (tySync Θ⊢ℓ1 Θ⊢ℓ2 C∶τ) =
  tySync (wfExtₗ Θ≈Θ' Θ⊢ℓ1) (wfExtₗ Θ≈Θ' Θ⊢ℓ2) (tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' C∶τ)
tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' (tyDefLocal {t1 = t1} {ℓ = ℓ} C∶t1 C∶τ2) =
  tyDefLocal (tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' C∶t1) (tyExt Θ≈Θ' (addLocCtxExt Δ≈Δ' ℓ t1) Γ≈Γ' C∶τ2)
tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' (tyFun C∶τ2) = tyFun (tyExt Θ≈Θ' Δ≈Δ' (addCtxExt Γ≈Γ') C∶τ2)
tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' (tyFix C∶τ) = tyFix (tyExt Θ≈Θ' Δ≈Δ' (addCtxExt Γ≈Γ') C∶τ)
tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' (tyApp C1∶τ1⇒τ2 C2∶τ1) =
  tyApp (tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' C1∶τ1⇒τ2) (tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' C2∶τ1)
tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' (tyLocAbs C∶τ) =
  tyLocAbs (tyExt (↑LocCtxExt Θ≈Θ') (↑LocalCtxExt Δ≈Δ') (↑CtxExt Γ≈Γ') C∶τ)
tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' (tyLocApp C∶τ Θ⊢ℓ) = tyLocApp (tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' C∶τ) (wfExtₗ Θ≈Θ' Θ⊢ℓ)
tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' (tyTellLet C∶Loc Θ⊢ρ1 Θ⊢ρ2 Θ⊢τ C∶τ) =
  tyTellLet (tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' C∶Loc) (wfExtₗₗ Θ≈Θ' Θ⊢ρ1) (wfExtₗₗ Θ≈Θ' Θ⊢ρ2)
    (wfExtₜ Θ≈Θ' Θ⊢τ) (tyExt (↑LocCtxExt Θ≈Θ') (↑LocalCtxExt Δ≈Δ') (↑CtxExt Γ≈Γ') C∶τ)

↑-pres-inj : ∀{ξ} → Injective _≡_ _≡_ ξ → Injective _≡_ _≡_ (↑ ξ)
↑-pres-inj ξ-inj {x = zero} {zero} refl = refl
↑-pres-inj ξ-inj {x = zero} {suc y} ()
↑-pres-inj ξ-inj {x = suc x} {zero} ()
↑-pres-inj ξ-inj {x = suc x} {suc y} sξx≡sξy = cong suc (ξ-inj (suc-injective sξx≡sξy))

-- Renaming commutes with ↑
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

↑LocalCtxFuse : ∀ Δ ξ → ↑LocalCtx (Δ ∘ₗ ξ) ≈₂ ↑LocalCtx Δ ∘ₗ ↑ ξ
↑LocalCtxFuse Δ ξ (Var zero) n = refl
↑LocalCtxFuse Δ ξ (Var (suc x)) n = refl
↑LocalCtxFuse Δ ξ (Lit L) n = refl

-- The typing relation has weakening on locations
tyWkₗ : ∀{Θ Θ' Δ Δ' Γ C τ} ξ →
        Injective _≡_ _≡_ ξ →
        Θ ≈ Θ' ∘ ξ →
        Δ ≈₂ Δ' ∘ₗ ξ →
        (Θ , Δ , Γ) ⊢ C ∶ τ →
        (Θ' , Δ' , renCtx Γ ξ) ⊢ renₗ C ξ ∶ renₜ τ ξ
tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ (tyVar Θ⊢Γ x) = tyVar (wfCtxWk ξ Θ≈Θ'∘ξ Θ⊢Γ) x
tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ (tyDone {e = e} {t = t} {ℓ = ℓ} Θ⊢ℓ Δ[ℓ]⊢e:t) =
  tyDone (wfWkₗ ξ Θ≈Θ'∘ξ Θ⊢ℓ) (tyExtₑ (Δ≈Δ'∘ξ ℓ) Δ[ℓ]⊢e:t)
tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ (tySend C∶τ Θ⊢ℓ2) =
  tySend (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ C∶τ) (wfWkₗ ξ Θ≈Θ'∘ξ Θ⊢ℓ2)
tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ (tyIf C∶Bool C1∶τ C2∶τ) =
  tyIf (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ C∶Bool) (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ C1∶τ) (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ C2∶τ)
tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ (tySync Θ⊢ℓ1 Θ⊢ℓ2 C∶τ) =
  tySync (wfWkₗ ξ Θ≈Θ'∘ξ Θ⊢ℓ1) (wfWkₗ ξ Θ≈Θ'∘ξ Θ⊢ℓ2) (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ C∶τ)
tyWkₗ {Θ} {Θ'} {Δ} {Δ'} {Γ} ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ (tyDefLocal {t1 = t1} {ℓ} {τ2} C1∶t1 C2∶τ2) =
  tyDefLocal (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ C1∶t1) (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ eq C2∶τ2)
    where
    open import Relation.Binary.Reasoning.Setoid (≈₂-Setoid′ Loc ℕ Typₑ)
    
    eq : (Δ ,,[ ℓ ] t1) ≈₂ ((Δ' ,,[ renₗ-Loc ℓ ξ ] t1) ∘ₗ ξ)
    eq = begin
      Δ ,,[ ℓ ] t1                  ≈⟨ addLocCtxExt Δ≈Δ'∘ξ ℓ t1 ⟩
      (Δ' ∘ₗ ξ) ,,[ ℓ ] t1           ≈⟨ ∘ₗ,, Δ' ξ ℓ t1 ξ-inj ⟩
      (Δ' ,,[ renₗ-Loc ℓ ξ ] t1) ∘ₗ ξ ∎
tyWkₗ {Θ} {Θ'} {Δ} {Δ'} {Γ} ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ (tyFun {τ1 = τ1} C∶τ2) =
  tyFun (tyExt ≈-refl ≈₂-refl (renCtx,, Γ τ1 ξ) (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ C∶τ2))
tyWkₗ {Θ} {Θ'} {Δ} {Δ'} {Γ} ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ (tyFix {τ = τ} C∶τ) =
  tyFix (tyExt ≈-refl ≈₂-refl (renCtx,, Γ τ ξ) (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ C∶τ))
tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ (tyApp C1∶τ1⇒τ2 C2∶τ2) =
  tyApp (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ C1∶τ1⇒τ2) (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ C2∶τ2)
tyWkₗ {Θ} {Θ'} {Δ} {Δ'} {Γ} ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ (tyLocAbs {C = C} {τ = τ} C∶τ) =
  tyLocAbs ↑Θ'；↑Δ'；↑[Γ⟨ξ⟩]⊢C⟨↑ξ⟩∶τ⟨↑ξ⟩
    where
    module _ where
      open import Relation.Binary.Reasoning.Setoid (≈-Setoid′ ℕ Set)
      
      ↑Θ≈↑Θ'∘↑ξ : ↑LocCtx Θ ≈ ↑LocCtx Θ' ∘ ↑ ξ
      ↑Θ≈↑Θ'∘↑ξ = begin
        ↑LocCtx Θ        ≈⟨ ↑LocCtxExt Θ≈Θ'∘ξ ⟩
        ↑LocCtx (Θ' ∘ ξ) ≈⟨ ↑LocCtxFuse Θ' ξ ⟩
        ↑LocCtx Θ' ∘ ↑ ξ ∎

    module _ where
      open import Relation.Binary.Reasoning.Setoid (≈₂-Setoid′ Loc ℕ Typₑ)

      ↑Δ≈↑Δ'∘↑ξ : ↑LocalCtx Δ ≈₂ ↑LocalCtx Δ' ∘ₗ ↑ ξ
      ↑Δ≈↑Δ'∘↑ξ = begin
        ↑LocalCtx Δ        ≈⟨ ↑LocalCtxExt Δ≈Δ'∘ξ ⟩
        ↑LocalCtx (Δ' ∘ₗ ξ) ≈⟨ ↑LocalCtxFuse Δ' ξ ⟩
        ↑LocalCtx Δ' ∘ₗ ↑ ξ ∎

    ↑Θ'；↑Δ'；[↑Γ]⟨↑ξ⟩⊢C⟨↑ξ⟩∶τ⟨↑ξ⟩ : (↑LocCtx Θ' , ↑LocalCtx Δ' , renCtx (↑Ctx Γ) (↑ ξ)) ⊢ renₗ C (↑ ξ) ∶ renₜ τ (↑ ξ)
    ↑Θ'；↑Δ'；[↑Γ]⟨↑ξ⟩⊢C⟨↑ξ⟩∶τ⟨↑ξ⟩ = tyWkₗ (↑ ξ) (↑-pres-inj ξ-inj) ↑Θ≈↑Θ'∘↑ξ ↑Δ≈↑Δ'∘↑ξ C∶τ

    ↑Θ'；↑Δ'；↑[Γ⟨ξ⟩]⊢C⟨↑ξ⟩∶τ⟨↑ξ⟩ : (↑LocCtx Θ' , ↑LocalCtx Δ' , ↑Ctx (renCtx Γ ξ)) ⊢ renₗ C (↑ ξ) ∶ renₜ τ (↑ ξ)
    ↑Θ'；↑Δ'；↑[Γ⟨ξ⟩]⊢C⟨↑ξ⟩∶τ⟨↑ξ⟩ = tyExt ≈-refl ≈₂-refl (renCtx↑ Γ ξ) ↑Θ'；↑Δ'；[↑Γ]⟨↑ξ⟩⊢C⟨↑ξ⟩∶τ⟨↑ξ⟩
tyWkₗ {Θ} {Θ'} {Δ} {Δ'} {Γ} ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ (tyLocApp {C = C} {τ = τ} {ℓ = ℓ} C∶τ Θ⊢ℓ) = Θ'；Δ'；Γ⟨ξ⟩⊢Cℓ
  where
  open ≡-Reasoning

  Θ'；Δ'；Γ⟨ξ⟩⊢C : (Θ' , Δ' , renCtx Γ ξ) ⊢ renₗ C ξ ∶ AllLoc (renₜ τ (↑ ξ))
  Θ'；Δ'；Γ⟨ξ⟩⊢C = tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ C∶τ

  Θ'⊢ℓ : Θ' ⊢ₗ renₗ-Loc ℓ ξ
  Θ'⊢ℓ = wfWkₗ ξ Θ≈Θ'∘ξ Θ⊢ℓ

  Θ'；Δ'；Γ⟨ξ⟩⊢Cℓ' : (Θ' , Δ' , renCtx Γ ξ) ⊢ LocApp (renₗ C ξ) (renₗ-Loc ℓ ξ) ∶ subₜ (renₜ τ (↑ ξ)) (idSubₗ ▸ₗ renₗ-Loc ℓ ξ)
  Θ'；Δ'；Γ⟨ξ⟩⊢Cℓ' = tyLocApp Θ'；Δ'；Γ⟨ξ⟩⊢C Θ'⊢ℓ

  sub-eq : (idSubₗ ▸ₗ renₗ-Loc ℓ ξ) •ₗ ιₗ (↑ ξ) ≈ ιₗ ξ •ₗ (idSubₗ ▸ₗ ℓ)
  sub-eq zero = sym (subιₗ-Loc ξ ℓ)
  sub-eq (suc n) = refl

  ty-eq : subₜ (renₜ τ (↑ ξ)) (idSubₗ ▸ₗ renₗ-Loc ℓ ξ) ≡ renₜ (subₜ τ (idSubₗ ▸ₗ ℓ)) ξ
  ty-eq =
    subₜ (renₜ τ (↑ ξ)) (idSubₗ ▸ₗ renₗ-Loc ℓ ξ)      ≡⟨ cong₂ subₜ (sym (subιₜ (↑ ξ) τ)) refl ⟩
    subₜ (subₜ τ (ιₗ (↑ ξ))) (idSubₗ ▸ₗ renₗ-Loc ℓ ξ) ≡⟨ sym (subFuseₜ (idSubₗ ▸ₗ renₗ-Loc ℓ ξ) (ιₗ (↑ ξ)) τ) ⟩
    subₜ τ ((idSubₗ ▸ₗ renₗ-Loc ℓ ξ) •ₗ ιₗ (↑ ξ))     ≡⟨ subExtₜ sub-eq τ ⟩
    subₜ τ (ιₗ ξ •ₗ (idSubₗ ▸ₗ ℓ))                    ≡⟨ subFuseₜ (ιₗ ξ) (idSubₗ ▸ₗ ℓ) τ ⟩
    subₜ (subₜ τ (idSubₗ ▸ₗ ℓ)) (ιₗ ξ)                ≡⟨ subιₜ ξ (subₜ τ (idSubₗ ▸ₗ ℓ)) ⟩
    renₜ (subₜ τ (idSubₗ ▸ₗ ℓ)) ξ                     ∎

  Θ'；Δ'；Γ⟨ξ⟩⊢Cℓ : (Θ' , Δ' , renCtx Γ ξ) ⊢ LocApp (renₗ C ξ) (renₗ-Loc ℓ ξ) ∶ renₜ (subₜ τ (idSubₗ ▸ₗ ℓ)) ξ
  Θ'；Δ'；Γ⟨ξ⟩⊢Cℓ = subst (λ x → (Θ' , Δ' , renCtx Γ ξ) ⊢ LocApp (renₗ C ξ) (renₗ-Loc ℓ ξ) ∶ x) ty-eq Θ'；Δ'；Γ⟨ξ⟩⊢Cℓ'
tyWkₗ {Θ} {Θ'} {Δ} {Δ'} {Γ} ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ (tyTellLet {C2 = C2} {τ = τ} C1∶Loc Θ⊢ρ1 Θ⊢ρ2 Θ⊢τ C2∶↑τ) =
  tyTellLet (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ C1∶Loc) (wfWkₗₗ ξ Θ≈Θ'∘ξ Θ⊢ρ1) (wfWkₗₗ ξ Θ≈Θ'∘ξ Θ⊢ρ2)
    (wfWkₜ ξ Θ≈Θ'∘ξ Θ⊢τ) ↑Θ'；↑Δ'；↑[Γ⟨ξ⟩]⊢C⟨↑ξ⟩∶↑τ⟨ξ⟩
  where
    module _ where
      open import Relation.Binary.Reasoning.Setoid (≈-Setoid′ ℕ Set)
      
      ↑Θ≈↑Θ'∘↑ξ : ↑LocCtx Θ ≈ ↑LocCtx Θ' ∘ ↑ ξ
      ↑Θ≈↑Θ'∘↑ξ = begin
        ↑LocCtx Θ        ≈⟨ ↑LocCtxExt Θ≈Θ'∘ξ ⟩
        ↑LocCtx (Θ' ∘ ξ) ≈⟨ ↑LocCtxFuse Θ' ξ ⟩
        ↑LocCtx Θ' ∘ ↑ ξ ∎

    module _ where
      open import Relation.Binary.Reasoning.Setoid (≈₂-Setoid′ Loc ℕ Typₑ)

      ↑Δ≈↑Δ'∘↑ξ : ↑LocalCtx Δ ≈₂ ↑LocalCtx Δ' ∘ₗ ↑ ξ
      ↑Δ≈↑Δ'∘↑ξ = begin
        ↑LocalCtx Δ         ≈⟨ ↑LocalCtxExt Δ≈Δ'∘ξ ⟩
        ↑LocalCtx (Δ' ∘ₗ ξ) ≈⟨ ↑LocalCtxFuse Δ' ξ ⟩
        ↑LocalCtx Δ' ∘ₗ ↑ ξ ∎

    ↑Θ'；↑Δ'；[↑Γ]⟨↑ξ⟩⊢C2⟨↑ξ⟩∶↑τ⟨↑ξ⟩ : (↑LocCtx Θ' , ↑LocalCtx Δ' , renCtx (↑Ctx Γ) (↑ ξ)) ⊢ renₗ C2 (↑ ξ) ∶ renₜ (↑ₜ τ) (↑ ξ)
    ↑Θ'；↑Δ'；[↑Γ]⟨↑ξ⟩⊢C2⟨↑ξ⟩∶↑τ⟨↑ξ⟩ = tyWkₗ (↑ ξ) (↑-pres-inj ξ-inj) ↑Θ≈↑Θ'∘↑ξ ↑Δ≈↑Δ'∘↑ξ C2∶↑τ

    ↑Θ'；↑Δ'；↑[Γ⟨ξ⟩]⊢C⟨↑ξ⟩∶↑τ⟨↑ξ⟩ : (↑LocCtx Θ' , ↑LocalCtx Δ' , ↑Ctx (renCtx Γ ξ)) ⊢ renₗ C2 (↑ ξ) ∶ renₜ (↑ₜ τ) (↑ ξ)
    ↑Θ'；↑Δ'；↑[Γ⟨ξ⟩]⊢C⟨↑ξ⟩∶↑τ⟨↑ξ⟩ = tyExt ≈-refl ≈₂-refl (renCtx↑ Γ ξ) ↑Θ'；↑Δ'；[↑Γ]⟨↑ξ⟩⊢C2⟨↑ξ⟩∶↑τ⟨↑ξ⟩

    open ≡-Reasoning

    ↑τ⟨↑ξ⟩≡↑τ⟨ξ⟩ : renₜ (↑ₜ τ) (↑ ξ) ≡ ↑ₜ (renₜ τ ξ)
    ↑τ⟨↑ξ⟩≡↑τ⟨ξ⟩ =
      renₜ (renₜ τ suc) (↑ ξ) ≡⟨ sym (renFuseₜ suc (↑ ξ) τ) ⟩
      renₜ τ (↑ ξ ∘ suc)      ≡⟨ renExtₜ (↑∘suc ξ) τ ⟩
      renₜ τ (suc ∘ ξ)        ≡⟨ renFuseₜ ξ suc τ ⟩
      renₜ (renₜ τ ξ) suc     ∎

    ↑Θ'；↑Δ'；↑[Γ⟨ξ⟩]⊢C⟨↑ξ⟩∶↑τ⟨ξ⟩ : (↑LocCtx Θ' , ↑LocalCtx Δ' , ↑Ctx (renCtx Γ ξ)) ⊢ renₗ C2 (↑ ξ) ∶ ↑ₜ (renₜ τ ξ)
    ↑Θ'；↑Δ'；↑[Γ⟨ξ⟩]⊢C⟨↑ξ⟩∶↑τ⟨ξ⟩ = subst (λ x → (↑LocCtx Θ' , ↑LocalCtx Δ' , ↑Ctx (renCtx Γ ξ)) ⊢ renₗ C2 (↑ ξ) ∶ x)
        ↑τ⟨↑ξ⟩≡↑τ⟨ξ⟩ ↑Θ'；↑Δ'；↑[Γ⟨ξ⟩]⊢C⟨↑ξ⟩∶↑τ⟨↑ξ⟩
