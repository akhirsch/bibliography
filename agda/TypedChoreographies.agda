{-# OPTIONS --safe #-}

open import Data.Unit
open import Data.Nat
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
open import LocationRenamings L E LE
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

↑ₜ : Typ → Typ
↑ₜ τ = renₜ τ suc

-- Location substitution on types
subₜ : Typ → (ℕ → Loc) → Typ
subₜ (At t ℓ) σ = At t (subₗ-Loc ℓ σ)
subₜ (Arrow τ1 τ2) σ = Arrow (subₜ τ1 σ) (subₜ τ2 σ)
subₜ (AllLoc τ) σ = AllLoc (subₜ τ (↑σₗ σ))

{-
  Location contexts are a natural number.
  We just need to know how many location variables are in scope.
-}
LocCtx : Set
LocCtx = ℕ

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

-- Location renaming on local contexts
renLocalCtx : LocalCtx → (ℕ → ℕ) → LocalCtx
renLocalCtx Δ ξ (Var x) = Δ (Var (ξ x))
renLocalCtx Δ ξ (Lit L) = Δ (Lit L)

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

-- Choreographic/global contexts
Ctx : Set
Ctx = ℕ → Typ

-- Add a global type to the context
_,,_ : Ctx → Typ → Ctx
(Γ ,, τ) zero = τ
(Γ ,, τ) (suc n) = Γ n

-- Location renaming on global contexts.
renCtx : Ctx → (ℕ → ℕ) → Ctx
renCtx Γ ξ n = renₜ (Γ n) ξ

↑Ctx : Ctx → Ctx
↑Ctx Γ = renCtx Γ suc

-- Location well-formedness
_⊢ₗ_ : LocCtx → Loc → Set
Θ ⊢ₗ Var x = x < Θ
Θ ⊢ₗ Lit L = ⊤

-- Location-list well-formedness
_⊢ₗₗ_ : LocCtx → LocList → Set
Θ ⊢ₗₗ [] = ⊤
Θ ⊢ₗₗ (ℓ ∷ ρ) = Θ ⊢ₗ ℓ × Θ ⊢ₗₗ ρ

-- Choreography type well-formedness
_⊢ₜ_ : LocCtx → Typ → Set
Θ ⊢ₜ At t ℓ = Θ ⊢ₗ ℓ
Θ ⊢ₜ Arrow τ1 τ2 = Θ ⊢ₜ τ1 × Θ ⊢ₜ τ2
Θ ⊢ₜ AllLoc τ = suc Θ ⊢ₜ τ

{-
  A Choreographic context is well-formed if
  each type that it maps to is well-formed
-}
_⊢_ : LocCtx → Ctx → Set
Θ ⊢ Γ = ∀ n → Θ ⊢ₜ Γ n

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
  tyVar : ∀{Θ Δ Γ x}
          (Θ⊢Γ : Θ ⊢ Γ) →
          (Θ , Δ , Γ) ⊢ Var x ∶ Γ x
  tyDone : ∀{Θ Δ Γ e t ℓ}
           (Θ⊢ℓ : Θ ⊢ₗ ℓ) →
           (Δ[ℓ]⊢e:t : Δ ℓ ⊢ₑ e ∶ t) →
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
             (↑Θ；↑Δ；↑Γ⊢C:τ : (suc Θ , ↑LocalCtx Δ , ↑Ctx Γ)  ⊢ C ∶ τ) →
             (Θ , Δ , Γ) ⊢ LocAbs C ∶ AllLoc τ
  tyLocApp : ∀{Θ Δ Γ C τ ℓ}
             (Θ；Δ；Γ⊢C:∀τ : (Θ , Δ , Γ)  ⊢ C ∶ AllLoc τ) →
             (Θ⊢ℓ : Θ ⊢ₗ ℓ) →
             (Θ , Δ , Γ) ⊢ LocApp C ℓ ∶ subₜ τ (idSubₗ ▸ₗ ℓ)
  tyTellLet : ∀{Θ Δ Γ C1 C2 ρ1 ρ2 ℓ τ} →
              (Θ；Δ；Γ⊢C1:ℓ_t : (Θ , Δ , Γ) ⊢ C1 ∶ At Locₑ ℓ)
              (Θ⊢ρ1 : Θ ⊢ₗₗ ρ1) (Θ⊢ρ2 : Θ ⊢ₗₗ ρ2)
              (Θ⊢τ : Θ ⊢ₜ τ)
              (↑Θ；↑Δ；↑Γ⊢C2:↑τ : (suc Θ , ↑LocalCtx Δ , ↑Ctx Γ) ⊢ C2 ∶ ↑ₜ τ) →
              (Θ , Δ , Γ) ⊢ TellLet ℓ ρ1 C1 ρ2 C2 ∶ τ
