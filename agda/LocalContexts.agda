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

module LocalContexts
  (L : Location)
  (E : Language L)
  (LE : LawfulLanguage L E)
  (TE : TypedLocalLanguage L E LE)
  where

open import Types L E LE TE
open import Choreographies L E LE TE
open import LocalRenamings L E LE TE
open import LocationRenamings L E LE TE
open import Renamings L E LE TE
open import Substitutions L E LE TE
open import LocationContexts L E LE TE
open Location L
open Language E
open LawfulLanguage LE
open TypedLocalLanguage TE


{-
  Local contexts are an infinite map from
  locations and local variables to local types
-}
LocalCtx : Set
LocalCtx = Loc → ℕ → Typₑ

-- Add a type to specified local context
_,,[_]_ : LocalCtx → Loc → Typₑ → LocalCtx
(Δ ,,[ ℓ ] t) ℓ' with ≡-dec-Loc ℓ ℓ'
... | yes _ = λ{ zero → t
              ; (suc n) → Δ ℓ n }
... | no  _ = Δ ℓ'

-- Adding to a local context respects extensional equality
addLocalCtxExt : ∀{Δ Δ'} →
               Δ ≈₂ Δ' →
               ∀ ℓ t →
               Δ ,,[ ℓ ] t ≈₂ Δ' ,,[ ℓ ] t
addLocalCtxExt Δ≈Δ' ℓ t ℓ' with ≡-dec-Loc ℓ ℓ'
... | yes _ = λ{ zero → refl ; (suc n) → Δ≈Δ' ℓ n }
... | no  _ = Δ≈Δ' ℓ'              

-- Renaming of locations in local contexts
_∘ₗ_ : LocalCtx → (ℕ → ℕ) → LocalCtx
(Δ ∘ₗ ξ) ℓ = Δ (renₗ-Loc ℓ ξ)

-- Renaming preserves injectivity
renₗ-Loc-inj : ∀{ℓ ℓ' ξ} →
               Injective _≡_ _≡_ ξ →
               renₗ-Loc ℓ ξ ≡ renₗ-Loc ℓ' ξ →
               ℓ ≡ ℓ'
renₗ-Loc-inj {ℓ = Var x} {Var x'} ξ-inj Vξx≡Vξx' = cong Var (ξ-inj (Varₗ-inj Vξx≡Vξx'))
renₗ-Loc-inj {ℓ = Var x} {Lit L'} ξ-inj ()
renₗ-Loc-inj {ℓ = Lit L} {Var x'} ξ-inj ()
renₗ-Loc-inj {ℓ = Lit L} {Lit .L} ξ-inj refl = refl

{-
  Composing a local context with an injective
  renaming distributes over adding to the context
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
  ↑ on local contexts.
  Arbitrarily assigns the boolean type to all variables
  of the newly introduced location variable. This should
  be OK because the local type system only cares about
  the variables which are in context.
-}
↑LocalCtx : LocalCtx → LocalCtx
↑LocalCtx Δ (Var zero) = λ _ → Boolₑ
↑LocalCtx Δ (Var (suc x)) = Δ (Var x)
↑LocalCtx Δ (Lit L) = Δ (Lit L)

-- ↑ respects extensional equality
↑LocalCtxExt : ∀{Δ1 Δ2} → Δ1 ≈₂ Δ2 → ↑LocalCtx Δ1 ≈₂ ↑LocalCtx Δ2
↑LocalCtxExt Δ1≈Δ2 (Var zero) n = refl
↑LocalCtxExt Δ1≈Δ2 (Var (suc x)) n = Δ1≈Δ2 (Var x) n
↑LocalCtxExt Δ1≈Δ2 (Lit L) n = Δ1≈Δ2 (Lit L) n

-- ↑ distributes over location renaming
↑LocalCtx-distr-∘ₗ : ∀ Δ ξ → ↑LocalCtx (Δ ∘ₗ ξ) ≈₂ ↑LocalCtx Δ ∘ₗ ↑ ξ
↑LocalCtx-distr-∘ₗ Δ ξ (Var zero) n = refl
↑LocalCtx-distr-∘ₗ Δ ξ (Var (suc x)) n = refl
↑LocalCtx-distr-∘ₗ Δ ξ (Lit L) n = refl

-- Renaming of local variables in local contexts
_∘ₗₑ_ : LocalCtx → LocalRen → LocalCtx
(Δ ∘ₗₑ ξ) ℓ n = Δ ℓ (ξ ℓ n)

{-
  Composing a local context with a local renaming
  distributes over adding to the context
-}
∘ₗₑ,, : ∀ Δ ξ ℓ t →
       (Δ ∘ₗₑ ξ) ,,[ ℓ ] t ≈₂ (Δ ,,[ ℓ ] t) ∘ₗₑ (↑[ ℓ ] ξ)
∘ₗₑ,, Δ ξ ℓ t ℓ' with ≡-dec-Loc ℓ ℓ'
... | yes refl = λ{ zero → refl
               ; (suc n) → refl }
... | no  _ = λ n →  refl

-- ↑ distributes over local renaming
↑LocalCtx-distr-∘ₗₑ : ∀ Δ ξ → ↑LocalCtx (Δ ∘ₗₑ ξ) ≈₂ ↑LocalCtx Δ ∘ₗₑ ↑ₗₑ ξ
↑LocalCtx-distr-∘ₗₑ Δ ξ (Var zero) n = refl
↑LocalCtx-distr-∘ₗₑ Δ ξ (Var (suc x)) n = refl
↑LocalCtx-distr-∘ₗₑ Δ ξ (Lit L) n = refl
