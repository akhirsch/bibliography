{-# OPTIONS --safe #-}

open import Data.Nat renaming (_≟_ to ≡-dec-ℕ)
open import Data.List
open import Data.List.Properties renaming (≡-dec to ≡-dec-List)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function

open import Common

module Locations where

record Location : Set₁ where
  field
    -- Literal location values
    LocVal : Set
    -- Literal locations should have decidable equality
    ≡-dec-LocVal : DecidableEquality LocVal

  -- Abstract locations are either a literal value or a variable
  data Loc : Set where
    Var : (x : ℕ) → Loc
    Lit : (L : LocVal) → Loc

  -- Locations have decidable equality
  ≡-dec-Loc : DecidableEquality Loc
  ≡-dec-Loc (Var x1) (Var x2) with ≡-dec-ℕ x1 x2
  ... | yes refl = yes refl
  ... | no x1≠x2 = no λ{ refl → x1≠x2 refl }
  ≡-dec-Loc (Var x) (Lit L) = no (λ ())
  ≡-dec-Loc (Lit L) (Var x) = no (λ ())
  ≡-dec-Loc (Lit L1) (Lit L2) with ≡-dec-LocVal L1 L2
  ... | yes refl = yes refl
  ... | no L1≠L2 = no λ{ refl → L1≠L2 refl }

  -- Lists of locations
  LocList : Set
  LocList = List Loc

  -- Lists of locations have decidable equality
  ≡-dec-LocList : DecidableEquality LocList
  ≡-dec-LocList = ≡-dec-List ≡-dec-Loc

  ----------------
  --- RENAMING ---
  ----------------

  -- Rename location variables
  renₗ-Loc : Loc → (ℕ → ℕ) → Loc
  renₗ-Loc (Var x) ξ = Var (ξ x)
  renₗ-Loc (Lit L) ξ = Lit L

  -- Renaming location variables in a location respects extensional equality
  renExtₗ-Loc : ∀{ξ1 ξ2} →
                ξ1 ≈ ξ2 →
                ∀ ℓ → renₗ-Loc ℓ ξ1 ≡ renₗ-Loc ℓ ξ2
  renExtₗ-Loc ξ1≈ξ2 (Var x) = cong Var (ξ1≈ξ2 x)
  renExtₗ-Loc ξ1≈ξ2 (Lit L) = refl

  -- Renaming location variables in a location respects the identity
  renIdₗ-Loc : ∀ ℓ → renₗ-Loc ℓ idRen ≡ ℓ
  renIdₗ-Loc (Var x) = refl
  renIdₗ-Loc (Lit L) = refl

  -- Renaming location variables in a location enjoys fusion
  renFuseₗ-Loc : ∀ ξ1 ξ2 ℓ → renₗ-Loc ℓ (ξ2 ∘ ξ1) ≡ renₗ-Loc (renₗ-Loc ℓ ξ1) ξ2
  renFuseₗ-Loc ξ1 ξ2 (Var x) = refl
  renFuseₗ-Loc ξ1 ξ2 (Lit L) = refl

  -- Rename location variables in a location list
  renₗ-List : LocList → (ℕ → ℕ) → LocList
  renₗ-List ρ ξ = Data.List.map (λ ℓ → renₗ-Loc ℓ ξ) ρ

  -- Renaming location variables in a location list respects extensional equality
  renExtₗ-List : ∀{ξ1 ξ2} →
                 ξ1 ≈ ξ2 →
                 ∀ ρ → renₗ-List ρ ξ1 ≡ renₗ-List ρ ξ2
  renExtₗ-List ξ1≈ξ2 [] = refl
  renExtₗ-List ξ1≈ξ2 (ℓ ∷ ρ) = cong₂ _∷_ (renExtₗ-Loc ξ1≈ξ2 ℓ) (renExtₗ-List ξ1≈ξ2 ρ)

  -- Renaming location variables in a location list respects the identity
  renIdₗ-List : ∀ ρ → renₗ-List ρ idRen ≡ ρ
  renIdₗ-List [] = refl
  renIdₗ-List (ℓ ∷ ρ) = cong₂ _∷_ (renIdₗ-Loc ℓ) (renIdₗ-List ρ)

  -- Renaming location variables in a location list enjoys fusion
  renFuseₗ-List : ∀ ξ1 ξ2 ρ → renₗ-List ρ (ξ2 ∘ ξ1) ≡ renₗ-List (renₗ-List ρ ξ1) ξ2
  renFuseₗ-List ξ1 ξ2 [] = refl
  renFuseₗ-List ξ1 ξ2 (ℓ ∷ ρ) = cong₂ _∷_ (renFuseₗ-Loc ξ1 ξ2 ℓ) (renFuseₗ-List ξ1 ξ2 ρ)

  --------------------
  --- SUBSTITUTION ---
  --------------------

  -- Identity location substitution
  idSubₗ : ℕ → Loc
  idSubₗ n = Var n

  -- The `up` construction on location substitutions
  ↑σₗ :  (ℕ → Loc) → ℕ → Loc
  ↑σₗ σ zero = Var zero
  ↑σₗ σ (suc n) = renₗ-Loc (σ n) suc
 
  -- Substitute location variables
  subₗ-Loc : Loc → (ℕ → Loc) → Loc
  subₗ-Loc (Var x) σ = σ x
  subₗ-Loc (Lit L) σ = Lit L

  -- Substituting location variables respects extensional equality
  subExtₗ-Loc : ∀{σ1 σ2} →
                σ1 ≈ σ2 →
                ∀ ℓ → subₗ-Loc ℓ σ1 ≡ subₗ-Loc ℓ σ2
  subExtₗ-Loc σ1≈σ2 (Var x) = σ1≈σ2 x
  subExtₗ-Loc σ1≈σ2 (Lit L) = refl

  -- Substituting location variables respects the identity
  subIdₗ-Loc : ∀ ℓ → subₗ-Loc ℓ idSubₗ ≡ ℓ
  subIdₗ-Loc (Var x) = refl
  subIdₗ-Loc (Lit L) = refl
  
  -- Inclusion from renamings to location substitutions
  ιₗ : (ℕ → ℕ) → ℕ → Loc
  ιₗ ξ n = Var (ξ n)

  -- The `up` construction commutes with the inclusion
  ↑σιₗ : ∀ ξ → ↑σₗ (ιₗ ξ) ≈ ιₗ (↑ ξ)
  ↑σιₗ ξ zero = refl
  ↑σιₗ ξ (suc n) = refl

  -- Substitution along an inclusion is the same as a renaming
  subιₗ-Loc : ∀ ξ ℓ → subₗ-Loc ℓ (ιₗ ξ) ≡ renₗ-Loc ℓ ξ
  subιₗ-Loc ξ (Var x) = refl
  subιₗ-Loc ξ (Lit L) = refl
