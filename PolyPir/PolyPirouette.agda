{-# OPTIONS --safe #-}

open import Data.Empty
open import Data.Unit
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map)
open import Data.Bool
open import Data.Nat
open import Data.List
open import Data.List.Properties
open import Data.Maybe renaming (map to mmap)
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr) hiding (map)
open import Relation.Nullary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality
open import Function

open ≡-Reasoning

open import Common

module PolyPir.PolyPirouette
  -- Local kinds
  (Kndₑ : Set)
  -- There should be a local kind for local types
  (*ₑ : Kndₑ)
  -- Local type constructor shape
  (TyShapeₑ : Set)
  -- Local type constructor signature
  (TyPosₑ : TyShapeₑ → List (List Kndₑ × Kndₑ) × Kndₑ)
  -- Location values
  (Loc : Set)
  -- Locations should have decidable equality
  (≡-dec-Loc : DecidableEquality Loc)
  where

open import ThirdOrderSyntax Kndₑ *ₑ TyShapeₑ TyPosₑ
  using ()
  renaming (TyVec to TyVecₑ; Ctx to KndCtxₑ)

-- Choreographic kinds
data Knd : Set where
  -- Kind of choreographic types
  * : Knd
  -- Kind of locations
  *ₗ : Knd
  -- Kind of sets of locations
  *ₛ : Knd
  -- Kind for local kinds
  LocKnd : Kndₑ → Knd

data TyShape : Set where
  -- Embedding of local types
  LocalTy : (sₑ : TyShapeₑ) → TyShape
  -- Type of bound local values
  Bnd : TyShape
  -- Type of choreographic local values
  At : TyShape

  -- Choreographic function type
  Fun : TyShape
  -- Choreographic universal quantification
  All : (κ : Knd) → TyShape

  -- Literal locations
  LitLoc : Loc → TyShape
  -- Empty location set
  Emp : TyShape
  -- Singleton location set
  Sng : TyShape
  -- Union of location sets
  Union : TyShape

-- Choreographic type signatures
TyPos : TyShape → List (List Knd × Knd) × Knd
-- sₑ Σₑ : κ ⊢ LocalTy{sₑ} Σₑ : κ
TyPos (LocalTy sₑ) = map (λ{ (Γ , κ) → map LocKnd Γ , LocKnd κ }) (TyPosₑ sₑ .fst) , LocKnd (TyPosₑ sₑ .snd)
-- Bnd *ₗ *ₑ : *
TyPos Bnd = ([] , *ₗ) ∷ ([] , LocKnd *ₑ) ∷ [] , *
-- At *ₗ *ₑ : *
TyPos At = ([] , *ₗ) ∷ ([] , LocKnd *ₑ) ∷ [] , *
-- Fun * * : *
TyPos Fun = ([] , *) ∷ ([] , *) ∷ [] , *
-- All{κ} [κ]* : *
TyPos (All κ) = (κ ∷ [] , *) ∷ [] , *
-- LitLoc{L} : *ₗ
TyPos (LitLoc L) = [] , *ₗ
-- Emp : *ₛ
TyPos Emp = [] , *ₛ
-- Sng *ₗ : *ₛ
TyPos Sng = ([] , *ₗ) ∷ [] , *ₛ
-- Union *ₛ *ₛ : *ₛ
TyPos Union = ([] , *ₛ) ∷ ([] , *ₛ) ∷ [] , *ₛ