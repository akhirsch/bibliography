{-# OPTIONS --safe #-}

open import Data.Nat renaming (_≟_ to ≡-dec-ℕ)
open import Data.Bool renaming (_≟_ to ≡-dec-Bool)
open import Data.List
open import Data.List.Properties renaming (≡-dec to ≡-dec-List)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function

open import LocalLang
open import Locations

module Choreographies
  (E : Language)
  (L : Location)
  where

open Language E
open Location L

-- Synchronization labels are represented by booleans
SyncLabel : Set
SyncLabel = Bool

-- Choreographic programs
data Chor : Set where
  Done : (ℓ : Loc) (e : Expr) → Chor
  Var : (x : ℕ) → Chor
  Send : (ℓ1 : Loc) (C : Chor) (ℓ2 : Loc) → Chor
  If : (ℓ : Loc) (C : Chor) (C1 : Chor) (C2 : Chor) → Chor
  Sync : (ℓ1 : Loc) (d : SyncLabel) (ℓ2 : Loc) (C : Chor) → Chor
  DefLocal : (ℓ : Loc) (C1 : Chor) (C2 : Chor) → Chor
  Fun Fix : (C : Chor) → Chor
  App : (C1 C2 : Chor) → Chor
  LocAbs : (C : Chor) → Chor
  LocApp : (C : Chor) (ℓ : Loc) → Chor
  TellLet : (ℓ : Loc) (ρ1 : LocList) (C1 : Chor) (ρ2 : LocList) (C2 : Chor) → Chor

{-
  Values of the language are either local expressions,
  global functions, or location abstractions
-}
data Val : Chor → Set where
  DoneVal : (L : LocVal) (v : Expr) → Valₑ v → Val (Done (Lit L) v)
  FunVal : (C : Chor) → Val (Fun C)
  LocAbsVal : (C : Chor) → Val (LocAbs C)
