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

module Choreographies
  (E : Language)
  (LE : LawfulLanguage E)
  (LocVal : Set)
  (≡-dec-LocVal : DecidableEquality LocVal)
  where

open Language E
open LawfulLanguage LE

-- Synchronization labels are represented by booleans
SyncLabel : Set
SyncLabel = Bool

-- Locations are either concrete or a variable
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

≡-dec-LocList : DecidableEquality LocList
≡-dec-LocList = ≡-dec-List ≡-dec-Loc

-- Choreographic programs
data Chor : Set where
  Done : (ℓ : Loc) (e : Expr) → Chor
  Var : (x : ℕ) → Chor
  Send : (ℓ1 : Loc) (C : Chor) (ℓ2 : Loc) → Chor
  If : (ℓ : Loc) (C : Chor) (C1 : Chor) (C2 : Chor) → Chor
  Sync : (ℓ1 : Loc) (d : SyncLabel) (ℓ2 : Loc) (C : Chor) → Chor
  DefLocal : (ℓ : Loc) (C1 : Chor) (C2 : Chor) → Chor
  Fun : (C : Chor) → Chor
  App : (C1 C2 : Chor) → Chor
  LocAbs : (C : Chor) → Chor
  LocApp : (C : Chor) (ℓ : Loc) → Chor
  TellLet : (ℓ : Loc) (ρ1 : LocList) (C1 : Chor) (ρ2 : LocList) (C2 : Chor) → Chor

{-
  Values of the language are either local expressions,
  global functions, or local value abstractions
-}
data Val : Chor → Set where
  DoneVal : (L : LocVal) (v : Expr) → Valₑ v → Val (Done (Lit L) v)
  FunVal : (C : Chor) → Val (Fun C)
  LocAbsVal : (C : Chor) → Val (LocAbs C)
