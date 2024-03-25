{-# OPTIONS --safe #-}

open import Data.Nat renaming (_≟_ to ≡-dec-ℕ)
open import Data.Bool renaming (_≟_ to ≡-dec-Bool)
open import Data.List
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function

open import Common
open import LocalLang
open import Locations

module Semantics
  (L : Location)
  (E : Language L)
  (LE : LawfulLanguage L E)
  where

open import Choreographies L E
open import Substitutions L E LE
open import LocalSubstitutions L E LE
open import LocationSubstitutions L E LE
open Location L
open Language E
open LawfulLanguage LE

data TraceElem : Set where
  • : TraceElem
  LocStep : LocVal → TraceElem
  SendVal : (L1 : LocVal) →
            (v : Expr) → Valₑ v →
            (L2 : LocVal) →
            TraceElem
  SendSync : (L1 : LocVal) →
             (d : SyncLabel) →
             (L2 : LocVal) →
             TraceElem
  TellLoc : (L1 : LocVal) →
            (L2 : LocVal) →
            (ρ1 ρ2 : List LocVal) →
            TraceElem

Trace : Set
Trace = List TraceElem

data _⇒[_]_ : Chor → TraceElem → Chor → Set where
  stepDone : ∀{e1 e2 L}
             (e1⇒e2 : e1 ⇒ₑ e2) →
             Done (Lit L) e1 ⇒[ LocStep L ] Done (Lit L) e2
             
  stepSend : ∀{C C' L1 L2 T}
             (C⇒C' : C ⇒[ T ] C) →
             Send L1 C L2 ⇒[ T ] Send L1 C' L2
  stepSendV : ∀{v L1 L2}
              (v-Val : Valₑ v) →
              Send (Lit L1) (Done (Lit L1) v) (Lit L2)
              ⇒[ SendVal L1 v v-Val L2 ]
              Done (Lit L2) v
  stepSync : ∀{L1 d L2 C} →
             Sync (Lit L1) d (Lit L2) C ⇒[ SendSync L1 d L2 ] C

  stepIf : ∀{C C' C1 C2 L T}
           (C⇒C' : C ⇒[ T ] C') →
           If L C C1 C2 ⇒[ T ] If L C' C1 C2
  stepIfT : ∀{C1 C2 L} →
            If (Lit L) (Done (Lit L) ttₑ) C1 C2 ⇒[ LocStep L ] C1
  stepIfF : ∀{C1 C2 L} →
            If (Lit L) (Done (Lit L) ffₑ) C1 C2 ⇒[ LocStep L ] C2
            
  stepDefLocal : ∀{C1 C1' C2 L T}
                 (C1⇒C1' : C1 ⇒[ T ] C1') →
                 DefLocal (Lit L) C1 C2 ⇒[ T ] DefLocal (Lit L) C1' C2
  stepDefLocalV : ∀{v C L}
                  (v-Val : Valₑ v) →
                  DefLocal (Lit L) (Done (Lit L) v) C ⇒[ • ]
                  subₗₑ C (idSubₗₑ ▸[ Lit L ] v)
                  
  stepAppFun : ∀{C1 C1' C2 T}
               (C1⇒C1' : C1 ⇒[ T ] C1') →
               App C1 C2 ⇒[ T ] App C1' C2
  stepAppArg : ∀{V C C' T} →
               (V-Val : Val V)
               (C⇒C' : C ⇒[ T ] C') →
               App V C ⇒[ T ] App V C'
  stepApp : ∀{V C}
            (V-Val : Val V) →
            App (Fun C) V ⇒[ • ] sub C (idSub ▸ V)
  stepFix : ∀{C} → Fix C ⇒[ • ] sub C (idSub ▸ Fix C)

  stepLocAppFun : ∀{C C' L T}
                  (C⇒C' : C ⇒[ T ] C') →
                  LocApp C (Lit L) ⇒[ T ] LocApp C' (Lit L)
  stepLocApp : ∀{C L} →
               (LocApp (LocAbs C) (Lit L))
               ⇒[ • ]
               subₗ C (idSubₗ ▸ₗ Lit L)

  stepTellLet : ∀{C1 C1' C2 T ρ1 ρ2 L} →
                (C1⇒C1' : C1 ⇒[ T ] C1') →
                TellLet (Lit L) (map Lit ρ1) C1 (map Lit ρ2) C2 ⇒[ T ]
                TellLet (Lit L) (map Lit ρ1) C1' (map Lit ρ2) C2
  stepTellLetV : ∀{L1 L2 C ρ1 ρ2} →
                 TellLet (Lit L1) (map Lit ρ1) (Done (Lit L1) (locₑ L2)) (map Lit ρ2) C
                 ⇒[ TellLoc L1 L2 ρ1 ρ2 ]
                 subₗ C (idSubₗ ▸ₗ Lit L2)

-- Values cannot step
valNoStep : ∀{V C T} → Val V → ¬ (V ⇒[ T ] C)
valNoStep (DoneVal L v v-val) (stepDone v⇒e) = valNoStepₑ v-val v⇒e