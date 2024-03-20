{-# OPTIONS --safe #-}

open import Data.Empty
open import Data.Unit
open import Data.Maybe
open import Data.Nat renaming (_≟_ to ≡-dec-ℕ)
open import Data.Bool renaming (_≟_ to ≡-dec-Bool)
open import Data.List
open import Data.List.Properties renaming (≡-dec to ≡-dec-List)
open import Data.Product
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

-- A view of two programs guarantees they agree on the constructor
ViewChor : (c1 c2 : Chor) → Set
ViewChor (Done ℓ e) (Done ℓ' e') = ℓ ≡ ℓ' × e ≡ e'
ViewChor (Var x) (Var x') = x ≡ x'
ViewChor (Send ℓ1 c1 ℓ2) (Send ℓ1' c1' ℓ2') = ℓ1 ≡ ℓ1' × ℓ2 ≡ ℓ2'
ViewChor (If ℓ c1 c2 c3) (If ℓ' c1' c2' c3')  = ℓ ≡ ℓ'
ViewChor (Sync ℓ1 d ℓ2 c1) (Sync ℓ1' d' ℓ2' c1') = ℓ1 ≡ ℓ1' × d ≡ d' × ℓ2 ≡ ℓ2'
ViewChor (DefLocal ℓ c1 c2) (DefLocal ℓ' c1' c2') = ℓ ≡ ℓ'
ViewChor (Fun c1) (Fun c1') = ⊤
ViewChor (App c1 c2) (App c1' c2') = ⊤
ViewChor (LocAbs c1) (LocAbs c1') = ⊤
ViewChor (LocApp c1 ℓ) (LocApp c1' ℓ') = ℓ ≡ ℓ'
ViewChor (TellLet ℓ ρ1 c1 ρ2 c2) (TellLet ℓ' ρ1' c1' ρ2' c2') = ℓ ≡ ℓ' × ρ1 ≡ ρ1' × ρ2 ≡ ρ2'
ViewChor _ _ = ⊥

-- Where we can, construct a view of two programs
viewChor : (c1 c2 : Chor) → Maybe (ViewChor c1 c2)
viewChor (Done ℓ e) (Done ℓ' e') with ≡-dec-Loc ℓ ℓ'
... | no ¬p = nothing
... | yes p with ≡-dec-Expr e e'
... | no ¬q = nothing
... | yes q = just (p , q)
viewChor (Var x) (Var x') with ≡-dec-ℕ x x'
... | no ¬p = nothing
... | yes p = just p
viewChor (Send ℓ1 c1 ℓ2) (Send ℓ1' c1' ℓ2') with ≡-dec-Loc ℓ1 ℓ1'
... | no ¬p = nothing
... | yes p with ≡-dec-Loc ℓ2 ℓ2'
... | no ¬q = nothing
... | yes q = just (p , q)
viewChor (If ℓ c1 c2 c3) (If ℓ' c1' c2' c3') with ≡-dec-Loc ℓ ℓ'
... | no ¬p = nothing
... | yes p = just p
viewChor (Sync ℓ1 d ℓ2 c1) (Sync ℓ1' d' ℓ2' c1') with ≡-dec-Loc ℓ1 ℓ1'
... | no ¬p = nothing
... | yes p with ≡-dec-Bool d d'
... | no ¬q = nothing
... | yes q with ≡-dec-Loc ℓ2 ℓ2'
... | no ¬r = nothing
... | yes r = just (p , q , r)
viewChor (DefLocal ℓ c1 c2) (DefLocal ℓ' c1' c2') with ≡-dec-Loc ℓ ℓ'
... | no ¬p = nothing
... | yes p = just p
viewChor (Fun c1) (Fun c1') = just tt
viewChor (App c1 c2) (App c1' c2') = just tt
viewChor (LocAbs c1) (LocAbs c1') = just tt
viewChor (LocApp c1 ℓ) (LocApp c1' ℓ') with ≡-dec-Loc ℓ ℓ'
... | no ¬p = nothing
... | yes p = just p
viewChor (TellLet ℓ ρ1 c1 ρ2 c2) (TellLet ℓ' ρ1' c1' ρ2' c2') with ≡-dec-Loc ℓ ℓ'
... | no ¬p = nothing
... | yes p with ≡-dec-LocList ρ1 ρ1'
... | no ¬q = nothing
... | yes q with ≡-dec-LocList ρ2 ρ2'
... | no ¬r = nothing
... | yes r = just (p , q , r)
viewChor _ _ = nothing

-- There must be a view between a program and itself
diagViewChor : (c : Chor) → ¬ (viewChor c c ≡ nothing)
diagViewChor (Done ℓ e) with ≡-dec-Loc ℓ ℓ
... | no ¬p = λ _ → ¬p refl
... | yes p with ≡-dec-Expr e e
... | no ¬q = λ _ → ¬q refl
... | yes q = λ ()
diagViewChor (Var x) with ≡-dec-ℕ x x
... | no ¬p = λ _ → ¬p refl
... | yes p = λ ()
diagViewChor (Send ℓ1 c1 ℓ2) with ≡-dec-Loc ℓ1 ℓ1
... | no ¬p = λ _ → ¬p refl
... | yes p with ≡-dec-Loc ℓ2 ℓ2
... | no ¬q = λ _ → ¬q refl
... | yes q = λ ()
diagViewChor (If ℓ c1 c2 c3) with ≡-dec-Loc ℓ ℓ
... | no ¬p = λ _ → ¬p refl
... | yes p = λ ()
diagViewChor (Sync ℓ1 d ℓ2 c1) with ≡-dec-Loc ℓ1 ℓ1
... | no ¬p = λ _ → ¬p refl
... | yes p with ≡-dec-Bool d d
... | no ¬q = λ _ → ¬q refl
... | yes q with ≡-dec-Loc ℓ2 ℓ2
... | no ¬r = λ _ → ¬r refl
... | yes r = λ ()
diagViewChor (DefLocal ℓ c1 c2) with ≡-dec-Loc ℓ ℓ
... | no ¬p = λ _ → ¬p refl
... | yes p = λ ()
diagViewChor (Fun c1) = λ ()
diagViewChor (App c1 c2) = λ ()
diagViewChor (LocAbs c1) = λ ()
diagViewChor (LocApp c1 ℓ) with ≡-dec-Loc ℓ ℓ
... | no ¬p = λ _ → ¬p refl
... | yes p = λ ()
diagViewChor (TellLet ℓ ρ1 c1 ρ2 c2) with ≡-dec-Loc ℓ ℓ
... | no ¬p = λ _ → ¬p refl
... | yes p with ≡-dec-LocList ρ1 ρ1
... | no ¬q = λ _ → ¬q refl
... | yes q with ≡-dec-LocList ρ2 ρ2
... | no ¬r = λ _ → ¬r refl
... | yes r = λ ()

{-
  We can decide equality by first trying to construct a view and inspecting
  to see if it succeeds, and then recursively deciding equality for
  all program subterms
-}
≡-dec-Chor : DecidableEquality Chor
≡-dec-Chor c1 c2 with viewChor c1 c2 | inspect (viewChor c1) c2
≡-dec-Chor (Done ℓ e) (Done .ℓ .e) | just (refl , refl) | eq = yes refl
≡-dec-Chor (Var x₁) (Var .x₁) | just refl | eq = yes refl
≡-dec-Chor (Send ℓ1 c1 ℓ2) (Send .ℓ1 c1' .ℓ2) | just (refl , refl) | eq with ≡-dec-Chor c1 c1'
... | no ¬p = no λ{ refl → ¬p refl }
... | yes refl = yes refl
≡-dec-Chor (If ℓ c1 c2 c3) (If .ℓ c1' c2' c3') | just refl | eq with ≡-dec-Chor c1 c1'
... | no ¬p = no λ{ refl → ¬p refl }
... | yes refl with ≡-dec-Chor c2 c2'
... | no ¬p = no λ{ refl → ¬p refl }
... | yes refl with ≡-dec-Chor c3 c3'
... | no ¬p = no λ{ refl → ¬p refl }
... | yes refl = yes refl
≡-dec-Chor (Sync ℓ1 d ℓ2 c1) (Sync .ℓ1 .d .ℓ2 c1') | just (refl , refl , refl) | eq with ≡-dec-Chor c1 c1'
... | no ¬p = no λ{ refl → ¬p refl }
... | yes refl = yes refl
≡-dec-Chor (DefLocal ℓ c1 c2) (DefLocal .ℓ c1' c2') | just refl | eq with ≡-dec-Chor c1 c1'
... | no ¬p = no λ{ refl → ¬p refl }
... | yes refl with ≡-dec-Chor c2 c2'
... | no ¬p = no λ{ refl → ¬p refl }
... | yes refl = yes refl
≡-dec-Chor (Fun c1) (Fun c1') | just tt | eq with ≡-dec-Chor c1 c1'
... | no ¬p = no λ{ refl → ¬p refl }
... | yes refl = yes refl
≡-dec-Chor (App c1 c2) (App c1' c2') | just tt | eq with ≡-dec-Chor c1 c1'
... | no ¬p = no λ{ refl → ¬p refl }
... | yes refl with ≡-dec-Chor c2 c2'
... | no ¬p = no λ{ refl → ¬p refl }
... | yes refl = yes refl
≡-dec-Chor (LocAbs c1) (LocAbs c1') | just tt | eq with ≡-dec-Chor c1 c1'
... | no ¬p = no λ{ refl → ¬p refl }
... | yes refl = yes refl
≡-dec-Chor (LocApp c1 ℓ) (LocApp c1' .ℓ) | just refl | eq with ≡-dec-Chor c1 c1'
... | no ¬p = no λ{ refl → ¬p refl }
... | yes refl = yes refl
≡-dec-Chor (TellLet ℓ ρ1 c1 ρ2 c2) (TellLet .ℓ .ρ1 c1' .ρ2 c2') | just (refl , refl , refl) | eq with ≡-dec-Chor c1 c1'
... | no ¬p = no λ{ refl → ¬p refl }
... | yes refl with ≡-dec-Chor c2 c2'
... | no ¬p = no λ{ refl → ¬p refl }
... | yes refl = yes refl
≡-dec-Chor c1 c2 | nothing | [ view≡⊥ ] = no λ{ refl → diagViewChor _ view≡⊥ }

data ChorVal : Chor → Set where
  DoneVal : (L : LocVal) (v : Expr) → Val v → ChorVal (Done (Lit L) v)
  FunVal : (C : Chor) → ChorVal (Fun C)
  LocAbsVal : (C : Chor) → ChorVal (LocAbs C)

