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
open ≡-Reasoning
open import Function

open import Common
open import LocalLang
open import Locations

module DecEq
  (L : Location)
  (E : Language L)
  where

open import Choreographies L E

open Location L
open Language E

{-
  A `view` of two elements of a recursive data type
  is a type whose inhabitance means they have the same constructor
-}
ViewChor : (c1 c2 : Chor) → Set
ViewChor (Done ℓ e) (Done ℓ' e') = ℓ ≡ ℓ' × e ≡ e'
ViewChor (Var x) (Var x') = x ≡ x'
ViewChor (Send ℓ1 c1 ℓ2) (Send ℓ1' c1' ℓ2') = ℓ1 ≡ ℓ1' × ℓ2 ≡ ℓ2'
ViewChor (If ℓ c1 c2 c3) (If ℓ' c1' c2' c3')  = ℓ ≡ ℓ'
ViewChor (Sync ℓ1 d ℓ2 c1) (Sync ℓ1' d' ℓ2' c1') = ℓ1 ≡ ℓ1' × d ≡ d' × ℓ2 ≡ ℓ2'
ViewChor (DefLocal ℓ c1 c2) (DefLocal ℓ' c1' c2') = ℓ ≡ ℓ'
ViewChor (Fun c) (Fun c') = ⊤
ViewChor (Fix c) (Fix c') = ⊤
ViewChor (App c1 c2) (App c1' c2') = ⊤
ViewChor (LocAbs c) (LocAbs c') = ⊤
ViewChor (LocApp c ℓ) (LocApp c' ℓ') = ℓ ≡ ℓ'
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
viewChor (Fun c) (Fun c') = just tt
viewChor (Fix c) (Fix c') = just tt
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
diagViewChor (Fix c1) = λ ()
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
≡-dec-Chor (Fix c1) (Fix c1') | just tt | eq with ≡-dec-Chor c1 c1'
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
