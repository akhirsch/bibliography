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
open import TypedLocalLang
open import Locations

module LocalSubstitutions
  (L : Location)
  (E : Language L)
  (LE : LawfulLanguage L E)
  (TE : TypedLocalLanguage L E LE)
  where

open import Types L E LE TE
open import Choreographies L E LE TE
open import LocalRenamings L E LE TE
open import LocalContexts L E LE TE
open Language E
open LawfulLanguage LE
open TypedLocalLanguage TE
open Location L
open ≡-Reasoning

data LocalSub : Set where
  ε : LocalSub
  AddSub : (σ : LocalSub) (ℓ : Loc) (t : Typₑ) (e : Expr) → LocalSub

-- Project a local substitution to a specific location
_σ⦊_ : LocalSub → Loc → ℕ → Expr
ε σ⦊ ℓ = idSubₑ
AddSub σ ℓ' t e σ⦊ ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = λ{ zero → e
               ; (suc n) → (σ σ⦊ ℓ) n }
... | no  _ = σ σ⦊ ℓ

renₗ-LocalSub : (ℕ → ℕ) → LocalSub → LocalSub
renₗ-LocalSub ξ ε = ε
renₗ-LocalSub ξ (AddSub σ ℓ t e) =
  AddSub (renₗ-LocalSub ξ σ) (renₗ-Loc ξ ℓ) t e

renLocalSub : LocalRen → LocalSub → LocalSub
renLocalSub ξ ε = ε
renLocalSub ξ (AddSub σ ℓ t e) =
  AddSub (renLocalSub ξ σ) ℓ t (renₑ (ξ ⦊ ℓ) e)

dropLocalSub : LocalSub → Loc → Typₑ → LocalSub
dropLocalSub σ ℓ t = renLocalSub (Drop Id ℓ t) σ

keepLocalSub : LocalSub → Loc → Typₑ → LocalSub
keepLocalSub σ ℓ t = AddSub (dropLocalSub σ ℓ t) ℓ t (varₑ zero)

idLocalSub : LocalCtx → LocalSub
idLocalSub [] = ε
idLocalSub ((ℓ , t) ∷ Δ) = keepLocalSub (idLocalSub Δ) ℓ t

-- Substitute local variables in a choreography
subₗₑ : (σ : LocalSub) (C : Chor) → Chor
subₗₑ σ (Done ℓ e) = Done ℓ (subₑ (σ σ⦊ ℓ) e)
subₗₑ σ (Var x) = Var x
subₗₑ σ (Send ℓ1 C ℓ2) = Send ℓ1 (subₗₑ σ C) ℓ2
subₗₑ σ (If ℓ C C1 C2) = If ℓ (subₗₑ σ C) (subₗₑ σ C1) (subₗₑ σ C2)
subₗₑ σ (Sync ℓ1 d ℓ2 C) = Sync ℓ1 d ℓ2 (subₗₑ σ C)
subₗₑ σ (DefLocal ℓ t C1 C2) = DefLocal ℓ t (subₗₑ σ C1) (subₗₑ (keepLocalSub σ ℓ t) C2)
subₗₑ σ (Fun τ C) = Fun τ (subₗₑ σ C)
subₗₑ σ (Fix τ C) = Fix τ (subₗₑ σ C)
subₗₑ σ (App C1 C2) = App (subₗₑ σ C1) (subₗₑ σ C2)
subₗₑ σ (LocAbs C) = LocAbs (subₗₑ (renₗ-LocalSub suc σ) C)
subₗₑ σ (LocApp C ℓ) = LocApp (subₗₑ σ C) ℓ
subₗₑ σ (TellLet ℓ ρ1 C1 ρ2 C2) =
  TellLet ℓ ρ1 (subₗₑ σ C1) ρ2 (subₗₑ (renₗ-LocalSub suc σ) C2)

data SUB : LocalSub → (Δ1 Δ2 : LocalCtx) → Set where
  -- IdSUB : ∀{Δ} → SUB Id Δ Δ
  εSUB : ∀{Δ} → SUB ε [] Δ
  AddSUB : ∀{Δ1 Δ2 σ e} → SUB σ Δ1 Δ2 → (ℓ : Loc) (t : Typₑ) →
           (Δ2∣ℓ⊢e∶t : (Δ2 ∣ ℓ) ⊢ₑ e ∶ t) →
           SUB (AddSub σ ℓ t e) ((ℓ , t) ∷ Δ1) Δ2

-- A well-formed local substitution changes contexts
SUB⦊⇒ : ∀{Δ1 Δ2 σ} → SUB σ Δ1 Δ2 → (ℓ : Loc) →
        (σ σ⦊ ℓ) ∶ Δ1 ∣ ℓ ⇒ₑ (Δ2 ∣ ℓ)
SUB⦊⇒ εSUB ℓ n t ()
SUB⦊⇒ (AddSUB σ ℓ' t' Δ2∣ℓ⊢e∶t) ℓ with ≡-dec-Loc ℓ ℓ'
... | yes refl = λ{ zero t refl → Δ2∣ℓ⊢e∶t
                 ; (suc n) → SUB⦊⇒ σ ℓ n }
... | no  _ = SUB⦊⇒ σ ℓ

-- Typing of local expressions is closed under well-formed local substitutions
tySUBₑ : ∀{Δ1 Δ2 e ℓ t σ} →
        SUB σ Δ1 Δ2 →
        (Δ1 ∣ ℓ) ⊢ₑ e ∶ t →
        (Δ2 ∣ ℓ) ⊢ₑ subₑ (σ σ⦊ ℓ) e ∶ t 
tySUBₑ {ℓ = ℓ} {t} {ξ} σ-SUB Δ1∣ℓ⊢e∶t = tySubₑ (SUB⦊⇒ σ-SUB ℓ) Δ1∣ℓ⊢e∶t

renₗ-SUB : ∀{Δ1 Δ2 σ ξ} →
           Injective _≡_ _≡_ ξ →
           SUB σ Δ1 Δ2 →
           SUB (renₗ-LocalSub ξ σ) (renₗ-LocalCtx ξ Δ1) (renₗ-LocalCtx ξ Δ2)
renₗ-SUB ξ-inj εSUB = εSUB
renₗ-SUB {ξ = ξ} ξ-inj (AddSUB {Δ1} {Δ2} {σ} {e} σSUB ℓ t Δ2∣ℓ⊢e∶t) =
  AddSUB (renₗ-SUB ξ-inj σSUB) (renₗ-Loc ξ ℓ) t (tyExtₑ (projInj Δ2 ℓ ξ-inj) Δ2∣ℓ⊢e∶t)

renLocalSUB : ∀{ξ σ Δ1 Δ2 Δ3} → OPE ξ Δ2 Δ3 → SUB σ Δ1 Δ2 → SUB (renLocalSub ξ σ) Δ1 Δ3
renLocalSUB ξ εSUB = εSUB
renLocalSUB ξ (AddSUB σ ℓ t Δ2∣ℓ⊢e∶t) =
  AddSUB (renLocalSUB ξ σ) ℓ t (tyWkOPEₑ ξ Δ2∣ℓ⊢e∶t)

dropLocalSUB : ∀{σ Δ1 Δ2} → SUB σ Δ1 Δ2 → (ℓ : Loc) (t : Typₑ) →
               SUB (dropLocalSub σ ℓ t) Δ1 ((ℓ , t) ∷ Δ2)
dropLocalSUB σ ℓ t = renLocalSUB (DropOPE IdOPE ℓ t) σ

tyProjZero : (Δ : LocalCtx) (ℓ : Loc) (t : Typₑ) →
              (((ℓ , t) ∷ Δ) ∣ ℓ) 0 ≡ just t
tyProjZero Δ ℓ t with ≡-dec-Loc ℓ ℓ
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

keepLocalSUB : ∀{σ Δ1 Δ2} → SUB σ Δ1 Δ2 → (ℓ : Loc) (t : Typₑ) →
               SUB (keepLocalSub σ ℓ t) ((ℓ , t) ∷ Δ1) ((ℓ , t) ∷ Δ2)
keepLocalSUB {Δ2 = Δ2} σ ℓ t =
  AddSUB (dropLocalSUB σ ℓ t) ℓ t (tyVarₑ (((ℓ , t) ∷ Δ2) ∣ ℓ) 0 t (tyProjZero Δ2 ℓ t))
