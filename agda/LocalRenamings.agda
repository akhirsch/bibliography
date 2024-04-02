{-# OPTIONS --safe #-}

open import Level using (Lift; lift)
open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Maybe
open import Data.Nat renaming (_≟_ to ≡-dec-Nat) 
open import Data.Nat.Properties
open import Data.List hiding (map)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function

open import Common
open import LocalLang
open import TypedLocalLang
open import Locations

module LocalRenamings
  (L : Location)
  (E : Language L)
  (LE : LawfulLanguage L E)
  (TE : TypedLocalLanguage L E LE)
  where

open import Types L E LE TE
open import Choreographies L E LE TE
open import LocalContexts L E LE TE
open import LocationRenamings L E LE TE
open import Renamings L E LE TE
open import LocationContexts L E LE TE
open Location L
open Language E
open LawfulLanguage LE
open TypedLocalLanguage TE


data LocalRen : Set where
  Id : LocalRen
  Keep : LocalRen → Loc → Typₑ → LocalRen
  Drop : LocalRen → Loc → Typₑ → LocalRen

-- Project a local renaming to a specific location
_⦊_ : LocalRen → Loc → ℕ → ℕ
Id ⦊ ℓ = λ n → n
Keep ξ ℓ' t ⦊ ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = ↑ (ξ ⦊ ℓ)
... | no  _ = ξ ⦊ ℓ
Drop ξ ℓ' t ⦊ ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = suc ∘ ξ ⦊ ℓ
... | no  _ = ξ ⦊ ℓ

renₗ-LocalRen : (ℕ → ℕ) → LocalRen → LocalRen
renₗ-LocalRen ξ1 Id = Id
renₗ-LocalRen ξ1 (Keep ξ2 ℓ t) = Keep (renₗ-LocalRen ξ1 ξ2) (renₗ-Loc ξ1 ℓ) t
renₗ-LocalRen ξ1 (Drop ξ2 ℓ t) = Drop (renₗ-LocalRen ξ1 ξ2) (renₗ-Loc ξ1 ℓ) t

-- Rename local variables in a choreography
renₗₑ : LocalRen → Chor → Chor
renₗₑ ξ (Done ℓ e) = Done ℓ (renₑ (ξ ⦊ ℓ) e)
renₗₑ ξ (Var x) = Var x
renₗₑ ξ (Send ℓ1 C ℓ2) = Send ℓ1 (renₗₑ ξ C) ℓ2
renₗₑ ξ (If ℓ C C1 C2) = If ℓ (renₗₑ ξ C) (renₗₑ ξ C1) (renₗₑ ξ C2)
renₗₑ ξ (Sync ℓ1 d ℓ2 C) = Sync ℓ1 d ℓ2 (renₗₑ ξ C)
renₗₑ ξ (DefLocal ℓ t C1 C2) = DefLocal ℓ t (renₗₑ ξ C1) (renₗₑ (Keep ξ ℓ t) C2)
renₗₑ ξ (Fun τ C) = Fun τ (renₗₑ ξ C)
renₗₑ ξ (Fix τ C) = Fix τ (renₗₑ ξ C)
renₗₑ ξ (App C1 C2) = App (renₗₑ ξ C1) (renₗₑ ξ C2)
renₗₑ ξ (LocAbs C) = LocAbs (renₗₑ (renₗ-LocalRen suc ξ) C)
renₗₑ ξ (LocApp C ℓ) = LocApp (renₗₑ ξ C) ℓ
renₗₑ ξ (TellLet ℓ ρ1 C1 ρ2 C2) = TellLet ℓ ρ1 (renₗₑ ξ C1) ρ2  (renₗₑ (renₗ-LocalRen suc ξ) C2)

-- Order preserving embeddings between local contexts
data OPE : LocalRen → (Δ1 Δ2 : LocalCtx) → Set where
  IdOPE : ∀{Δ} → OPE Id Δ Δ
  KeepOPE : ∀{ξ Δ1 Δ2} → OPE ξ Δ1 Δ2 → (ℓ : Loc) (t : Typₑ) → OPE (Keep ξ ℓ t) ((ℓ , t) ∷ Δ1) ((ℓ , t) ∷ Δ2)
  DropOPE : ∀{ξ Δ1 Δ2} → OPE ξ Δ1 Δ2 → (ℓ : Loc) (t : Typₑ) → OPE (Drop ξ ℓ t) Δ1 ((ℓ , t) ∷ Δ2)

renₗ-OPE : ∀{Δ1 Δ2 ξ2} (ξ1 : ℕ → ℕ) → OPE ξ2 Δ1 Δ2 →
           OPE (renₗ-LocalRen ξ1 ξ2) (renₗ-LocalCtx ξ1 Δ1) (renₗ-LocalCtx ξ1 Δ2)
renₗ-OPE ξ1 IdOPE = IdOPE
renₗ-OPE ξ1 (KeepOPE ξ2 ℓ t) = KeepOPE (renₗ-OPE ξ1 ξ2) (renₗ-Loc ξ1 ℓ) t
renₗ-OPE ξ1 (DropOPE ξ2 ℓ t) = DropOPE (renₗ-OPE ξ1 ξ2) (renₗ-Loc ξ1 ℓ) t

OPE⦊⇒ : ∀{Δ1 Δ2 ξ} → OPE ξ Δ1 Δ2 → (ℓ : Loc) →
     (Δ1 ∣ ℓ) ≈ (Δ2 ∣ ℓ) ∘ (ξ ⦊ ℓ)
OPE⦊⇒ IdOPE ℓ n = refl
OPE⦊⇒ (KeepOPE ξ-OPE ℓ' t) ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = λ{ zero → refl
               ; (suc n) → OPE⦊⇒ ξ-OPE ℓ n }
... | no _ = OPE⦊⇒ ξ-OPE ℓ
OPE⦊⇒ (DropOPE ξ-OPE ℓ' t) ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = OPE⦊⇒ ξ-OPE ℓ
... | no _ = OPE⦊⇒ ξ-OPE ℓ

-- Typing of local expressions is closed under projected OPEs
tyWkOPEₑ : ∀{Δ1 Δ2 e ℓ t ξ} →
           OPE ξ Δ1 Δ2 →
           (Δ1 ∣ ℓ) ⊢ₑ e ∶ t →
           (Δ2 ∣ ℓ) ⊢ₑ renₑ (ξ ⦊ ℓ) e ∶ t 
tyWkOPEₑ {ℓ = ℓ} {t} {ξ} ξ-OPE Δ1∣ℓ⊢e∶t = tyWkₑ (ξ ⦊ ℓ) (OPE⦊⇒ ξ-OPE ℓ) Δ1∣ℓ⊢e∶t