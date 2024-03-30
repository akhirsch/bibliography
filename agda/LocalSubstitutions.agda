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
open Language E
open LawfulLanguage LE
open Location L
open ≡-Reasoning

-- Substitute local variables in a choreography
subₗₑ : (c : Chor) (σ : ℕ → Expr) → Chor
subₗₑ (Done ℓ e) σ = Done ℓ (subₑ σ e)
subₗₑ (Var x) σ = Var x
subₗₑ (Send ℓ1 c ℓ2) σ = Send ℓ1 (subₗₑ c σ) ℓ2
subₗₑ (If ℓ c c1 c2) σ = If ℓ (subₗₑ c σ) (subₗₑ c1 σ) (subₗₑ c2 σ)
subₗₑ (Sync ℓ1 d ℓ2 c) σ = Sync ℓ1 d ℓ2 (subₗₑ c σ)
subₗₑ (DefLocal ℓ c1 c2) σ = DefLocal ℓ (subₗₑ c1 σ) (subₗₑ c2 (↑σₑ σ))
subₗₑ (Fun τ c) σ = Fun τ (subₗₑ c σ)
subₗₑ (Fix τ c) σ = Fix τ (subₗₑ c σ)
subₗₑ (App c1 c2) σ = App (subₗₑ c1 σ) (subₗₑ c2 σ)
subₗₑ (LocAbs c) σ = LocAbs (subₗₑ c σ)
subₗₑ (LocApp c ℓ) σ = LocApp (subₗₑ c σ) ℓ
subₗₑ (TellLet ℓ ρ1 c1 ρ2 c2) σ = TellLet ℓ ρ1 (subₗₑ c1 σ) ρ2 (subₗₑ c2 σ)

-- Substituting local variables respects extensional equality
subExtₗₑ : ∀{σ1 σ2} →
          σ1 ≈ σ2 →
          ∀ c → subₗₑ c σ1 ≡ subₗₑ c σ2
subExtₗₑ σ1≈σ2 (Done ℓ e) = cong₂ Done refl (subExtₑ σ1≈σ2 e)
subExtₗₑ σ1≈σ2 (Var x) = refl
subExtₗₑ σ1≈σ2 (Send ℓ1 c ℓ2) = cong₃ Send refl (subExtₗₑ σ1≈σ2 c) refl
subExtₗₑ σ1≈σ2 (If ℓ c c₁ c₂) =
  cong₄ If refl (subExtₗₑ σ1≈σ2 c) (subExtₗₑ σ1≈σ2 c₁) (subExtₗₑ σ1≈σ2 c₂)
subExtₗₑ σ1≈σ2 (Sync ℓ1 d ℓ2 c) = cong₄ Sync refl refl refl (subExtₗₑ σ1≈σ2 c)
subExtₗₑ σ1≈σ2 (DefLocal ℓ c1 c2) =
  cong₃ DefLocal refl (subExtₗₑ σ1≈σ2 c1) (subExtₗₑ (↑σExt σ1≈σ2) c2)
subExtₗₑ σ1≈σ2 (Fun τ c) = cong₂ Fun refl (subExtₗₑ σ1≈σ2 c)
subExtₗₑ σ1≈σ2 (Fix τ c) = cong₂ Fix refl (subExtₗₑ σ1≈σ2 c)
subExtₗₑ σ1≈σ2 (App c1 c2) = cong₂ App (subExtₗₑ σ1≈σ2 c1) (subExtₗₑ σ1≈σ2 c2)
subExtₗₑ σ1≈σ2 (LocAbs c) = cong LocAbs (subExtₗₑ σ1≈σ2 c)
subExtₗₑ σ1≈σ2 (LocApp c ℓ) = cong₂ LocApp (subExtₗₑ σ1≈σ2 c) refl
subExtₗₑ σ1≈σ2 (TellLet ℓ ρ1 c1 ρ2 c2) =
  cong₅ TellLet refl refl (subExtₗₑ σ1≈σ2 c1) refl (subExtₗₑ σ1≈σ2 c2)

-- Substituting local variables respects the identity
subIdₗₑ : ∀ c → subₗₑ c idSubₑ ≡ c
subIdₗₑ (Done ℓ e) = cong₂ Done refl (subIdₑ e)
subIdₗₑ (Var x) = refl
subIdₗₑ (Send ℓ1 c ℓ2) = cong₃ Send refl (subIdₗₑ c) refl
subIdₗₑ (If ℓ c c₁ c₂) = cong₄ If refl (subIdₗₑ c) (subIdₗₑ c₁) (subIdₗₑ c₂)
subIdₗₑ (Sync ℓ1 d ℓ2 c) = cong₄ Sync refl refl refl (subIdₗₑ c)
subIdₗₑ (DefLocal ℓ c1 c2) = cong₃ DefLocal refl (subIdₗₑ c1) (subExtₗₑ ↑σIdₑ c2 ∙ subIdₗₑ c2)
subIdₗₑ (Fun τ c) = cong₂ Fun refl (subIdₗₑ c)
subIdₗₑ (Fix τ c) = cong₂ Fix refl (subIdₗₑ c)
subIdₗₑ (App c1 c2) = cong₂ App (subIdₗₑ c1) (subIdₗₑ c2)
subIdₗₑ (LocAbs c) = cong LocAbs (subIdₗₑ c)
subIdₗₑ (LocApp c ℓ) = cong₂ LocApp (subIdₗₑ c) refl
subIdₗₑ (TellLet ℓ ρ1 c1 ρ2 c2) = cong₅ TellLet refl refl (subIdₗₑ c1) refl (subIdₗₑ c2)

-- Substitution respects the inclusion
subιₗₑ : ∀ ξ c → subₗₑ c (ιₑ ξ) ≡ renₗₑ c ξ
subιₗₑ ξ (Done ℓ e) = cong₂ Done refl (subRenₑ ξ e)
subιₗₑ ξ (Var x) = refl
subιₗₑ ξ (Send ℓ1 c ℓ2) = cong₃ Send refl (subιₗₑ ξ c) refl
subιₗₑ ξ (If ℓ c c₁ c₂) = cong₄ If refl (subιₗₑ ξ c) (subιₗₑ ξ c₁) (subιₗₑ ξ c₂)
subιₗₑ ξ (Sync ℓ1 d ℓ2 c) = cong₄ Sync refl refl refl (subιₗₑ ξ c)
subιₗₑ ξ (DefLocal ℓ c1 c2) = cong₃ DefLocal refl (subιₗₑ ξ c1) (subExtₗₑ (↑σιₑ ξ) c2 ∙ subιₗₑ (↑ ξ) c2)
subιₗₑ ξ (Fun τ c) = cong₂ Fun refl (subιₗₑ ξ c)
subιₗₑ ξ (Fix τ c) = cong₂ Fix refl (subιₗₑ ξ c)
subιₗₑ ξ (App c1 c2) = cong₂ App (subιₗₑ ξ c1) (subιₗₑ ξ c2)
subιₗₑ ξ (LocAbs c) = cong LocAbs (subιₗₑ ξ c)
subιₗₑ ξ (LocApp c ℓ) = cong₂ LocApp (subιₗₑ ξ c) refl
subιₗₑ ξ (TellLet ℓ ρ1 c1 ρ2 c2) =
  cong₅ TellLet refl refl (subιₗₑ ξ c1) refl (subιₗₑ ξ c2)
