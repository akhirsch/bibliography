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

module LocationSubstitutions
  (L : Location)
  (E : Language L)
  (LE : LawfulLanguage L E)
  (TE : TypedLocalLanguage L E LE)
  where

open import Types L E LE TE
open import Choreographies L E LE TE
open import LocationRenamings L E LE TE
open Language E
open LawfulLanguage LE
open Location L
open ≡-Reasoning

-- Substitute location variables in a choreography
subₗ : (c : Chor) (σ : ℕ → Loc) → Chor
subₗ (Done ℓ e) σ = Done (subₗ-Loc ℓ σ) e
subₗ (Var x) σ = Var x
subₗ (Send ℓ1 c ℓ2) σ = Send (subₗ-Loc ℓ1 σ) (subₗ c σ) (subₗ-Loc ℓ2 σ)
subₗ (If ℓ c c1 c2) σ = If (subₗ-Loc ℓ σ) (subₗ c σ) (subₗ c1 σ) (subₗ c2 σ)
subₗ (Sync ℓ1 d ℓ2 c) σ = Sync (subₗ-Loc ℓ1 σ) d (subₗ-Loc ℓ2 σ) (subₗ c σ)
subₗ (DefLocal ℓ c1 c2) σ = DefLocal (subₗ-Loc ℓ σ) (subₗ c1 σ) (subₗ c2 σ)
subₗ (Fun τ c) σ = Fun (subₜ τ σ) (subₗ c σ)
subₗ (Fix τ c) σ = Fix (subₜ τ σ) (subₗ c σ)
subₗ (App c1 c2) σ = App (subₗ c1 σ) (subₗ c2 σ)
subₗ (LocAbs c) σ = LocAbs (subₗ c (↑σₗ σ))
subₗ (LocApp c ℓ) σ = LocApp (subₗ c σ) (subₗ-Loc ℓ σ)
subₗ (TellLet ℓ ρ1 c1 ρ2 c2) σ =
  TellLet (subₗ-Loc ℓ σ) (subₗ-List ρ1 σ) (subₗ c1 σ)
    (subₗ-List ρ2 σ) (subₗ c2 (↑σₗ σ))

-- Substituting location variables respects extensional equality
subExtₗ : ∀{σ1 σ2} →
         σ1 ≈ σ2 →
         ∀ c → subₗ c σ1 ≡ subₗ c σ2
subExtₗ σ1≈σ2 (Done ℓ e) = cong₂ Done (subExtₗ-Loc σ1≈σ2 ℓ) refl
subExtₗ σ1≈σ2 (Var x) = refl
subExtₗ σ1≈σ2 (Send ℓ1 c ℓ2) = cong₃ Send (subExtₗ-Loc σ1≈σ2 ℓ1) (subExtₗ σ1≈σ2 c) (subExtₗ-Loc σ1≈σ2 ℓ2)
subExtₗ σ1≈σ2 (If ℓ c c1 c2) = cong₄ If (subExtₗ-Loc σ1≈σ2 ℓ) (subExtₗ σ1≈σ2 c) (subExtₗ σ1≈σ2 c1) (subExtₗ σ1≈σ2 c2)
subExtₗ σ1≈σ2 (Sync ℓ1 d ℓ2 c) = cong₄ Sync (subExtₗ-Loc σ1≈σ2 ℓ1) refl (subExtₗ-Loc σ1≈σ2 ℓ2) (subExtₗ σ1≈σ2 c)
subExtₗ σ1≈σ2 (DefLocal ℓ c1 c2) = cong₃ DefLocal (subExtₗ-Loc σ1≈σ2 ℓ) (subExtₗ σ1≈σ2 c1) (subExtₗ σ1≈σ2 c2)
subExtₗ σ1≈σ2 (Fun τ c) = cong₂ Fun (subExtₜ σ1≈σ2 τ) (subExtₗ σ1≈σ2 c)
subExtₗ σ1≈σ2 (Fix τ c) = cong₂ Fix (subExtₜ σ1≈σ2 τ) (subExtₗ σ1≈σ2 c)
subExtₗ σ1≈σ2 (App c1 c2) = cong₂ App (subExtₗ σ1≈σ2 c1) (subExtₗ σ1≈σ2 c2)
subExtₗ σ1≈σ2 (LocAbs c) = cong LocAbs (subExtₗ (↑σExtₗ σ1≈σ2) c)
subExtₗ σ1≈σ2 (LocApp c ℓ) = cong₂ LocApp (subExtₗ σ1≈σ2 c) (subExtₗ-Loc σ1≈σ2 ℓ)
subExtₗ σ1≈σ2 (TellLet ℓ ρ1 c1 ρ2 c2) =
  cong₅ TellLet (subExtₗ-Loc σ1≈σ2 ℓ) (subExtₗ-List σ1≈σ2 ρ1) (subExtₗ σ1≈σ2 c1)
  (subExtₗ-List σ1≈σ2 ρ2) (subExtₗ (↑σExtₗ σ1≈σ2) c2)

-- Substituting location variables respects the identity
subIdₗ : ∀ c → subₗ c idSubₗ ≡ c
subIdₗ (Done ℓ e) = cong₂ Done (subIdₗ-Loc ℓ) refl
subIdₗ (Var x) = refl
subIdₗ (Send ℓ1 c ℓ2) = cong₃ Send (subIdₗ-Loc ℓ1) (subIdₗ c) (subIdₗ-Loc ℓ2)
subIdₗ (If ℓ c c1 c2) = cong₄ If (subIdₗ-Loc ℓ) (subIdₗ c) (subIdₗ c1) (subIdₗ c2)
subIdₗ (Sync ℓ1 d ℓ2 c) = cong₄ Sync (subIdₗ-Loc ℓ1) refl (subIdₗ-Loc ℓ2) (subIdₗ c)
subIdₗ (DefLocal ℓ c1 c2) = cong₃ DefLocal (subIdₗ-Loc ℓ) (subIdₗ c1) (subIdₗ c2)
subIdₗ (Fun τ c) = cong₂ Fun (subIdₜ τ) (subIdₗ c)
subIdₗ (Fix τ c) = cong₂ Fix (subIdₜ τ) (subIdₗ c)
subIdₗ (App c1 c2) = cong₂ App (subIdₗ c1) (subIdₗ c2)
subIdₗ (LocAbs c) = cong LocAbs c⟨↑id⟩≡c
  where
  c⟨↑id⟩≡c : subₗ c (↑σₗ idSubₗ) ≡ c
  c⟨↑id⟩≡c = 
    subₗ c (↑σₗ idSubₗ) ≡⟨ subExtₗ ↑σIdₗ c ⟩
    subₗ c idSubₗ       ≡⟨ subIdₗ c ⟩
    c                 ∎
subIdₗ (LocApp c ℓ) = cong₂ LocApp (subIdₗ c) (subIdₗ-Loc ℓ)
subIdₗ (TellLet ℓ ρ1 c1 ρ2 c2) =
  cong₅ TellLet (subIdₗ-Loc ℓ) (subIdₗ-List ρ1) (subIdₗ c1)
    (subIdₗ-List ρ2) c2⟨↑id⟩≡c2
  where
    c2⟨↑id⟩≡c2 : subₗ c2 (↑σₗ idSubₗ) ≡ c2
    c2⟨↑id⟩≡c2 = 
      subₗ c2 (↑σₗ idSubₗ) ≡⟨ subExtₗ ↑σIdₗ c2 ⟩
      subₗ c2 idSubₗ       ≡⟨ subIdₗ c2 ⟩
      c2                   ∎

-- Substitution along an inclusion is the same as a renaming
subιₗ : ∀ ξ c → subₗ c (ιₗ ξ) ≡ renₗ c ξ
subιₗ ξ (Done ℓ e) = cong₂ Done (subιₗ-Loc ξ ℓ) refl
subιₗ ξ (Var x) = refl
subιₗ ξ (Send ℓ1 c ℓ2) = cong₃ Send (subιₗ-Loc ξ ℓ1) (subιₗ ξ c) (subιₗ-Loc ξ ℓ2)
subιₗ ξ (If ℓ c c1 c2) = cong₄ If (subιₗ-Loc ξ ℓ) (subιₗ ξ c) (subιₗ ξ c1) (subιₗ ξ c2)
subιₗ ξ (Sync ℓ1 d ℓ2 c) = cong₄ Sync (subιₗ-Loc ξ ℓ1) refl (subιₗ-Loc ξ ℓ2) (subιₗ ξ c)
subιₗ ξ (DefLocal ℓ c1 c2) = cong₃ DefLocal (subιₗ-Loc ξ ℓ) (subιₗ ξ c1) (subιₗ ξ c2)
subιₗ ξ (Fun τ c) = cong₂ Fun (subιₜ ξ τ) (subιₗ ξ c)
subιₗ ξ (Fix τ c) = cong₂ Fix (subιₜ ξ τ) (subιₗ ξ c)
subιₗ ξ (App c1 c2) = cong₂ App (subιₗ ξ c1) (subιₗ ξ c2)
subιₗ ξ (LocAbs c) = cong LocAbs c⟨↑ιξ⟩≡c⟨↑ξ⟩
  where
  c⟨↑ιξ⟩≡c⟨↑ξ⟩ : subₗ c (↑σₗ (ιₗ ξ)) ≡ renₗ c (↑ ξ)
  c⟨↑ιξ⟩≡c⟨↑ξ⟩ =
    subₗ c (↑σₗ (ιₗ ξ)) ≡⟨ subExtₗ (↑σιₗ ξ)  c ⟩
    subₗ c (ιₗ (↑ ξ))  ≡⟨ subιₗ (↑ ξ) c ⟩
    renₗ c (↑ ξ)       ∎
subιₗ ξ (LocApp c ℓ) = cong₂ LocApp (subιₗ ξ c) (subιₗ-Loc ξ ℓ)
subιₗ ξ (TellLet ℓ ρ1 c1 ρ2 c2) =
  cong₅ TellLet (subιₗ-Loc ξ ℓ) (subιₗ-List ξ ρ1) (subιₗ ξ c1)
    (subιₗ-List ξ ρ2) c2⟨↑ιξ⟩≡c2⟨↑ξ⟩ 
  where
    c2⟨↑ιξ⟩≡c2⟨↑ξ⟩ : subₗ c2 (↑σₗ (ιₗ ξ)) ≡ renₗ c2 (↑ ξ)
    c2⟨↑ιξ⟩≡c2⟨↑ξ⟩ =
      subₗ c2 (↑σₗ (ιₗ ξ)) ≡⟨ subExtₗ (↑σιₗ ξ)  c2 ⟩
      subₗ c2 (ιₗ (↑ ξ))  ≡⟨ subιₗ (↑ ξ) c2 ⟩
      renₗ c2 (↑ ξ)       ∎