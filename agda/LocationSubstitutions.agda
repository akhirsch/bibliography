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
subₗ : (ℕ → Loc) → Chor → Chor
subₗ σ (Done ℓ e) = Done (subₗ-Loc σ ℓ) e
subₗ σ (Var x) = Var x
subₗ σ (Send ℓ1 c ℓ2) = Send (subₗ-Loc σ ℓ1) (subₗ σ c) (subₗ-Loc σ ℓ2)
subₗ σ (If ℓ c c1 c2) = If (subₗ-Loc σ ℓ) (subₗ σ c) (subₗ σ c1) (subₗ σ c2)
subₗ σ (Sync ℓ1 d ℓ2 c) = Sync (subₗ-Loc σ ℓ1) d (subₗ-Loc σ ℓ2) (subₗ σ c)
subₗ σ (DefLocal ℓ c1 c2) = DefLocal (subₗ-Loc σ ℓ) (subₗ σ c1) (subₗ σ c2)
subₗ σ (Fun τ c) = Fun (subₜ σ τ) (subₗ σ c)
subₗ σ (Fix τ c) = Fix (subₜ σ τ) (subₗ σ c)
subₗ σ (App c1 c2) = App (subₗ σ c1) (subₗ σ c2)
subₗ σ (LocAbs c) = LocAbs (subₗ (↑σₗ σ) c)
subₗ σ (LocApp c ℓ) = LocApp (subₗ σ c) (subₗ-Loc σ ℓ)
subₗ σ (TellLet ℓ ρ1 c1 ρ2 c2) =
  TellLet (subₗ-Loc σ ℓ) (subₗ-List σ ρ1) (subₗ σ c1)
    (subₗ-List σ ρ2) (subₗ (↑σₗ σ) c2)

-- Substitution respects extensional equality
subExtₗ : ∀{σ1 σ2} →
         σ1 ≈ σ2 →
         subₗ σ1 ≈ subₗ σ2
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

-- Substitution respects the identity
subIdₗ : ∀ c → subₗ idSubₗ c ≡ c
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
  c⟨↑id⟩≡c : subₗ (↑σₗ idSubₗ) c ≡ c
  c⟨↑id⟩≡c = 
    subₗ (↑σₗ idSubₗ) c ≡⟨ subExtₗ ↑σIdₗ c ⟩
    subₗ idSubₗ c       ≡⟨ subIdₗ c ⟩
    c                   ∎
subIdₗ (LocApp c ℓ) = cong₂ LocApp (subIdₗ c) (subIdₗ-Loc ℓ)
subIdₗ (TellLet ℓ ρ1 c1 ρ2 c2) =
  cong₅ TellLet (subIdₗ-Loc ℓ) (subIdₗ-List ρ1) (subIdₗ c1)
    (subIdₗ-List ρ2) c2⟨↑id⟩≡c2
  where
    c2⟨↑id⟩≡c2 : subₗ (↑σₗ idSubₗ) c2 ≡ c2
    c2⟨↑id⟩≡c2 = 
      subₗ (↑σₗ idSubₗ) c2 ≡⟨ subExtₗ ↑σIdₗ c2 ⟩
      subₗ idSubₗ c2       ≡⟨ subIdₗ c2 ⟩
      c2                   ∎

-- Substitution respects the inclusion
subιₗ : ∀ ξ → subₗ (ιₗ ξ) ≈ renₗ ξ
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
  c⟨↑ιξ⟩≡c⟨↑ξ⟩ : subₗ (↑σₗ (ιₗ ξ)) c ≡ renₗ (↑ ξ) c
  c⟨↑ιξ⟩≡c⟨↑ξ⟩ =
    subₗ (↑σₗ (ιₗ ξ)) c ≡⟨ subExtₗ (↑σιₗ ξ) c ⟩
    subₗ (ιₗ (↑ ξ)) c   ≡⟨ subιₗ (↑ ξ) c ⟩
    renₗ (↑ ξ) c        ∎
subιₗ ξ (LocApp c ℓ) = cong₂ LocApp (subιₗ ξ c) (subιₗ-Loc ξ ℓ)
subιₗ ξ (TellLet ℓ ρ1 c1 ρ2 c2) =
  cong₅ TellLet (subιₗ-Loc ξ ℓ) (subιₗ-List ξ ρ1) (subιₗ ξ c1)
    (subιₗ-List ξ ρ2) c2⟨↑ιξ⟩≡c2⟨↑ξ⟩ 
  where
    c2⟨↑ιξ⟩≡c2⟨↑ξ⟩ : subₗ (↑σₗ (ιₗ ξ)) c2 ≡ renₗ (↑ ξ) c2
    c2⟨↑ιξ⟩≡c2⟨↑ξ⟩ =
      subₗ (↑σₗ (ιₗ ξ)) c2 ≡⟨ subExtₗ (↑σιₗ ξ)  c2 ⟩
      subₗ (ιₗ (↑ ξ)) c2   ≡⟨ subιₗ (↑ ξ) c2 ⟩
      renₗ (↑ ξ) c2        ∎ 