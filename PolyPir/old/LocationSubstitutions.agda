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
  (E : TypedLocalLanguage L)
  where

open import Types L E
open import Choreographies L E
open import LocationRenamings L E
open import LocalContexts L E
open TypedLocalLanguage E
open Location L
open ≡-Reasoning

-- Substitute location variables in a choreography
subₗ : LocalCtx → (ℕ → Loc) → Chor → Chor
subₗ Δ σ (Done ℓ e) = Done (subₗ-Loc σ ℓ) (renₑ (locSubProj Δ σ ℓ) e)
subₗ Δ σ (Var x) = Var x
subₗ Δ σ (Send ℓ1 c ℓ2) = Send (subₗ-Loc σ ℓ1) (subₗ Δ σ c) (subₗ-Loc σ ℓ2)
subₗ Δ σ (If ℓ c c1 c2) = If (subₗ-Loc σ ℓ) (subₗ Δ σ c) (subₗ Δ σ c1) (subₗ Δ σ c2)
subₗ Δ σ (Sync ℓ1 d ℓ2 c) = Sync (subₗ-Loc σ ℓ1) d (subₗ-Loc σ ℓ2) (subₗ Δ σ c)
subₗ Δ σ (DefLocal ℓ t c1 c2) = DefLocal (subₗ-Loc σ ℓ) t (subₗ Δ σ c1) (subₗ ((ℓ , t) ∷ Δ) σ c2)
subₗ Δ σ (Fun τ c) = Fun (subₜ σ τ) (subₗ Δ σ c)
subₗ Δ σ (Fix τ c) = Fix (subₜ σ τ) (subₗ Δ σ c)
subₗ Δ σ (App c1 c2) = App (subₗ Δ σ c1) (subₗ Δ σ c2)
subₗ Δ σ (LocAbs c) = LocAbs (subₗ (renₗ-LocalCtx suc Δ) (↑σₗ σ) c)
subₗ Δ σ (LocApp c ℓ) = LocApp (subₗ Δ σ c) (subₗ-Loc σ ℓ)
subₗ Δ σ (TellLet ℓ ρ1 c1 ρ2 c2) =
  TellLet (subₗ-Loc σ ℓ) (subₗ-List σ ρ1) (subₗ Δ σ c1)
    (subₗ-List σ ρ2) (subₗ (renₗ-LocalCtx suc Δ) (↑σₗ σ) c2)

-- Substitution respects extensional equality
subExtₗ : ∀{Δ σ1 σ2} →
         σ1 ≈ σ2 →
         subₗ Δ σ1 ≈ subₗ Δ σ2
subExtₗ {Δ} σ1≈σ2 (Done ℓ e) =
  cong₂ Done (subExtₗ-Loc σ1≈σ2 ℓ) (renExtₑ (locSubProjExt Δ σ1≈σ2 ℓ) e)
subExtₗ σ1≈σ2 (Var x) = refl
subExtₗ σ1≈σ2 (Send ℓ1 c ℓ2) =
  cong₃ Send (subExtₗ-Loc σ1≈σ2 ℓ1) (subExtₗ σ1≈σ2 c) (subExtₗ-Loc σ1≈σ2 ℓ2)
subExtₗ σ1≈σ2 (If ℓ c c1 c2) =
  cong₄ If (subExtₗ-Loc σ1≈σ2 ℓ) (subExtₗ σ1≈σ2 c) (subExtₗ σ1≈σ2 c1) (subExtₗ σ1≈σ2 c2)
subExtₗ σ1≈σ2 (Sync ℓ1 d ℓ2 c) =
  cong₄ Sync (subExtₗ-Loc σ1≈σ2 ℓ1) refl (subExtₗ-Loc σ1≈σ2 ℓ2) (subExtₗ σ1≈σ2 c)
subExtₗ σ1≈σ2 (DefLocal ℓ t c1 c2) =
  cong₄ DefLocal (subExtₗ-Loc σ1≈σ2 ℓ) refl (subExtₗ σ1≈σ2 c1) (subExtₗ σ1≈σ2 c2)
subExtₗ σ1≈σ2 (Fun τ c) = cong₂ Fun (subExtₜ σ1≈σ2 τ) (subExtₗ σ1≈σ2 c)
subExtₗ σ1≈σ2 (Fix τ c) = cong₂ Fix (subExtₜ σ1≈σ2 τ) (subExtₗ σ1≈σ2 c)
subExtₗ σ1≈σ2 (App c1 c2) = cong₂ App (subExtₗ σ1≈σ2 c1) (subExtₗ σ1≈σ2 c2)
subExtₗ σ1≈σ2 (LocAbs c) = cong LocAbs (subExtₗ (↑σExtₗ σ1≈σ2) c)
subExtₗ σ1≈σ2 (LocApp c ℓ) = cong₂ LocApp (subExtₗ σ1≈σ2 c) (subExtₗ-Loc σ1≈σ2 ℓ)
subExtₗ σ1≈σ2 (TellLet ℓ ρ1 c1 ρ2 c2) =
  cong₅ TellLet (subExtₗ-Loc σ1≈σ2 ℓ) (subExtₗ-List σ1≈σ2 ρ1) (subExtₗ σ1≈σ2 c1)
  (subExtₗ-List σ1≈σ2 ρ2) (subExtₗ (↑σExtₗ σ1≈σ2) c2)

-- Substitution respects the identity
subIdₗ : ∀{Δ} c → subₗ Δ idSubₗ c ≡ c
subIdₗ {Δ} (Done ℓ e) = cong₂ Done (subIdₗ-Loc ℓ) e⟨Δ⇒σ⦊ℓ⟩≡e
  where
  e⟨Δ⇒σ⦊ℓ⟩≡e : renₑ (locSubProj Δ idSubₗ ℓ) e ≡ e
  e⟨Δ⇒σ⦊ℓ⟩≡e =
    renₑ (locSubProj Δ idSubₗ ℓ) e
      ≡⟨ renExtₑ (locSubProjId Δ ℓ) e ⟩
    renₑ idRenₑ e
      ≡⟨ renIdₑ e ⟩
    e ∎
subIdₗ (Var x) = refl
subIdₗ (Send ℓ1 c ℓ2) = cong₃ Send (subIdₗ-Loc ℓ1) (subIdₗ c) (subIdₗ-Loc ℓ2)
subIdₗ (If ℓ c c1 c2) = cong₄ If (subIdₗ-Loc ℓ) (subIdₗ c) (subIdₗ c1) (subIdₗ c2)
subIdₗ (Sync ℓ1 d ℓ2 c) = cong₄ Sync (subIdₗ-Loc ℓ1) refl (subIdₗ-Loc ℓ2) (subIdₗ c)
subIdₗ (DefLocal ℓ t c1 c2) = cong₄ DefLocal (subIdₗ-Loc ℓ) refl (subIdₗ c1) (subIdₗ c2)
subIdₗ (Fun τ c) = cong₂ Fun (subIdₜ τ) (subIdₗ c)
subIdₗ (Fix τ c) = cong₂ Fix (subIdₜ τ) (subIdₗ c)
subIdₗ (App c1 c2) = cong₂ App (subIdₗ c1) (subIdₗ c2)
subIdₗ {Δ} (LocAbs c) = cong LocAbs c⟨↑id⟩≡c
  where
  c⟨↑id⟩≡c : subₗ (renₗ-LocalCtx suc Δ) (↑σₗ idSubₗ) c ≡ c
  c⟨↑id⟩≡c =
    subₗ (renₗ-LocalCtx suc Δ) (↑σₗ idSubₗ) c
      ≡⟨ subExtₗ (λ{ zero → refl ; (suc n) → refl }) c ⟩
    subₗ (renₗ-LocalCtx suc Δ) idSubₗ c
      ≡⟨ subIdₗ c ⟩
    c ∎
subIdₗ (LocApp c ℓ) = cong₂ LocApp (subIdₗ c) (subIdₗ-Loc ℓ)
subIdₗ {Δ} (TellLet ℓ ρ1 c1 ρ2 c2) =
  cong₅ TellLet (subIdₗ-Loc ℓ) (subIdₗ-List ρ1) (subIdₗ c1) (subIdₗ-List ρ2) c2⟨↑id⟩≡c2
  where
  c2⟨↑id⟩≡c2 : subₗ (renₗ-LocalCtx suc Δ) (↑σₗ idSubₗ) c2 ≡ c2
  c2⟨↑id⟩≡c2 =
    subₗ (renₗ-LocalCtx suc Δ) (↑σₗ idSubₗ) c2
      ≡⟨ subExtₗ (λ{ zero → refl ; (suc n) → refl }) c2 ⟩
    subₗ (renₗ-LocalCtx suc Δ) idSubₗ c2
      ≡⟨ subIdₗ c2 ⟩
    c2 ∎

-- Substitution respects the inclusion
subιₗ : ∀{Δ} ξ → Injective _≡_ _≡_ ξ → subₗ Δ (ιₗ ξ) ≈ renₗ ξ
subιₗ {Δ} ξ ξ-inj (Done ℓ e) = cong₂ Done (subιₗ-Loc ξ ℓ) e⟨Δ⇒ξ⦊ℓ⟩≡e
  where
  e⟨Δ⇒ξ⦊ℓ⟩≡e : renₑ (locSubProj Δ (ιₗ ξ) ℓ) e ≡ e
  e⟨Δ⇒ξ⦊ℓ⟩≡e =
    renₑ (locSubProj Δ (ιₗ ξ) ℓ) e
      ≡⟨ renExtₑ (locSubProjι Δ ξ ℓ ξ-inj) e ⟩
    renₑ idRen e
      ≡⟨ renIdₑ e ⟩
    e ∎
subιₗ ξ ξ-inj (Var x) = refl
subιₗ ξ ξ-inj (Send ℓ1 c ℓ2) = cong₃ Send (subιₗ-Loc ξ ℓ1) (subιₗ ξ ξ-inj c) (subιₗ-Loc ξ ℓ2)
subιₗ ξ ξ-inj (If ℓ c c1 c2) = cong₄ If (subιₗ-Loc ξ ℓ) (subιₗ ξ ξ-inj c) (subιₗ ξ ξ-inj c1) (subιₗ ξ ξ-inj c2)
subιₗ ξ ξ-inj (Sync ℓ1 d ℓ2 c) = cong₄ Sync (subιₗ-Loc ξ ℓ1) refl (subιₗ-Loc ξ ℓ2) (subιₗ ξ ξ-inj c)
subιₗ ξ ξ-inj (DefLocal ℓ t c1 c2) = cong₄ DefLocal (subιₗ-Loc ξ ℓ) refl (subιₗ ξ ξ-inj c1) (subιₗ ξ ξ-inj c2)
subιₗ ξ ξ-inj (Fun τ c) = cong₂ Fun (subιₜ ξ τ) (subιₗ ξ ξ-inj c)
subιₗ ξ ξ-inj (Fix τ c) = cong₂ Fix (subιₜ ξ τ) (subιₗ ξ ξ-inj c)
subιₗ ξ ξ-inj (App c1 c2) = cong₂ App (subιₗ ξ ξ-inj c1) (subιₗ ξ ξ-inj c2)
subιₗ {Δ} ξ ξ-inj (LocAbs c) = cong LocAbs c⟨↑ιξ⟩≡c⟨↑ξ⟩
  where
  c⟨↑ιξ⟩≡c⟨↑ξ⟩ : subₗ (renₗ-LocalCtx suc Δ) (↑σₗ (ιₗ ξ)) c ≡ renₗ (↑ ξ) c
  c⟨↑ιξ⟩≡c⟨↑ξ⟩ =
    subₗ (renₗ-LocalCtx suc Δ) (↑σₗ (ιₗ ξ)) c
      ≡⟨ subExtₗ (↑σιₗ ξ) c ⟩
    subₗ (renₗ-LocalCtx suc Δ) (ιₗ (↑ ξ)) c
      ≡⟨ subιₗ (↑ ξ) (↑-pres-inj ξ-inj) c ⟩
    renₗ (↑ ξ) c        ∎
subιₗ ξ ξ-inj (LocApp c ℓ) = cong₂ LocApp (subιₗ ξ ξ-inj c) (subιₗ-Loc ξ ℓ)
subιₗ {Δ} ξ ξ-inj (TellLet ℓ ρ1 c1 ρ2 c2) =
  cong₅ TellLet (subιₗ-Loc ξ ℓ) (subιₗ-List ξ ρ1) (subιₗ ξ ξ-inj c1)
    (subιₗ-List ξ ρ2) c2⟨↑ιξ⟩≡c2⟨↑ξ⟩ 
  where
    c2⟨↑ιξ⟩≡c2⟨↑ξ⟩ : subₗ (renₗ-LocalCtx suc Δ) (↑σₗ (ιₗ ξ)) c2 ≡ renₗ (↑ ξ) c2
    c2⟨↑ιξ⟩≡c2⟨↑ξ⟩ =
      subₗ (renₗ-LocalCtx suc Δ) (↑σₗ (ιₗ ξ)) c2 ≡⟨ subExtₗ (↑σιₗ ξ)  c2 ⟩
      subₗ (renₗ-LocalCtx suc Δ) (ιₗ (↑ ξ)) c2   ≡⟨ subιₗ (↑ ξ) (↑-pres-inj ξ-inj) c2 ⟩
      renₗ (↑ ξ) c2        ∎
