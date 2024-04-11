{-# OPTIONS --safe #-}

open import Data.Nat renaming (_≟_ to ≡-dec-ℕ)
open import Data.Bool renaming (_≟_ to ≡-dec-Bool)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Function

open import Common
open import LocalLang
open import TypedLocalLang
open import Locations

module Renamings
  (L : Location)
  (E : TypedLocalLanguage L)
  where

open import Types L E
open import Choreographies L E
open TypedLocalLanguage E

-- Renaming global variables
ren : (ℕ → ℕ) → Chor → Chor
ren ξ (Done ℓ e) = Done ℓ e
ren ξ (Var x) = Var (ξ x)
ren ξ (Send ℓ1 c ℓ2) = Send ℓ1 (ren ξ c) ℓ2
ren ξ (If ℓ c c₁ c₂) = If ℓ (ren ξ c) (ren ξ c₁) (ren ξ c₂)
ren ξ (Sync ℓ1 d ℓ2 c) = Sync ℓ1 d ℓ2 (ren ξ c)
ren ξ (DefLocal ℓ t c c₁) = DefLocal ℓ t (ren ξ c) (ren ξ c₁)
ren ξ (Fun τ c) = Fun τ (ren (↑ ξ) c)
ren ξ (Fix τ c) = Fix τ (ren (↑ ξ) c)
ren ξ (App c c₁) = App (ren ξ c) (ren ξ c₁)
ren ξ (LocAbs c) = LocAbs (ren ξ c)
ren ξ (LocApp c ℓ) = LocApp (ren ξ c) ℓ
ren ξ (TellLet ℓ ρ1 c ρ2 c₁) = TellLet ℓ ρ1 (ren ξ c) ρ2 (ren ξ c₁)

-- Renaming global variables respects extensional equality
renExt : ∀{ξ1 ξ2} →
         ξ1 ≈ ξ2 →
         ∀ c → ren ξ1 c ≡ ren ξ2 c
renExt ξ1≈ξ2 (Done ℓ e) = refl
renExt ξ1≈ξ2 (Var x) = cong Var (ξ1≈ξ2 x)
renExt ξ1≈ξ2 (Send ℓ1 c ℓ2) = cong₃ Send refl (renExt ξ1≈ξ2 c) refl
renExt ξ1≈ξ2 (If ℓ c c₁ c₂) = cong₄ If refl (renExt ξ1≈ξ2 c) (renExt ξ1≈ξ2 c₁) (renExt ξ1≈ξ2 c₂)
renExt ξ1≈ξ2 (Sync ℓ1 d ℓ2 c) = cong₄ Sync refl refl refl (renExt ξ1≈ξ2 c)
renExt ξ1≈ξ2 (DefLocal ℓ t c c₁) = cong₄ DefLocal refl refl (renExt ξ1≈ξ2 c) (renExt ξ1≈ξ2 c₁)
renExt ξ1≈ξ2 (Fun τ c) = cong₂ Fun refl (renExt (↑Ext ξ1≈ξ2) c)
renExt ξ1≈ξ2 (Fix τ c) = cong₂ Fix refl (renExt (↑Ext ξ1≈ξ2) c)
renExt ξ1≈ξ2 (App c c₁) = cong₂ App (renExt ξ1≈ξ2 c) (renExt ξ1≈ξ2 c₁)
renExt ξ1≈ξ2 (LocAbs c) = cong LocAbs (renExt ξ1≈ξ2 c)
renExt ξ1≈ξ2 (LocApp c ℓ) = cong₂ LocApp (renExt ξ1≈ξ2 c) refl
renExt ξ1≈ξ2 (TellLet ℓ ρ1 c ρ2 c₁) = cong₅ TellLet refl refl (renExt ξ1≈ξ2 c) refl (renExt ξ1≈ξ2 c₁)

-- Renaming global variables respects the identity
renId : ∀ c → ren idRen c ≡ c
renId (Done ℓ e) = refl
renId (Var x) = refl
renId (Send ℓ1 c ℓ2) = cong₃ Send refl (renId c) refl
renId (If ℓ c c₁ c₂) = cong₄ If refl (renId c) (renId c₁) (renId c₂)
renId (Sync ℓ1 d ℓ2 c) = cong₄ Sync refl refl refl (renId c)
renId (DefLocal ℓ t c c₁) = cong₄ DefLocal refl refl (renId c) (renId c₁)
renId (Fun τ c) = cong₂ Fun refl c⟨↑id⟩≡c
  where
  c⟨↑id⟩≡c : ren (↑ idRen) c ≡ c
  c⟨↑id⟩≡c = 
    ren (↑ idRen) c ≡⟨ renExt ↑Id c ⟩
    ren idRen c        ≡⟨ renId c ⟩
    c                     ∎
renId (Fix τ c) = cong₂ Fix refl c⟨↑id⟩≡c
  where
  c⟨↑id⟩≡c : ren (↑ idRen) c ≡ c
  c⟨↑id⟩≡c = 
    ren (↑ idRen) c ≡⟨ renExt ↑Id c ⟩
    ren idRen c        ≡⟨ renId c ⟩
    c                     ∎
renId (App c c₁) = cong₂ App (renId c) (renId c₁)
renId (LocAbs c) = cong LocAbs (renId c)
renId (LocApp c ℓ) = cong₂ LocApp (renId c) refl
renId (TellLet ℓ ρ1 c ρ2 c₁) = cong₅ TellLet refl refl (renId c) refl (renId c₁)

-- Renaming global variables enjoys fusion
renFuse : ∀ ξ1 ξ2 → ren (ξ1 ∘ ξ2) ≈ ren ξ1 ∘ ren ξ2
renFuse ξ1 ξ2 (Done ℓ e) = refl
renFuse ξ1 ξ2 (Var x) = cong Var refl
renFuse ξ1 ξ2 (Send ℓ1 c ℓ2) = cong₃ Send refl (renFuse ξ1 ξ2 c) refl
renFuse ξ1 ξ2 (If ℓ c c₁ c₂) = cong₄ If refl (renFuse ξ1 ξ2 c) (renFuse ξ1 ξ2 c₁) (renFuse ξ1 ξ2 c₂)
renFuse ξ1 ξ2 (Sync ℓ1 d ℓ2 c) = cong₄ Sync refl refl refl (renFuse ξ1 ξ2 c)
renFuse ξ1 ξ2 (DefLocal ℓ t c c₁) = cong₄ DefLocal refl refl (renFuse ξ1 ξ2 c) (renFuse ξ1 ξ2 c₁)
renFuse ξ1 ξ2 (Fun τ c) = cong₂ Fun refl c⟨↑[ξ1∘ξ2]⟩≡c⟨↑ξ2⟩⟨↑ξ1⟩
  where
  c⟨↑[ξ1∘ξ2]⟩≡c⟨↑ξ2⟩⟨↑ξ1⟩ : ren (↑ (ξ1 ∘ ξ2)) c ≡ ren (↑ ξ1) (ren (↑ ξ2) c)
  c⟨↑[ξ1∘ξ2]⟩≡c⟨↑ξ2⟩⟨↑ξ1⟩ = 
    ren (↑ (ξ1 ∘ ξ2)) c       ≡⟨ renExt (↑Fuse ξ1 ξ2) c ⟩
    ren (↑ ξ1 ∘ ↑ ξ2) c       ≡⟨ renFuse (↑ ξ1) (↑ ξ2) c ⟩
    ren (↑ ξ1) (ren (↑ ξ2) c) ∎
renFuse ξ1 ξ2 (Fix τ c) = cong₂ Fix refl c⟨↑[ξ1∘ξ2]⟩≡c⟨↑ξ2⟩⟨↑ξ1⟩
  where
  c⟨↑[ξ1∘ξ2]⟩≡c⟨↑ξ2⟩⟨↑ξ1⟩ : ren (↑ (ξ1 ∘ ξ2)) c ≡ ren (↑ ξ1) (ren (↑ ξ2) c)
  c⟨↑[ξ1∘ξ2]⟩≡c⟨↑ξ2⟩⟨↑ξ1⟩ = 
    ren (↑ (ξ1 ∘ ξ2)) c       ≡⟨ renExt (↑Fuse ξ1 ξ2) c ⟩
    ren (↑ ξ1 ∘ ↑ ξ2) c       ≡⟨ renFuse (↑ ξ1) (↑ ξ2) c ⟩
    ren (↑ ξ1) (ren (↑ ξ2) c) ∎
renFuse ξ1 ξ2 (App c c₁) = cong₂ App (renFuse ξ1 ξ2 c) (renFuse ξ1 ξ2 c₁)
renFuse ξ1 ξ2 (LocAbs c) = cong LocAbs (renFuse ξ1 ξ2 c)
renFuse ξ1 ξ2 (LocApp c ℓ) = cong₂ LocApp (renFuse ξ1 ξ2 c) refl
renFuse ξ1 ξ2 (TellLet ℓ ρ1 c ρ2 c₁) = cong₅ TellLet refl refl (renFuse ξ1 ξ2 c) refl (renFuse ξ1 ξ2 c₁)
