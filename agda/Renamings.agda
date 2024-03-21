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

module Renamings
  (E : Language)
  (LE : LawfulLanguage E)
  (LocVal : Set)
  (≡-dec-LocVal : DecidableEquality LocVal)
  where

open import Choreographies E LE LocVal ≡-dec-LocVal
open Language E
open LawfulLanguage LE

-- Renaming global variables
ren : (c : Chor) (ξ : ℕ → ℕ) → Chor
ren (Done ℓ e) ξ = Done ℓ e
ren (Var x) ξ = Var (ξ x)
ren (Send ℓ1 c ℓ2) ξ = Send ℓ1 (ren c ξ) ℓ2
ren (If ℓ c c₁ c₂) ξ = If ℓ (ren c ξ) (ren c₁ ξ) (ren c₂ ξ)
ren (Sync ℓ1 d ℓ2 c) ξ = Sync ℓ1 d ℓ2 (ren c ξ)
ren (DefLocal ℓ c c₁) ξ = DefLocal ℓ (ren c ξ) (ren c₁ ξ)
ren (Fun c) ξ = Fun (ren c (↑ ξ))
ren (Fix c) ξ = Fix (ren c (↑ ξ))
ren (App c c₁) ξ = App (ren c ξ) (ren c₁ ξ)
ren (LocAbs c) ξ = LocAbs (ren c ξ)
ren (LocApp c ℓ) ξ = LocApp (ren c ξ) ℓ
ren (TellLet ℓ ρ1 c ρ2 c₁) ξ = TellLet ℓ ρ1 (ren c ξ) ρ2 (ren c₁ ξ)

-- Renaming global variables respects extensional equality
renExt : ∀{ξ1 ξ2} →
         ξ1 ≈ ξ2 →
         ∀ c → ren c ξ1 ≡ ren c ξ2
renExt ξ1≈ξ2 (Done ℓ e) = refl
renExt ξ1≈ξ2 (Var x) = cong Var (ξ1≈ξ2 x)
renExt ξ1≈ξ2 (Send ℓ1 c ℓ2) = cong₃ Send refl (renExt ξ1≈ξ2 c) refl
renExt ξ1≈ξ2 (If ℓ c c₁ c₂) = cong₄ If refl (renExt ξ1≈ξ2 c) (renExt ξ1≈ξ2 c₁) (renExt ξ1≈ξ2 c₂)
renExt ξ1≈ξ2 (Sync ℓ1 d ℓ2 c) = cong₄ Sync refl refl refl (renExt ξ1≈ξ2 c)
renExt ξ1≈ξ2 (DefLocal ℓ c c₁) = cong₃ DefLocal refl (renExt ξ1≈ξ2 c) (renExt ξ1≈ξ2 c₁)
renExt ξ1≈ξ2 (Fun c) = cong Fun (renExt (↑Ext ξ1≈ξ2) c)
renExt ξ1≈ξ2 (Fix c) = cong Fix (renExt (↑Ext ξ1≈ξ2) c)
renExt ξ1≈ξ2 (App c c₁) = cong₂ App (renExt ξ1≈ξ2 c) (renExt ξ1≈ξ2 c₁)
renExt ξ1≈ξ2 (LocAbs c) = cong LocAbs (renExt ξ1≈ξ2 c)
renExt ξ1≈ξ2 (LocApp c ℓ) = cong₂ LocApp (renExt ξ1≈ξ2 c) refl
renExt ξ1≈ξ2 (TellLet ℓ ρ1 c ρ2 c₁) = cong₅ TellLet refl refl (renExt ξ1≈ξ2 c) refl (renExt ξ1≈ξ2 c₁)

-- Renaming global variables respects the identity
renId : ∀ c → ren c idRen ≡ c
renId (Done ℓ e) = refl
renId (Var x) = refl
renId (Send ℓ1 c ℓ2) = cong₃ Send refl (renId c) refl
renId (If ℓ c c₁ c₂) = cong₄ If refl (renId c) (renId c₁) (renId c₂)
renId (Sync ℓ1 d ℓ2 c) = cong₄ Sync refl refl refl (renId c)
renId (DefLocal ℓ c c₁) = cong₃ DefLocal refl (renId c) (renId c₁)
renId (Fun c) = cong Fun c⟨↑id⟩≡c
  where
  c⟨↑id⟩≡c : ren c (↑ idRen) ≡ c
  c⟨↑id⟩≡c = 
    ren c (↑ idRen) ≡⟨ renExt ↑Id c ⟩
    ren c idRen        ≡⟨ renId c ⟩
    c                     ∎
renId (Fix c) = cong Fix c⟨↑id⟩≡c
  where
  c⟨↑id⟩≡c : ren c (↑ idRen) ≡ c
  c⟨↑id⟩≡c = 
    ren c (↑ idRen) ≡⟨ renExt ↑Id c ⟩
    ren c idRen        ≡⟨ renId c ⟩
    c                     ∎
renId (App c c₁) = cong₂ App (renId c) (renId c₁)
renId (LocAbs c) = cong LocAbs (renId c)
renId (LocApp c ℓ) = cong₂ LocApp (renId c) refl
renId (TellLet ℓ ρ1 c ρ2 c₁) = cong₅ TellLet refl refl (renId c) refl (renId c₁)

-- Renaming global variables enjoys fusion
renFuse : ∀ ξ1 ξ2 c → ren c (ξ2 ∘ ξ1) ≡ ren (ren c ξ1) ξ2
renFuse ξ1 ξ2 (Done ℓ e) = refl
renFuse ξ1 ξ2 (Var x) = cong Var refl
renFuse ξ1 ξ2 (Send ℓ1 c ℓ2) = cong₃ Send refl (renFuse ξ1 ξ2 c) refl
renFuse ξ1 ξ2 (If ℓ c c₁ c₂) = cong₄ If refl (renFuse ξ1 ξ2 c) (renFuse ξ1 ξ2 c₁) (renFuse ξ1 ξ2 c₂)
renFuse ξ1 ξ2 (Sync ℓ1 d ℓ2 c) = cong₄ Sync refl refl refl (renFuse ξ1 ξ2 c)
renFuse ξ1 ξ2 (DefLocal ℓ c c₁) = cong₃ DefLocal refl (renFuse ξ1 ξ2 c) (renFuse ξ1 ξ2 c₁)
renFuse ξ1 ξ2 (Fun c) = cong Fun c⟨↑[ξ2∘ξ1]⟩≡c⟨↑ξ1⟩⟨↑ξ2⟩
  where
  c⟨↑[ξ2∘ξ1]⟩≡c⟨↑ξ1⟩⟨↑ξ2⟩ : ren c (↑ (ξ2 ∘ ξ1)) ≡ ren (ren c (↑ ξ1)) (↑ ξ2)
  c⟨↑[ξ2∘ξ1]⟩≡c⟨↑ξ1⟩⟨↑ξ2⟩ = 
    ren c (↑ (ξ2 ∘ ξ1))       ≡⟨ renExt (↑Fuse ξ1 ξ2) c ⟩
    ren c (↑ ξ2 ∘ ↑ ξ1)       ≡⟨ renFuse (↑ ξ1) (↑ ξ2) c ⟩
    ren (ren c (↑ ξ1)) (↑ ξ2) ∎
renFuse ξ1 ξ2 (Fix c) = cong Fix c⟨↑[ξ2∘ξ1]⟩≡c⟨↑ξ1⟩⟨↑ξ2⟩
  where
  c⟨↑[ξ2∘ξ1]⟩≡c⟨↑ξ1⟩⟨↑ξ2⟩ : ren c (↑ (ξ2 ∘ ξ1)) ≡ ren (ren c (↑ ξ1)) (↑ ξ2)
  c⟨↑[ξ2∘ξ1]⟩≡c⟨↑ξ1⟩⟨↑ξ2⟩ = 
    ren c (↑ (ξ2 ∘ ξ1))       ≡⟨ renExt (↑Fuse ξ1 ξ2) c ⟩
    ren c (↑ ξ2 ∘ ↑ ξ1)       ≡⟨ renFuse (↑ ξ1) (↑ ξ2) c ⟩
    ren (ren c (↑ ξ1)) (↑ ξ2) ∎
renFuse ξ1 ξ2 (App c c₁) = cong₂ App (renFuse ξ1 ξ2 c) (renFuse ξ1 ξ2 c₁)
renFuse ξ1 ξ2 (LocAbs c) = cong LocAbs (renFuse ξ1 ξ2 c)
renFuse ξ1 ξ2 (LocApp c ℓ) = cong₂ LocApp (renFuse ξ1 ξ2 c) refl
renFuse ξ1 ξ2 (TellLet ℓ ρ1 c ρ2 c₁) = cong₅ TellLet refl refl (renFuse ξ1 ξ2 c) refl (renFuse ξ1 ξ2 c₁)
