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

open import Common
open import LocalLang
open import TypedLocalLang
open import Locations

module LocationRenamings
  (L : Location)
  (E : Language L)
  (LE : LawfulLanguage L E)
  (TE : TypedLocalLanguage L E LE)
  where

open import Types L E LE TE
open import Choreographies L E LE TE
open Language E
open LawfulLanguage LE
open Location L
open ≡-Reasoning

-- Rename the location variables in a choreography
renₗ : Chor → (ℕ → ℕ) → Chor
renₗ (Done ℓ e) ξ = Done (renₗ-Loc ℓ ξ) e
renₗ (Var x) ξ = Var x
renₗ (Send ℓ1 c ℓ2) ξ = Send (renₗ-Loc ℓ1 ξ) (renₗ c ξ) (renₗ-Loc ℓ2 ξ)
renₗ (If ℓ c c₁ c₂) ξ = If (renₗ-Loc ℓ ξ) (renₗ c ξ) (renₗ c₁ ξ) (renₗ c₂ ξ)
renₗ (Sync ℓ1 d ℓ2 c) ξ = Sync (renₗ-Loc ℓ1 ξ) d (renₗ-Loc ℓ2 ξ) (renₗ c ξ)
renₗ (DefLocal ℓ c c₁) ξ = DefLocal (renₗ-Loc ℓ ξ) (renₗ c ξ) (renₗ c₁ ξ)
renₗ (Fun τ c) ξ = Fun (renₜ τ ξ) (renₗ c ξ)
renₗ (Fix τ c) ξ = Fix (renₜ τ ξ) (renₗ c ξ)
renₗ (App c1 c2) ξ = App (renₗ c1 ξ) (renₗ c2 ξ)
renₗ (LocAbs c) ξ = LocAbs (renₗ c (↑ ξ))
renₗ (LocApp c ℓ) ξ = LocApp (renₗ c ξ) (renₗ-Loc ℓ ξ)
renₗ (TellLet ℓ ρ1 c1 ρ2 c2) ξ =
  TellLet (renₗ-Loc ℓ ξ) (renₗ-List ρ1 ξ) (renₗ c1 ξ) (renₗ-List ρ2 ξ) (renₗ c2 (↑ ξ))

-- Renaming the location variables in a choreography respects extensional equality
renExtₗ : ∀{ξ1 ξ2} →
         ξ1 ≈ ξ2 →
         ∀ c → renₗ c ξ1 ≡ renₗ c ξ2
renExtₗ ξ1≈ξ2 (Done ℓ e) = cong₂ Done (renExtₗ-Loc ξ1≈ξ2 ℓ) refl
renExtₗ ξ1≈ξ2 (Var x) = refl
renExtₗ ξ1≈ξ2 (Send ℓ1 c ℓ2) = cong₃ Send (renExtₗ-Loc ξ1≈ξ2 ℓ1) (renExtₗ ξ1≈ξ2 c) (renExtₗ-Loc ξ1≈ξ2 ℓ2)
renExtₗ ξ1≈ξ2 (If ℓ c c₁ c₂) = cong₄ If (renExtₗ-Loc ξ1≈ξ2 ℓ) (renExtₗ ξ1≈ξ2 c) (renExtₗ ξ1≈ξ2 c₁) (renExtₗ ξ1≈ξ2 c₂)
renExtₗ ξ1≈ξ2 (Sync ℓ1 d ℓ2 c) = cong₄ Sync (renExtₗ-Loc ξ1≈ξ2 ℓ1) refl (renExtₗ-Loc ξ1≈ξ2 ℓ2) (renExtₗ ξ1≈ξ2 c)
renExtₗ ξ1≈ξ2 (DefLocal ℓ c c₁) = cong₃ DefLocal (renExtₗ-Loc ξ1≈ξ2 ℓ) (renExtₗ ξ1≈ξ2 c) (renExtₗ ξ1≈ξ2 c₁)
renExtₗ ξ1≈ξ2 (Fun τ c) = cong₂ Fun (renExtₜ ξ1≈ξ2 τ) (renExtₗ ξ1≈ξ2 c)
renExtₗ ξ1≈ξ2 (Fix τ c) = cong₂ Fix (renExtₜ ξ1≈ξ2 τ) (renExtₗ ξ1≈ξ2 c)
renExtₗ ξ1≈ξ2 (App c c₁) = cong₂ App (renExtₗ ξ1≈ξ2 c) (renExtₗ ξ1≈ξ2 c₁)
renExtₗ ξ1≈ξ2 (LocAbs c) = cong LocAbs (renExtₗ (↑Ext ξ1≈ξ2) c)
renExtₗ ξ1≈ξ2 (LocApp c ℓ) = cong₂ LocApp (renExtₗ ξ1≈ξ2 c) (renExtₗ-Loc ξ1≈ξ2 ℓ)
renExtₗ ξ1≈ξ2 (TellLet ℓ ρ1 c1 ρ2 c2) = cong₅ TellLet
    (renExtₗ-Loc ξ1≈ξ2 ℓ) (renExtₗ-List ξ1≈ξ2 ρ1) (renExtₗ ξ1≈ξ2 c1) (renExtₗ-List ξ1≈ξ2 ρ2) (renExtₗ (↑Ext ξ1≈ξ2) c2)

-- Renaming the location variables in a choreography respects the identity
renIdₗ :  ∀ c → renₗ c idRen ≡ c
renIdₗ (Done ℓ e) = cong₂ Done (renIdₗ-Loc ℓ) refl
renIdₗ (Var x) = refl
renIdₗ (Send ℓ1 c ℓ2) = cong₃ Send (renIdₗ-Loc ℓ1) (renIdₗ c) (renIdₗ-Loc ℓ2)
renIdₗ (If ℓ c c₁ c₂) = cong₄ If (renIdₗ-Loc ℓ) (renIdₗ c) (renIdₗ c₁) (renIdₗ c₂)
renIdₗ (Sync ℓ1 d ℓ2 c) = cong₄ Sync (renIdₗ-Loc ℓ1) refl (renIdₗ-Loc ℓ2) (renIdₗ c)
renIdₗ (DefLocal ℓ c c₁) = cong₃ DefLocal (renIdₗ-Loc ℓ) (renIdₗ c) (renIdₗ c₁)
renIdₗ (Fun τ c) = cong₂ Fun (renIdₜ τ) (renIdₗ c)
renIdₗ (Fix τ c) = cong₂ Fix (renIdₜ τ) (renIdₗ c)
renIdₗ (App c c₁) = cong₂ App (renIdₗ c) (renIdₗ c₁)
renIdₗ (LocAbs c) = cong LocAbs c⟨↑id⟩≡c
  where
  c⟨↑id⟩≡c : renₗ c (↑ idRen) ≡ c
  c⟨↑id⟩≡c = 
    renₗ c (↑ idRen) ≡⟨ renExtₗ ↑Id c ⟩
    renₗ c idRen     ≡⟨ renIdₗ c ⟩
    c                ∎
renIdₗ (LocApp c ℓ) = cong₂ LocApp (renIdₗ c) (renIdₗ-Loc ℓ)
renIdₗ (TellLet ℓ ρ1 c1 ρ2 c2) =
  cong₅ TellLet (renIdₗ-Loc ℓ) (renIdₗ-List ρ1)
    (renIdₗ c1) (renIdₗ-List ρ2) c2⟨↑Id⟩≡c2
  where
    c2⟨↑Id⟩≡c2 : renₗ c2 (↑ idRen) ≡ c2
    c2⟨↑Id⟩≡c2 =
      renₗ c2 (↑ idRen) ≡⟨ renExtₗ ↑Id c2 ⟩
      renₗ c2 idRen     ≡⟨ renIdₗ c2 ⟩
      c2                ∎

-- Renaming the location variables in a choreography enjoys fusion
renFuseₗ :  ∀ ξ1 ξ2 c → renₗ c (ξ2 ∘ ξ1) ≡ renₗ (renₗ c ξ1) ξ2
renFuseₗ ξ1 ξ2 (Done ℓ e) = cong₂ Done (renFuseₗ-Loc ξ1 ξ2 ℓ) refl
renFuseₗ ξ1 ξ2 (Var x) = refl
renFuseₗ ξ1 ξ2 (Send ℓ1 c ℓ2) = cong₃ Send (renFuseₗ-Loc ξ1 ξ2 ℓ1) (renFuseₗ ξ1 ξ2 c) (renFuseₗ-Loc ξ1 ξ2 ℓ2)
renFuseₗ ξ1 ξ2 (If ℓ c c₁ c₂) = cong₄ If (renFuseₗ-Loc ξ1 ξ2 ℓ) (renFuseₗ ξ1 ξ2 c) (renFuseₗ ξ1 ξ2 c₁) (renFuseₗ ξ1 ξ2 c₂)
renFuseₗ ξ1 ξ2 (Sync ℓ1 d ℓ2 c) = cong₄ Sync (renFuseₗ-Loc ξ1 ξ2 ℓ1) refl (renFuseₗ-Loc ξ1 ξ2 ℓ2) (renFuseₗ ξ1 ξ2 c)
renFuseₗ ξ1 ξ2 (DefLocal ℓ c c₁) = cong₃ DefLocal (renFuseₗ-Loc ξ1 ξ2 ℓ) (renFuseₗ ξ1 ξ2 c) (renFuseₗ ξ1 ξ2 c₁)
renFuseₗ ξ1 ξ2 (Fun τ c) = cong₂ Fun (renFuseₜ ξ1 ξ2 τ)  (renFuseₗ ξ1 ξ2 c)
renFuseₗ ξ1 ξ2 (Fix τ c) = cong₂ Fix (renFuseₜ ξ1 ξ2 τ) (renFuseₗ ξ1 ξ2 c)
renFuseₗ ξ1 ξ2 (App c1 c2) = cong₂ App (renFuseₗ ξ1 ξ2 c1) (renFuseₗ ξ1 ξ2 c2)
renFuseₗ ξ1 ξ2 (LocAbs c) = cong LocAbs c⟨↑[ξ2∘ξ1]⟩≡c⟨↑ξ1⟩⟨↑ξ2⟩
    where
    c⟨↑[ξ2∘ξ1]⟩≡c⟨↑ξ1⟩⟨↑ξ2⟩ : renₗ c (↑ (ξ2 ∘ ξ1)) ≡ renₗ (renₗ c (↑ ξ1)) (↑ ξ2)
    c⟨↑[ξ2∘ξ1]⟩≡c⟨↑ξ1⟩⟨↑ξ2⟩ =
        renₗ c (↑ (ξ2 ∘ ξ1))        ≡⟨ renExtₗ (↑Fuse ξ1 ξ2) c ⟩
        renₗ c (↑ ξ2 ∘ ↑ ξ1)        ≡⟨ renFuseₗ (↑ ξ1) (↑ ξ2) c ⟩
        renₗ (renₗ c (↑ ξ1)) (↑ ξ2) ∎
renFuseₗ ξ1 ξ2 (LocApp c ℓ) = cong₂ LocApp (renFuseₗ ξ1 ξ2 c) (renFuseₗ-Loc ξ1 ξ2 ℓ)
renFuseₗ ξ1 ξ2 (TellLet ℓ ρ1 c1 ρ2 c2) =
  cong₅ TellLet (renFuseₗ-Loc ξ1 ξ2 ℓ) (renFuseₗ-List ξ1 ξ2 ρ1)
  (renFuseₗ ξ1 ξ2 c1) (renFuseₗ-List ξ1 ξ2 ρ2) c2⟨↑[ξ2∘ξ1]⟩≡c⟨↑ξ1⟩⟨↑ξ2⟩
  where
    c2⟨↑[ξ2∘ξ1]⟩≡c⟨↑ξ1⟩⟨↑ξ2⟩ : renₗ c2 (↑ (ξ2 ∘ ξ1)) ≡ renₗ (renₗ c2 (↑ ξ1)) (↑ ξ2)
    c2⟨↑[ξ2∘ξ1]⟩≡c⟨↑ξ1⟩⟨↑ξ2⟩ =
        renₗ c2 (↑ (ξ2 ∘ ξ1))        ≡⟨ renExtₗ (↑Fuse ξ1 ξ2) c2 ⟩
        renₗ c2 (↑ ξ2 ∘ ↑ ξ1)        ≡⟨ renFuseₗ (↑ ξ1) (↑ ξ2) c2 ⟩
        renₗ (renₗ c2 (↑ ξ1)) (↑ ξ2) ∎
