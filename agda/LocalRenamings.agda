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

module LocalRenamings
  (E : Language)
  (LE : LawfulLanguage E)
  (LocVal : Set)
  (≡-dec-LocVal : DecidableEquality LocVal)
  where

open import Choreographies E LE LocVal ≡-dec-LocVal
open Language E
open LawfulLanguage LE

-- `up` construction on local variable renamings
↑ₗₑ : (Loc → ℕ → ℕ) → Loc → Loc → ℕ → ℕ
↑ₗₑ ξ ℓ1 ℓ2 with ≡-dec-Loc ℓ1 ℓ2
... | yes _ = ↑ₑ (ξ ℓ2)
... | no  _ = ξ ℓ2

-- Renaming local variables in a choreography
renₗₑ : (c : Chor) (ξ : Loc → ℕ → ℕ) → Chor
renₗₑ (Done ℓ e) ξ = Done ℓ (renₑ e (ξ ℓ))
renₗₑ (Var x) ξ = Var x
renₗₑ (Send ℓ1 c ℓ2) ξ = Send ℓ1 (renₗₑ c ξ) ℓ2
renₗₑ (If ℓ c c₁ c₂) ξ = If ℓ (renₗₑ c ξ) (renₗₑ c₁ ξ) (renₗₑ c₂ ξ)
renₗₑ (Sync ℓ1 d ℓ2 c) ξ = Sync ℓ1 d ℓ2 (renₗₑ c ξ)
renₗₑ (DefLocal ℓ c c₁) ξ = DefLocal ℓ (renₗₑ c ξ) (renₗₑ c₁ (↑ₗₑ ξ ℓ))
renₗₑ (Fun c) ξ = Fun (renₗₑ c ξ)
renₗₑ (App c c₁) ξ = App (renₗₑ c ξ) (renₗₑ c₁ ξ)
renₗₑ (LocAbs c) ξ = LocAbs (renₗₑ c ξ)
renₗₑ (LocApp c ℓ) ξ = LocApp (renₗₑ c ξ) ℓ
renₗₑ (TellLet ℓ ρ1 c ρ2 c₁) ξ = TellLet ℓ ρ1 (renₗₑ c ξ) ρ2 (renₗₑ c₁ ξ)

idRenₗₑ : Loc → ℕ → ℕ
idRenₗₑ ℓ = idRenₑ

-- The local `up` construction has no extensional effect on the identity renaming
↑Idₗₑ : ∀ ℓ ℓ' n → ↑ₗₑ idRenₗₑ ℓ ℓ' n ≡ idRenₗₑ ℓ' n
↑Idₗₑ ℓ ℓ' n with ≡-dec-Loc ℓ ℓ'
... | yes _ = ↑Idₑ n
... | no  _ = refl

-- The local `up` construction extensionally commutes with composition
↑Fuseₗₑ : ∀ ξ1 ξ2 ℓ ℓ' n → ↑ₗₑ (λ ℓ'' → ξ2 ℓ'' ∘ ξ1 ℓ'') ℓ ℓ' n ≡ ↑ₗₑ ξ2 ℓ ℓ' (↑ₗₑ ξ1 ℓ ℓ' n)
↑Fuseₗₑ ξ1 ξ2 ℓ ℓ' n with ≡-dec-Loc ℓ ℓ'
... | yes _ = ↑Fuseₑ (ξ1 ℓ') (ξ2 ℓ') n
... | no  _ = refl

-- The local `up` construction respects extensional equality
↑Extₗₑ : ∀{ξ1 ξ2} →
              (∀ ℓ n → ξ1 ℓ n ≡ ξ2 ℓ n) →
              ∀ ℓ ℓ' n → ↑ₗₑ ξ1 ℓ ℓ' n ≡ ↑ₗₑ ξ2 ℓ ℓ' n
↑Extₗₑ ξ1≈ξ2 ℓ ℓ' n with ≡-dec-Loc ℓ ℓ'
... | yes _ = ↑Extₑ (ξ1≈ξ2 ℓ') n
... | no  _ = ξ1≈ξ2 ℓ' n

-- Renaming local variables respects extensional equality
renExtₗₑ : ∀{ξ1 ξ2} →
            (∀ ℓ n → ξ1 ℓ n ≡ ξ2 ℓ n) →
            ∀ c → renₗₑ c ξ1 ≡ renₗₑ c ξ2
renExtₗₑ ξ1≈ξ2 (Done ℓ e) = cong (Done ℓ) (renExtₑ (ξ1≈ξ2 ℓ) e)
renExtₗₑ ξ1≈ξ2 (Var x) = refl
renExtₗₑ ξ1≈ξ2 (Send ℓ1 c ℓ2) = cong₃ Send refl (renExtₗₑ ξ1≈ξ2 c) refl
renExtₗₑ ξ1≈ξ2 (If ℓ c c₁ c₂) = cong₃ (If ℓ) (renExtₗₑ ξ1≈ξ2 c) (renExtₗₑ ξ1≈ξ2 c₁) (renExtₗₑ ξ1≈ξ2 c₂)
renExtₗₑ ξ1≈ξ2 (Sync ℓ1 d ℓ2 c) = cong (Sync ℓ1 d ℓ2) (renExtₗₑ ξ1≈ξ2 c)
renExtₗₑ ξ1≈ξ2 (DefLocal ℓ c c₁) = cong₂ (DefLocal ℓ) (renExtₗₑ ξ1≈ξ2 c) (renExtₗₑ (↑Extₗₑ ξ1≈ξ2 ℓ) c₁)
renExtₗₑ ξ1≈ξ2 (Fun c) = cong Fun (renExtₗₑ ξ1≈ξ2 c)
renExtₗₑ ξ1≈ξ2 (App c c₁) = cong₂ App (renExtₗₑ ξ1≈ξ2 c) (renExtₗₑ ξ1≈ξ2 c₁)
renExtₗₑ ξ1≈ξ2 (LocAbs c) = cong LocAbs (renExtₗₑ ξ1≈ξ2 c)
renExtₗₑ ξ1≈ξ2 (LocApp c ℓ) = cong₂ LocApp (renExtₗₑ ξ1≈ξ2 c) refl
renExtₗₑ ξ1≈ξ2 (TellLet ℓ ρ1 c ρ2 c₁) = cong₅ TellLet refl refl (renExtₗₑ ξ1≈ξ2 c) refl (renExtₗₑ ξ1≈ξ2 c₁)

-- Renaming local variables respects the identity
renIdₗₑ : ∀ c → renₗₑ c idRenₗₑ ≡ c
renIdₗₑ (Done ℓ e) = cong (Done ℓ) (renIdₑ e)
renIdₗₑ (Var x) = refl
renIdₗₑ (Send ℓ1 c ℓ2) = cong₃ Send refl (renIdₗₑ c) refl
renIdₗₑ (If ℓ c c₁ c₂) = cong₄ If refl (renIdₗₑ c) (renIdₗₑ c₁) (renIdₗₑ c₂)
renIdₗₑ (Sync ℓ1 d ℓ2 c) = cong (Sync ℓ1 d ℓ2) (renIdₗₑ c)
renIdₗₑ (DefLocal ℓ c1 c2) = cong₂ (DefLocal ℓ) (renIdₗₑ c1) c2⟨↑id⟩≡c2
  where
  c2⟨↑id⟩≡c2 : renₗₑ c2 (↑ₗₑ idRenₗₑ ℓ) ≡ c2
  c2⟨↑id⟩≡c2 = 
    renₗₑ c2 (↑ₗₑ idRenₗₑ ℓ) ≡⟨ renExtₗₑ (↑Idₗₑ ℓ) c2 ⟩
    renₗₑ c2 idRenₗₑ        ≡⟨ renIdₗₑ c2 ⟩
    c2                     ∎
renIdₗₑ (Fun c) = cong Fun (renIdₗₑ c)
renIdₗₑ (App c c₁) = cong₂ App (renIdₗₑ c) (renIdₗₑ c₁)
renIdₗₑ (LocAbs c) = cong LocAbs (renIdₗₑ c)
renIdₗₑ (LocApp c ℓ) = cong₂ LocApp (renIdₗₑ c) refl
renIdₗₑ (TellLet ℓ ρ1 c ρ2 c₁) = cong₃ (TellLet ℓ ρ1) (renIdₗₑ c) refl (renIdₗₑ c₁)

-- Renaming local variables enjoys fusion
renFuseₗₑ : ∀ ξ1 ξ2 c → renₗₑ c (λ ℓ → ξ2 ℓ ∘ ξ1 ℓ) ≡ renₗₑ (renₗₑ c ξ1) ξ2
renFuseₗₑ ξ1 ξ2 (Done ℓ e) = cong (Done ℓ) (renFuseₑ (ξ1 ℓ) (ξ2 ℓ) e)
renFuseₗₑ ξ1 ξ2 (Var x) = refl
renFuseₗₑ ξ1 ξ2 (Send ℓ1 c ℓ2) = cong (λ x → Send ℓ1 x ℓ2) (renFuseₗₑ ξ1 ξ2 c)
renFuseₗₑ ξ1 ξ2 (If ℓ c c₁ c₂) = cong₃ (If ℓ) (renFuseₗₑ ξ1 ξ2 c) (renFuseₗₑ ξ1 ξ2 c₁) (renFuseₗₑ ξ1 ξ2 c₂)
renFuseₗₑ ξ1 ξ2 (Sync ℓ1 d ℓ2 c) = cong (Sync ℓ1 d ℓ2) (renFuseₗₑ ξ1 ξ2 c)
renFuseₗₑ ξ1 ξ2 (DefLocal ℓ c1 c2) = cong₂ (DefLocal ℓ) (renFuseₗₑ ξ1 ξ2 c1) c2⟨↑[ξ2∘ξ1]⟩≡c2⟨↑ξ1⟩⟨↑ξ2⟩
  where
  c2⟨↑[ξ2∘ξ1]⟩≡c2⟨↑ξ1⟩⟨↑ξ2⟩ : renₗₑ c2 (↑ₗₑ (λ ℓ1 → ξ2 ℓ1 ∘ ξ1 ℓ1) ℓ) ≡ renₗₑ (renₗₑ c2 (↑ₗₑ ξ1 ℓ)) (↑ₗₑ ξ2 ℓ)
  c2⟨↑[ξ2∘ξ1]⟩≡c2⟨↑ξ1⟩⟨↑ξ2⟩ =
    renₗₑ c2 (↑ₗₑ (λ ℓ1 → ξ2 ℓ1 ∘ ξ1 ℓ1) ℓ)    ≡⟨ renExtₗₑ (↑Fuseₗₑ ξ1 ξ2 ℓ) c2 ⟩
    renₗₑ c2 (λ ℓ1 → ↑ₗₑ ξ2 ℓ ℓ1 ∘ ↑ₗₑ ξ1 ℓ ℓ1) ≡⟨ renFuseₗₑ (↑ₗₑ ξ1 ℓ) (↑ₗₑ ξ2 ℓ) c2 ⟩
    renₗₑ (renₗₑ c2 (↑ₗₑ ξ1 ℓ)) (↑ₗₑ ξ2 ℓ)        ∎
renFuseₗₑ ξ1 ξ2 (Fun c) = cong Fun (renFuseₗₑ ξ1 ξ2 c)
renFuseₗₑ ξ1 ξ2 (App c c₁) = cong₂ App (renFuseₗₑ ξ1 ξ2 c) (renFuseₗₑ ξ1 ξ2 c₁)
renFuseₗₑ ξ1 ξ2 (LocAbs c) = cong LocAbs (renFuseₗₑ ξ1 ξ2 c)
renFuseₗₑ ξ1 ξ2 (LocApp c ℓ) = cong₂ LocApp (renFuseₗₑ ξ1 ξ2 c) refl
renFuseₗₑ ξ1 ξ2 (TellLet ℓ ρ1 c ρ2 c₁) = cong₅ TellLet refl refl (renFuseₗₑ ξ1 ξ2 c) refl (renFuseₗₑ ξ1 ξ2 c₁)
