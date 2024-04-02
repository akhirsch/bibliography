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

module LocalRenamings
  (L : Location)
  (E : Language L)
  (LE : LawfulLanguage L E)
  (TE : TypedLocalLanguage L E LE)
  where

open import Choreographies L E LE TE
-- open import LocalContexts L E LE TE
open Language E
open LawfulLanguage LE
open Location L



-- Renaming local variables in a choreography
-- renₗₑ : (ξ : Loc → ℕ → ℕ) (c : Chor) → Chor
-- renₗₑ ξ (Done ℓ e) = Done ℓ (renₑ (ξ ℓ) e)
-- renₗₑ ξ (Var x) = Var x
-- renₗₑ ξ (Send ℓ1 c ℓ2) = Send ℓ1 (renₗₑ ξ c) ℓ2
-- renₗₑ ξ (If ℓ c c₁ c₂) = If ℓ (renₗₑ ξ c) (renₗₑ ξ c₁) (renₗₑ ξ c₂)
-- renₗₑ ξ (Sync ℓ1 d ℓ2 c) = Sync ℓ1 d ℓ2 (renₗₑ ξ c)
-- renₗₑ ξ (DefLocal ℓ c1 c2) = DefLocal ℓ (renₗₑ ξ c1) (renₗₑ (↑ₗₑ ξ) c2)
-- renₗₑ ξ (Fun τ c) = Fun τ (renₗₑ ξ c)
-- renₗₑ ξ (Fix τ c) = Fix τ (renₗₑ ξ c)
-- renₗₑ ξ (App c c₁) = App (renₗₑ ξ c) (renₗₑ ξ c₁)
-- renₗₑ ξ (LocAbs c) = LocAbs (renₗₑ ξ c)
-- renₗₑ ξ (LocApp c ℓ) = LocApp (renₗₑ ξ c) ℓ
-- renₗₑ ξ (TellLet ℓ ρ1 c1 ρ2 c2) = TellLet ℓ ρ1 (renₗₑ ξ c1) ρ2 (renₗₑ ξ c2)

-- -- Renaming local variables respects extensional equality
-- renExtₗₑ : ∀{ξ1 ξ2} →
--           ξ1 ≈₂ ξ2 →
--           renₗₑ ξ1 ≈ renₗₑ ξ2
-- renExtₗₑ ξ1≈ξ2 (Done ℓ e) = cong (Done ℓ) ? -- (renExtₑ ξ1≈ξ2 e)
-- renExtₗₑ ξ1≈ξ2 (Var x) = refl
-- renExtₗₑ ξ1≈ξ2 (Send ℓ1 c ℓ2) = cong₃ Send refl (renExtₗₑ ξ1≈ξ2 c) refl
-- renExtₗₑ ξ1≈ξ2 (If ℓ c c₁ c₂) =
--   cong₃ (If ℓ) (renExtₗₑ ξ1≈ξ2 c) (renExtₗₑ ξ1≈ξ2 c₁) (renExtₗₑ ξ1≈ξ2 c₂)
-- renExtₗₑ ξ1≈ξ2 (Sync ℓ1 d ℓ2 c) = cong (Sync ℓ1 d ℓ2) (renExtₗₑ ξ1≈ξ2 c)
-- renExtₗₑ ξ1≈ξ2 (DefLocal ℓ c1 c2) =
--   cong₂ (DefLocal ℓ) (renExtₗₑ ξ1≈ξ2 c1) (renExtₗₑ (↑Extₗₑ ξ1≈ξ2) c2)
-- renExtₗₑ ξ1≈ξ2 (Fun τ c) = cong₂ Fun refl (renExtₗₑ ξ1≈ξ2 c)
-- renExtₗₑ ξ1≈ξ2 (Fix τ c) = cong₂ Fix refl (renExtₗₑ ξ1≈ξ2 c)
-- renExtₗₑ ξ1≈ξ2 (App c c₁) = cong₂ App (renExtₗₑ ξ1≈ξ2 c) (renExtₗₑ ξ1≈ξ2 c₁)
-- renExtₗₑ ξ1≈ξ2 (LocAbs c) = cong LocAbs (renExtₗₑ ξ1≈ξ2 c)
-- renExtₗₑ ξ1≈ξ2 (LocApp c ℓ) = cong₂ LocApp (renExtₗₑ ξ1≈ξ2 c) refl
-- renExtₗₑ ξ1≈ξ2 (TellLet ℓ ρ1 c1 ρ2 c2) =
--   cong₅ TellLet refl refl (renExtₗₑ ξ1≈ξ2 c1) refl (renExtₗₑ ξ1≈ξ2 c2)

-- -- Renaming local variables respects the identity
-- renIdₗₑ : ∀ c → renₗₑ idRen c ≡ c
-- renIdₗₑ (Done ℓ e) = cong (Done ℓ) (renIdₑ e)
-- renIdₗₑ (Var x) = refl
-- renIdₗₑ (Send ℓ1 c ℓ2) = cong₃ Send refl (renIdₗₑ c) refl
-- renIdₗₑ (If ℓ c c₁ c₂) = cong₄ If refl (renIdₗₑ c) (renIdₗₑ c₁) (renIdₗₑ c₂)
-- renIdₗₑ (Sync ℓ1 d ℓ2 c) = cong (Sync ℓ1 d ℓ2) (renIdₗₑ c)
-- renIdₗₑ (DefLocal ℓ c1 c2) = cong₂ (DefLocal ℓ) (renIdₗₑ c1) c2⟨↑id⟩≡c2
--   where
--   c2⟨↑id⟩≡c2 : renₗₑ (↑ idRen) c2 ≡ c2
--   c2⟨↑id⟩≡c2 = 
--     renₗₑ (↑ idRen) c2 ≡⟨ renExtₗₑ ↑Id c2 ⟩
--     renₗₑ idRen c2     ≡⟨ renIdₗₑ c2 ⟩
--     c2                 ∎
-- renIdₗₑ (Fun τ c) = cong₂ Fun refl (renIdₗₑ c)
-- renIdₗₑ (Fix τ c) = cong₂ Fix refl (renIdₗₑ c)
-- renIdₗₑ (App c c₁) = cong₂ App (renIdₗₑ c) (renIdₗₑ c₁)
-- renIdₗₑ (LocAbs c) = cong LocAbs (renIdₗₑ c)
-- renIdₗₑ (LocApp c ℓ) = cong₂ LocApp (renIdₗₑ c) refl
-- renIdₗₑ (TellLet ℓ ρ1 c1 ρ2 c2) =
--   cong₅ TellLet refl refl (renIdₗₑ c1) refl (renIdₗₑ c2)

-- -- Renaming local variables enjoys fusion
-- renFuseₗₑ : ∀ ξ1 ξ2 → renₗₑ (ξ1 ∘ ξ2) ≈ renₗₑ ξ1 ∘ renₗₑ ξ2
-- renFuseₗₑ ξ1 ξ2 (Done ℓ e) = cong (Done ℓ) (renFuseₑ ξ1 ξ2 e)
-- renFuseₗₑ ξ1 ξ2 (Var x) = refl
-- renFuseₗₑ ξ1 ξ2 (Send ℓ1 c ℓ2) = cong (λ x → Send ℓ1 x ℓ2) (renFuseₗₑ ξ1 ξ2 c)
-- renFuseₗₑ ξ1 ξ2 (If ℓ c c₁ c₂) = cong₃ (If ℓ) (renFuseₗₑ ξ1 ξ2 c) (renFuseₗₑ ξ1 ξ2 c₁) (renFuseₗₑ ξ1 ξ2 c₂)
-- renFuseₗₑ ξ1 ξ2 (Sync ℓ1 d ℓ2 c) = cong (Sync ℓ1 d ℓ2) (renFuseₗₑ ξ1 ξ2 c)
-- renFuseₗₑ ξ1 ξ2 (DefLocal ℓ c1 c2) = cong₂ (DefLocal ℓ) (renFuseₗₑ ξ1 ξ2 c1) c2⟨↑[ξ2∘ξ1]⟩≡c2⟨↑ξ1⟩⟨↑ξ2⟩
--   where
--   c2⟨↑[ξ2∘ξ1]⟩≡c2⟨↑ξ1⟩⟨↑ξ2⟩ : renₗₑ (↑ (ξ1 ∘ ξ2)) c2 ≡ renₗₑ (↑ ξ1) (renₗₑ (↑ ξ2) c2)
--   c2⟨↑[ξ2∘ξ1]⟩≡c2⟨↑ξ1⟩⟨↑ξ2⟩ =
--     renₗₑ (↑ (ξ1 ∘ ξ2)) c2         ≡⟨ renExtₗₑ (↑Fuse ξ1 ξ2) c2 ⟩
--     renₗₑ (↑ ξ1 ∘ ↑ ξ2) c2         ≡⟨ renFuseₗₑ (↑ ξ1) (↑ ξ2) c2 ⟩
--     renₗₑ (↑ ξ1) (renₗₑ (↑ ξ2) c2) ∎
-- renFuseₗₑ ξ1 ξ2 (Fun τ c) = cong₂ Fun refl (renFuseₗₑ ξ1 ξ2 c)
-- renFuseₗₑ ξ1 ξ2 (Fix τ c) = cong₂ Fix refl (renFuseₗₑ ξ1 ξ2 c)
-- renFuseₗₑ ξ1 ξ2 (App c c₁) = cong₂ App (renFuseₗₑ ξ1 ξ2 c) (renFuseₗₑ ξ1 ξ2 c₁)
-- renFuseₗₑ ξ1 ξ2 (LocAbs c) = cong LocAbs (renFuseₗₑ ξ1 ξ2 c)
-- renFuseₗₑ ξ1 ξ2 (LocApp c ℓ) = cong₂ LocApp (renFuseₗₑ ξ1 ξ2 c) refl
-- renFuseₗₑ ξ1 ξ2 (TellLet ℓ ρ1 c1 ρ2 c2) =
--   cong₅ TellLet refl refl (renFuseₗₑ ξ1 ξ2 c1) refl (renFuseₗₑ ξ1 ξ2 c2)
