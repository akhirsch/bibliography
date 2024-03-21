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

{-
  `up` construction on local variable renamings.
   Used when going past a binder of a specified
   location to ensure that counting is done correctly.
-}
upLocRen : (Loc → ℕ → ℕ) → Loc → Loc → ℕ → ℕ
upLocRen ξ ℓ1 ℓ2 with ≡-dec-Loc ℓ1 ℓ2
... | yes _ = upRenExpr (ξ ℓ2)
... | no  _ = ξ ℓ2

-- Renaming local expressions in a choreography
locRen : (c : Chor) (ξ : Loc → ℕ → ℕ) → Chor
locRen (Done ℓ e) ξ = Done ℓ (renExpr e (ξ ℓ))
locRen (Var x) ξ = Var x
locRen (Send ℓ1 c ℓ2) ξ = Send ℓ1 (locRen c ξ) ℓ2
locRen (If ℓ c c₁ c₂) ξ = If ℓ (locRen c ξ) (locRen c₁ ξ) (locRen c₂ ξ)
locRen (Sync ℓ1 d ℓ2 c) ξ = Sync ℓ1 d ℓ2 (locRen c ξ)
locRen (DefLocal ℓ c c₁) ξ = DefLocal ℓ (locRen c ξ) (locRen c₁ (upLocRen ξ ℓ))
locRen (Fun c) ξ = Fun (locRen c ξ)
locRen (App c c₁) ξ = App (locRen c ξ) (locRen c₁ ξ)
locRen (LocAbs c) ξ = LocAbs (locRen c ξ)
locRen (LocApp c ℓ) ξ = LocApp (locRen c ξ) ℓ
locRen (TellLet ℓ ρ1 c ρ2 c₁) ξ = TellLet ℓ ρ1 (locRen c ξ) ρ2 (locRen c₁ ξ)

idRenLoc : Loc → ℕ → ℕ
idRenLoc ℓ = idRenExpr

-- The local `up` construction has no extensional effect on the identity renaming
upLocRenId : ∀ ℓ ℓ' n → upLocRen idRenLoc ℓ ℓ' n ≡ idRenLoc ℓ' n
upLocRenId ℓ ℓ' n with ≡-dec-Loc ℓ ℓ'
... | yes _ = upRenIdExpr n
... | no  _ = refl

-- The local `up` construction respects extensional equality
upLocRenExt : ∀{ξ1 ξ2} →
              (∀ ℓ n → ξ1 ℓ n ≡ ξ2 ℓ n) →
              ∀ ℓ ℓ' n → upLocRen ξ1 ℓ ℓ' n ≡ upLocRen ξ2 ℓ ℓ' n
upLocRenExt ξ1≈ξ2 ℓ ℓ' n with ≡-dec-Loc ℓ ℓ'
... | yes _ = upRenExprExt (ξ1≈ξ2 ℓ') n
... | no  _ = ξ1≈ξ2 ℓ' n

-- Renaming local expressions respects extensional equality
locRenExt : ∀{ξ1 ξ2} →
            (∀ ℓ n → ξ1 ℓ n ≡ ξ2 ℓ n) →
            ∀ c → locRen c ξ1 ≡ locRen c ξ2
locRenExt ξ1≈ξ2 (Done ℓ e) = cong (Done ℓ) (renExprExt (ξ1≈ξ2 ℓ) e)
locRenExt ξ1≈ξ2 (Var x) = refl
locRenExt ξ1≈ξ2 (Send ℓ1 c ℓ2) = cong (λ x → Send ℓ1 x ℓ2) (locRenExt ξ1≈ξ2 c)
locRenExt ξ1≈ξ2 (If ℓ c c₁ c₂) = cong₃ (If ℓ) (locRenExt ξ1≈ξ2 c) (locRenExt ξ1≈ξ2 c₁) (locRenExt ξ1≈ξ2 c₂)
locRenExt ξ1≈ξ2 (Sync ℓ1 d ℓ2 c) = cong (Sync ℓ1 d ℓ2) (locRenExt ξ1≈ξ2 c)
locRenExt ξ1≈ξ2 (DefLocal ℓ c c₁) = cong₂ (DefLocal ℓ) (locRenExt ξ1≈ξ2 c) (locRenExt (upLocRenExt ξ1≈ξ2 ℓ) c₁)
locRenExt ξ1≈ξ2 (Fun c) = cong Fun (locRenExt ξ1≈ξ2 c)
locRenExt ξ1≈ξ2 (App c c₁) = cong₂ App (locRenExt ξ1≈ξ2 c) (locRenExt ξ1≈ξ2 c₁)
locRenExt ξ1≈ξ2 (LocAbs c) = cong LocAbs (locRenExt ξ1≈ξ2 c)
locRenExt ξ1≈ξ2 (LocApp c ℓ) = cong (λ x → LocApp x ℓ) (locRenExt ξ1≈ξ2 c)
locRenExt ξ1≈ξ2 (TellLet ℓ ρ1 c ρ2 c₁) = cong₂ (λ x y → TellLet ℓ ρ1 x ρ2 y) (locRenExt ξ1≈ξ2 c) (locRenExt ξ1≈ξ2 c₁)

-- The local `up` construction extensionally commutes with composition.
upLocRen∘ : ∀ ξ1 ξ2 ℓ ℓ' n → upLocRen (λ ℓ'' → ξ2 ℓ'' ∘ ξ1 ℓ'') ℓ ℓ' n ≡ upLocRen ξ2 ℓ ℓ' (upLocRen ξ1 ℓ ℓ' n)
upLocRen∘ ξ1 ξ2 ℓ ℓ' n with ≡-dec-Loc ℓ ℓ'
... | yes _ = upRenExpr∘ (ξ1 ℓ') (ξ2 ℓ') n
... | no  _ = refl

-- Renaming locally enjoys fusion
locRen∘ : ∀ ξ1 ξ2 c → locRen c (λ ℓ → ξ2 ℓ ∘ ξ1 ℓ) ≡ locRen (locRen c ξ1) ξ2
locRen∘ ξ1 ξ2 (Done ℓ e) = cong (Done ℓ) (renExpr∘ (ξ1 ℓ) (ξ2 ℓ) e)
locRen∘ ξ1 ξ2 (Var x) = refl
locRen∘ ξ1 ξ2 (Send ℓ1 c ℓ2) = cong (λ x → Send ℓ1 x ℓ2) (locRen∘ ξ1 ξ2 c)
locRen∘ ξ1 ξ2 (If ℓ c c₁ c₂) = cong₃ (If ℓ) (locRen∘ ξ1 ξ2 c) (locRen∘ ξ1 ξ2 c₁) (locRen∘ ξ1 ξ2 c₂)
locRen∘ ξ1 ξ2 (Sync ℓ1 d ℓ2 c) = cong (Sync ℓ1 d ℓ2) (locRen∘ ξ1 ξ2 c)
locRen∘ ξ1 ξ2 (DefLocal ℓ c1 c2) = cong₂ (DefLocal ℓ) (locRen∘ ξ1 ξ2 c1) c2⟨ξ2∘ξ1⟩≡c⟨ξ1⟩⟨ξ2⟩
  where
  c2⟨ξ2∘ξ1⟩≡c⟨ξ1⟩⟨ξ2⟩ : locRen c2 (upLocRen (λ ℓ1 → ξ2 ℓ1 ∘ ξ1 ℓ1) ℓ) ≡ locRen (locRen c2 (upLocRen ξ1 ℓ)) (upLocRen ξ2 ℓ)
  c2⟨ξ2∘ξ1⟩≡c⟨ξ1⟩⟨ξ2⟩ =
    locRen c2 (upLocRen (λ ℓ1 → ξ2 ℓ1 ∘ ξ1 ℓ1) ℓ)          ≡⟨ locRenExt (upLocRen∘ ξ1 ξ2 ℓ) c2 ⟩
    locRen c2 (λ ℓ1 → upLocRen ξ2 ℓ ℓ1 ∘ upLocRen ξ1 ℓ ℓ1) ≡⟨ locRen∘ (upLocRen ξ1 ℓ) (upLocRen ξ2 ℓ) c2 ⟩
    locRen (locRen c2 (upLocRen ξ1 ℓ)) (upLocRen ξ2 ℓ)    ∎
locRen∘ ξ1 ξ2 (Fun c) = cong Fun (locRen∘ ξ1 ξ2 c)
locRen∘ ξ1 ξ2 (App c c₁) = cong₂ App (locRen∘ ξ1 ξ2 c) (locRen∘ ξ1 ξ2 c₁)
locRen∘ ξ1 ξ2 (LocAbs c) = cong LocAbs (locRen∘ ξ1 ξ2 c)
locRen∘ ξ1 ξ2 (LocApp c ℓ) = cong (λ x → LocApp x ℓ) (locRen∘ ξ1 ξ2 c)
locRen∘ ξ1 ξ2 (TellLet ℓ ρ1 c ρ2 c₁) = cong₂ (λ x y → TellLet ℓ ρ1 x ρ2 y) (locRen∘ ξ1 ξ2 c) (locRen∘ ξ1 ξ2 c₁)