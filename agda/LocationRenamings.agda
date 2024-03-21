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

module LocationRenamings
  (E : Language)
  (LE : LawfulLanguage E)
  (LocVal : Set)
  (≡-dec-LocVal : DecidableEquality LocVal)
  where

open import Choreographies E LE LocVal ≡-dec-LocVal
open Language E
open LawfulLanguage LE

--- Locations

-- Rename a location
renLoc-Loc : Loc → (ℕ → ℕ) → Loc
renLoc-Loc (Var x) ξ = Var (ξ x)
renLoc-Loc (Lit L) ξ = Lit L

-- Renaming locations respects extensional equality
renLocExt-Loc : ∀{ξ1 ξ2} →
                (∀ n → ξ1 n ≡ ξ2 n) →
                ∀ ℓ → renLoc-Loc ℓ ξ1 ≡ renLoc-Loc ℓ ξ2
renLocExt-Loc ξ1≈ξ2 (Var x) = cong Var (ξ1≈ξ2 x)
renLocExt-Loc ξ1≈ξ2 (Lit L) = refl

-- Renaming locations enjoys fusion
renLoc∘-Loc : ∀ ξ1 ξ2 ℓ → renLoc-Loc ℓ (ξ2 ∘ ξ1) ≡ renLoc-Loc (renLoc-Loc ℓ ξ1) ξ2
renLoc∘-Loc ξ1 ξ2 (Var x) = refl
renLoc∘-Loc ξ1 ξ2 (Lit L) = refl

--- Location lists

-- Rename a location list
renLoc-List : LocList → (ℕ → ℕ) → LocList
renLoc-List ℓs ξ = Data.List.map (λ ℓ → renLoc-Loc ℓ ξ) ℓs

-- Renaming location lists respects extensional equality
renLocExt-List : ∀{ξ1 ξ2} →
                (∀ n → ξ1 n ≡ ξ2 n) →
                ∀ ρ → renLoc-List ρ ξ1 ≡ renLoc-List ρ ξ2
renLocExt-List ξ1≈ξ2 [] = refl
renLocExt-List ξ1≈ξ2 (ℓ ∷ ρ) = cong₂ _∷_ (renLocExt-Loc ξ1≈ξ2 ℓ) (renLocExt-List ξ1≈ξ2 ρ)

-- Renaming location lists enjoys fusion
renLoc∘-List : ∀ ξ1 ξ2 ρ → renLoc-List ρ (ξ2 ∘ ξ1) ≡ renLoc-List (renLoc-List ρ ξ1) ξ2
renLoc∘-List ξ1 ξ2 [] = refl
renLoc∘-List ξ1 ξ2 (ℓ ∷ ρ) = cong₂ _∷_ (renLoc∘-Loc ξ1 ξ2 ℓ) (renLoc∘-List ξ1 ξ2 ρ)

--- Choreographies

-- Rename the locations in a choreography
renLoc : Chor → (ℕ → ℕ) → Chor
renLoc (Done ℓ e) ξ = Done (renLoc-Loc ℓ ξ) e
renLoc (Var x) ξ = Var x
renLoc (Send ℓ1 c ℓ2) ξ = Send (renLoc-Loc ℓ1 ξ) (renLoc c ξ) (renLoc-Loc ℓ2 ξ)
renLoc (If ℓ c c₁ c₂) ξ = If (renLoc-Loc ℓ ξ) (renLoc c ξ) (renLoc c₁ ξ) (renLoc c₂ ξ)
renLoc (Sync ℓ1 d ℓ2 c) ξ = Sync (renLoc-Loc ℓ1 ξ) d (renLoc-Loc ℓ2 ξ) (renLoc c ξ)
renLoc (DefLocal ℓ c c₁) ξ = DefLocal (renLoc-Loc ℓ ξ) (renLoc c ξ) (renLoc c₁ ξ)
renLoc (Fun c) ξ = Fun (renLoc c ξ)
renLoc (App c1 c2) ξ = App (renLoc c1 ξ) (renLoc c2 ξ)
renLoc (LocAbs c) ξ = LocAbs (renLoc c (upRen ξ))
renLoc (LocApp c ℓ) ξ = LocApp (renLoc c ξ) (renLoc-Loc ℓ ξ)
renLoc (TellLet ℓ ρ1 c ρ2 c₁) ξ = TellLet (renLoc-Loc ℓ ξ) (renLoc-List ρ1 ξ) (renLoc c ξ) (renLoc-List ρ2 ξ) (renLoc c₁ ξ)

-- Renaming locations respects extensional equality
renLocExt : ∀{ξ1 ξ2} →
            (∀ n → ξ1 n ≡ ξ2 n) →
            ∀ c → renLoc c ξ1 ≡ renLoc c ξ2
renLocExt ξ1≈ξ2 (Done ℓ e) = cong₂ Done (renLocExt-Loc ξ1≈ξ2 ℓ) refl
renLocExt ξ1≈ξ2 (Var x) = refl
renLocExt ξ1≈ξ2 (Send ℓ1 c ℓ2) = cong₃ Send (renLocExt-Loc ξ1≈ξ2 ℓ1) (renLocExt ξ1≈ξ2 c) (renLocExt-Loc ξ1≈ξ2 ℓ2)
renLocExt ξ1≈ξ2 (If ℓ c c₁ c₂) = cong₄ If (renLocExt-Loc ξ1≈ξ2 ℓ) (renLocExt ξ1≈ξ2 c) (renLocExt ξ1≈ξ2 c₁) (renLocExt ξ1≈ξ2 c₂)
renLocExt ξ1≈ξ2 (Sync ℓ1 d ℓ2 c) = cong₄ Sync (renLocExt-Loc ξ1≈ξ2 ℓ1) refl (renLocExt-Loc ξ1≈ξ2 ℓ2) (renLocExt ξ1≈ξ2 c)
renLocExt ξ1≈ξ2 (DefLocal ℓ c c₁) = cong₃ DefLocal (renLocExt-Loc ξ1≈ξ2 ℓ) (renLocExt ξ1≈ξ2 c) (renLocExt ξ1≈ξ2 c₁)
renLocExt ξ1≈ξ2 (Fun c) = cong Fun (renLocExt ξ1≈ξ2 c)
renLocExt ξ1≈ξ2 (App c c₁) = cong₂ App (renLocExt ξ1≈ξ2 c) (renLocExt ξ1≈ξ2 c₁)
renLocExt ξ1≈ξ2 (LocAbs c) = cong LocAbs (renLocExt (upRenExt ξ1≈ξ2) c)
renLocExt ξ1≈ξ2 (LocApp c ℓ) = cong₂ LocApp (renLocExt ξ1≈ξ2 c) (renLocExt-Loc ξ1≈ξ2 ℓ)
renLocExt ξ1≈ξ2 (TellLet ℓ ρ1 c ρ2 c₁) = cong₅ TellLet
    (renLocExt-Loc ξ1≈ξ2 ℓ) (renLocExt-List ξ1≈ξ2 ρ1) (renLocExt ξ1≈ξ2 c) (renLocExt-List ξ1≈ξ2 ρ2) (renLocExt ξ1≈ξ2 c₁)

-- Renaming locations enjoys fusion
renLoc∘ :  ∀ ξ1 ξ2 c → renLoc c (ξ2 ∘ ξ1) ≡ renLoc (renLoc c ξ1) ξ2
renLoc∘ ξ1 ξ2 (Done ℓ e) = cong₂ Done (renLoc∘-Loc ξ1 ξ2 ℓ) refl
renLoc∘ ξ1 ξ2 (Var x) = refl
renLoc∘ ξ1 ξ2 (Send ℓ1 c ℓ2) = cong₃ Send (renLoc∘-Loc ξ1 ξ2 ℓ1) (renLoc∘ ξ1 ξ2 c) (renLoc∘-Loc ξ1 ξ2 ℓ2)
renLoc∘ ξ1 ξ2 (If ℓ c c₁ c₂) = cong₄ If (renLoc∘-Loc ξ1 ξ2 ℓ) (renLoc∘ ξ1 ξ2 c) (renLoc∘ ξ1 ξ2 c₁) (renLoc∘ ξ1 ξ2 c₂)
renLoc∘ ξ1 ξ2 (Sync ℓ1 d ℓ2 c) = cong₄ Sync (renLoc∘-Loc ξ1 ξ2 ℓ1) refl (renLoc∘-Loc ξ1 ξ2 ℓ2) (renLoc∘ ξ1 ξ2 c)
renLoc∘ ξ1 ξ2 (DefLocal ℓ c c₁) = cong₃ DefLocal (renLoc∘-Loc ξ1 ξ2 ℓ) (renLoc∘ ξ1 ξ2 c) (renLoc∘ ξ1 ξ2 c₁)
renLoc∘ ξ1 ξ2 (Fun c) = cong Fun (renLoc∘ ξ1 ξ2 c)
renLoc∘ ξ1 ξ2 (App c c₁) = cong₂ App (renLoc∘ ξ1 ξ2 c) (renLoc∘ ξ1 ξ2 c₁)
renLoc∘ ξ1 ξ2 (LocAbs c) = cong LocAbs c⟨ξ2∘ξ⟩≡c⟨ξ1⟩⟨ξ2⟩
    where
    c⟨ξ2∘ξ⟩≡c⟨ξ1⟩⟨ξ2⟩ : renLoc c (upRen (ξ2 ∘ ξ1)) ≡ renLoc (renLoc c (upRen ξ1)) (upRen ξ2)
    c⟨ξ2∘ξ⟩≡c⟨ξ1⟩⟨ξ2⟩ =
        renLoc c (upRen (ξ2 ∘ ξ1))              ≡⟨ renLocExt (upRen∘ ξ1 ξ2) c ⟩
        renLoc c (upRen ξ2 ∘ upRen ξ1)          ≡⟨ renLoc∘ (upRen ξ1) (upRen ξ2) c ⟩
        renLoc (renLoc c (upRen ξ1)) (upRen ξ2) ∎
renLoc∘ ξ1 ξ2 (LocApp c ℓ) = cong₂ LocApp (renLoc∘ ξ1 ξ2 c) (renLoc∘-Loc ξ1 ξ2 ℓ)
renLoc∘ ξ1 ξ2 (TellLet ℓ ρ1 c ρ2 c₁) = cong₅ TellLet
    (renLoc∘-Loc ξ1 ξ2 ℓ) (renLoc∘-List ξ1 ξ2 ρ1) (renLoc∘ ξ1 ξ2 c) (renLoc∘-List ξ1 ξ2 ρ2) (renLoc∘ ξ1 ξ2 c₁)
