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

module Substitutions
  (E : Language)
  (LE : LawfulLanguage E)
  (LocVal : Set)
  (≡-dec-LocVal : DecidableEquality LocVal)
  where

open import Choreographies E LE LocVal ≡-dec-LocVal
open Language E
open LawfulLanguage LE
open import Renamings E LE LocVal ≡-dec-LocVal


-- Identity substitution
idSub : ℕ → Chor
idSub n = Var n

-- The `up` construction on substitutions
↑σ : (σ : ℕ → Chor) → ℕ → Chor
↑σ σ zero = Var zero
↑σ σ (suc n) = ren (σ n) suc

-- The `up` construction respects extensional equality
↑σExt : ∀{σ1 σ2} → σ1 ≈ σ2 → ↑σ σ1 ≈ ↑σ σ2
↑σExt σ1≈σ2 zero = refl
↑σExt σ1≈σ2 (suc n) = cong₂ ren (σ1≈σ2 n) refl

-- The `up` construction respects the identity
↑σId : ↑σ idSub ≈ idSub
↑σId zero = refl
↑σId (suc n) = refl

-- Substituting global variables
sub : (c : Chor) (σ : ℕ → Chor) → Chor
sub (Done ℓ e) σ = Done ℓ e
sub (Var x) σ = σ x
sub (Send ℓ1 c ℓ2) σ = Send ℓ1 (sub c σ) ℓ2
sub (If ℓ c c₁ c₂) σ = If ℓ (sub c σ) (sub c₁ σ) (sub c₂ σ)
sub (Sync ℓ1 d ℓ2 c) σ = Sync ℓ1 d ℓ2 (sub c σ)
sub (DefLocal ℓ c c₁) σ = DefLocal ℓ (sub c σ) (sub c₁ σ)
sub (Fun c) σ = Fun (sub c (↑σ σ))
sub (Fix c) σ = Fix (sub c (↑σ σ))
sub (App c1 c2) σ = App (sub c1 σ) (sub c2 σ)
sub (LocAbs c) σ = LocAbs (sub c σ)
sub (LocApp c ℓ) σ = LocApp (sub c σ) ℓ
sub (TellLet ℓ ρ1 c ρ2 c₁) σ = TellLet ℓ ρ1 (sub c σ) ρ2 (sub c₁ σ)

-- Substituting global variables respects extensional equality
subExt : ∀{σ1 σ2} →
         σ1 ≈ σ2 →
         ∀ c → sub c σ1 ≡ sub c σ2
subExt σ1≈σ2 (Done ℓ e) = refl
subExt σ1≈σ2 (Var x) = σ1≈σ2 x
subExt σ1≈σ2 (Send ℓ1 c ℓ2) = cong₃ Send refl (subExt σ1≈σ2 c) refl
subExt σ1≈σ2 (If ℓ c c₁ c₂) = cong₄ If refl (subExt σ1≈σ2 c) (subExt σ1≈σ2 c₁) (subExt σ1≈σ2 c₂)
subExt σ1≈σ2 (Sync ℓ1 d ℓ2 c) = cong₄ Sync refl refl refl (subExt σ1≈σ2 c)
subExt σ1≈σ2 (DefLocal ℓ c c₁) = cong₃ DefLocal refl (subExt σ1≈σ2 c) (subExt σ1≈σ2 c₁)
subExt σ1≈σ2 (Fun c) = cong Fun (subExt (↑σExt σ1≈σ2) c)
subExt σ1≈σ2 (Fix c) = cong Fix (subExt (↑σExt σ1≈σ2) c)
subExt σ1≈σ2 (App c1 c2) = cong₂ App (subExt σ1≈σ2 c1) (subExt σ1≈σ2 c2)
subExt σ1≈σ2 (LocAbs c) = cong LocAbs (subExt σ1≈σ2 c)
subExt σ1≈σ2 (LocApp c ℓ) = cong₂ LocApp (subExt σ1≈σ2 c) refl
subExt σ1≈σ2 (TellLet ℓ ρ1 c ρ2 c₁) = cong₅ TellLet refl refl (subExt σ1≈σ2 c) refl (subExt σ1≈σ2 c₁)

-- Substituting global variables respects the identity
subId : ∀ c → sub c idSub ≡ c
subId (Done ℓ e) = refl
subId (Var x) = refl
subId (Send ℓ1 c ℓ2) = cong₃ Send refl (subId c) refl
subId (If ℓ c c₁ c₂) = cong₄ If refl (subId c) (subId c₁) (subId c₂)
subId (Sync ℓ1 d ℓ2 c) = cong₄ Sync refl refl refl (subId c)
subId (DefLocal ℓ c c₁) = cong₃ DefLocal refl (subId c) (subId c₁)
subId (Fun c) = cong Fun c⟨↑id⟩≡c
  where
  c⟨↑id⟩≡c : sub c (↑σ idSub) ≡ c
  c⟨↑id⟩≡c = 
    sub c (↑σ idSub) ≡⟨ subExt ↑σId c ⟩
    sub c idSub      ≡⟨ subId c ⟩
    c                ∎
subId (Fix c) = cong Fix c⟨↑id⟩≡c
  where
  c⟨↑id⟩≡c : sub c (↑σ idSub) ≡ c
  c⟨↑id⟩≡c = 
    sub c (↑σ idSub) ≡⟨ subExt ↑σId c ⟩
    sub c idSub      ≡⟨ subId c ⟩
    c                ∎
subId (App c1 c2) = cong₂ App (subId c1) (subId c2)
subId (LocAbs c) = cong LocAbs (subId c)
subId (LocApp c ℓ) = cong₂ LocApp (subId c) refl
subId (TellLet ℓ ρ1 c ρ2 c₁) = cong₅ TellLet refl refl (subId c) refl (subId c₁)

-- Inclusion from renamings to substitutions
ι : (ℕ → ℕ) → ℕ → Chor
ι ξ n = Var (ξ n)

-- The `up` construction commutes with the inclusion
↑σι : ∀ ξ → ↑σ (ι ξ) ≈ ι (↑ ξ)
↑σι ξ zero = refl
↑σι ξ (suc n) = refl

-- Substitution along an inclusion is the same as a renaming
subι : ∀ ξ c → sub c (ι ξ) ≡ ren c ξ
subι ξ (Done ℓ e) = refl
subι ξ (Var x) = refl
subι ξ (Send ℓ1 c ℓ2) = cong₃ Send refl (subι ξ c) refl
subι ξ (If ℓ c c₁ c₂) = cong₄ If refl (subι ξ c) (subι ξ c₁) (subι ξ c₂)
subι ξ (Sync ℓ1 d ℓ2 c) = cong₄ Sync refl refl refl (subι ξ c)
subι ξ (DefLocal ℓ c c₁) = cong₃ DefLocal refl (subι ξ c) (subι ξ c₁)
subι ξ (Fun c) = cong Fun c⟨↑ιξ⟩≡c⟨↑ξ⟩
  where
  c⟨↑ιξ⟩≡c⟨↑ξ⟩ : sub c (↑σ (ι ξ)) ≡ ren c (↑ ξ)
  c⟨↑ιξ⟩≡c⟨↑ξ⟩ = 
    sub c (↑σ (ι ξ)) ≡⟨ subExt (↑σι ξ) c ⟩
    sub c (ι (↑ ξ))  ≡⟨ subι (↑ ξ) c ⟩
    ren c (↑ ξ)      ∎
subι ξ (Fix c) = cong Fix c⟨↑ιξ⟩≡c⟨↑ξ⟩
  where
  c⟨↑ιξ⟩≡c⟨↑ξ⟩ : sub c (↑σ (ι ξ)) ≡ ren c (↑ ξ)
  c⟨↑ιξ⟩≡c⟨↑ξ⟩ = 
    sub c (↑σ (ι ξ)) ≡⟨ subExt (↑σι ξ) c ⟩
    sub c (ι (↑ ξ))  ≡⟨ subι (↑ ξ) c ⟩
    ren c (↑ ξ)      ∎
subι ξ (App c1 c2) = cong₂ App (subι ξ c1) (subι ξ c2)
subι ξ (LocAbs c) = cong LocAbs (subι ξ c)
subι ξ (LocApp c ℓ) = cong₂ LocApp (subι ξ c) refl
subι ξ (TellLet ℓ ρ1 c ρ2 c₁) = cong₅ TellLet refl refl (subι ξ c) refl (subι ξ c₁)