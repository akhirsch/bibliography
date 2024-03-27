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

module Substitutions
  (L : Location)
  (E : Language L)
  (LE : LawfulLanguage L E)
  (TE : TypedLocalLanguage L E LE)
  where

open import Types L E LE TE
open import Choreographies L E LE TE
open import LocationRenamings L E LE TE
open import LocalRenamings L E LE TE
open import Renamings L E LE TE

-- Identity substitution
idSub : ℕ → Chor
idSub n = Var n

-- Substitution with the topmost variable instantiated 
_▸_ : (ℕ → Chor) → Chor → ℕ → Chor
(σ ▸ c) zero = c
(σ ▸ c) (suc n) = σ n

-- Adding a topmost term respects extensional equality
▸Ext : ∀{σ1 σ2} → σ1 ≈ σ2 → ∀ c → σ1 ▸ c ≈ σ2 ▸ c
▸Ext σ1≈σ2 c zero = refl
▸Ext σ1≈σ2 c (suc n) = σ1≈σ2 n

-- ↑ on substitutions
↑σ : (ℕ → Chor) → ℕ → Chor
↑σ σ = (λ n → ren (σ n) suc) ▸ Var zero

-- ↑ respects extensional equality
↑σExt : ∀{σ1 σ2} → σ1 ≈ σ2 → ↑σ σ1 ≈ ↑σ σ2
↑σExt σ1≈σ2 zero = refl
↑σExt σ1≈σ2 (suc n) = cong₂ ren (σ1≈σ2 n) refl

-- ↑ respects the identity
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
sub (DefLocal ℓ c1 c2) σ =
  DefLocal ℓ (sub c1 σ) (sub c2 λ n → renₗₑ (σ n) suc[ ℓ ])
sub (Fun τ c) σ = Fun τ (sub c (↑σ σ))
sub (Fix τ c) σ = Fix τ (sub c (↑σ σ))
sub (App c1 c2) σ = App (sub c1 σ) (sub c2 σ)
sub (LocAbs c) σ = LocAbs (sub c λ n → renₗ (σ n) suc)
sub (LocApp c ℓ) σ = LocApp (sub c σ) ℓ
sub (TellLet ℓ ρ1 c1 ρ2 c2) σ =
  TellLet ℓ ρ1 (sub c1 σ) ρ2 (sub c2 λ n → renₗ (σ n) suc)

-- Substituting global variables respects extensional equality
subExt : ∀{σ1 σ2} →
         σ1 ≈ σ2 →
         ∀ c → sub c σ1 ≡ sub c σ2
subExt σ1≈σ2 (Done ℓ e) = refl
subExt σ1≈σ2 (Var x) = σ1≈σ2 x
subExt σ1≈σ2 (Send ℓ1 c ℓ2) = cong₃ Send refl (subExt σ1≈σ2 c) refl
subExt σ1≈σ2 (If ℓ c c₁ c₂) = cong₄ If refl (subExt σ1≈σ2 c) (subExt σ1≈σ2 c₁) (subExt σ1≈σ2 c₂)
subExt σ1≈σ2 (Sync ℓ1 d ℓ2 c) = cong₄ Sync refl refl refl (subExt σ1≈σ2 c)
subExt σ1≈σ2 (DefLocal ℓ c1 c2) =
  cong₃ DefLocal refl (subExt σ1≈σ2 c1)
    (subExt (λ n → cong (flip renₗₑ ⟨ ℓ ∣ suc ∣ idRenₗₑ ⟩) (σ1≈σ2 n)) c2)
subExt σ1≈σ2 (Fun τ c) = cong₂ Fun refl (subExt (↑σExt σ1≈σ2) c)
subExt σ1≈σ2 (Fix τ c) = cong₂ Fix refl (subExt (↑σExt σ1≈σ2) c)
subExt σ1≈σ2 (App c1 c2) = cong₂ App (subExt σ1≈σ2 c1) (subExt σ1≈σ2 c2)
subExt σ1≈σ2 (LocAbs c) = cong LocAbs (subExt (λ n → cong (flip renₗ suc) (σ1≈σ2 n)) c)
subExt σ1≈σ2 (LocApp c ℓ) = cong₂ LocApp (subExt σ1≈σ2 c) refl
subExt σ1≈σ2 (TellLet ℓ ρ1 c1 ρ2 c2) =
  cong₅ TellLet refl refl (subExt σ1≈σ2 c1) refl (subExt (λ n → cong (flip renₗ suc) (σ1≈σ2 n)) c2)

-- Substituting global variables respects the identity
subId : ∀ c → sub c idSub ≡ c
subId (Done ℓ e) = refl
subId (Var x) = refl
subId (Send ℓ1 c ℓ2) = cong₃ Send refl (subId c) refl
subId (If ℓ c c₁ c₂) = cong₄ If refl (subId c) (subId c₁) (subId c₂)
subId (Sync ℓ1 d ℓ2 c) = cong₄ Sync refl refl refl (subId c)
subId (DefLocal ℓ c c₁) = cong₃ DefLocal refl (subId c) (subId c₁)
subId (Fun τ c) = cong₂ Fun refl c⟨↑id⟩≡c
  where
  c⟨↑id⟩≡c : sub c (↑σ idSub) ≡ c
  c⟨↑id⟩≡c = 
    sub c (↑σ idSub) ≡⟨ subExt ↑σId c ⟩
    sub c idSub      ≡⟨ subId c ⟩
    c                ∎
subId (Fix τ c) = cong₂ Fix refl c⟨↑id⟩≡c
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

-- ↑ commutes with the inclusion
↑σι : ∀ ξ → ↑σ (ι ξ) ≈ ι (↑ ξ)
↑σι ξ zero = refl
↑σι ξ (suc n) = refl

-- The inclusion respects the identity
ιId : ι idRen ≈ idSub
ιId zero = refl
ιId (suc n) = refl

-- Substitution respects the inclusion
subι : ∀ ξ c → sub c (ι ξ) ≡ ren c ξ
subι ξ (Done ℓ e) = refl
subι ξ (Var x) = refl
subι ξ (Send ℓ1 c ℓ2) = cong₃ Send refl (subι ξ c) refl
subι ξ (If ℓ c c1 c2) = cong₄ If refl (subι ξ c) (subι ξ c1) (subι ξ c2)
subι ξ (Sync ℓ1 d ℓ2 c) = cong₄ Sync refl refl refl (subι ξ c)
subι ξ (DefLocal ℓ c1 c2) = cong₃ DefLocal refl (subι ξ c1) (subι ξ c2)
subι ξ (Fun τ c) = cong₂ Fun refl c⟨↑ιξ⟩≡c⟨↑ξ⟩
  where
  c⟨↑ιξ⟩≡c⟨↑ξ⟩ : sub c (↑σ (ι ξ)) ≡ ren c (↑ ξ)
  c⟨↑ιξ⟩≡c⟨↑ξ⟩ = 
    sub c (↑σ (ι ξ)) ≡⟨ subExt (↑σι ξ) c ⟩
    sub c (ι (↑ ξ))  ≡⟨ subι (↑ ξ) c ⟩
    ren c (↑ ξ)      ∎
subι ξ (Fix τ c) = cong₂ Fix refl c⟨↑ιξ⟩≡c⟨↑ξ⟩
  where
  c⟨↑ιξ⟩≡c⟨↑ξ⟩ : sub c (↑σ (ι ξ)) ≡ ren c (↑ ξ)
  c⟨↑ιξ⟩≡c⟨↑ξ⟩ = 
    sub c (↑σ (ι ξ)) ≡⟨ subExt (↑σι ξ) c ⟩
    sub c (ι (↑ ξ))  ≡⟨ subι (↑ ξ) c ⟩
    ren c (↑ ξ)      ∎
subι ξ (App c1 c2) = cong₂ App (subι ξ c1) (subι ξ c2)
subι ξ (LocAbs c) = cong LocAbs (subι ξ c)
subι ξ (LocApp c ℓ) = cong₂ LocApp (subι ξ c) refl
subι ξ (TellLet ℓ ρ1 c1 ρ2 c2) = cong₅ TellLet refl refl (subι ξ c1) refl (subι ξ c2)

