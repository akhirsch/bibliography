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
  (E : TypedLocalLanguage L)
  where

open import Types L E
open import Choreographies L E
open import LocationRenamings L E
open import LocalRenamings L E
open import Renamings L E
open import LocalContexts L E

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
↑σ σ = (λ n → ren suc (σ n)) ▸ Var zero

-- ↑ respects extensional equality
↑σExt : ∀{σ1 σ2} → σ1 ≈ σ2 → ↑σ σ1 ≈ ↑σ σ2
↑σExt σ1≈σ2 zero = refl
↑σExt σ1≈σ2 (suc n) = cong₂ ren refl (σ1≈σ2 n)

-- ↑ respects the identity
↑σId : ↑σ idSub ≈ idSub
↑σId zero = refl
↑σId (suc n) = refl

-- Substituting global variables
sub : (ℕ → Chor) → Chor → Chor
sub σ (Done ℓ e) = Done ℓ e
sub σ (Var x) = σ x
sub σ (Send ℓ1 c ℓ2) = Send ℓ1 (sub σ c) ℓ2
sub σ (If ℓ c c₁ c₂) = If ℓ (sub σ c) (sub σ c₁) (sub σ c₂)
sub σ (Sync ℓ1 d ℓ2 c) = Sync ℓ1 d ℓ2 (sub σ c)
sub σ (DefLocal ℓ t c1 c2) =
  DefLocal ℓ t (sub σ c1) (sub (renₗₑ (Drop Id ℓ t) ∘ σ) c2)
sub σ (Fun τ c) = Fun τ (sub (↑σ σ) c)
sub σ (Fix τ c) = Fix τ (sub (↑σ σ) c)
sub σ (App c1 c2) = App (sub σ c1) (sub σ c2)
sub σ (LocAbs c) = LocAbs (sub (renₗ suc ∘ σ) c)
sub σ (LocApp c ℓ) = LocApp (sub σ c) ℓ
sub σ (TellLet ℓ ρ1 c1 ρ2 c2) =
  TellLet ℓ ρ1 (sub σ c1) ρ2 (sub (renₗ suc ∘ σ) c2)

-- Substituting global variables respects extensional equality
subExt : ∀{σ1 σ2} →
         σ1 ≈ σ2 →
         sub σ1 ≈ sub σ2
subExt σ1≈σ2 (Done ℓ e) = refl
subExt σ1≈σ2 (Var x) = σ1≈σ2 x
subExt σ1≈σ2 (Send ℓ1 c ℓ2) = cong₃ Send refl (subExt σ1≈σ2 c) refl
subExt σ1≈σ2 (If ℓ c c₁ c₂) = cong₄ If refl (subExt σ1≈σ2 c) (subExt σ1≈σ2 c₁) (subExt σ1≈σ2 c₂)
subExt σ1≈σ2 (Sync ℓ1 d ℓ2 c) = cong₄ Sync refl refl refl (subExt σ1≈σ2 c)
subExt σ1≈σ2 (DefLocal ℓ t c1 c2) =
  cong₄ DefLocal refl refl (subExt σ1≈σ2 c1)
    (subExt (λ n → cong (renₗₑ (Drop Id ℓ t)) (σ1≈σ2 n)) c2)
subExt σ1≈σ2 (Fun τ c) = cong₂ Fun refl (subExt (↑σExt σ1≈σ2) c)
subExt σ1≈σ2 (Fix τ c) = cong₂ Fix refl (subExt (↑σExt σ1≈σ2) c)
subExt σ1≈σ2 (App c1 c2) = cong₂ App (subExt σ1≈σ2 c1) (subExt σ1≈σ2 c2)
subExt σ1≈σ2 (LocAbs c) = cong LocAbs (subExt (λ n → cong (renₗ suc) (σ1≈σ2 n)) c)
subExt σ1≈σ2 (LocApp c ℓ) = cong₂ LocApp (subExt σ1≈σ2 c) refl
subExt σ1≈σ2 (TellLet ℓ ρ1 c1 ρ2 c2) =
  cong₅ TellLet refl refl (subExt σ1≈σ2 c1) refl (subExt (λ n → cong (renₗ suc) (σ1≈σ2 n)) c2)

-- Substituting global variables respects the identity
subId : ∀ c → sub idSub c ≡ c
subId (Done ℓ e) = refl
subId (Var x) = refl
subId (Send ℓ1 c ℓ2) = cong₃ Send refl (subId c) refl
subId (If ℓ c c₁ c₂) = cong₄ If refl (subId c) (subId c₁) (subId c₂)
subId (Sync ℓ1 d ℓ2 c) = cong₄ Sync refl refl refl (subId c)
subId (DefLocal ℓ t C1 C2) = cong₄ DefLocal refl refl (subId C1) (subId C2)
subId (Fun τ c) = cong₂ Fun refl c⟨↑id⟩≡c
  where
  c⟨↑id⟩≡c : sub (↑σ idSub) c ≡ c
  c⟨↑id⟩≡c = 
    sub (↑σ idSub) c ≡⟨ subExt ↑σId c ⟩
    sub idSub c      ≡⟨ subId c ⟩
    c                ∎
subId (Fix τ c) = cong₂ Fix refl c⟨↑id⟩≡c
  where
  c⟨↑id⟩≡c : sub (↑σ idSub) c ≡ c
  c⟨↑id⟩≡c = 
    sub (↑σ idSub) c ≡⟨ subExt ↑σId c ⟩
    sub idSub c      ≡⟨ subId c ⟩
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
subι : ∀ ξ c → sub (ι ξ) c ≡ ren ξ c
subι ξ (Done ℓ e) = refl
subι ξ (Var x) = refl
subι ξ (Send ℓ1 c ℓ2) = cong₃ Send refl (subι ξ c) refl
subι ξ (If ℓ c c1 c2) = cong₄ If refl (subι ξ c) (subι ξ c1) (subι ξ c2)
subι ξ (Sync ℓ1 d ℓ2 c) = cong₄ Sync refl refl refl (subι ξ c)
subι ξ (DefLocal ℓ t C1 C2) = cong₄ DefLocal refl refl (subι ξ C1) (subι ξ C2)
subι ξ (Fun τ c) = cong₂ Fun refl c⟨↑ιξ⟩≡c⟨↑ξ⟩
  where
  c⟨↑ιξ⟩≡c⟨↑ξ⟩ : sub (↑σ (ι ξ)) c ≡ ren (↑ ξ) c
  c⟨↑ιξ⟩≡c⟨↑ξ⟩ = 
    sub (↑σ (ι ξ)) c ≡⟨ subExt (↑σι ξ) c ⟩
    sub (ι (↑ ξ)) c  ≡⟨ subι (↑ ξ) c ⟩
    ren (↑ ξ) c      ∎
subι ξ (Fix τ c) = cong₂ Fix refl c⟨↑ιξ⟩≡c⟨↑ξ⟩
  where
  c⟨↑ιξ⟩≡c⟨↑ξ⟩ : sub (↑σ (ι ξ)) c ≡ ren (↑ ξ) c
  c⟨↑ιξ⟩≡c⟨↑ξ⟩ = 
    sub (↑σ (ι ξ)) c ≡⟨ subExt (↑σι ξ) c ⟩
    sub (ι (↑ ξ)) c  ≡⟨ subι (↑ ξ) c ⟩
    ren (↑ ξ) c      ∎
subι ξ (App c1 c2) = cong₂ App (subι ξ c1) (subι ξ c2)
subι ξ (LocAbs c) = cong LocAbs (subι ξ c)
subι ξ (LocApp c ℓ) = cong₂ LocApp (subι ξ c) refl
subι ξ (TellLet ℓ ρ1 c1 ρ2 c2) = cong₅ TellLet refl refl (subι ξ c1) refl (subι ξ c2)

