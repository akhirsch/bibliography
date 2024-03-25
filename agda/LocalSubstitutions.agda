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
open import Locations

module LocalSubstitutions
  (L : Location)
  (E : Language L)
  (LE : LawfulLanguage L E)
  where

open import Choreographies L E
open import Renamings L E LE
open import LocalRenamings L E LE
open Location L
open Language E
open LawfulLanguage LE

LocalSubst : Set
LocalSubst = Loc → ℕ → Expr

-- Identity local variable substitution
idSubₗₑ : LocalSubst
idSubₗₑ ℓ n = varₑ n

{-
  Substitution with the topmost variable instantiated
  at a specified location
-}
_▸[_]_ : LocalSubst → Loc → Expr → LocalSubst
(σ ▸[ ℓ ] e) ℓ' with ≡-dec-Loc ℓ ℓ'
... | yes _ = λ{ zero → e ; (suc n) → renₑ (σ ℓ n) suc }
... | no  _ = σ ℓ'

-- Adding a topmost term respects extensional equality
▸Extₗₑ : ∀{σ1 σ2} → σ1 ≈₂ σ2 →
         ∀ ℓ e → σ1 ▸[ ℓ ] e ≈₂ σ2 ▸[ ℓ ] e
▸Extₗₑ σ1≈σ2 ℓ e ℓ' with ≡-dec-Loc ℓ ℓ'
... | yes _ = λ{ zero → refl ; (suc n) → cong₂ renₑ (σ1≈σ2 ℓ n) refl }
... | no  _ = σ1≈σ2 ℓ'

{-
  ↑ on local variable substitutions at a specified location ℓ.
  Used when binding a local variable.
-}
↑σ[_] : Loc → LocalSubst → LocalSubst
↑σ[ ℓ ] σ = σ ▸[ ℓ ] varₑ zero

-- ↑[ℓ] respects extensional equality
↑σ[ℓ]Ext : ∀{σ1 σ2} → σ1 ≈₂ σ2 →
          ∀ ℓ → ↑σ[ ℓ ] σ1 ≈₂ ↑σ[ ℓ ] σ2
↑σ[ℓ]Ext σ1≈σ2 ℓ = ▸Extₗₑ σ1≈σ2 ℓ (varₑ zero)

-- ↑[ℓ] respects the identity
↑σ[ℓ]Id : ∀ ℓ → ↑σ[ ℓ ] idSubₗₑ ≈₂ idSubₗₑ
↑σ[ℓ]Id ℓ ℓ' with ≡-dec-Loc ℓ ℓ'
... | yes _ = λ{ zero → refl ; (suc n) → renVarₑ n suc }
... | no  _ = λ n → refl

{-
  Add a top-most location variable to a local renaming.
  Used when binding a location variable.
-}
↑σₗₑ : LocalSubst → LocalSubst
↑σₗₑ σ (Var zero) = λ n → varₑ n
↑σₗₑ σ (Var (suc x)) = σ (Var x)
↑σₗₑ σ (Lit L) = σ (Lit L)

-- ↑ respects the identity
↑σIdₗₑ : ↑σₗₑ idSubₗₑ ≈₂ idSubₗₑ
↑σIdₗₑ (Var zero) n = refl
↑σIdₗₑ (Var (suc x)) n = refl
↑σIdₗₑ (Lit L) n = refl

-- ↑ respects extensional equality
↑σExtₗₑ : ∀{σ1 σ2} →
          σ1 ≈₂ σ2 →
          ↑σₗₑ σ1 ≈₂ ↑σₗₑ σ2
↑σExtₗₑ ξ1≈ξ2 (Var zero) n = refl
↑σExtₗₑ ξ1≈ξ2 (Var (suc x)) n = ξ1≈ξ2 (Var x) n
↑σExtₗₑ ξ1≈ξ2 (Lit L) n = ξ1≈ξ2 (Lit L) n

-- Substitute local variables in a choreography
subₗₑ : (c : Chor) (σ : LocalSubst) → Chor
subₗₑ (Done ℓ e) σ = Done ℓ (subₑ e (σ ℓ))
subₗₑ (Var x) σ = Var x
subₗₑ (Send ℓ1 c ℓ2) σ = Send ℓ1 (subₗₑ c σ) ℓ2
subₗₑ (If ℓ c c1 c2) σ = If ℓ (subₗₑ c σ) (subₗₑ c1 σ) (subₗₑ c2 σ)
subₗₑ (Sync ℓ1 d ℓ2 c) σ = Sync ℓ1 d ℓ2 (subₗₑ c σ)
subₗₑ (DefLocal ℓ c1 c2) σ = DefLocal ℓ (subₗₑ c1 σ) (subₗₑ c2 (↑σ[ ℓ ] σ))
subₗₑ (Fun c) σ = Fun (subₗₑ c σ)
subₗₑ (Fix c) σ = Fix (subₗₑ c σ)
subₗₑ (App c1 c2) σ = App (subₗₑ c1 σ) (subₗₑ c2 σ)
subₗₑ (LocAbs c) σ = LocAbs (subₗₑ c (↑σₗₑ σ))
subₗₑ (LocApp c ℓ) σ = LocApp (subₗₑ c σ) ℓ
subₗₑ (TellLet ℓ ρ1 c1 ρ2 c2) σ = TellLet ℓ ρ1 (subₗₑ c1 σ) ρ2 (subₗₑ c2 (↑σₗₑ σ))

-- Substituting local variables respects extensional equality
subExtₗₑ : ∀{σ1 σ2} →
          σ1 ≈₂ σ2 →
          ∀ c → subₗₑ c σ1 ≡ subₗₑ c σ2
subExtₗₑ σ1≈σ2 (Done ℓ e) = cong₂ Done refl (subExtₑ (σ1≈σ2 ℓ) e)
subExtₗₑ σ1≈σ2 (Var x) = refl
subExtₗₑ σ1≈σ2 (Send ℓ1 c ℓ2) = cong₃ Send refl (subExtₗₑ σ1≈σ2 c) refl
subExtₗₑ σ1≈σ2 (If ℓ c c₁ c₂) =
  cong₄ If refl (subExtₗₑ σ1≈σ2 c) (subExtₗₑ σ1≈σ2 c₁) (subExtₗₑ σ1≈σ2 c₂)
subExtₗₑ σ1≈σ2 (Sync ℓ1 d ℓ2 c) = cong₄ Sync refl refl refl (subExtₗₑ σ1≈σ2 c)
subExtₗₑ σ1≈σ2 (DefLocal ℓ c1 c2) =
  cong₃ DefLocal refl (subExtₗₑ σ1≈σ2 c1) (subExtₗₑ (↑σ[ℓ]Ext σ1≈σ2 ℓ) c2)
subExtₗₑ σ1≈σ2 (Fun c) = cong Fun (subExtₗₑ σ1≈σ2 c)
subExtₗₑ σ1≈σ2 (Fix c) = cong Fix (subExtₗₑ σ1≈σ2 c)
subExtₗₑ σ1≈σ2 (App c1 c2) = cong₂ App (subExtₗₑ σ1≈σ2 c1) (subExtₗₑ σ1≈σ2 c2)
subExtₗₑ σ1≈σ2 (LocAbs c) = cong LocAbs (subExtₗₑ (↑σExtₗₑ σ1≈σ2) c)
subExtₗₑ σ1≈σ2 (LocApp c ℓ) = cong₂ LocApp (subExtₗₑ σ1≈σ2 c) refl
subExtₗₑ σ1≈σ2 (TellLet ℓ ρ1 c1 ρ2 c2) =
  cong₅ TellLet refl refl (subExtₗₑ σ1≈σ2 c1) refl (subExtₗₑ (↑σExtₗₑ σ1≈σ2) c2)

-- Substituting local variables respects the identity
subIdₗₑ : ∀ c → subₗₑ c idSubₗₑ ≡ c
subIdₗₑ (Done ℓ e) = cong₂ Done refl (subIdₑ e)
subIdₗₑ (Var x) = refl
subIdₗₑ (Send ℓ1 c ℓ2) = cong₃ Send refl (subIdₗₑ c) refl
subIdₗₑ (If ℓ c c₁ c₂) = cong₄ If refl (subIdₗₑ c) (subIdₗₑ c₁) (subIdₗₑ c₂)
subIdₗₑ (Sync ℓ1 d ℓ2 c) = cong₄ Sync refl refl refl (subIdₗₑ c)
subIdₗₑ (DefLocal ℓ c1 c2) = cong₃ DefLocal refl (subIdₗₑ c1) c2⟨↑[ℓ]id⟩≡c2
  where
  c2⟨↑[ℓ]id⟩≡c2 : subₗₑ c2 (↑σ[ ℓ ] idSubₗₑ) ≡ c2
  c2⟨↑[ℓ]id⟩≡c2 = 
    subₗₑ c2 (↑σ[ ℓ ] idSubₗₑ) ≡⟨ subExtₗₑ (↑σ[ℓ]Id ℓ) c2 ⟩
    subₗₑ c2 idSubₗₑ           ≡⟨ subIdₗₑ c2 ⟩
    c2                        ∎
subIdₗₑ (Fun c) = cong Fun (subIdₗₑ c)
subIdₗₑ (Fix c) = cong Fix (subIdₗₑ c)
subIdₗₑ (App c1 c2) = cong₂ App (subIdₗₑ c1) (subIdₗₑ c2)
subIdₗₑ (LocAbs c) = cong LocAbs c⟨↑id⟩≡c
  where
  c⟨↑id⟩≡c : subₗₑ c (↑σₗₑ idSubₗₑ) ≡ c
  c⟨↑id⟩≡c =
    subₗₑ c (↑σₗₑ idSubₗₑ) ≡⟨ subExtₗₑ ↑σIdₗₑ c ⟩
    subₗₑ c idSubₗₑ        ≡⟨ subIdₗₑ c ⟩
    c                      ∎
subIdₗₑ (LocApp c ℓ) = cong₂ LocApp (subIdₗₑ c) refl
subIdₗₑ (TellLet ℓ ρ1 c1 ρ2 c2) =
  cong₅ TellLet refl refl (subIdₗₑ c1) refl c2⟨↑id⟩≡c2
  where
  c2⟨↑id⟩≡c2 : subₗₑ c2 (↑σₗₑ idSubₗₑ) ≡ c2
  c2⟨↑id⟩≡c2 =
    subₗₑ c2 (↑σₗₑ idSubₗₑ) ≡⟨ subExtₗₑ ↑σIdₗₑ c2 ⟩
    subₗₑ c2 idSubₗₑ        ≡⟨ subIdₗₑ c2 ⟩
    c2                      ∎

-- Inclusion from renamings to substitutions
ιₗₑ : (Loc → ℕ → ℕ) → LocalSubst
ιₗₑ ξ ℓ n = varₑ (ξ ℓ n)

-- ↑[ℓ] commutes with the inclusion
↑σ[ℓ]ιₗₑ : ∀ ξ ℓ → ↑σ[ ℓ ] (ιₗₑ ξ) ≈₂ ιₗₑ (↑[ ℓ ] ξ)
↑σ[ℓ]ιₗₑ ξ ℓ ℓ' with ≡-dec-Loc ℓ ℓ'
... | yes refl = λ{ zero → refl ; (suc n) → renVarₑ (ξ ℓ n) suc }
... | no  _ = λ n → refl

-- ↑ commutes with the inclusion
↑σιₗₑ : ∀ ξ → ↑σₗₑ (ιₗₑ ξ) ≈₂ ιₗₑ (↑ₗₑ ξ)
↑σιₗₑ ξ (Var zero) n = refl
↑σιₗₑ ξ (Var (suc x)) n = refl
↑σιₗₑ ξ (Lit L) n = refl

-- Substitution respects the inclusion
subιₗₑ : ∀ ξ c → subₗₑ c (ιₗₑ ξ) ≡ renₗₑ c ξ
subιₗₑ ξ (Done ℓ e) = cong₂ Done refl (subRenₑ (ξ ℓ) e)
subιₗₑ ξ (Var x) = refl
subιₗₑ ξ (Send ℓ1 c ℓ2) = cong₃ Send refl (subιₗₑ ξ c) refl
subιₗₑ ξ (If ℓ c c₁ c₂) = cong₄ If refl (subιₗₑ ξ c) (subιₗₑ ξ c₁) (subιₗₑ ξ c₂)
subιₗₑ ξ (Sync ℓ1 d ℓ2 c) = cong₄ Sync refl refl refl (subιₗₑ ξ c)
subιₗₑ ξ (DefLocal ℓ c1 c2) = cong₃ DefLocal refl (subιₗₑ ξ c1) c2⟨↑[ℓ]ιξ⟩≡c2⟨↑[ℓ]ξ⟩
  where
  c2⟨↑[ℓ]ιξ⟩≡c2⟨↑[ℓ]ξ⟩ : subₗₑ c2 (↑σ[ ℓ ] (ιₗₑ ξ)) ≡ renₗₑ c2 (↑[ ℓ ] ξ)
  c2⟨↑[ℓ]ιξ⟩≡c2⟨↑[ℓ]ξ⟩ = 
    subₗₑ c2 (↑σ[ ℓ ] (ιₗₑ ξ)) ≡⟨ subExtₗₑ (↑σ[ℓ]ιₗₑ ξ ℓ) c2 ⟩
    subₗₑ c2 (ιₗₑ (↑[ ℓ ] ξ))  ≡⟨ subιₗₑ (↑[ ℓ ] ξ) c2 ⟩
    renₗₑ c2 (↑[ ℓ ] ξ)       ∎
subιₗₑ ξ (Fun c) = cong Fun (subιₗₑ ξ c)
subιₗₑ ξ (Fix c) = cong Fix (subιₗₑ ξ c)
subιₗₑ ξ (App c1 c2) = cong₂ App (subιₗₑ ξ c1) (subιₗₑ ξ c2)
subιₗₑ ξ (LocAbs c) = cong LocAbs c⟨↑ιξ⟩≡c⟨ξ⟩
  where
  c⟨↑ιξ⟩≡c⟨ξ⟩ : subₗₑ c (↑σₗₑ (ιₗₑ ξ)) ≡ renₗₑ c (↑ₗₑ ξ)
  c⟨↑ιξ⟩≡c⟨ξ⟩ =
    subₗₑ c (↑σₗₑ (ιₗₑ ξ)) ≡⟨ subExtₗₑ (↑σιₗₑ ξ) c ⟩
    subₗₑ c (ιₗₑ (↑ₗₑ ξ))  ≡⟨ subιₗₑ (↑ₗₑ ξ) c ⟩
    renₗₑ c (↑ₗₑ ξ)        ∎
subιₗₑ ξ (LocApp c ℓ) = cong₂ LocApp (subιₗₑ ξ c) refl
subιₗₑ ξ (TellLet ℓ ρ1 c1 ρ2 c2) =
  cong₅ TellLet refl refl (subιₗₑ ξ c1) refl c2⟨↑ιξ⟩≡c2⟨ξ⟩
  where
  c2⟨↑ιξ⟩≡c2⟨ξ⟩ : subₗₑ c2 (↑σₗₑ (ιₗₑ ξ)) ≡ renₗₑ c2 (↑ₗₑ ξ)
  c2⟨↑ιξ⟩≡c2⟨ξ⟩ =
    subₗₑ c2 (↑σₗₑ (ιₗₑ ξ)) ≡⟨ subExtₗₑ (↑σιₗₑ ξ) c2 ⟩
    subₗₑ c2 (ιₗₑ (↑ₗₑ ξ))  ≡⟨ subιₗₑ (↑ₗₑ ξ) c2 ⟩
    renₗₑ c2 (↑ₗₑ ξ)        ∎