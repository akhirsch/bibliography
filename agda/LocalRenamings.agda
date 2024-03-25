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
open Language E
open LawfulLanguage LE
open Location L

LocalRen : Set
LocalRen = Loc → ℕ → ℕ

idRenₗₑ : LocalRen
idRenₗₑ ℓ = idRenₑ

{-
  ↑ on local variable renamings at a specified location ℓ.
  Used when binding a local variable.
-}
↑[_] : Loc → LocalRen → LocalRen
↑[ ℓ ] ξ ℓ' with ≡-dec-Loc ℓ ℓ'
... | yes _ = ↑ (ξ ℓ')
... | no  _ = ξ ℓ'

-- ↑[ℓ] respects the identity
↑[ℓ]Id : ∀ ℓ → ↑[ ℓ ] idRenₗₑ ≈₂ idRenₗₑ
↑[ℓ]Id ℓ ℓ' n with ≡-dec-Loc ℓ ℓ'
... | yes _ = ↑Idₑ n
... | no  _ = refl

-- ↑[ℓ] enjoys fusion
↑[ℓ]Fuse : ∀ ξ1 ξ2 ℓ → ↑[ ℓ ] (∣ ξ2 ⟫- ξ1) ≈₂ (∣ ↑[ ℓ ] ξ2 ⟫- ↑[ ℓ ] ξ1)
↑[ℓ]Fuse ξ1 ξ2 ℓ ℓ' n with ≡-dec-Loc ℓ ℓ'
... | yes _ = ↑Fuseₑ (ξ1 ℓ') (ξ2 ℓ') n
... | no  _ = refl

-- ↑[ℓ] respects extensional equality
↑[ℓ]Ext : ∀{ξ1 ξ2} →
        ξ1 ≈₂ ξ2 →
        ∀ ℓ → ↑[ ℓ ] ξ1 ≈₂ ↑[ ℓ ] ξ2
↑[ℓ]Ext ξ1≈ξ2 ℓ ℓ' n with ≡-dec-Loc ℓ ℓ'
... | yes _ = ↑Extₑ (ξ1≈ξ2 ℓ') n
... | no  _ = ξ1≈ξ2 ℓ' n

{-
  Add a top-most location variable to a local renaming.
  Used when binding a location variable.
-}
↑ₗₑ : LocalRen → LocalRen
↑ₗₑ ξ (Var zero) n = n
↑ₗₑ ξ (Var (suc x)) n = ξ (Var x) n
↑ₗₑ ξ (Lit L) n = ξ (Lit L) n

-- ↑ respects the identity
↑Idₗₑ : ↑ₗₑ idRenₗₑ ≈₂ idRenₗₑ
↑Idₗₑ (Var zero) n = refl
↑Idₗₑ (Var (suc x)) n = refl
↑Idₗₑ (Lit L) n = refl

-- ↑ enjoys fusion
↑Fuseₗₑ : ∀ ξ1 ξ2 → ↑ₗₑ (∣ ξ2 ⟫- ξ1) ≈₂ (∣ ↑ₗₑ ξ2 ⟫- ↑ₗₑ ξ1)
↑Fuseₗₑ ξ1 ξ2 (Var zero) n = refl
↑Fuseₗₑ ξ1 ξ2 (Var (suc x)) n = refl
↑Fuseₗₑ ξ1 ξ2 (Lit L) n = refl

-- ↑ respects extensional equality
↑Extₗₑ : ∀{ξ1 ξ2} →
         ξ1 ≈₂ ξ2 →
         ↑ₗₑ ξ1 ≈₂ ↑ₗₑ ξ2
↑Extₗₑ ξ1≈ξ2 (Var zero) n = refl
↑Extₗₑ ξ1≈ξ2 (Var (suc x)) n = ξ1≈ξ2 (Var x) n
↑Extₗₑ ξ1≈ξ2 (Lit L) n = ξ1≈ξ2 (Lit L) n

-- Renaming local variables in a choreography
renₗₑ : (c : Chor) (ξ : LocalRen) → Chor
renₗₑ (Done ℓ e) ξ = Done ℓ (renₑ e (ξ ℓ))
renₗₑ (Var x) ξ = Var x
renₗₑ (Send ℓ1 c ℓ2) ξ = Send ℓ1 (renₗₑ c ξ) ℓ2
renₗₑ (If ℓ c c₁ c₂) ξ = If ℓ (renₗₑ c ξ) (renₗₑ c₁ ξ) (renₗₑ c₂ ξ)
renₗₑ (Sync ℓ1 d ℓ2 c) ξ = Sync ℓ1 d ℓ2 (renₗₑ c ξ)
renₗₑ (DefLocal ℓ c1 c2) ξ = DefLocal ℓ (renₗₑ c1 ξ) (renₗₑ c2 (↑[ ℓ ] ξ))
renₗₑ (Fun τ c) ξ = Fun τ (renₗₑ c ξ)
renₗₑ (Fix τ c) ξ = Fix τ (renₗₑ c ξ)
renₗₑ (App c c₁) ξ = App (renₗₑ c ξ) (renₗₑ c₁ ξ)
renₗₑ (LocAbs c) ξ = LocAbs (renₗₑ c (↑ₗₑ ξ))
renₗₑ (LocApp c ℓ) ξ = LocApp (renₗₑ c ξ) ℓ
renₗₑ (TellLet ℓ ρ1 c1 ρ2 c2) ξ = TellLet ℓ ρ1 (renₗₑ c1 ξ) ρ2 (renₗₑ c2 (↑ₗₑ ξ))

-- Renaming local variables respects extensional equality
renExtₗₑ : ∀{ξ1 ξ2} →
          ξ1 ≈₂ ξ2 →
          ∀ c → renₗₑ c ξ1 ≡ renₗₑ c ξ2
renExtₗₑ ξ1≈ξ2 (Done ℓ e) = cong (Done ℓ) (renExtₑ (ξ1≈ξ2 ℓ) e)
renExtₗₑ ξ1≈ξ2 (Var x) = refl
renExtₗₑ ξ1≈ξ2 (Send ℓ1 c ℓ2) = cong₃ Send refl (renExtₗₑ ξ1≈ξ2 c) refl
renExtₗₑ ξ1≈ξ2 (If ℓ c c₁ c₂) =
  cong₃ (If ℓ) (renExtₗₑ ξ1≈ξ2 c) (renExtₗₑ ξ1≈ξ2 c₁) (renExtₗₑ ξ1≈ξ2 c₂)
renExtₗₑ ξ1≈ξ2 (Sync ℓ1 d ℓ2 c) = cong (Sync ℓ1 d ℓ2) (renExtₗₑ ξ1≈ξ2 c)
renExtₗₑ ξ1≈ξ2 (DefLocal ℓ c1 c2) =
  cong₂ (DefLocal ℓ) (renExtₗₑ ξ1≈ξ2 c1) (renExtₗₑ (↑[ℓ]Ext ξ1≈ξ2 ℓ) c2)
renExtₗₑ ξ1≈ξ2 (Fun τ c) = cong₂ Fun refl (renExtₗₑ ξ1≈ξ2 c)
renExtₗₑ ξ1≈ξ2 (Fix τ c) = cong₂ Fix refl (renExtₗₑ ξ1≈ξ2 c)
renExtₗₑ ξ1≈ξ2 (App c c₁) = cong₂ App (renExtₗₑ ξ1≈ξ2 c) (renExtₗₑ ξ1≈ξ2 c₁)
renExtₗₑ ξ1≈ξ2 (LocAbs c) = cong LocAbs (renExtₗₑ (↑Extₗₑ ξ1≈ξ2) c)
renExtₗₑ ξ1≈ξ2 (LocApp c ℓ) = cong₂ LocApp (renExtₗₑ ξ1≈ξ2 c) refl
renExtₗₑ ξ1≈ξ2 (TellLet ℓ ρ1 c1 ρ2 c2) =
  cong₅ TellLet refl refl (renExtₗₑ ξ1≈ξ2 c1) refl (renExtₗₑ (↑Extₗₑ ξ1≈ξ2) c2)

-- Renaming local variables respects the identity
renIdₗₑ : ∀ c → renₗₑ c idRenₗₑ ≡ c
renIdₗₑ (Done ℓ e) = cong (Done ℓ) (renIdₑ e)
renIdₗₑ (Var x) = refl
renIdₗₑ (Send ℓ1 c ℓ2) = cong₃ Send refl (renIdₗₑ c) refl
renIdₗₑ (If ℓ c c₁ c₂) = cong₄ If refl (renIdₗₑ c) (renIdₗₑ c₁) (renIdₗₑ c₂)
renIdₗₑ (Sync ℓ1 d ℓ2 c) = cong (Sync ℓ1 d ℓ2) (renIdₗₑ c)
renIdₗₑ (DefLocal ℓ c1 c2) = cong₂ (DefLocal ℓ) (renIdₗₑ c1) c2⟨↑id⟩≡c2
  where
  c2⟨↑id⟩≡c2 : renₗₑ c2 (↑[ ℓ ] idRenₗₑ) ≡ c2
  c2⟨↑id⟩≡c2 = 
    renₗₑ c2 (↑[ ℓ ] idRenₗₑ) ≡⟨ renExtₗₑ (↑[ℓ]Id ℓ) c2 ⟩
    renₗₑ c2 idRenₗₑ          ≡⟨ renIdₗₑ c2 ⟩
    c2                        ∎
renIdₗₑ (Fun τ c) = cong₂ Fun refl (renIdₗₑ c)
renIdₗₑ (Fix τ c) = cong₂ Fix refl (renIdₗₑ c)
renIdₗₑ (App c c₁) = cong₂ App (renIdₗₑ c) (renIdₗₑ c₁)
renIdₗₑ (LocAbs c) = cong LocAbs c⟨↑Id⟩≡c -- cong LocAbs (renIdₗₑ c)
  where
  open ≡-Reasoning

  c⟨↑Id⟩≡c : renₗₑ c (↑ₗₑ idRenₗₑ) ≡ c
  c⟨↑Id⟩≡c =
    renₗₑ c (↑ₗₑ idRenₗₑ) ≡⟨ renExtₗₑ ↑Idₗₑ c ⟩
    renₗₑ c idRenₗₑ       ≡⟨ renIdₗₑ c ⟩
    c ∎
renIdₗₑ (LocApp c ℓ) = cong₂ LocApp (renIdₗₑ c) refl
renIdₗₑ (TellLet ℓ ρ1 c1 ρ2 c2) =
  cong₅ TellLet refl refl (renIdₗₑ c1) refl c2⟨↑Id⟩≡c2
  where
  open ≡-Reasoning

  c2⟨↑Id⟩≡c2 : renₗₑ c2 (↑ₗₑ idRenₗₑ) ≡ c2
  c2⟨↑Id⟩≡c2 =
    renₗₑ c2 (↑ₗₑ idRenₗₑ) ≡⟨ renExtₗₑ ↑Idₗₑ c2 ⟩
    renₗₑ c2 idRenₗₑ       ≡⟨ renIdₗₑ c2 ⟩
    c2 ∎

-- Renaming local variables enjoys fusion
renFuseₗₑ : ∀ ξ1 ξ2 c → renₗₑ c (∣ ξ2 ⟫- ξ1) ≡ renₗₑ (renₗₑ c ξ1) ξ2
renFuseₗₑ ξ1 ξ2 (Done ℓ e) = cong (Done ℓ) (renFuseₑ (ξ1 ℓ) (ξ2 ℓ) e)
renFuseₗₑ ξ1 ξ2 (Var x) = refl
renFuseₗₑ ξ1 ξ2 (Send ℓ1 c ℓ2) = cong (λ x → Send ℓ1 x ℓ2) (renFuseₗₑ ξ1 ξ2 c)
renFuseₗₑ ξ1 ξ2 (If ℓ c c₁ c₂) = cong₃ (If ℓ) (renFuseₗₑ ξ1 ξ2 c) (renFuseₗₑ ξ1 ξ2 c₁) (renFuseₗₑ ξ1 ξ2 c₂)
renFuseₗₑ ξ1 ξ2 (Sync ℓ1 d ℓ2 c) = cong (Sync ℓ1 d ℓ2) (renFuseₗₑ ξ1 ξ2 c)
renFuseₗₑ ξ1 ξ2 (DefLocal ℓ c1 c2) = cong₂ (DefLocal ℓ) (renFuseₗₑ ξ1 ξ2 c1) c2⟨↑[ξ2∘ξ1]⟩≡c2⟨↑ξ1⟩⟨↑ξ2⟩
  where
  c2⟨↑[ξ2∘ξ1]⟩≡c2⟨↑ξ1⟩⟨↑ξ2⟩ : renₗₑ c2 (↑[ ℓ ] (∣ ξ2 ⟫- ξ1)) ≡ renₗₑ (renₗₑ c2 (↑[ ℓ ] ξ1)) (↑[ ℓ ] ξ2)
  c2⟨↑[ξ2∘ξ1]⟩≡c2⟨↑ξ1⟩⟨↑ξ2⟩ =
    renₗₑ c2 (↑[ ℓ ] (∣ ξ2 ⟫- ξ1))    ≡⟨ renExtₗₑ (↑[ℓ]Fuse ξ1 ξ2 ℓ) c2 ⟩
    renₗₑ c2 (∣ ↑[ ℓ ] ξ2 ⟫- ↑[ ℓ ] ξ1) ≡⟨ renFuseₗₑ (↑[ ℓ ] ξ1) (↑[ ℓ ] ξ2) c2 ⟩
    renₗₑ (renₗₑ c2 (↑[ ℓ ] ξ1)) (↑[ ℓ ] ξ2)        ∎
renFuseₗₑ ξ1 ξ2 (Fun τ c) = cong₂ Fun refl (renFuseₗₑ ξ1 ξ2 c)
renFuseₗₑ ξ1 ξ2 (Fix τ c) = cong₂ Fix refl (renFuseₗₑ ξ1 ξ2 c)
renFuseₗₑ ξ1 ξ2 (App c c₁) = cong₂ App (renFuseₗₑ ξ1 ξ2 c) (renFuseₗₑ ξ1 ξ2 c₁)
renFuseₗₑ ξ1 ξ2 (LocAbs c) = cong LocAbs eq
  where
  open ≡-Reasoning

  eq : renₗₑ c (↑ₗₑ (∣ ξ2 ⟫- ξ1)) ≡ renₗₑ (renₗₑ c (↑ₗₑ ξ1)) (↑ₗₑ ξ2)
  eq =
    renₗₑ c (↑ₗₑ (∣ ξ2 ⟫- ξ1))        ≡⟨ renExtₗₑ (↑Fuseₗₑ ξ1 ξ2) c ⟩
    renₗₑ c (∣ ↑ₗₑ ξ2 ⟫- ↑ₗₑ ξ1)      ≡⟨ renFuseₗₑ (↑ₗₑ ξ1) (↑ₗₑ ξ2) c ⟩
    renₗₑ (renₗₑ c (↑ₗₑ ξ1)) (↑ₗₑ ξ2) ∎
renFuseₗₑ ξ1 ξ2 (LocApp c ℓ) = cong₂ LocApp (renFuseₗₑ ξ1 ξ2 c) refl
renFuseₗₑ ξ1 ξ2 (TellLet ℓ ρ1 c1 ρ2 c2) =
  cong₅ TellLet refl refl (renFuseₗₑ ξ1 ξ2 c1) refl eq
  where
  open ≡-Reasoning

  eq : renₗₑ c2 (↑ₗₑ (∣ ξ2 ⟫- ξ1)) ≡ renₗₑ (renₗₑ c2 (↑ₗₑ ξ1)) (↑ₗₑ ξ2)
  eq =
    renₗₑ c2 (↑ₗₑ (∣ ξ2 ⟫- ξ1))        ≡⟨ renExtₗₑ (↑Fuseₗₑ ξ1 ξ2) c2 ⟩
    renₗₑ c2 (∣ ↑ₗₑ ξ2 ⟫- ↑ₗₑ ξ1)      ≡⟨ renFuseₗₑ (↑ₗₑ ξ1) (↑ₗₑ ξ2) c2 ⟩
    renₗₑ (renₗₑ c2 (↑ₗₑ ξ1)) (↑ₗₑ ξ2) ∎
