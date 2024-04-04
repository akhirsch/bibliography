{-# OPTIONS --safe #-}

open import Data.Nat renaming (_≟_ to ≡-dec-ℕ)
open import Data.Bool renaming (_≟_ to ≡-dec-Bool)
open import Data.List
open import Data.List.Properties renaming (≡-dec to ≡-dec-List)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function

open import Common
open import Locations
open import LocalLang

module ControlLang
  (L : Location)
  (E : LawfulLanguage L)
  where

open Location L
open LawfulLanguage E
open ≡-Reasoning


data Ctrl : Set
data Choices : Set

data Ctrl where
  Return : (e : Expr) → Ctrl
  Var : (x : ℕ) → Ctrl
  Fail : Ctrl
  Then : (E1 E2 : Ctrl) → Ctrl
  App : (E1 E2 : Ctrl) → Ctrl
  Fun : (E : Ctrl) → Ctrl
  Fix : (E : Ctrl) → Ctrl
  DefLocal : (E1 E2 : Ctrl) → Ctrl
  LocAbs : (E : Ctrl) → Ctrl
  LocApp : (E : Ctrl) (ℓ : Loc) → Ctrl
  Send : (E : Ctrl) (ℓ : Loc) → Ctrl
  Receive : (ℓ : Loc) → Ctrl
  If : (E E1 E2 : Ctrl) → Ctrl
  ChooseFor : (d : Bool) (ℓ : Loc) (E : Ctrl) → Ctrl
  AllowChoice : (ℓ : Loc) (C : Choices) → Ctrl
  SendLoc : (ρ : LocList) (E1 E2 : Ctrl) → Ctrl
  ReceiveLoc : (ℓ : Loc) (E : Ctrl) → Ctrl
  AmI : (ℓ : Loc) (E1 E2 : Ctrl) → Ctrl

data Choices where
  NoChoice : Choices
  TChoice : (ET : Ctrl) → Choices
  FChoice : (EF : Ctrl) → Choices
  TFChoice : (ET EF : Ctrl) → Choices

-- Rename the location variables in a control expression
renCtrlₗ : (ℕ → ℕ) → Ctrl → Ctrl
renChoicesₗ : (ℕ → ℕ) → Choices → Choices

renCtrlₗ ξ (Return e) = Return e
renCtrlₗ ξ (Var x) = Var x
renCtrlₗ ξ Fail = Fail
renCtrlₗ ξ (Then E1 E2) = Then (renCtrlₗ ξ E1) (renCtrlₗ ξ E2)
renCtrlₗ ξ (App E1 E2) = App (renCtrlₗ ξ E1) (renCtrlₗ ξ E2)
renCtrlₗ ξ (Fun E) = Fun (renCtrlₗ ξ E)
renCtrlₗ ξ (Fix E) = Fix (renCtrlₗ ξ E)
renCtrlₗ ξ (DefLocal E1 E2) = DefLocal (renCtrlₗ ξ E1) (renCtrlₗ ξ E2)
renCtrlₗ ξ (LocAbs E) = LocAbs (renCtrlₗ (↑ ξ) E)
renCtrlₗ ξ (LocApp E ℓ) = LocApp (renCtrlₗ ξ E) (renₗ-Loc ξ ℓ)
renCtrlₗ ξ (Send E ℓ) = Send (renCtrlₗ ξ E) (renₗ-Loc ξ ℓ)
renCtrlₗ ξ (Receive ℓ) = Receive (renₗ-Loc ξ ℓ)
renCtrlₗ ξ (If E E1 E2) = If (renCtrlₗ ξ E) (renCtrlₗ ξ E1) (renCtrlₗ ξ E2)
renCtrlₗ ξ (ChooseFor d ℓ E) = ChooseFor d (renₗ-Loc ξ ℓ) (renCtrlₗ ξ E)
renCtrlₗ ξ (AllowChoice ℓ C) = AllowChoice (renₗ-Loc ξ ℓ) (renChoicesₗ ξ C)
renCtrlₗ ξ (SendLoc ρ E1 E2) = SendLoc (renₗ-List ξ ρ) (renCtrlₗ ξ E1) (renCtrlₗ (↑ ξ) E2)
renCtrlₗ ξ (ReceiveLoc ℓ E) = ReceiveLoc (renₗ-Loc ξ ℓ) (renCtrlₗ (↑ ξ) E)
renCtrlₗ ξ (AmI ℓ E1 E2) = AmI (renₗ-Loc ξ ℓ) (renCtrlₗ ξ E1) (renCtrlₗ ξ E2)

renChoicesₗ ξ NoChoice = NoChoice
renChoicesₗ ξ (TChoice ET) = TChoice (renCtrlₗ ξ ET)
renChoicesₗ ξ (FChoice EF) = FChoice (renCtrlₗ ξ EF)
renChoicesₗ ξ (TFChoice ET EF) = TFChoice (renCtrlₗ ξ ET) (renCtrlₗ ξ EF)

-- Renaming locations respects extensional equality
renCtrlExtₗ : ∀{ξ1 ξ2} → ξ1 ≈ ξ2 → renCtrlₗ ξ1 ≈ renCtrlₗ ξ2
renChoicesExtₗ : ∀{ξ1 ξ2} → ξ1 ≈ ξ2 → renChoicesₗ ξ1 ≈ renChoicesₗ ξ2

renCtrlExtₗ ξ1≈ξ2 (Return e) = refl
renCtrlExtₗ ξ1≈ξ2 (Var x) = refl
renCtrlExtₗ ξ1≈ξ2 Fail = refl
renCtrlExtₗ ξ1≈ξ2 (Then E1 E2) = cong₂ Then (renCtrlExtₗ ξ1≈ξ2 E1) (renCtrlExtₗ ξ1≈ξ2 E2)
renCtrlExtₗ ξ1≈ξ2 (App E1 E2) = cong₂ App (renCtrlExtₗ ξ1≈ξ2 E1) (renCtrlExtₗ ξ1≈ξ2 E2)
renCtrlExtₗ ξ1≈ξ2 (Fun E) = cong Fun (renCtrlExtₗ ξ1≈ξ2 E)
renCtrlExtₗ ξ1≈ξ2 (Fix E) = cong Fix (renCtrlExtₗ ξ1≈ξ2 E)
renCtrlExtₗ ξ1≈ξ2 (DefLocal E1 E2) =
  cong₂ DefLocal (renCtrlExtₗ ξ1≈ξ2 E1) (renCtrlExtₗ ξ1≈ξ2 E2)
renCtrlExtₗ ξ1≈ξ2 (LocAbs E) = cong LocAbs (renCtrlExtₗ (↑Ext ξ1≈ξ2) E)
renCtrlExtₗ ξ1≈ξ2 (LocApp E ℓ) = cong₂ LocApp (renCtrlExtₗ ξ1≈ξ2 E) (renExtₗ-Loc ξ1≈ξ2 ℓ)
renCtrlExtₗ ξ1≈ξ2 (Send E ℓ) = cong₂ Send (renCtrlExtₗ ξ1≈ξ2 E) (renExtₗ-Loc ξ1≈ξ2 ℓ)
renCtrlExtₗ ξ1≈ξ2 (Receive ℓ) = cong Receive (renExtₗ-Loc ξ1≈ξ2 ℓ)
renCtrlExtₗ ξ1≈ξ2 (If E E1 E2) =
  cong₃ If (renCtrlExtₗ ξ1≈ξ2 E) (renCtrlExtₗ ξ1≈ξ2 E1) (renCtrlExtₗ ξ1≈ξ2 E2)
renCtrlExtₗ ξ1≈ξ2 (ChooseFor d ℓ E) =
  cong₃ ChooseFor refl (renExtₗ-Loc ξ1≈ξ2 ℓ) (renCtrlExtₗ ξ1≈ξ2 E)
renCtrlExtₗ ξ1≈ξ2 (AllowChoice ℓ C) =
  cong₂ AllowChoice (renExtₗ-Loc ξ1≈ξ2 ℓ) (renChoicesExtₗ ξ1≈ξ2 C)
renCtrlExtₗ ξ1≈ξ2 (SendLoc ρ E1 E2) =
  cong₃ SendLoc (renExtₗ-List ξ1≈ξ2 ρ) (renCtrlExtₗ ξ1≈ξ2 E1) (renCtrlExtₗ (↑Ext ξ1≈ξ2) E2)
renCtrlExtₗ ξ1≈ξ2 (ReceiveLoc ℓ E) =
  cong₂ ReceiveLoc (renExtₗ-Loc ξ1≈ξ2 ℓ) (renCtrlExtₗ (↑Ext ξ1≈ξ2) E)
renCtrlExtₗ ξ1≈ξ2 (AmI ℓ E1 E2) =
  cong₃ AmI (renExtₗ-Loc ξ1≈ξ2 ℓ) (renCtrlExtₗ ξ1≈ξ2 E1) (renCtrlExtₗ ξ1≈ξ2 E2)

renChoicesExtₗ ξ1≈ξ2 NoChoice = refl
renChoicesExtₗ ξ1≈ξ2 (TChoice ET) = cong TChoice (renCtrlExtₗ ξ1≈ξ2 ET)
renChoicesExtₗ ξ1≈ξ2 (FChoice EF) = cong FChoice (renCtrlExtₗ ξ1≈ξ2 EF)
renChoicesExtₗ ξ1≈ξ2 (TFChoice ET EF) = cong₂ TFChoice (renCtrlExtₗ ξ1≈ξ2 ET) (renCtrlExtₗ ξ1≈ξ2 EF)

-- Renaming locations respects the identity
renCtrlIdₗ : (E : Ctrl) → renCtrlₗ idRen E ≡ E
renChoicesIdₗ : (C : Choices) → renChoicesₗ idRen C ≡ C

renCtrlIdₗ (Return e) = refl
renCtrlIdₗ (Var x) = refl
renCtrlIdₗ Fail = refl
renCtrlIdₗ (Then E1 E2) = cong₂ Then (renCtrlIdₗ E1) (renCtrlIdₗ E2)
renCtrlIdₗ (App E1 E2) = cong₂ App (renCtrlIdₗ E1) (renCtrlIdₗ E2)
renCtrlIdₗ (Fun E) = cong Fun (renCtrlIdₗ E)
renCtrlIdₗ (Fix E) = cong Fix (renCtrlIdₗ E)
renCtrlIdₗ (DefLocal E1 E2) =
  cong₂ DefLocal (renCtrlIdₗ E1) (renCtrlIdₗ E2)
renCtrlIdₗ (LocAbs E) = cong LocAbs (renCtrlExtₗ ↑Id E ∙ renCtrlIdₗ E)
renCtrlIdₗ (LocApp E ℓ) = cong₂ LocApp (renCtrlIdₗ E) (renIdₗ-Loc ℓ)
renCtrlIdₗ (Send E ℓ) = cong₂ Send (renCtrlIdₗ E) (renIdₗ-Loc ℓ)
renCtrlIdₗ (Receive ℓ) = cong Receive (renIdₗ-Loc ℓ)
renCtrlIdₗ (If E E1 E2) =
  cong₃ If (renCtrlIdₗ E) (renCtrlIdₗ E1) (renCtrlIdₗ E2)
renCtrlIdₗ (ChooseFor d ℓ E) =
  cong₃ ChooseFor refl (renIdₗ-Loc ℓ) (renCtrlIdₗ E)
renCtrlIdₗ (AllowChoice ℓ C) =
  cong₂ AllowChoice (renIdₗ-Loc ℓ) (renChoicesIdₗ C)
renCtrlIdₗ (SendLoc ρ E1 E2) =
  cong₃ SendLoc (renIdₗ-List ρ) (renCtrlIdₗ E1) (renCtrlExtₗ ↑Id E2 ∙ renCtrlIdₗ E2)
renCtrlIdₗ (ReceiveLoc ℓ E) =
  cong₂ ReceiveLoc (renIdₗ-Loc ℓ) (renCtrlExtₗ ↑Id E ∙ renCtrlIdₗ E)
renCtrlIdₗ (AmI ℓ E1 E2) =
  cong₃ AmI (renIdₗ-Loc ℓ) (renCtrlIdₗ E1) (renCtrlIdₗ E2)

renChoicesIdₗ NoChoice = refl
renChoicesIdₗ (TChoice ET) = cong TChoice (renCtrlIdₗ ET)
renChoicesIdₗ (FChoice EF) = cong FChoice (renCtrlIdₗ EF)
renChoicesIdₗ (TFChoice ET EF) = cong₂ TFChoice (renCtrlIdₗ ET) (renCtrlIdₗ EF)

-- Renaming locations enjoys fusion
renCtrlFuseₗ : (ξ1 ξ2 : ℕ → ℕ) → renCtrlₗ (ξ1 ∘ ξ2) ≈ renCtrlₗ ξ1 ∘ renCtrlₗ ξ2
renChoicesFuseₗ : (ξ1 ξ2 : ℕ → ℕ) → renChoicesₗ (ξ1 ∘ ξ2) ≈ renChoicesₗ ξ1 ∘ renChoicesₗ ξ2

renCtrlFuseₗ ξ1 ξ2 (Return e) = refl
renCtrlFuseₗ ξ1 ξ2 (Var x) = refl
renCtrlFuseₗ ξ1 ξ2 Fail = refl
renCtrlFuseₗ ξ1 ξ2 (Then E1 E2) = cong₂ Then (renCtrlFuseₗ ξ1 ξ2 E1) (renCtrlFuseₗ ξ1 ξ2 E2)
renCtrlFuseₗ ξ1 ξ2 (App E1 E2) = cong₂ App (renCtrlFuseₗ ξ1 ξ2 E1) (renCtrlFuseₗ ξ1 ξ2 E2)
renCtrlFuseₗ ξ1 ξ2 (Fun E) = cong Fun (renCtrlFuseₗ ξ1 ξ2 E)
renCtrlFuseₗ ξ1 ξ2 (Fix E) = cong Fix (renCtrlFuseₗ ξ1 ξ2 E)
renCtrlFuseₗ ξ1 ξ2 (DefLocal E1 E2) =
  cong₂ DefLocal (renCtrlFuseₗ ξ1 ξ2 E1) (renCtrlFuseₗ ξ1 ξ2 E2)
renCtrlFuseₗ ξ1 ξ2 (LocAbs E) = cong LocAbs (renCtrlExtₗ (↑Fuse ξ1 ξ2) E ∙ renCtrlFuseₗ (↑ ξ1) (↑ ξ2) E)
renCtrlFuseₗ ξ1 ξ2 (LocApp E ℓ) = cong₂ LocApp (renCtrlFuseₗ ξ1 ξ2 E) (renFuseₗ-Loc ξ1 ξ2 ℓ)
renCtrlFuseₗ ξ1 ξ2 (Send E ℓ) = cong₂ Send (renCtrlFuseₗ ξ1 ξ2 E) (renFuseₗ-Loc ξ1 ξ2 ℓ)
renCtrlFuseₗ ξ1 ξ2 (Receive ℓ) = cong Receive (renFuseₗ-Loc ξ1 ξ2 ℓ)
renCtrlFuseₗ ξ1 ξ2 (If E E1 E2) =
  cong₃ If (renCtrlFuseₗ ξ1 ξ2 E) (renCtrlFuseₗ ξ1 ξ2 E1) (renCtrlFuseₗ ξ1 ξ2 E2)
renCtrlFuseₗ ξ1 ξ2 (ChooseFor d ℓ E) =
  cong₃ ChooseFor refl (renFuseₗ-Loc ξ1 ξ2 ℓ) (renCtrlFuseₗ ξ1 ξ2 E)
renCtrlFuseₗ ξ1 ξ2 (AllowChoice ℓ C) =
  cong₂ AllowChoice (renFuseₗ-Loc ξ1 ξ2 ℓ) (renChoicesFuseₗ ξ1 ξ2 C)
renCtrlFuseₗ ξ1 ξ2 (SendLoc ρ E1 E2) =
  cong₃ SendLoc (renFuseₗ-List ξ1 ξ2 ρ) (renCtrlFuseₗ ξ1 ξ2 E1) (renCtrlExtₗ (↑Fuse ξ1 ξ2) E2 ∙ renCtrlFuseₗ (↑ ξ1) (↑ ξ2) E2)
renCtrlFuseₗ ξ1 ξ2 (ReceiveLoc ℓ E) =
  cong₂ ReceiveLoc (renFuseₗ-Loc ξ1 ξ2 ℓ) (renCtrlExtₗ (↑Fuse ξ1 ξ2) E ∙ renCtrlFuseₗ (↑ ξ1) (↑ ξ2) E)
renCtrlFuseₗ ξ1 ξ2 (AmI ℓ E1 E2) =
  cong₃ AmI (renFuseₗ-Loc ξ1 ξ2 ℓ) (renCtrlFuseₗ ξ1 ξ2 E1) (renCtrlFuseₗ ξ1 ξ2 E2)

renChoicesFuseₗ ξ1 ξ2 NoChoice = refl
renChoicesFuseₗ ξ1 ξ2 (TChoice ET) = cong TChoice (renCtrlFuseₗ ξ1 ξ2 ET)
renChoicesFuseₗ ξ1 ξ2 (FChoice EF) = cong FChoice (renCtrlFuseₗ ξ1 ξ2 EF)
renChoicesFuseₗ ξ1 ξ2 (TFChoice ET EF) = cong₂ TFChoice (renCtrlFuseₗ ξ1 ξ2 ET) (renCtrlFuseₗ ξ1 ξ2 EF)


-- Substitute the location variables in a control expression
subCtrlₗ : (ℕ → Loc) → Ctrl → Ctrl
subChoicesₗ : (ℕ → Loc) → Choices → Choices

subCtrlₗ σ (Return e) = Return e
subCtrlₗ σ (Var x) = Var x
subCtrlₗ σ Fail = Fail
subCtrlₗ σ (Then E1 E2) = Then (subCtrlₗ σ E1) (subCtrlₗ σ E2)
subCtrlₗ σ (App E1 E2) = App (subCtrlₗ σ E1) (subCtrlₗ σ E2)
subCtrlₗ σ (Fun E) = Fun (subCtrlₗ σ E)
subCtrlₗ σ (Fix E) = Fix (subCtrlₗ σ E)
subCtrlₗ σ (DefLocal E1 E2) = DefLocal (subCtrlₗ σ E1) (subCtrlₗ σ E2)
subCtrlₗ σ (LocAbs E) = LocAbs (subCtrlₗ (↑σₗ σ) E)
subCtrlₗ σ (LocApp E ℓ) = LocApp (subCtrlₗ σ E) (subₗ-Loc σ ℓ)
subCtrlₗ σ (Send E ℓ) = Send (subCtrlₗ σ E) (subₗ-Loc σ ℓ)
subCtrlₗ σ (Receive ℓ) = Receive (subₗ-Loc σ ℓ)
subCtrlₗ σ (If E E1 E2) = If (subCtrlₗ σ E) (subCtrlₗ σ E1) (subCtrlₗ σ E2)
subCtrlₗ σ (ChooseFor d ℓ E) = ChooseFor d (subₗ-Loc σ ℓ) (subCtrlₗ σ E)
subCtrlₗ σ (AllowChoice ℓ C) = AllowChoice (subₗ-Loc σ ℓ) (subChoicesₗ σ C)
subCtrlₗ σ (SendLoc ρ E1 E2) = SendLoc (subₗ-List σ ρ) (subCtrlₗ σ E1) (subCtrlₗ (↑σₗ σ) E2)
subCtrlₗ σ (ReceiveLoc ℓ E) = ReceiveLoc (subₗ-Loc σ ℓ) (subCtrlₗ (↑σₗ σ) E)
subCtrlₗ σ (AmI ℓ E1 E2) = AmI (subₗ-Loc σ ℓ) (subCtrlₗ σ E1) (subCtrlₗ σ E2)

subChoicesₗ σ NoChoice = NoChoice
subChoicesₗ σ (TChoice ET) = TChoice (subCtrlₗ σ ET)
subChoicesₗ σ (FChoice EF) = FChoice (subCtrlₗ σ EF)
subChoicesₗ σ (TFChoice ET EF) = TFChoice (subCtrlₗ σ ET) (subCtrlₗ σ EF)

-- Substituting locations respects extensional equality
subCtrlExtₗ : ∀{σ1 σ2} → σ1 ≈ σ2 → subCtrlₗ σ1 ≈ subCtrlₗ σ2
subChoicesExtₗ : ∀{σ1 σ2} → σ1 ≈ σ2 → subChoicesₗ σ1 ≈ subChoicesₗ σ2

subCtrlExtₗ σ1≈σ2 (Return e) = refl
subCtrlExtₗ σ1≈σ2 (Var x) = refl
subCtrlExtₗ σ1≈σ2 Fail = refl
subCtrlExtₗ σ1≈σ2 (Then E1 E2) = cong₂ Then (subCtrlExtₗ σ1≈σ2 E1) (subCtrlExtₗ σ1≈σ2 E2)
subCtrlExtₗ σ1≈σ2 (App E1 E2) = cong₂ App (subCtrlExtₗ σ1≈σ2 E1) (subCtrlExtₗ σ1≈σ2 E2)
subCtrlExtₗ σ1≈σ2 (Fun E) = cong Fun (subCtrlExtₗ σ1≈σ2 E)
subCtrlExtₗ σ1≈σ2 (Fix E) = cong Fix (subCtrlExtₗ σ1≈σ2 E)
subCtrlExtₗ σ1≈σ2 (DefLocal E1 E2) =
  cong₂ DefLocal (subCtrlExtₗ σ1≈σ2 E1) (subCtrlExtₗ σ1≈σ2 E2)
subCtrlExtₗ σ1≈σ2 (LocAbs E) = cong LocAbs (subCtrlExtₗ (↑σExtₗ σ1≈σ2) E)
subCtrlExtₗ σ1≈σ2 (LocApp E ℓ) = cong₂ LocApp (subCtrlExtₗ σ1≈σ2 E) (subExtₗ-Loc σ1≈σ2 ℓ)
subCtrlExtₗ σ1≈σ2 (Send E ℓ) = cong₂ Send (subCtrlExtₗ σ1≈σ2 E) (subExtₗ-Loc σ1≈σ2 ℓ)
subCtrlExtₗ σ1≈σ2 (Receive ℓ) = cong Receive (subExtₗ-Loc σ1≈σ2 ℓ)
subCtrlExtₗ σ1≈σ2 (If E E1 E2) =
  cong₃ If (subCtrlExtₗ σ1≈σ2 E) (subCtrlExtₗ σ1≈σ2 E1) (subCtrlExtₗ σ1≈σ2 E2)
subCtrlExtₗ σ1≈σ2 (ChooseFor d ℓ E) =
  cong₃ ChooseFor refl (subExtₗ-Loc σ1≈σ2 ℓ) (subCtrlExtₗ σ1≈σ2 E)
subCtrlExtₗ σ1≈σ2 (AllowChoice ℓ C) =
  cong₂ AllowChoice (subExtₗ-Loc σ1≈σ2 ℓ) (subChoicesExtₗ σ1≈σ2 C)
subCtrlExtₗ σ1≈σ2 (SendLoc ρ E1 E2) =
  cong₃ SendLoc (subExtₗ-List σ1≈σ2 ρ) (subCtrlExtₗ σ1≈σ2 E1) (subCtrlExtₗ (↑σExtₗ σ1≈σ2) E2)
subCtrlExtₗ σ1≈σ2 (ReceiveLoc ℓ E) =
  cong₂ ReceiveLoc (subExtₗ-Loc σ1≈σ2 ℓ) (subCtrlExtₗ (↑σExtₗ σ1≈σ2) E)
subCtrlExtₗ σ1≈σ2 (AmI ℓ E1 E2) =
  cong₃ AmI (subExtₗ-Loc σ1≈σ2 ℓ) (subCtrlExtₗ σ1≈σ2 E1) (subCtrlExtₗ σ1≈σ2 E2)

subChoicesExtₗ σ1≈σ2 NoChoice = refl
subChoicesExtₗ σ1≈σ2 (TChoice ET) = cong TChoice (subCtrlExtₗ σ1≈σ2 ET)
subChoicesExtₗ σ1≈σ2 (FChoice EF) = cong FChoice (subCtrlExtₗ σ1≈σ2 EF)
subChoicesExtₗ σ1≈σ2 (TFChoice ET EF) = cong₂ TFChoice (subCtrlExtₗ σ1≈σ2 ET) (subCtrlExtₗ σ1≈σ2 EF)

-- Substituting locations respects the identity
subCtrlIdₗ : (E : Ctrl) → subCtrlₗ idSubₗ E ≡ E
subChoicesIdₗ : (C : Choices) → subChoicesₗ idSubₗ C ≡ C

subCtrlIdₗ (Return e) = refl
subCtrlIdₗ (Var x) = refl
subCtrlIdₗ Fail = refl
subCtrlIdₗ (Then E1 E2) = cong₂ Then (subCtrlIdₗ E1) (subCtrlIdₗ E2)
subCtrlIdₗ (App E1 E2) = cong₂ App (subCtrlIdₗ E1) (subCtrlIdₗ E2)
subCtrlIdₗ (Fun E) = cong Fun (subCtrlIdₗ E)
subCtrlIdₗ (Fix E) = cong Fix (subCtrlIdₗ E)
subCtrlIdₗ (DefLocal E1 E2) =
  cong₂ DefLocal (subCtrlIdₗ E1) (subCtrlIdₗ E2)
subCtrlIdₗ (LocAbs E) = cong LocAbs (subCtrlExtₗ ↑σIdₗ E ∙ subCtrlIdₗ E)
subCtrlIdₗ (LocApp E ℓ) = cong₂ LocApp (subCtrlIdₗ E) (subIdₗ-Loc ℓ)
subCtrlIdₗ (Send E ℓ) = cong₂ Send (subCtrlIdₗ E) (subIdₗ-Loc ℓ)
subCtrlIdₗ (Receive ℓ) = cong Receive (subIdₗ-Loc ℓ)
subCtrlIdₗ (If E E1 E2) =
  cong₃ If (subCtrlIdₗ E) (subCtrlIdₗ E1) (subCtrlIdₗ E2)
subCtrlIdₗ (ChooseFor d ℓ E) =
  cong₃ ChooseFor refl (subIdₗ-Loc ℓ) (subCtrlIdₗ E)
subCtrlIdₗ (AllowChoice ℓ C) =
  cong₂ AllowChoice (subIdₗ-Loc ℓ) (subChoicesIdₗ C)
subCtrlIdₗ (SendLoc ρ E1 E2) =
  cong₃ SendLoc (subIdₗ-List ρ) (subCtrlIdₗ E1) (subCtrlExtₗ ↑σIdₗ E2 ∙ subCtrlIdₗ E2)
subCtrlIdₗ (ReceiveLoc ℓ E) =
  cong₂ ReceiveLoc (subIdₗ-Loc ℓ) (subCtrlExtₗ ↑σIdₗ E ∙ subCtrlIdₗ E)
subCtrlIdₗ (AmI ℓ E1 E2) =
  cong₃ AmI (subIdₗ-Loc ℓ) (subCtrlIdₗ E1) (subCtrlIdₗ E2)

subChoicesIdₗ NoChoice = refl
subChoicesIdₗ (TChoice ET) = cong TChoice (subCtrlIdₗ ET)
subChoicesIdₗ (FChoice EF) = cong FChoice (subCtrlIdₗ EF)
subChoicesIdₗ (TFChoice ET EF) = cong₂ TFChoice (subCtrlIdₗ ET) (subCtrlIdₗ EF)

-- Rename the variables in a control expression
renCtrl : (ℕ → ℕ) → Ctrl → Ctrl
renChoices : (ℕ → ℕ) → Choices → Choices

renCtrl ξ (Return e) = Return e
renCtrl ξ (Var x) = Var (ξ x)
renCtrl ξ Fail = Fail
renCtrl ξ (Then E1 E2) = Then (renCtrl ξ E1) (renCtrl ξ E2)
renCtrl ξ (App E1 E2) = App (renCtrl ξ E1) (renCtrl ξ E2)
renCtrl ξ (Fun E) = Fun (renCtrl (↑ ξ) E)
renCtrl ξ (Fix E) = Fix (renCtrl (↑ ξ) E)
renCtrl ξ (DefLocal E1 E2) = DefLocal (renCtrl ξ E1) (renCtrl ξ E2)
renCtrl ξ (LocAbs E) = LocAbs (renCtrl ξ E)
renCtrl ξ (LocApp E ℓ) = LocApp (renCtrl ξ E) ℓ
renCtrl ξ (Send E ℓ) = Send (renCtrl ξ E) ℓ
renCtrl ξ (Receive ℓ) = Receive ℓ
renCtrl ξ (If E E1 E2) = If (renCtrl ξ E) (renCtrl ξ E1) (renCtrl ξ E2)
renCtrl ξ (ChooseFor d ℓ E) = ChooseFor d ℓ (renCtrl ξ E)
renCtrl ξ (AllowChoice ℓ C) = AllowChoice ℓ (renChoices ξ C)
renCtrl ξ (SendLoc ρ E1 E2) = SendLoc ρ (renCtrl ξ E1) (renCtrl ξ E2)
renCtrl ξ (ReceiveLoc ℓ E) = ReceiveLoc ℓ (renCtrl ξ E)
renCtrl ξ (AmI ℓ E1 E2) = AmI ℓ (renCtrl ξ E1) (renCtrl ξ E2)

renChoices ξ NoChoice = NoChoice
renChoices ξ (TChoice ET) = TChoice (renCtrl ξ ET)
renChoices ξ (FChoice EF) = FChoice (renCtrl ξ EF)
renChoices ξ (TFChoice ET EF) = TFChoice (renCtrl ξ ET) (renCtrl ξ EF)

-- Renaming respects extensional equality
renCtrlExt : ∀{ξ1 ξ2} → ξ1 ≈ ξ2 → renCtrl ξ1 ≈ renCtrl ξ2
renChoicesExt : ∀{ξ1 ξ2} → ξ1 ≈ ξ2 → renChoices ξ1 ≈ renChoices ξ2

renCtrlExt ξ1≈ξ2 (Return e) = refl
renCtrlExt ξ1≈ξ2 (Var x) = cong Var (ξ1≈ξ2 x)
renCtrlExt ξ1≈ξ2 Fail = refl
renCtrlExt ξ1≈ξ2 (Then E1 E2) = cong₂ Then (renCtrlExt ξ1≈ξ2 E1) (renCtrlExt ξ1≈ξ2 E2)
renCtrlExt ξ1≈ξ2 (App E1 E2) = cong₂ App (renCtrlExt ξ1≈ξ2 E1) (renCtrlExt ξ1≈ξ2 E2)
renCtrlExt ξ1≈ξ2 (Fun E) = cong Fun (renCtrlExt (↑Ext ξ1≈ξ2) E)
renCtrlExt ξ1≈ξ2 (Fix E) = cong Fix (renCtrlExt (↑Ext ξ1≈ξ2) E)
renCtrlExt ξ1≈ξ2 (DefLocal E1 E2) = cong₂ DefLocal (renCtrlExt ξ1≈ξ2 E1) (renCtrlExt ξ1≈ξ2 E2)
renCtrlExt ξ1≈ξ2 (LocAbs E) = cong LocAbs (renCtrlExt ξ1≈ξ2 E)
renCtrlExt ξ1≈ξ2 (LocApp E ℓ) = cong₂ LocApp (renCtrlExt ξ1≈ξ2 E) refl
renCtrlExt ξ1≈ξ2 (Send E ℓ) = cong₂ Send (renCtrlExt ξ1≈ξ2 E) refl
renCtrlExt ξ1≈ξ2 (Receive ℓ) = cong Receive refl
renCtrlExt ξ1≈ξ2 (If E E1 E2) = cong₃ If (renCtrlExt ξ1≈ξ2 E) (renCtrlExt ξ1≈ξ2 E1) (renCtrlExt ξ1≈ξ2 E2)
renCtrlExt ξ1≈ξ2 (ChooseFor d ℓ E) = cong₃ ChooseFor refl refl (renCtrlExt ξ1≈ξ2 E)
renCtrlExt ξ1≈ξ2 (AllowChoice ℓ C) = cong₂ AllowChoice refl (renChoicesExt ξ1≈ξ2 C)
renCtrlExt ξ1≈ξ2 (SendLoc ρ E1 E2) = cong₃ SendLoc refl (renCtrlExt ξ1≈ξ2 E1) (renCtrlExt ξ1≈ξ2 E2)
renCtrlExt ξ1≈ξ2 (ReceiveLoc ℓ E) = cong₂ ReceiveLoc refl (renCtrlExt ξ1≈ξ2 E)
renCtrlExt ξ1≈ξ2 (AmI ℓ E1 E2) = cong₃ AmI refl (renCtrlExt ξ1≈ξ2 E1) (renCtrlExt ξ1≈ξ2 E2)

renChoicesExt ξ1≈ξ2 NoChoice = refl
renChoicesExt ξ1≈ξ2 (TChoice ET) = cong TChoice (renCtrlExt ξ1≈ξ2 ET)
renChoicesExt ξ1≈ξ2 (FChoice EF) = cong FChoice (renCtrlExt ξ1≈ξ2 EF)
renChoicesExt ξ1≈ξ2 (TFChoice ET EF) = cong₂ TFChoice (renCtrlExt ξ1≈ξ2 ET) (renCtrlExt ξ1≈ξ2 EF)

-- Renaming respects the identity
renCtrlId : (E : Ctrl) → renCtrl idRen E ≡ E
renChoicesId : (C : Choices) → renChoices idRen C ≡ C

renCtrlId (Return e) = refl
renCtrlId (Var x) = refl
renCtrlId Fail = refl
renCtrlId (Then E1 E2) = cong₂ Then (renCtrlId E1) (renCtrlId E2)
renCtrlId (App E1 E2) = cong₂ App (renCtrlId E1) (renCtrlId E2)
renCtrlId (Fun E) = cong Fun (renCtrlExt ↑Id E ∙ renCtrlId E)
renCtrlId (Fix E) = cong Fix (renCtrlExt ↑Id E ∙ renCtrlId E)
renCtrlId (DefLocal E1 E2) = cong₂ DefLocal (renCtrlId E1) (renCtrlId E2)
renCtrlId (LocAbs E) = cong LocAbs (renCtrlId E)
renCtrlId (LocApp E ℓ) = cong₂ LocApp (renCtrlId E) refl
renCtrlId (Send E ℓ) = cong₂ Send (renCtrlId E) refl
renCtrlId (Receive ℓ) = cong Receive refl
renCtrlId (If E E1 E2) = cong₃ If (renCtrlId E) (renCtrlId E1) (renCtrlId E2)
renCtrlId (ChooseFor d ℓ E) = cong₃ ChooseFor refl refl (renCtrlId E)
renCtrlId (AllowChoice ℓ C) = cong₂ AllowChoice refl (renChoicesId C)
renCtrlId (SendLoc ρ E1 E2) = cong₃ SendLoc refl (renCtrlId E1) (renCtrlId E2)
renCtrlId (ReceiveLoc ℓ E) = cong₂ ReceiveLoc refl (renCtrlId E)
renCtrlId (AmI ℓ E1 E2) = cong₃ AmI refl (renCtrlId E1) (renCtrlId E2)

renChoicesId NoChoice = refl
renChoicesId (TChoice ET) = cong TChoice (renCtrlId ET)
renChoicesId (FChoice EF) = cong FChoice (renCtrlId EF)
renChoicesId (TFChoice ET EF) = cong₂ TFChoice (renCtrlId ET) (renCtrlId EF)

-- Renaming enjoys fusion
renCtrlFuse : (ξ1 ξ2 : ℕ → ℕ) → renCtrl (ξ1 ∘ ξ2) ≈ renCtrl ξ1 ∘ renCtrl ξ2
renChoicesFuse : (ξ1 ξ2 : ℕ → ℕ) → renChoices (ξ1 ∘ ξ2) ≈ renChoices ξ1 ∘ renChoices ξ2

renCtrlFuse ξ1 ξ2 (Return e) = refl
renCtrlFuse ξ1 ξ2 (Var x) = refl
renCtrlFuse ξ1 ξ2 Fail = refl
renCtrlFuse ξ1 ξ2 (Then E1 E2) = cong₂ Then (renCtrlFuse ξ1 ξ2 E1) (renCtrlFuse ξ1 ξ2 E2)
renCtrlFuse ξ1 ξ2 (App E1 E2) = cong₂ App (renCtrlFuse ξ1 ξ2 E1) (renCtrlFuse ξ1 ξ2 E2)
renCtrlFuse ξ1 ξ2 (Fun E) = cong Fun (renCtrlExt (↑Fuse ξ1 ξ2) E ∙ renCtrlFuse (↑ ξ1) (↑ ξ2) E)
renCtrlFuse ξ1 ξ2 (Fix E) = cong Fix (renCtrlExt (↑Fuse ξ1 ξ2) E ∙ renCtrlFuse (↑ ξ1) (↑ ξ2) E)
renCtrlFuse ξ1 ξ2 (DefLocal E1 E2) = cong₂ DefLocal (renCtrlFuse ξ1 ξ2 E1) (renCtrlFuse ξ1 ξ2 E2)
renCtrlFuse ξ1 ξ2 (LocAbs E) = cong LocAbs (renCtrlFuse ξ1 ξ2 E)
renCtrlFuse ξ1 ξ2 (LocApp E ℓ) = cong₂ LocApp (renCtrlFuse ξ1 ξ2 E) refl
renCtrlFuse ξ1 ξ2 (Send E ℓ) = cong₂ Send (renCtrlFuse ξ1 ξ2 E) refl
renCtrlFuse ξ1 ξ2 (Receive ℓ) = cong Receive refl
renCtrlFuse ξ1 ξ2 (If E E1 E2) = cong₃ If (renCtrlFuse ξ1 ξ2 E) (renCtrlFuse ξ1 ξ2 E1) (renCtrlFuse ξ1 ξ2 E2)
renCtrlFuse ξ1 ξ2 (ChooseFor d ℓ E) = cong₃ ChooseFor refl refl (renCtrlFuse ξ1 ξ2 E)
renCtrlFuse ξ1 ξ2 (AllowChoice ℓ C) = cong₂ AllowChoice refl (renChoicesFuse ξ1 ξ2 C)
renCtrlFuse ξ1 ξ2 (SendLoc ρ E1 E2) = cong₃ SendLoc refl (renCtrlFuse ξ1 ξ2 E1) (renCtrlFuse ξ1 ξ2 E2)
renCtrlFuse ξ1 ξ2 (ReceiveLoc ℓ E) = cong₂ ReceiveLoc refl (renCtrlFuse ξ1 ξ2 E)
renCtrlFuse ξ1 ξ2 (AmI ℓ E1 E2) = cong₃ AmI refl (renCtrlFuse ξ1 ξ2 E1) (renCtrlFuse ξ1 ξ2 E2)

renChoicesFuse ξ1 ξ2 NoChoice = refl
renChoicesFuse ξ1 ξ2 (TChoice ET) = cong TChoice (renCtrlFuse ξ1 ξ2 ET)
renChoicesFuse ξ1 ξ2 (FChoice EF) = cong FChoice (renCtrlFuse ξ1 ξ2 EF)
renChoicesFuse ξ1 ξ2 (TFChoice ET EF) = cong₂ TFChoice (renCtrlFuse ξ1 ξ2 ET) (renCtrlFuse ξ1 ξ2 EF)

-- Control language substitutions
idSubCtrl : ℕ → Ctrl
idSubCtrl = Var

↑σCtrl : (ℕ → Ctrl) → ℕ → Ctrl
↑σCtrl σ zero = Var zero
↑σCtrl σ (suc n) = renCtrl suc (↑σCtrl σ n)

↑σCtrlExt : ∀{σ1 σ2} → σ1 ≈ σ2 → ↑σCtrl σ1 ≈ ↑σCtrl σ2
↑σCtrlExt σ1≈σ2 zero = refl
↑σCtrlExt σ1≈σ2 (suc n) = cong (renCtrl suc) (↑σCtrlExt σ1≈σ2 n)

↑σCtrlId : ↑σCtrl idSubCtrl ≈ idSubCtrl
↑σCtrlId zero = refl
↑σCtrlId (suc n) = cong (renCtrl suc) (↑σCtrlId n)

-- Substitute the variables in a control expression
subCtrl : (ℕ → Ctrl) → Ctrl → Ctrl
subChoices : (ℕ → Ctrl) → Choices → Choices

subCtrl σ (Return e) = Return e
subCtrl σ (Var x) = σ x
subCtrl σ Fail = Fail
subCtrl σ (Then E1 E2) = Then (subCtrl σ E1) (subCtrl σ E2)
subCtrl σ (App E1 E2) = App (subCtrl σ E1) (subCtrl σ E2)
subCtrl σ (Fun E) = Fun (subCtrl (↑σCtrl σ) E)
subCtrl σ (Fix E) = Fix (subCtrl (↑σCtrl σ) E)
subCtrl σ (DefLocal E1 E2) = DefLocal (subCtrl σ E1) (subCtrl σ E2)
subCtrl σ (LocAbs E) = LocAbs (subCtrl σ E)
subCtrl σ (LocApp E ℓ) = LocApp (subCtrl σ E) ℓ
subCtrl σ (Send E ℓ) = Send (subCtrl σ E) ℓ
subCtrl σ (Receive ℓ) = Receive ℓ
subCtrl σ (If E E1 E2) = If (subCtrl σ E) (subCtrl σ E1) (subCtrl σ E2)
subCtrl σ (ChooseFor d ℓ E) = ChooseFor d ℓ (subCtrl σ E)
subCtrl σ (AllowChoice ℓ C) = AllowChoice ℓ (subChoices σ C)
subCtrl σ (SendLoc ρ E1 E2) = SendLoc ρ (subCtrl σ E1) (subCtrl σ E2)
subCtrl σ (ReceiveLoc ℓ E) = ReceiveLoc ℓ (subCtrl σ E)
subCtrl σ (AmI ℓ E1 E2) = AmI ℓ (subCtrl σ E1) (subCtrl σ E2)

subChoices σ NoChoice = NoChoice
subChoices σ (TChoice ET) = TChoice (subCtrl σ ET)
subChoices σ (FChoice EF) = FChoice (subCtrl σ EF)
subChoices σ (TFChoice ET EF) = TFChoice (subCtrl σ ET) (subCtrl σ EF)

-- Substitution respects extensional equality
subCtrlExt : ∀{σ1 σ2} → σ1 ≈ σ2 → subCtrl σ1 ≈ subCtrl σ2
subChoicesExt : ∀{σ1 σ2} → σ1 ≈ σ2 → subChoices σ1 ≈ subChoices σ2

subCtrlExt σ1≈σ2 (Return e) = refl
subCtrlExt σ1≈σ2 (Var x) = σ1≈σ2 x
subCtrlExt σ1≈σ2 Fail = refl
subCtrlExt σ1≈σ2 (Then E1 E2) = cong₂ Then (subCtrlExt σ1≈σ2 E1) (subCtrlExt σ1≈σ2 E2)
subCtrlExt σ1≈σ2 (App E1 E2) = cong₂ App (subCtrlExt σ1≈σ2 E1) (subCtrlExt σ1≈σ2 E2)
subCtrlExt σ1≈σ2 (Fun E) = cong Fun (subCtrlExt (↑σCtrlExt σ1≈σ2) E)
subCtrlExt σ1≈σ2 (Fix E) = cong Fix (subCtrlExt (↑σCtrlExt σ1≈σ2) E)
subCtrlExt σ1≈σ2 (DefLocal E1 E2) = cong₂ DefLocal (subCtrlExt σ1≈σ2 E1) (subCtrlExt σ1≈σ2 E2)
subCtrlExt σ1≈σ2 (LocAbs E) = cong LocAbs (subCtrlExt σ1≈σ2 E)
subCtrlExt σ1≈σ2 (LocApp E ℓ) = cong₂ LocApp (subCtrlExt σ1≈σ2 E) refl
subCtrlExt σ1≈σ2 (Send E ℓ) = cong₂ Send (subCtrlExt σ1≈σ2 E) refl
subCtrlExt σ1≈σ2 (Receive ℓ) = cong Receive refl
subCtrlExt σ1≈σ2 (If E E1 E2) = cong₃ If (subCtrlExt σ1≈σ2 E) (subCtrlExt σ1≈σ2 E1) (subCtrlExt σ1≈σ2 E2)
subCtrlExt σ1≈σ2 (ChooseFor d ℓ E) = cong₃ ChooseFor refl refl (subCtrlExt σ1≈σ2 E)
subCtrlExt σ1≈σ2 (AllowChoice ℓ C) = cong₂ AllowChoice refl (subChoicesExt σ1≈σ2 C)
subCtrlExt σ1≈σ2 (SendLoc ρ E1 E2) = cong₃ SendLoc refl (subCtrlExt σ1≈σ2 E1) (subCtrlExt σ1≈σ2 E2)
subCtrlExt σ1≈σ2 (ReceiveLoc ℓ E) = cong₂ ReceiveLoc refl (subCtrlExt σ1≈σ2 E)
subCtrlExt σ1≈σ2 (AmI ℓ E1 E2) = cong₃ AmI refl (subCtrlExt σ1≈σ2 E1) (subCtrlExt σ1≈σ2 E2)

subChoicesExt σ1≈σ2 NoChoice = refl
subChoicesExt σ1≈σ2 (TChoice ET) = cong TChoice (subCtrlExt σ1≈σ2 ET)
subChoicesExt σ1≈σ2 (FChoice EF) = cong FChoice (subCtrlExt σ1≈σ2 EF)
subChoicesExt σ1≈σ2 (TFChoice ET EF) = cong₂ TFChoice (subCtrlExt σ1≈σ2 ET) (subCtrlExt σ1≈σ2 EF)

-- Substitution respects the identity
subCtrlId : (E : Ctrl) → subCtrl idSubCtrl E ≡ E
subChoicesId : (C : Choices) → subChoices idSubCtrl C ≡ C

subCtrlId (Return e) = refl
subCtrlId (Var x) = refl
subCtrlId Fail = refl
subCtrlId (Then E1 E2) = cong₂ Then (subCtrlId E1) (subCtrlId E2)
subCtrlId (App E1 E2) = cong₂ App (subCtrlId E1) (subCtrlId E2)
subCtrlId (Fun E) = cong Fun (subCtrlExt ↑σCtrlId E ∙ subCtrlId E)
subCtrlId (Fix E) = cong Fix (subCtrlExt ↑σCtrlId E ∙ subCtrlId E)
subCtrlId (DefLocal E1 E2) = cong₂ DefLocal (subCtrlId E1) (subCtrlId E2)
subCtrlId (LocAbs E) = cong LocAbs (subCtrlId E)
subCtrlId (LocApp E ℓ) = cong₂ LocApp (subCtrlId E) refl
subCtrlId (Send E ℓ) = cong₂ Send (subCtrlId E) refl
subCtrlId (Receive ℓ) = cong Receive refl
subCtrlId (If E E1 E2) = cong₃ If (subCtrlId E) (subCtrlId E1) (subCtrlId E2)
subCtrlId (ChooseFor d ℓ E) = cong₃ ChooseFor refl refl (subCtrlId E)
subCtrlId (AllowChoice ℓ C) = cong₂ AllowChoice refl (subChoicesId C)
subCtrlId (SendLoc ρ E1 E2) = cong₃ SendLoc refl (subCtrlId E1) (subCtrlId E2)
subCtrlId (ReceiveLoc ℓ E) = cong₂ ReceiveLoc refl (subCtrlId E)
subCtrlId (AmI ℓ E1 E2) = cong₃ AmI refl (subCtrlId E1) (subCtrlId E2)

subChoicesId NoChoice = refl
subChoicesId (TChoice ET) = cong TChoice (subCtrlId ET)
subChoicesId (FChoice EF) = cong FChoice (subCtrlId EF)
subChoicesId (TFChoice ET EF) = cong₂ TFChoice (subCtrlId ET) (subCtrlId EF)


-- Rename the local variables in a control expression
renCtrlₗₑ : (ℕ → ℕ) → Ctrl → Ctrl
renChoicesₗₑ : (ℕ → ℕ) → Choices → Choices

renCtrlₗₑ ξ (Return e) = Return (renₑ ξ e)
renCtrlₗₑ ξ (Var x) = Var x
renCtrlₗₑ ξ Fail = Fail
renCtrlₗₑ ξ (Then E1 E2) = Then (renCtrlₗₑ ξ E1) (renCtrlₗₑ ξ E2)
renCtrlₗₑ ξ (App E1 E2) = App (renCtrlₗₑ ξ E1) (renCtrlₗₑ ξ E2)
renCtrlₗₑ ξ (Fun E) = Fun (renCtrlₗₑ ξ E)
renCtrlₗₑ ξ (Fix E) = Fix (renCtrlₗₑ ξ E)
renCtrlₗₑ ξ (DefLocal E1 E2) = DefLocal (renCtrlₗₑ ξ E1) (renCtrlₗₑ (↑ ξ) E2)
renCtrlₗₑ ξ (LocAbs E) = LocAbs (renCtrlₗₑ ξ E)
renCtrlₗₑ ξ (LocApp E ℓ) = LocApp (renCtrlₗₑ ξ E) ℓ
renCtrlₗₑ ξ (Send E ℓ) = Send (renCtrlₗₑ ξ E) ℓ
renCtrlₗₑ ξ (Receive ℓ) = Receive ℓ
renCtrlₗₑ ξ (If E E1 E2) = If (renCtrlₗₑ ξ E) (renCtrlₗₑ ξ E1) (renCtrlₗₑ ξ E2)
renCtrlₗₑ ξ (ChooseFor d ℓ E) = ChooseFor d ℓ (renCtrlₗₑ ξ E)
renCtrlₗₑ ξ (AllowChoice ℓ C) = AllowChoice ℓ (renChoicesₗₑ ξ C)
renCtrlₗₑ ξ (SendLoc ρ E1 E2) = SendLoc ρ (renCtrlₗₑ ξ E1) (renCtrlₗₑ ξ E2)
renCtrlₗₑ ξ (ReceiveLoc ℓ E) = ReceiveLoc ℓ (renCtrlₗₑ ξ E)
renCtrlₗₑ ξ (AmI ℓ E1 E2) = AmI ℓ (renCtrlₗₑ ξ E1) (renCtrlₗₑ ξ E2)

renChoicesₗₑ ξ NoChoice = NoChoice
renChoicesₗₑ ξ (TChoice ET) = TChoice (renCtrlₗₑ ξ ET)
renChoicesₗₑ ξ (FChoice EF) = FChoice (renCtrlₗₑ ξ EF)
renChoicesₗₑ ξ (TFChoice ET EF) = TFChoice (renCtrlₗₑ ξ ET) (renCtrlₗₑ ξ EF)

-- Renaming local variables respects extensional equality
renCtrlExtₗₑ : ∀{ξ1 ξ2} → ξ1 ≈ ξ2 → renCtrlₗₑ ξ1 ≈ renCtrlₗₑ ξ2
renChoicesExtₗₑ : ∀{ξ1 ξ2} → ξ1 ≈ ξ2 → renChoicesₗₑ ξ1 ≈ renChoicesₗₑ ξ2

renCtrlExtₗₑ ξ1≈ξ2 (Return e) = cong Return (renExtₑ ξ1≈ξ2 e)
renCtrlExtₗₑ ξ1≈ξ2 (Var x) = refl
renCtrlExtₗₑ ξ1≈ξ2 Fail = refl
renCtrlExtₗₑ ξ1≈ξ2 (Then E1 E2) = cong₂ Then (renCtrlExtₗₑ ξ1≈ξ2 E1) (renCtrlExtₗₑ ξ1≈ξ2 E2)
renCtrlExtₗₑ ξ1≈ξ2 (App E1 E2) = cong₂ App (renCtrlExtₗₑ ξ1≈ξ2 E1) (renCtrlExtₗₑ ξ1≈ξ2 E2)
renCtrlExtₗₑ ξ1≈ξ2 (Fun E) = cong Fun (renCtrlExtₗₑ ξ1≈ξ2 E)
renCtrlExtₗₑ ξ1≈ξ2 (Fix E) = cong Fix (renCtrlExtₗₑ ξ1≈ξ2 E)
renCtrlExtₗₑ ξ1≈ξ2 (DefLocal E1 E2) = cong₂ DefLocal (renCtrlExtₗₑ ξ1≈ξ2 E1) (renCtrlExtₗₑ (↑Ext ξ1≈ξ2) E2)
renCtrlExtₗₑ ξ1≈ξ2 (LocAbs E) = cong LocAbs (renCtrlExtₗₑ ξ1≈ξ2 E)
renCtrlExtₗₑ ξ1≈ξ2 (LocApp E ℓ) = cong₂ LocApp (renCtrlExtₗₑ ξ1≈ξ2 E) refl
renCtrlExtₗₑ ξ1≈ξ2 (Send E ℓ) = cong₂ Send (renCtrlExtₗₑ ξ1≈ξ2 E) refl
renCtrlExtₗₑ ξ1≈ξ2 (Receive ℓ) = cong Receive refl
renCtrlExtₗₑ ξ1≈ξ2 (If E E1 E2) = cong₃ If (renCtrlExtₗₑ ξ1≈ξ2 E) (renCtrlExtₗₑ ξ1≈ξ2 E1) (renCtrlExtₗₑ ξ1≈ξ2 E2)
renCtrlExtₗₑ ξ1≈ξ2 (ChooseFor d ℓ E) = cong₃ ChooseFor refl refl (renCtrlExtₗₑ ξ1≈ξ2 E)
renCtrlExtₗₑ ξ1≈ξ2 (AllowChoice ℓ C) = cong₂ AllowChoice refl (renChoicesExtₗₑ ξ1≈ξ2 C)
renCtrlExtₗₑ ξ1≈ξ2 (SendLoc ρ E1 E2) = cong₃ SendLoc refl (renCtrlExtₗₑ ξ1≈ξ2 E1) (renCtrlExtₗₑ ξ1≈ξ2 E2)
renCtrlExtₗₑ ξ1≈ξ2 (ReceiveLoc ℓ E) = cong₂ ReceiveLoc refl (renCtrlExtₗₑ ξ1≈ξ2 E)
renCtrlExtₗₑ ξ1≈ξ2 (AmI ℓ E1 E2) = cong₃ AmI refl (renCtrlExtₗₑ ξ1≈ξ2 E1) (renCtrlExtₗₑ ξ1≈ξ2 E2)

renChoicesExtₗₑ ξ1≈ξ2 NoChoice = refl
renChoicesExtₗₑ ξ1≈ξ2 (TChoice ET) = cong TChoice (renCtrlExtₗₑ ξ1≈ξ2 ET)
renChoicesExtₗₑ ξ1≈ξ2 (FChoice EF) = cong FChoice (renCtrlExtₗₑ ξ1≈ξ2 EF)
renChoicesExtₗₑ ξ1≈ξ2 (TFChoice ET EF) = cong₂ TFChoice (renCtrlExtₗₑ ξ1≈ξ2 ET) (renCtrlExtₗₑ ξ1≈ξ2 EF)

-- Renaming local variables respects the identity
renCtrlIdₗₑ : (E : Ctrl) → renCtrlₗₑ idRen E ≡ E
renChoicesIdₗₑ : (C : Choices) → renChoicesₗₑ idRen C ≡ C

renCtrlIdₗₑ (Return e) = cong Return (renIdₑ e)
renCtrlIdₗₑ (Var x) = refl
renCtrlIdₗₑ Fail = refl
renCtrlIdₗₑ (Then E1 E2) = cong₂ Then (renCtrlIdₗₑ E1) (renCtrlIdₗₑ E2)
renCtrlIdₗₑ (App E1 E2) = cong₂ App (renCtrlIdₗₑ E1) (renCtrlIdₗₑ E2)
renCtrlIdₗₑ (Fun E) = cong Fun (renCtrlIdₗₑ E)
renCtrlIdₗₑ (Fix E) = cong Fix (renCtrlIdₗₑ E)
renCtrlIdₗₑ (DefLocal E1 E2) = cong₂ DefLocal (renCtrlIdₗₑ E1) (renCtrlExtₗₑ ↑Id E2 ∙ renCtrlIdₗₑ E2)
renCtrlIdₗₑ (LocAbs E) = cong LocAbs (renCtrlIdₗₑ E)
renCtrlIdₗₑ (LocApp E ℓ) = cong₂ LocApp (renCtrlIdₗₑ E) refl
renCtrlIdₗₑ (Send E ℓ) = cong₂ Send (renCtrlIdₗₑ E) refl
renCtrlIdₗₑ (Receive ℓ) = cong Receive refl
renCtrlIdₗₑ (If E E1 E2) = cong₃ If (renCtrlIdₗₑ E) (renCtrlIdₗₑ E1) (renCtrlIdₗₑ E2)
renCtrlIdₗₑ (ChooseFor d ℓ E) = cong₃ ChooseFor refl refl (renCtrlIdₗₑ E)
renCtrlIdₗₑ (AllowChoice ℓ C) = cong₂ AllowChoice refl (renChoicesIdₗₑ C)
renCtrlIdₗₑ (SendLoc ρ E1 E2) = cong₃ SendLoc refl (renCtrlIdₗₑ E1) (renCtrlIdₗₑ E2)
renCtrlIdₗₑ (ReceiveLoc ℓ E) = cong₂ ReceiveLoc refl (renCtrlIdₗₑ E)
renCtrlIdₗₑ (AmI ℓ E1 E2) = cong₃ AmI refl (renCtrlIdₗₑ E1) (renCtrlIdₗₑ E2)

renChoicesIdₗₑ NoChoice = refl
renChoicesIdₗₑ (TChoice ET) = cong TChoice (renCtrlIdₗₑ ET)
renChoicesIdₗₑ (FChoice EF) = cong FChoice (renCtrlIdₗₑ EF)
renChoicesIdₗₑ (TFChoice ET EF) = cong₂ TFChoice (renCtrlIdₗₑ ET) (renCtrlIdₗₑ EF)

-- Renaming local variables enjoys fusion
renCtrlFuseₗₑ : (ξ1 ξ2 : ℕ → ℕ) → renCtrlₗₑ (ξ1 ∘ ξ2) ≈ renCtrlₗₑ ξ1 ∘ renCtrlₗₑ ξ2
renChoicesFuseₗₑ : (ξ1 ξ2 : ℕ → ℕ) → renChoicesₗₑ (ξ1 ∘ ξ2) ≈ renChoicesₗₑ ξ1 ∘ renChoicesₗₑ ξ2

renCtrlFuseₗₑ ξ1 ξ2 (Return e) = cong Return (renFuseₑ ξ1 ξ2 e)
renCtrlFuseₗₑ ξ1 ξ2 (Var x) = refl
renCtrlFuseₗₑ ξ1 ξ2 Fail = refl
renCtrlFuseₗₑ ξ1 ξ2 (Then E1 E2) = cong₂ Then (renCtrlFuseₗₑ ξ1 ξ2 E1) (renCtrlFuseₗₑ ξ1 ξ2 E2)
renCtrlFuseₗₑ ξ1 ξ2 (App E1 E2) = cong₂ App (renCtrlFuseₗₑ ξ1 ξ2 E1) (renCtrlFuseₗₑ ξ1 ξ2 E2)
renCtrlFuseₗₑ ξ1 ξ2 (Fun E) = cong Fun (renCtrlFuseₗₑ ξ1 ξ2 E)
renCtrlFuseₗₑ ξ1 ξ2 (Fix E) = cong Fix (renCtrlFuseₗₑ ξ1 ξ2 E)
renCtrlFuseₗₑ ξ1 ξ2 (DefLocal E1 E2) = cong₂ DefLocal (renCtrlFuseₗₑ ξ1 ξ2 E1) (renCtrlExtₗₑ (↑Fuse ξ1 ξ2) E2 ∙ renCtrlFuseₗₑ (↑ ξ1) (↑ ξ2) E2)
renCtrlFuseₗₑ ξ1 ξ2 (LocAbs E) = cong LocAbs (renCtrlFuseₗₑ ξ1 ξ2 E)
renCtrlFuseₗₑ ξ1 ξ2 (LocApp E ℓ) = cong₂ LocApp (renCtrlFuseₗₑ ξ1 ξ2 E) refl
renCtrlFuseₗₑ ξ1 ξ2 (Send E ℓ) = cong₂ Send (renCtrlFuseₗₑ ξ1 ξ2 E) refl
renCtrlFuseₗₑ ξ1 ξ2 (Receive ℓ) = cong Receive refl
renCtrlFuseₗₑ ξ1 ξ2 (If E E1 E2) = cong₃ If (renCtrlFuseₗₑ ξ1 ξ2 E) (renCtrlFuseₗₑ ξ1 ξ2 E1) (renCtrlFuseₗₑ ξ1 ξ2 E2)
renCtrlFuseₗₑ ξ1 ξ2 (ChooseFor d ℓ E) = cong₃ ChooseFor refl refl (renCtrlFuseₗₑ ξ1 ξ2 E)
renCtrlFuseₗₑ ξ1 ξ2 (AllowChoice ℓ C) = cong₂ AllowChoice refl (renChoicesFuseₗₑ ξ1 ξ2 C)
renCtrlFuseₗₑ ξ1 ξ2 (SendLoc ρ E1 E2) = cong₃ SendLoc refl (renCtrlFuseₗₑ ξ1 ξ2 E1) (renCtrlFuseₗₑ ξ1 ξ2 E2)
renCtrlFuseₗₑ ξ1 ξ2 (ReceiveLoc ℓ E) = cong₂ ReceiveLoc refl (renCtrlFuseₗₑ ξ1 ξ2 E)
renCtrlFuseₗₑ ξ1 ξ2 (AmI ℓ E1 E2) = cong₃ AmI refl (renCtrlFuseₗₑ ξ1 ξ2 E1) (renCtrlFuseₗₑ ξ1 ξ2 E2)

renChoicesFuseₗₑ ξ1 ξ2 NoChoice = refl
renChoicesFuseₗₑ ξ1 ξ2 (TChoice ET) = cong TChoice (renCtrlFuseₗₑ ξ1 ξ2 ET)
renChoicesFuseₗₑ ξ1 ξ2 (FChoice EF) = cong FChoice (renCtrlFuseₗₑ ξ1 ξ2 EF)
renChoicesFuseₗₑ ξ1 ξ2 (TFChoice ET EF) = cong₂ TFChoice (renCtrlFuseₗₑ ξ1 ξ2 ET) (renCtrlFuseₗₑ ξ1 ξ2 EF)


-- Substitute the local variables in a control expression
subCtrlₗₑ : (ℕ → Expr) → Ctrl → Ctrl
subChoicesₗₑ : (ℕ → Expr) → Choices → Choices

subCtrlₗₑ σ (Return e) = Return (subₑ σ e)
subCtrlₗₑ σ (Var x) = Var x
subCtrlₗₑ σ Fail = Fail
subCtrlₗₑ σ (Then E1 E2) = Then (subCtrlₗₑ σ E1) (subCtrlₗₑ σ E2)
subCtrlₗₑ σ (App E1 E2) = App (subCtrlₗₑ σ E1) (subCtrlₗₑ σ E2)
subCtrlₗₑ σ (Fun E) = Fun (subCtrlₗₑ σ E)
subCtrlₗₑ σ (Fix E) = Fix (subCtrlₗₑ σ E)
subCtrlₗₑ σ (DefLocal E1 E2) = DefLocal (subCtrlₗₑ σ E1) (subCtrlₗₑ (↑σₑ σ) E2)
subCtrlₗₑ σ (LocAbs E) = LocAbs (subCtrlₗₑ σ E)
subCtrlₗₑ σ (LocApp E ℓ) = LocApp (subCtrlₗₑ σ E) ℓ
subCtrlₗₑ σ (Send E ℓ) = Send (subCtrlₗₑ σ E) ℓ
subCtrlₗₑ σ (Receive ℓ) = Receive ℓ
subCtrlₗₑ σ (If E E1 E2) = If (subCtrlₗₑ σ E) (subCtrlₗₑ σ E1) (subCtrlₗₑ σ E2)
subCtrlₗₑ σ (ChooseFor d ℓ E) = ChooseFor d ℓ (subCtrlₗₑ σ E)
subCtrlₗₑ σ (AllowChoice ℓ C) = AllowChoice ℓ (subChoicesₗₑ σ C)
subCtrlₗₑ σ (SendLoc ρ E1 E2) = SendLoc ρ (subCtrlₗₑ σ E1) (subCtrlₗₑ σ E2)
subCtrlₗₑ σ (ReceiveLoc ℓ E) = ReceiveLoc ℓ (subCtrlₗₑ σ E)
subCtrlₗₑ σ (AmI ℓ E1 E2) = AmI ℓ (subCtrlₗₑ σ E1) (subCtrlₗₑ σ E2)

subChoicesₗₑ σ NoChoice = NoChoice
subChoicesₗₑ σ (TChoice ET) = TChoice (subCtrlₗₑ σ ET)
subChoicesₗₑ σ (FChoice EF) = FChoice (subCtrlₗₑ σ EF)
subChoicesₗₑ σ (TFChoice ET EF) = TFChoice (subCtrlₗₑ σ ET) (subCtrlₗₑ σ EF)

-- Substituting local variables respects extensional equality
subCtrlExtₗₑ : ∀{σ1 σ2} → σ1 ≈ σ2 → subCtrlₗₑ σ1 ≈ subCtrlₗₑ σ2
subChoicesExtₗₑ : ∀{σ1 σ2} → σ1 ≈ σ2 → subChoicesₗₑ σ1 ≈ subChoicesₗₑ σ2

subCtrlExtₗₑ σ1≈σ2 (Return e) = cong Return (subExtₑ σ1≈σ2 e)
subCtrlExtₗₑ σ1≈σ2 (Var x) = refl
subCtrlExtₗₑ σ1≈σ2 Fail = refl
subCtrlExtₗₑ σ1≈σ2 (Then E1 E2) = cong₂ Then (subCtrlExtₗₑ σ1≈σ2 E1) (subCtrlExtₗₑ σ1≈σ2 E2)
subCtrlExtₗₑ σ1≈σ2 (App E1 E2) = cong₂ App (subCtrlExtₗₑ σ1≈σ2 E1) (subCtrlExtₗₑ σ1≈σ2 E2)
subCtrlExtₗₑ σ1≈σ2 (Fun E) = cong Fun (subCtrlExtₗₑ σ1≈σ2 E)
subCtrlExtₗₑ σ1≈σ2 (Fix E) = cong Fix (subCtrlExtₗₑ σ1≈σ2 E)
subCtrlExtₗₑ σ1≈σ2 (DefLocal E1 E2) = cong₂ DefLocal (subCtrlExtₗₑ σ1≈σ2 E1) (subCtrlExtₗₑ (↑σExtₑ σ1≈σ2) E2)
subCtrlExtₗₑ σ1≈σ2 (LocAbs E) = cong LocAbs (subCtrlExtₗₑ σ1≈σ2 E)
subCtrlExtₗₑ σ1≈σ2 (LocApp E ℓ) = cong₂ LocApp (subCtrlExtₗₑ σ1≈σ2 E) refl
subCtrlExtₗₑ σ1≈σ2 (Send E ℓ) = cong₂ Send (subCtrlExtₗₑ σ1≈σ2 E) refl
subCtrlExtₗₑ σ1≈σ2 (Receive ℓ) = cong Receive refl
subCtrlExtₗₑ σ1≈σ2 (If E E1 E2) = cong₃ If (subCtrlExtₗₑ σ1≈σ2 E) (subCtrlExtₗₑ σ1≈σ2 E1) (subCtrlExtₗₑ σ1≈σ2 E2)
subCtrlExtₗₑ σ1≈σ2 (ChooseFor d ℓ E) = cong₃ ChooseFor refl refl (subCtrlExtₗₑ σ1≈σ2 E)
subCtrlExtₗₑ σ1≈σ2 (AllowChoice ℓ C) = cong₂ AllowChoice refl (subChoicesExtₗₑ σ1≈σ2 C)
subCtrlExtₗₑ σ1≈σ2 (SendLoc ρ E1 E2) = cong₃ SendLoc refl (subCtrlExtₗₑ σ1≈σ2 E1) (subCtrlExtₗₑ σ1≈σ2 E2)
subCtrlExtₗₑ σ1≈σ2 (ReceiveLoc ℓ E) = cong₂ ReceiveLoc refl (subCtrlExtₗₑ σ1≈σ2 E)
subCtrlExtₗₑ σ1≈σ2 (AmI ℓ E1 E2) = cong₃ AmI refl (subCtrlExtₗₑ σ1≈σ2 E1) (subCtrlExtₗₑ σ1≈σ2 E2)

subChoicesExtₗₑ σ1≈σ2 NoChoice = refl
subChoicesExtₗₑ σ1≈σ2 (TChoice ET) = cong TChoice (subCtrlExtₗₑ σ1≈σ2 ET)
subChoicesExtₗₑ σ1≈σ2 (FChoice EF) = cong FChoice (subCtrlExtₗₑ σ1≈σ2 EF)
subChoicesExtₗₑ σ1≈σ2 (TFChoice ET EF) = cong₂ TFChoice (subCtrlExtₗₑ σ1≈σ2 ET) (subCtrlExtₗₑ σ1≈σ2 EF)

-- Substituting local variables respects the identity
subCtrlIdₗₑ : ∀ E → subCtrlₗₑ idSubₑ E ≡ E
subChoicesIdₗₑ : ∀ C → subChoicesₗₑ idSubₑ C ≡ C

subCtrlIdₗₑ (Return e) = cong Return (subIdₑ e)
subCtrlIdₗₑ (Var x) = refl
subCtrlIdₗₑ Fail = refl
subCtrlIdₗₑ (Then E1 E2) = cong₂ Then (subCtrlIdₗₑ E1) (subCtrlIdₗₑ E2)
subCtrlIdₗₑ (App E1 E2) = cong₂ App (subCtrlIdₗₑ E1) (subCtrlIdₗₑ E2)
subCtrlIdₗₑ (Fun E) = cong Fun (subCtrlIdₗₑ E)
subCtrlIdₗₑ (Fix E) = cong Fix (subCtrlIdₗₑ E)
subCtrlIdₗₑ (DefLocal E1 E2) = cong₂ DefLocal (subCtrlIdₗₑ E1) (subCtrlExtₗₑ ↑σIdₑ E2 ∙ subCtrlIdₗₑ E2)
subCtrlIdₗₑ (LocAbs E) = cong LocAbs (subCtrlIdₗₑ E)
subCtrlIdₗₑ (LocApp E ℓ) = cong₂ LocApp (subCtrlIdₗₑ E) refl
subCtrlIdₗₑ (Send E ℓ) = cong₂ Send (subCtrlIdₗₑ E) refl
subCtrlIdₗₑ (Receive ℓ) = cong Receive refl
subCtrlIdₗₑ (If E E1 E2) = cong₃ If (subCtrlIdₗₑ E) (subCtrlIdₗₑ E1) (subCtrlIdₗₑ E2)
subCtrlIdₗₑ (ChooseFor d ℓ E) = cong₃ ChooseFor refl refl (subCtrlIdₗₑ E)
subCtrlIdₗₑ (AllowChoice ℓ C) = cong₂ AllowChoice refl (subChoicesIdₗₑ C)
subCtrlIdₗₑ (SendLoc ρ E1 E2) = cong₃ SendLoc refl (subCtrlIdₗₑ E1) (subCtrlIdₗₑ E2)
subCtrlIdₗₑ (ReceiveLoc ℓ E) = cong₂ ReceiveLoc refl (subCtrlIdₗₑ E)
subCtrlIdₗₑ (AmI ℓ E1 E2) = cong₃ AmI refl (subCtrlIdₗₑ E1) (subCtrlIdₗₑ E2)

subChoicesIdₗₑ NoChoice = refl
subChoicesIdₗₑ (TChoice ET) = cong TChoice (subCtrlIdₗₑ ET)
subChoicesIdₗₑ (FChoice EF) = cong FChoice (subCtrlIdₗₑ EF)
subChoicesIdₗₑ (TFChoice ET EF) = cong₂ TFChoice (subCtrlIdₗₑ ET) (subCtrlIdₗₑ EF)
