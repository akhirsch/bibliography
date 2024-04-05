{-# OPTIONS --safe #-}

open import Level renaming (_⊔_ to ℓ-max; suc to ℓ-suc; zero to ℓ-zero)
open import Data.Nat renaming (_≟_ to ≡-dec-ℕ; _⊔_ to max)
open import Data.Nat.Induction
open import Data.Bool renaming (_≟_ to ≡-dec-Bool) hiding (_<_)
open import Data.Maybe
open import Data.List hiding (map)
open import Data.List.Properties renaming (≡-dec to ≡-dec-List)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function
open import Induction.WellFounded

open import Common
open import TypedLocalLang
open import Locations

module EndpointProjection
  (L : Location)
  (E : TypedLocalLanguage L)
  where

open import Types L E
open import Choreographies L E
open import LocalRenamings L E
open import LocationRenamings L E
open import Renamings L E
open import LocationSubstitutions L E
open import LocalSubstitutions L E
open import Substitutions L E
open import LocationContexts L E
open import LocalContexts L E
open import GlobalContexts L E
open import ControlLang L E

open Location L
open TypedLocalLanguage E

open ≡-Reasoning

-- Merging operator
data Merge : (E1 E2 E : Ctrl) → Set
data MergeChoice : (C1 C2 C : Choices) → Set

data Merge where
  MergeRet : ∀{e} → Merge (Return e) (Return e) (Return e)
  MergeVar : ∀{x} → Merge (Var x) (Var x) (Var x)
  MergeEnd : Merge End End End
  MergeThen : ∀{E11 E12 E21 E22 E1 E2} →
              Merge E11 E12 E1 →
              Merge E21 E22 E2 →
              Merge (Then E11 E12) (Then E21 E22) (Then E1 E2)
  MergeApp : ∀{E11 E12 E21 E22 E1 E2} →
              Merge E11 E12 E1 →
              Merge E21 E22 E2 →
              Merge (App E11 E12) (App E21 E22) (App E1 E2)
  MergeFun : ∀{E1 E2 E} →
             Merge E1 E2 E →
             Merge (Fun E1) (Fun E2) (Fun E)
  MergeFix : ∀{E1 E2 E} →
             Merge E1 E2 E →
             Merge (Fix E1) (Fix E2) (Fix E)
  MergeDefLocal : ∀{E11 E12 E21 E22 E1 E2} →
                  Merge E11 E12 E1 →
                  Merge E21 E22 E2 →
                  Merge (DefLocal E11 E12) (DefLocal E21 E22) (DefLocal E1 E2)
  MergeLocAbs : ∀{E1 E2 E} →
                Merge E1 E2 E →
                Merge (LocAbs E1) (LocAbs E2) (LocAbs E)
  MergeLocApp : ∀{E1 E2 E ℓ} →
                Merge E1 E2 E →
                Merge (LocApp E1 ℓ) (LocApp E2 ℓ) (LocApp E ℓ)
  MergeSend : ∀{E1 E2 E ℓ} →
              Merge E1 E2 E →
              Merge (Send E1 ℓ) (Send E2 ℓ) (Send E ℓ)
  MergeReceive : ∀{ℓ} → Merge (Receive ℓ) (Receive ℓ) (Receive ℓ)
  MergeIf : ∀{E1 E11 E12 E2 E21 E22 E E1 E2 : Ctrl} →
            Merge E1 E2 E →
            Merge E11 E12 E1 →
            Merge E21 E22 E2 →
            Merge (If E1 E11 E12) (If E2 E21 E22) (If E E1 E2)
  MergeChooseFor : ∀{ℓ d E1 E2 E} →
                   Merge E1 E2 E →
                   Merge (ChooseFor ℓ d E1) (ChooseFor ℓ d E2) (ChooseFor ℓ d E)
  MergeAllowChoice : ∀{ℓ C1 C2 C} →
                     MergeChoice C1 C2 C →
                     Merge (AllowChoice ℓ C1) (AllowChoice ℓ C2) (AllowChoice ℓ C)
  MergeSendLoc : ∀{ρ E11 E12 E21 E22 E1 E2} →
                  Merge E11 E12 E1 →
                  Merge E21 E22 E2 →
                  Merge (SendLoc ρ E11 E12) (SendLoc ρ E21 E22) (SendLoc ρ E1 E2)
  MergeReceiveLoc : ∀{E1 E2 E ℓ} →
                    Merge E1 E2 E →
                    Merge (ReceiveLoc ℓ E1) (ReceiveLoc ℓ E2) (ReceiveLoc ℓ E)
  MergeAmI : ∀{ℓ E11 E12 E21 E22 E1 E2} →
             Merge E11 E12 E1 →
             Merge E21 E22 E2 →
             Merge (AmI ℓ E11 E12) (AmI ℓ E21 E22) (AmI ℓ E1 E2)

data MergeChoice where
  MergeN₁ : ∀{C} → MergeChoice NoChoice C C
  MergeN₂ : ∀{C} → MergeChoice C NoChoice C
  MergeTT : ∀{E1 E2 E} → 
            Merge E1 E2 E →
            MergeChoice (TChoice E1) (TChoice E2) (TChoice E)
  MergeFF : ∀{E1 E2 E} → 
            Merge E1 E2 E →
            MergeChoice (FChoice E1) (FChoice E2) (FChoice E)
  MergeTF : ∀{E1 E2} → MergeChoice (TChoice E1) (FChoice E2) (TFChoice E1 E2)
  MergeFT : ∀{E1 E2} → MergeChoice (FChoice E1) (TChoice E2) (TFChoice E2 E1)
  MergeTTF : ∀{E1T E2T E2F ET} →
             Merge E1T E2T ET →
             MergeChoice (TChoice E1T) (TFChoice E2T E2F) (TFChoice ET E2F)
  MergeFTF : ∀{E1F E2T E2F EF} →
             Merge E1F E2F EF →
             MergeChoice (FChoice E1F) (TFChoice E2T E2F) (TFChoice E2T EF)
  MergeTFT : ∀{E1T E1F E2T ET} →
             Merge E1T E2T ET →
             MergeChoice (TFChoice E1T E1F) (TChoice E2T) (TFChoice ET E1F)
  MergeTFF : ∀{E1T E1F E2F EF} →
             Merge E1F E2F EF →
             MergeChoice (TFChoice E1T E1F) (FChoice E2F) (TFChoice E1T EF)
  MergeTFTF : ∀{E1T E1F E2T E2F ET EF} →
              Merge E1T E2T ET →
              Merge E1F E2F EF →
              MergeChoice (TFChoice E1T E1F) (TFChoice E2T E2F) (TFChoice ET EF)

-- Endpoint projection
data ⟦_⊢_∣_⟧≡_ : LocalCtx → Chor → LocVal → Ctrl → Set where
  ProjDoneYes : ∀{Δ L e} → ⟦ Δ ⊢ Done (Lit L) e ∣ L ⟧≡ Return e
  ProjDoneNo : ∀{Δ L ℓ e} → L ≢ ℓ → ⟦ Δ ⊢ Done (Lit ℓ) e ∣ L ⟧≡ End

  ProjVar : ∀{Δ L x} → ⟦ Δ ⊢ Var x ∣ L ⟧≡ Var x

  ProjSendYesYes : ∀{Δ L C E} →
                   ⟦ Δ ⊢ C ∣ L ⟧≡ E →
                   ⟦ Δ ⊢ Send (Lit L) C (Lit L) ∣ L ⟧≡ E
  ProjSendYesNo : ∀{Δ L ℓ₂ C E} →
                  Lit L ≢ ℓ₂ →
                  ⟦ Δ ⊢ C ∣ L ⟧≡ E →
                  ⟦ Δ ⊢ Send (Lit L) C ℓ₂ ∣ L ⟧≡ Send E ℓ₂
  ProjSendNoYes : ∀{Δ L ℓ₁ C E} →
                  Lit L ≢ ℓ₁ →
                  ⟦ Δ ⊢ C ∣ L ⟧≡ E →
                  ⟦ Δ ⊢ Send ℓ₁ C (Lit L) ∣ L ⟧≡ App (Fun E) (Receive ℓ₁)
  ProjSendNoNo : ∀{Δ L ℓ₁ ℓ₂ C E} →
                  Lit L ≢ ℓ₁ →
                  Lit L ≢ ℓ₂ →
                  ⟦ Δ ⊢ C ∣ L ⟧≡ E →
                  ⟦ Δ ⊢ Send ℓ₁ C ℓ₂ ∣ L ⟧≡ End
  
  ProjIfYes : ∀{Δ L C C1 C2 E E1 E2} →
              ⟦ Δ ⊢ C ∣ L ⟧≡ E →
              ⟦ Δ ⊢ C1 ∣ L ⟧≡ E1 →
              ⟦ Δ ⊢ C2 ∣ L ⟧≡ E2 →
              ⟦ Δ ⊢ If (Lit L) C C1 C2 ∣ L ⟧≡ If E E1 E2
  ProjIfNo : ∀{Δ L ℓ C C1 C2 E1 E2 E1⊔E2} →
              Lit L ≢ ℓ →
              ⟦ Δ ⊢ C1 ∣ L ⟧≡ E1 →
              ⟦ Δ ⊢ C2 ∣ L ⟧≡ E2 →
              Merge E1 E2 E1⊔E2 →
              ⟦ Δ ⊢ If ℓ C C1 C2 ∣ L ⟧≡ E1⊔E2

  ProjSyncYesYes : ∀{Δ L d C E} →
                   ⟦ Δ ⊢ C ∣ L ⟧≡ E →
                   ⟦ Δ ⊢ Sync (Lit L) d (Lit L) C ∣ L ⟧≡ E
  ProjSyncYesNo : ∀{Δ L d ℓ₂ C E} →
                  Lit L ≢ ℓ₂ →
                  ⟦ Δ ⊢ C ∣ L ⟧≡ E →
                  ⟦ Δ ⊢ Sync (Lit L) d ℓ₂ C ∣ L ⟧≡ ChooseFor d ℓ₂ E
  ProjSyncNoYesTrue : ∀{Δ L ℓ₁ C E} →
                      Lit L ≢ ℓ₁ →
                      ⟦ Δ ⊢ C ∣ L ⟧≡ E →
                      ⟦ Δ ⊢ Sync ℓ₁ true (Lit L) C ∣ L ⟧≡ AllowChoice ℓ₁ (TChoice E)
  ProjSyncNoYesFalse : ∀{Δ L ℓ₁ C E} →
                       Lit L ≢ ℓ₁ →
                       ⟦ Δ ⊢ C ∣ L ⟧≡ E →
                       ⟦ Δ ⊢ Sync ℓ₁ false (Lit L) C ∣ L ⟧≡ AllowChoice ℓ₁ (FChoice E)
  ProjSyncNoNo : ∀{Δ L ℓ₁ d ℓ₂ C E} →
                  Lit L ≢ ℓ₁ →
                  Lit L ≢ ℓ₂ →
                  ⟦ Δ ⊢ C ∣ L ⟧≡ E →
                  ⟦ Δ ⊢ Sync ℓ₁ d ℓ₂ C ∣ L ⟧≡ E
  
  ProjDefLocalYes : ∀{Δ L t C1 C2 E1 E2} →
                    ⟦ Δ ⊢ C1 ∣ L ⟧≡ E1 →
                    ⟦ (Lit L , t) ∷ Δ ⊢ C2 ∣ L ⟧≡ E2 →
                    ⟦ Δ ⊢ DefLocal (Lit L) t C1 C2 ∣ L ⟧≡ DefLocal E1 E2
  ProjDefLocalNo : ∀{Δ L ℓ t C1 C2 E1 E2} →
                    Lit L ≢ ℓ →
                    ⟦ Δ ⊢ C1 ∣ L ⟧≡ E1 →
                    ⟦ (ℓ , t) ∷ Δ ⊢ C2 ∣ L ⟧≡ E2 →
                    ⟦ Δ ⊢ DefLocal ℓ t C1 C2 ∣ L ⟧≡ App (Fun E2) E1

  ProjFun : ∀{Δ L τ C E} →
            ⟦ Δ ⊢ C ∣ L ⟧≡ E →
            ⟦ Δ ⊢ Fun τ C ∣ L ⟧≡ Fun E
  ProjFix : ∀{Δ L τ C E} →
            ⟦ Δ ⊢ C ∣ L ⟧≡ E →
            ⟦ Δ ⊢ Fix τ C ∣ L ⟧≡ Fix E
  ProjApp : ∀{Δ L C1 C2 E1 E2} →
            ⟦ Δ ⊢ C1 ∣ L ⟧≡ E1 →
            ⟦ Δ ⊢ C2 ∣ L ⟧≡ E2 →
            ⟦ Δ ⊢ App C1 C2 ∣ L ⟧≡ App E1 E2
  
  ProjLocAbs : ∀{Δ L C E EL} →
               ⟦ Δ ⊢ subₗ Δ (idSubₗ ▸ₗ Lit L) C ∣ L ⟧≡ EL →
               ⟦ Δ ⊢ C ∣ L ⟧≡ E →
               ⟦ Δ ⊢ LocAbs C ∣ L ⟧≡ LocAbs (AmI (Var zero) (renCtrlₗ suc EL) E)
  ProjLocApp : ∀{Δ L C ℓ E} →
                ⟦ Δ ⊢ C ∣ L ⟧≡ E →
                ⟦ Δ ⊢ LocApp C ℓ ∣ L ⟧≡ LocApp E ℓ

  ProjTellLetYesYes : ∀{Δ L ρ1 C1 ρ2 C2 E1 E2 E2L} →
                      Lit L ∈ (ρ1 ++ ρ2) →
                      ⟦ Δ ⊢ C1 ∣ L ⟧≡ E1 →
                      ⟦ Δ ⊢ subₗ Δ (idSubₗ ▸ₗ Lit L) C2 ∣ L ⟧≡ E2L →
                      ⟦ Δ ⊢ C2 ∣ L ⟧≡ E2 →
                      ⟦ Δ ⊢ TellLet (Lit L) ρ1 C1 ρ2 C2 ∣ L ⟧≡
                      SendLoc (ρ1 ++ ρ2) E1 (AmI (Var zero) (renCtrlₗ suc E2L) E2)
  ProjTellLetYesNo : ∀{Δ L ρ1 C1 ρ2 C2 E1 E2} →
                      Lit L ∉ (ρ1 ++ ρ2) →
                      ⟦ Δ ⊢ C1 ∣ L ⟧≡ E1 →
                      ⟦ Δ ⊢ C2 ∣ L ⟧≡ E2 →
                      ⟦ Δ ⊢ TellLet (Lit L) ρ1 C1 ρ2 C2 ∣ L ⟧≡
                      SendLoc (ρ1 ++ ρ2) E1 E2
  ProjTellLetNoYes : ∀{Δ L ℓ ρ1 C1 ρ2 C2 E1 E2 E2L} →
                      Lit L ≢ ℓ →
                      Lit L ∈ (ρ1 ++ ρ2) →
                      ⟦ Δ ⊢ C1 ∣ L ⟧≡ E1 →
                      ⟦ Δ ⊢ subₗ Δ (idSubₗ ▸ₗ Lit L) C2 ∣ L ⟧≡ E2L →
                      ⟦ Δ ⊢ C2 ∣ L ⟧≡ E2 →
                      ⟦ Δ ⊢ TellLet (Lit L) ρ1 C1 ρ2 C2 ∣ L ⟧≡
                      ReceiveLoc ℓ (AmI (Var zero) (renCtrlₗ suc E2L) E2)
  ProjTellLetNoNo : ∀{Δ L ℓ ρ1 C1 ρ2 C2 E1 E2} →
                      Lit L ≢ ℓ →
                      Lit L ∉ (ρ1 ++ ρ2) →
                      ⟦ Δ ⊢ C1 ∣ L ⟧≡ E1 →
                      ⟦ Δ ⊢ C2 ∣ L ⟧≡ E2 →
                      ⟦ Δ ⊢ TellLet (Lit L) ρ1 C1 ρ2 C2 ∣ L ⟧≡
                      App (Fun E2) E1
