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

module ControlSemantics
  (L : Location)
  (E : LawfulLanguage L)
  where

open Location L
open LawfulLanguage E
open import ControlLang L E
open ≡-Reasoning

data CtrlTraceElem : Set where
  • : CtrlTraceElem
  SendVal : (v : Expr) →
            (v-Val : Valₑ v) →
            (L : LocVal) →
            CtrlTraceElem
  RecvVal : (L : LocVal) →
            (v : Expr) →
            (v-Val : Valₑ v) →
            CtrlTraceElem
  SendChoice : (d : Bool) →
               (L : LocVal) →
               CtrlTraceElem
  RecvChoice : (L : LocVal) →
               (d : Bool) →
               CtrlTraceElem
  Sync : CtrlTraceElem
  Fun Arg : CtrlTraceElem → CtrlTraceElem
  SendLoc : (LV : LocVal) →
            (LS : List LocVal) →
            CtrlTraceElem
  RecvLoc : (L : LocVal) →
            (LV : LocVal) →
            CtrlTraceElem

CtrlTrace : Set
CtrlTrace = List CtrlTraceElem

data _⇒[_∣_]E_ : Ctrl → CtrlTraceElem → LocVal → Ctrl → Set where
  stepReturn : ∀{e1 e2 L} →
               (e1⇒e2 : e1 ⇒ₑ e2) →
               Return e1
               ⇒[ • ∣ L ]E
               Return e2
  
  stepThen : ∀{E1 E1' E2 T L} →
              (E1⇒E1' : E1 ⇒[ T ∣ L ]E E1') →
              Then E1 E2 ⇒[ T ∣ L ]E Then E1' E2
  stepThenV : ∀{V E L} →
              (V-Val : ValE V) →
              Then V E ⇒[ • ∣ L ]E E
  
  stepAppFun : ∀{E1 E1' E2 T L}
               (E1⇒E1' : E1 ⇒[ T ∣ L ]E E1') →
               App E1 E2 ⇒[ Fun T ∣ L ]E App E1' E2
  stepAppArg : ∀{V E E' T L} →
               (V-Val : ValE V)
               (E⇒E' : E ⇒[ T ∣ L ]E E') →
               App V E ⇒[ Arg T ∣ L ]E App V E'
  stepApp : ∀{V E L}
            (V-Val : ValE V) →
            App (Fun E) V
            ⇒[ • ∣ L ]E
            subCtrl (idSubCtrl ▸Ctrl V) E
  stepFix : ∀{E L} →
            Fix E
            ⇒[ • ∣ L ]E
            subCtrl (idSubCtrl ▸Ctrl Fix E) E

  stepDefLocal : ∀{E1 E1' E2 T L}
                  (E1⇒E1' : E1 ⇒[ T ∣ L ]E E1') →
                  DefLocal E1 E2
                  ⇒[ T ∣ L ]E
                  DefLocal E1' E2
  stepDefLocalV : ∀{v E L}
                  (v-Val : Valₑ v) →
                  DefLocal (Return v) E
                  ⇒[ • ∣ L ]E
                  subCtrlₗₑ (idSubₑ ▸ₑ v) E

  stepLocAppFun : ∀{E E' T L L'} →
                  (E⇒E' : E ⇒[ T ∣ L' ]E E') →
                  LocApp E (Lit L)
                  ⇒[ T ∣ L' ]E
                  LocApp E' (Lit L)
  stepLocApp : ∀{E L L'} →
                LocApp (LocAbs E) (Lit L)
                ⇒[ • ∣ L' ]E
                subCtrlₗ (idSubₗ ▸ₗ Lit L) E

  stepSend : ∀{E E' L T L'}
              (E⇒E' : E ⇒[ T ∣ L' ]E E') →
              Send E (Lit L)
              ⇒[ T ∣ L' ]E
              Send E' (Lit L)
  stepSendV : ∀{v L L'}
              (v-Val : Valₑ v) →
              Send (Return v) (Lit L)
              ⇒[ SendVal v v-Val L ∣ L' ]E
              End
  stepReceive : ∀{L v L'} →
                (v-Val : Valₑ v) →
                Receive (Lit L)
                ⇒[ RecvVal L v v-Val ∣ L' ]E
                Return v

  stepIf : ∀{E E' E1 E2 T L} →
           (E⇒E' : E ⇒[ T ∣ L ]E E') →
           If E E1 E2
           ⇒[ T ∣ L ]E
           If E' E1 E2
  stepIfT : ∀{E1 E2 L} →
            If (Return ttₑ) E1 E2
            ⇒[ • ∣ L ]E
            E1
  stepIfF : ∀{E1 E2 L} →
            If (Return ffₑ) E1 E2
            ⇒[ • ∣ L ]E
            E1

  stepChooseFor : ∀{d L E L'} →
                  ChooseFor d (Lit L) E
                  ⇒[ SendChoice d L ∣ L' ]E
                  E
  stepAllowChoiceT : ∀{L E1 E2 L'} →
                    AllowChoice (Lit L) (TFChoice E1 E2)
                    ⇒[ RecvChoice L true ∣ L' ]E
                    E1
  stepAllowChoiceF : ∀{L E1 E2 L'} →
                    AllowChoice (Lit L) (TFChoice E1 E2)
                    ⇒[ RecvChoice L false ∣ L' ]E
                    E2

  stepSendLoc : ∀{ρ E1 E1' E2 T} L →
                (E1⇒E1' : E1 ⇒[ T ∣ L ]E E1') →
                SendLoc ρ E1 E2
                ⇒[ T ∣ L ]E
                SendLoc ρ E1' E2
  stepSendLocV : ∀{LS LV E2 L} →
                 SendLoc (map Lit LS) (Return (locₑ LV)) E2
                 ⇒[ SendLoc LV LS ∣ L ]E
                 subCtrlₗ (idSubₗ ▸ₗ Lit LV) E2
  stepReceiveLoc : ∀{L LV E L'} →
                   ReceiveLoc (Lit L) E
                   ⇒[ RecvLoc L LV ∣ L' ]E
                   subCtrlₗ (idSubₗ ▸ₗ Lit LV) E
  
  stepAmIT : ∀{L E1 E2} →
             AmI (Lit L) E1 E2
             ⇒[ • ∣ L ]E
             E1
  stepAmIF : ∀{L E1 E2 L'} →
             (L≢L' : L ≢ L') →
             AmI (Lit L) E1 E2
             ⇒[ • ∣ L' ]E
             E2