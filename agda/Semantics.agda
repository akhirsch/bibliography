{-# OPTIONS --safe #-}

open import Data.Empty
open import Data.Unit
open import Data.Nat renaming (_≟_ to ≡-dec-ℕ)
open import Data.Bool renaming (_≟_ to ≡-dec-Bool)
open import Data.List
open import Data.Maybe hiding (map)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function

open import Common
open import LocalLang
open import TypedLocalLang
open import Locations

module Semantics
  (L : Location)
  (E : Language L)
  (LE : LawfulLanguage L E)
  (TE : TypedLocalLanguage L E LE)
  where

open import Choreographies L E LE TE
open import TypedChoreographies L E LE TE
open import LocalRenamings L E LE TE
open import LocationRenamings L E LE TE
open import Renamings L E LE TE
open import LocationSubstitutions L E LE TE
open import LocalSubstitutions L E LE TE
open import Substitutions L E LE TE
open import Types L E LE TE
open import LocationContexts L E LE TE
open import LocalContexts L E LE TE
open import GlobalContexts L E LE TE

open Location L
open Language E
open LawfulLanguage LE
open TypedLocalLanguage TE

data TraceElem : Set where
  • : TraceElem
  LocStep : LocVal → TraceElem
  SendVal : (L1 : LocVal) →
            (v : Expr) → Valₑ v →
            (L2 : LocVal) →
            TraceElem
  SendSync : (L1 : LocVal) →
             (d : SyncLabel) →
             (L2 : LocVal) →
             TraceElem
  TellLoc : (L1 : LocVal) →
            (L2 : LocVal) →
            (ρ1 ρ2 : List LocVal) →
            TraceElem

Trace : Set
Trace = List TraceElem

-- Small-step operations semantics for ground terms
data _⇒[_]_ : Chor → TraceElem → Chor → Set where
  stepDone : ∀{e1 e2 L}
             (e1⇒e2 : e1 ⇒ₑ e2) →
             Done (Lit L) e1 ⇒[ LocStep L ] Done (Lit L) e2
             
  stepSend : ∀{C C' L1 L2 T}
             (C⇒C' : C ⇒[ T ] C') →
             Send L1 C L2 ⇒[ T ] Send L1 C' L2
  stepSendV : ∀{v L1 L2}
              (v-Val : Valₑ v) →
              Send (Lit L1) (Done (Lit L1) v) (Lit L2)
              ⇒[ SendVal L1 v v-Val L2 ]
              Done (Lit L2) v
  stepSync : ∀{L1 d L2 C} →
             Sync (Lit L1) d (Lit L2) C ⇒[ SendSync L1 d L2 ] C

  stepIf : ∀{C C' C1 C2 L T}
           (C⇒C' : C ⇒[ T ] C') →
           If L C C1 C2 ⇒[ T ] If L C' C1 C2
  stepIfT : ∀{C1 C2 L} →
            If (Lit L) (Done (Lit L) ttₑ) C1 C2 ⇒[ LocStep L ] C1
  stepIfF : ∀{C1 C2 L} →
            If (Lit L) (Done (Lit L) ffₑ) C1 C2 ⇒[ LocStep L ] C2

  stepDefLocal : ∀{C1 C1' C2 L t T}
                 (C1⇒C1' : C1 ⇒[ T ] C1') →
                 DefLocal (Lit L) t C1 C2
                 ⇒[ T ]
                 DefLocal (Lit L) t C1' C2

  stepDefLocalV : ∀{v C L t}
                  (v-Val : Valₑ v) →
                  DefLocal (Lit L) t (Done (Lit L) v) C
                  ⇒[ • ]
                  subₗₑ (AddSub ε (Lit L) t v) C

  stepAppFun : ∀{C1 C1' C2 T}
               (C1⇒C1' : C1 ⇒[ T ] C1') →
               App C1 C2 ⇒[ T ] App C1' C2
  stepAppArg : ∀{V C C' T} →
               (V-Val : Val V)
               (C⇒C' : C ⇒[ T ] C') →
               App V C ⇒[ T ] App V C'
  stepApp : ∀{V C τ}
            (V-Val : Val V) →
            App (Fun τ C) V ⇒[ • ] sub (idSub ▸ V) C
  stepFix : ∀{C τ} → Fix τ C ⇒[ • ] sub (idSub ▸ Fix τ C) C

  stepLocAppFun : ∀{C C' L T}
                  (C⇒C' : C ⇒[ T ] C') →
                  LocApp C (Lit L) ⇒[ T ] LocApp C' (Lit L)
  stepLocApp : ∀{C L} →
               (LocApp (LocAbs C) (Lit L))
               ⇒[ • ]
               subₗ [] (idSubₗ ▸ₗ Lit L) C

  stepTellLet : ∀{C1 C1' C2 T ρ1 ρ2 L} →
                (C1⇒C1' : C1 ⇒[ T ] C1') →
                TellLet (Lit L) (map Lit ρ1) C1 (map Lit ρ2) C2
                ⇒[ T ]
                TellLet (Lit L) (map Lit ρ1) C1' (map Lit ρ2) C2
  stepTellLetV : ∀{L1 L2 C ρ1 ρ2} →
                 TellLet (Lit L1) (map Lit ρ1) (Done (Lit L1) (locₑ L2)) (map Lit ρ2) C
                 ⇒[ TellLoc L1 L2 ρ1 ρ2 ]
                 subₗ [] (idSubₗ ▸ₗ Lit L2) C

-- Values cannot step
valNoStep : ∀{V C T} → Val V → ¬ (V ⇒[ T ] C)
valNoStep (DoneVal L v v-val) (stepDone v⇒e) = valNoStepₑ v-val v⇒e

-- Types are preserved under the operational semantics
preservation : ∀{τ T C1 C2} →
               ((λ _ → ⊥) , [] , λ _ → nothing) ⊢ C1 ∶ τ →
               C1 ⇒[ T ] C2 →
               ((λ _ → ⊥) , [] , λ _ → nothing) ⊢ C2 ∶ τ
preservation (tyDone Θ⊢Γ Θ⊢ℓ e∶t) (stepDone e1⇒e2) =
  tyDone Θ⊢Γ Θ⊢ℓ (preservationₑ e∶t e1⇒e2)
preservation (tySend C1 Θ⊢ℓ2) (stepSend C1⇒C2) =
  tySend (preservation C1 C1⇒C2) Θ⊢ℓ2
preservation (tySend (tyDone Θ⊢Γ Θ⊢ℓ e∶t) Θ⊢ℓ2) (stepSendV v-Val) =
  tyDone Θ⊢Γ (wfLit _) (tyValₑ v-Val e∶t)
preservation (tyIf C C1 C2) (stepIf C⇒C') = tyIf (preservation C C⇒C') C1 C2
preservation (tyIf C C1 C2) stepIfT = C1
preservation (tyIf C C1 C2) stepIfF = C2
preservation (tySync Θ⊢ℓ1 Θ⊢ℓ2 C) stepSync = C
preservation (tyDefLocal C1 C2) (stepDefLocal C1⇒C1') =
  tyDefLocal (preservation C1 C1⇒C1') C2
preservation (tyDefLocal {t1 = t1} (tyDone Θ⊢Γ Θ⊢ℓ v∶t1) C∶τ2) (stepDefLocalV {L = L} V-Val) =
  tySubₗₑ (AddSUB εSUB (Lit L) t1 v∶t1) C∶τ2
preservation (tyFix {C = C} {τ = τ} C∶τ) stepFix =
  tySub (λ{ n τ () }) (λ{ zero .τ refl → tyFix C∶τ ; (suc n) τ () }) C∶τ
preservation (tyApp C1 C2) (stepAppFun C1⇒C1') = tyApp (preservation C1 C1⇒C1') C2
preservation (tyApp C1 C2) (stepAppArg V-Val C2⇒C2') = tyApp C1 (preservation C2 C2⇒C2')
preservation (tyApp (tyFun C∶τ2) V∶τ1) (stepApp {V = V} {C = C} V-Val) =
  tySub (λ{ n τ () }) (λ{ zero τ refl → V∶τ1 ; (suc n) τ () }) C∶τ2
preservation (tyLocApp C Θ⊢ℓ) (stepLocAppFun C⇒C') = tyLocApp (preservation C C⇒C') Θ⊢ℓ
preservation (tyLocApp (tyLocAbs Θ⊢Γ C∶τ) Θ⊢ℓ) (stepLocApp {L = L}) =
  tySubₗ (λ{ zero tt → wfLit L ; (suc n) () }) C∶τ
preservation (tyTellLet C1 Θ⊢ρ1 Θ⊢ρ2 Θ⊢τ C2) (stepTellLet C1⇒C1') =
  tyTellLet (preservation C1 C1⇒C1') Θ⊢ρ1 Θ⊢ρ2 Θ⊢τ C2
preservation (tyTellLet {C2 = C2} {τ = τ} (tyDone Θ⊢Γ Θ⊢ℓ L2∶t) Θ⊢ρ1 Θ⊢ρ2 Θ⊢τ C2:↑τ) (stepTellLetV {L2 = L2}) =
  C2⟨L2⟩:τ
  where
  open ≡-Reasoning

  C2⟨L2⟩:↑τ⟨id▸L2⟩ : ((λ _ → ⊥) , [] , (λ _ → nothing))
                    ⊢ subₗ [] (idSubₗ ▸ₗ Lit L2) C2
                    ∶ subₜ (idSubₗ ▸ₗ Lit L2) (↑ₜ τ)
  C2⟨L2⟩:↑τ⟨id▸L2⟩ = tySubₗ (λ{ zero tt → wfLit L2 ; (suc n) ()}) C2:↑τ 

  ↑τ⟨id▸L2⟩≡τ : subₜ (idSubₗ ▸ₗ Lit L2) (↑ₜ τ) ≡ τ
  ↑τ⟨id▸L2⟩≡τ =
    subₜ (idSubₗ ▸ₗ Lit L2) (renₜ suc τ)
      ≡⟨ cong (subₜ (idSubₗ ▸ₗ Lit L2)) (sym (subιₜ suc τ)) ⟩
    subₜ (idSubₗ ▸ₗ Lit L2) (subₜ (ιₗ suc) τ)
      ≡⟨ sym (subFuseₜ (idSubₗ ▸ₗ Lit L2) (ιₗ suc) τ) ⟩
    subₜ idSubₗ τ
      ≡⟨ subIdₜ τ ⟩
    τ ∎

  C2⟨L2⟩:τ : ((λ _ → ⊥) , [] , (λ _ → nothing))
               ⊢ subₗ [] (idSubₗ ▸ₗ Lit L2) C2
               ∶ τ
  C2⟨L2⟩:τ =
    subst (λ x → ((λ _ → ⊥) , [] , (λ _ → nothing)) ⊢ subₗ [] (idSubₗ ▸ₗ Lit L2) C2 ∶ x)
      ↑τ⟨id▸L2⟩≡τ C2⟨L2⟩:↑τ⟨id▸L2⟩
