{-# OPTIONS --safe #-}

open import Data.Empty
open import Data.Unit
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr) hiding (map)
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
  (E : TypedLocalLanguage L)
  where

open import Choreographies L E
open import TypedChoreographies L E
open import LocalRenamings L E
open import LocationRenamings L E
open import Renamings L E
open import LocationSubstitutions L E
open import LocalSubstitutions L E
open import Substitutions L E
open import Types L E
open import LocationContexts L E
open import LocalContexts L E
open import GlobalContexts L E

open Location L
open TypedLocalLanguage E

data TraceElem : Set where
  • : TraceElem
  LocStep : LocVal → TraceElem
  SendVal : (L1 : LocVal) →
            (v : Expr) →
            Valₑ v →
            (L2 : LocVal) →
            TraceElem
  SendSync : (L1 : LocVal) →
             (d : SyncLabel) →
             (L2 : LocVal) →
             TraceElem
  TellLoc : (L1 L2 : LocVal) →
            (LS1 LS2 : List LocVal) →
            TraceElem

Trace : Set
Trace = List TraceElem

-- Small-step operations semantics for ground terms
data _⇒[_]_ : Chor → TraceElem → Chor → Set where
  stepDone : ∀{e1 e2 L}
             (e1⇒e2 : e1 ⇒ₑ e2) →
             Done (Lit L) e1
             ⇒[ LocStep L ]
             Done (Lit L) e2
             
  stepSend : ∀{C C' L1 L2 T}
             (C⇒C' : C ⇒[ T ] C') →
             Send (Lit L1) C (Lit L2)
             ⇒[ T ]
             Send (Lit L1) C' (Lit L2)
  stepSendV : ∀{v L1 L2}
              (v-Val : Valₑ v) →
              Send (Lit L1) (Done (Lit L1) v) (Lit L2)
              ⇒[ SendVal L1 v v-Val L2 ]
              Done (Lit L2) v
  stepSync : ∀{L1 d L2 C} →
             Sync (Lit L1) d (Lit L2) C
             ⇒[ SendSync L1 d L2 ]
             C

  stepIf : ∀{C C' C1 C2 L T}
           (C⇒C' : C ⇒[ T ] C') →
           If (Lit L) C C1 C2
           ⇒[ T ]
           If (Lit L) C' C1 C2
  stepIfT : ∀{C1 C2 L} →
            If (Lit L) (Done (Lit L) ttₑ) C1 C2
            ⇒[ LocStep L ]
            C1
  stepIfF : ∀{C1 C2 L} →
            If (Lit L) (Done (Lit L) ffₑ) C1 C2
            ⇒[ LocStep L ]
            C2

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
                  LocApp C (Lit L)
                  ⇒[ T ]
                  LocApp C' (Lit L)
  stepLocApp : ∀{C L} →
               (LocApp (LocAbs C) (Lit L))
               ⇒[ • ]
               subₗ [] (idSubₗ ▸ₗ Lit L) C

  stepTellLet : ∀{C1 C1' C2 T ρ1 ρ2 L} →
                (C1⇒C1' : C1 ⇒[ T ] C1') →
                TellLet (Lit L) (map Lit ρ1) C1 (map Lit ρ2) C2
                ⇒[ T ]
                TellLet (Lit L) (map Lit ρ1) C1' (map Lit ρ2) C2
  stepTellLetV : ∀{L1 L2 C LS1 LS2} →
                 TellLet (Lit L1) (map Lit LS1) (Done (Lit L1) (locₑ L2)) (map Lit LS2) C
                 ⇒[ TellLoc L1 L2 LS1 LS2 ]
                 subₗ [] (idSubₗ ▸ₗ Lit L2) C

-- Values cannot step
valNoStep : ∀{V C T} → Val V → ¬ (V ⇒[ T ] C)
valNoStep (DoneVal L v v-Val) (stepDone v⇒e) = valNoStepₑ v-Val v⇒e

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

-- Each ground location is a location value
LocVal≡Lit : ∀{ℓ} → (λ _ → ⊥) ⊢ₗ ℓ → Σ[ L ∈ LocVal ] (ℓ ≡ Lit L)
LocVal≡Lit {Var x} (wfVar ())
LocVal≡Lit {Lit L} (wfLit L) = L , refl

-- Each ground list of locations is a list of location values
LocListVal≡Lit : ∀{ρ} → (λ _ → ⊥) ⊢ₗₗ ρ → Σ[ LS ∈ List LocVal ] (ρ ≡ map Lit LS)
LocListVal≡Lit {[]} wfNil = [] , refl
LocListVal≡Lit {ℓ ∷ ρ} (wfCons Θ⊢ℓ Θ⊢ρ) with LocVal≡Lit Θ⊢ℓ | LocListVal≡Lit Θ⊢ρ
... | (L , refl) | (LS , refl) = L ∷ LS , refl

-- Destructor for well-formedness of "At" types
wfAt⇒wfLoc : ∀{Θ t ℓ} → Θ ⊢ₜ At t ℓ → Θ ⊢ₗ ℓ
wfAt⇒wfLoc (wfAt Θ⊢ℓ) = Θ⊢ℓ

-- Each well-typed ground term is either a value or can step
progress : ∀{τ C} →
           ((λ _ → ⊥) , [] , λ _ → nothing) ⊢ C ∶ τ →
           (Val C) ⊎ (Σ[ T ∈ TraceElem ] Σ[ C' ∈ Chor ] (C ⇒[ T ] C'))
progress (tyDone {ℓ = Var x} Θ⊢Γ (wfVar ()) e∶t)
progress (tyDone {e = e} {ℓ = Lit L} Θ⊢Γ Θ⊢ℓ e∶t) with progressₑ e∶t
... | inl e-Val = inl (DoneVal L e e-Val)
... | inr (e' , e⇒e') = inr (LocStep L , Done (Lit L) e' , stepDone e⇒e')
progress (tySend {ℓ1 = ℓ1} {Var x} C∶t1 (wfVar ()))
progress (tySend {ℓ1 = Var x} {Lit L2} C∶t1 Θ⊢ℓ2) with ty⇒wfTy C∶t1
... | wfAt (wfVar ())
progress (tySend {C = C} {ℓ1 = Lit L1} {Lit L2} C∶t1 Θ⊢ℓ2) with progress C∶t1
progress (tySend {ℓ1 = Lit L1} {Lit L2} (tyDone Θ⊢Γ Θ⊢ℓ e∶t) Θ⊢ℓ2) | inl (DoneVal _ v v-Val) =
  inr (SendVal L1 v v-Val L2 , Done (Lit L2) v , stepSendV v-Val)
... | inr (T , C' , C⇒[T]C') = inr (T , Send (Lit L1) C' (Lit L2) , stepSend C⇒[T]C')
progress (tyIf {ℓ = Var x} C∶bool C1∶τ C2∶τ) with ty⇒wfTy C∶bool
... | wfAt (wfVar ())
progress (tyIf {C1 = C1} {C2} {ℓ = Lit L} C∶bool C1∶τ C2∶τ) with progress C∶bool
progress (tyIf {C1 = C1} {C2} {ℓ = Lit L} (tyDone Θ⊢Γ Θ⊢ℓ v∶bool) C1∶τ C2∶τ) | inl (DoneVal L v v-Val) with boolInvertₑ v∶bool v-Val
... | inl refl = inr (LocStep L , C1 , stepIfT)
... | inr refl = inr (LocStep L , C2 , stepIfF)
progress (tyIf {C1 = C1} {C2} {ℓ = Lit L} C∶bool C1∶τ C2∶τ) | inr (T , C' , C⇒[T]C') = inr (T , If (Lit L) C' C1 C2 , stepIf C⇒[T]C')
progress (tySync {C = C} {ℓ1 = Location.Var x} {ℓ2} (wfVar ()) Θ⊢ℓ2 C∶τ)
progress (tySync {C = C} {ℓ1 = Lit L1} {Var x} Θ⊢ℓ1 (wfVar ()) C∶τ)
progress (tySync {C = C} {ℓ1 = Lit L1} {Lit L2} {d = d} Θ⊢ℓ1 Θ⊢ℓ2 C∶τ) =
  inr (SendSync L1 d L2 , C , stepSync)
progress (tyDefLocal {C1 = C1} {C2} {t1} {Var x} C1∶t1 C2∶τ2) with ty⇒wfTy C1∶t1
... | wfAt (wfVar ())
progress (tyDefLocal {C1 = C1} {C2} {t1} {Lit L} C1∶t1 C2∶τ2) with progress C1∶t1
progress (tyDefLocal {C2 = C2} {t1} {Lit L} (tyDone Θ⊢Γ Θ⊢ℓ v∶t) C2∶τ2) | inl (DoneVal _ v v-Val) =
  inr (• , subₗₑ (AddSub ε (Lit L) t1 v) C2 , stepDefLocalV v-Val)
... | inr (T , C1' , C1⇒[T]C1') = inr (T , DefLocal (Lit L) t1 C1' C2 , stepDefLocal C1⇒[T]C1' )
progress (tyFun {C = C} {τ1} {τ2} C∶τ2) = inl (FunVal τ1 C)
progress (tyFix {C = C} {τ} C∶τ) = inr (• , sub (idSub ▸ Fix τ C) C , stepFix)
progress (tyApp {C1 = C1} {C2} C1∶τ1⇒τ2 C2∶τ1) with progress C1∶τ1⇒τ2
progress (tyApp {C1 = _} {C2} (tyFun C1∶τ2) C2∶τ1) | inl (FunVal τ1 C1) with progress C2∶τ1
... | inl C2-Val = inr (• , sub (idSub ▸ C2) C1 , stepApp C2-Val)
... | inr (T , C2' , C2⇒[T]C2') = inr (T , App (Fun τ1 C1) C2' , stepAppArg (FunVal τ1 C1) C2⇒[T]C2')
progress (tyApp {C1 = C1} {C2} C1∶τ1⇒τ2 C2∶τ1) | inr (T , C1' , C1⇒[T]C1') = inr (T , App C1' C2 , stepAppFun C1⇒[T]C1')
progress (tyLocAbs {C = C} Θ⊢Γ C∶τ) = inl (LocAbsVal C)
progress (tyLocApp {ℓ = Var x} C∶∀τ (wfVar ()))
progress (tyLocApp {ℓ = Lit L} C∶∀τ Θ⊢ℓ) with progress C∶∀τ
... | inl (LocAbsVal C) = inr (• , subₗ [] (idSubₗ ▸ₗ Lit L) C , stepLocApp)
... | inr (T , C' , C⇒[T]C') = inr (T , LocApp C' (Lit L) , stepLocAppFun C⇒[T]C')
progress (tyTellLet {C1 = C1} {C2} {ρ1} {ρ2} {ℓ} C1∶Loc Θ⊢ρ1 Θ⊢ρ2 Θ⊢τ C2∶↑τ) with
  LocListVal≡Lit Θ⊢ρ1 | LocListVal≡Lit Θ⊢ρ2 | LocVal≡Lit (wfAt⇒wfLoc (ty⇒wfTy C1∶Loc))
... | (LS1 , refl) | (LS2 , refl) | (L , refl) with progress C1∶Loc
... | inr (T , C1' , C1⇒[T]C1') = inr (T , TellLet (Lit L) (map Lit LS1) C1' (map Lit LS2) C2 , stepTellLet C1⇒[T]C1')
progress (tyTellLet {C2 = C2} (tyDone Θ⊢Γ Θ⊢ℓ v∶Loc) Θ⊢ρ1 Θ⊢ρ2 Θ⊢τ C2∶↑τ)
    | LS1 , refl | LS2 , refl | L1 , refl | inl (DoneVal L v v-Val) with locInvertₑ v∶Loc v-Val
... | (L2 , refl) =
  inr (TellLoc L1 L2 LS1 LS2 , subₗ [] (idSubₗ ▸ₗ Lit L2) C2 , stepTellLetV)
