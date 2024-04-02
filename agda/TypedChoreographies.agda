{-# OPTIONS --safe #-}

open import Data.Empty
open import Data.Unit
open import Data.Maybe
open import Data.Nat
open import Data.Nat.Properties
open import Data.List hiding (map)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function

open import Common
open import LocalLang
open import TypedLocalLang
open import Locations

module TypedChoreographies
  (L : Location)
  (E : Language L)
  (LE : LawfulLanguage L E)
  (TE : TypedLocalLanguage L E LE)
  where

open import Types L E LE TE
open import Choreographies L E LE TE
-- open import LocalRenamings L E LE TE
open import LocationRenamings L E LE TE
open import Renamings L E LE TE
open import LocationSubstitutions L E LE TE
open import LocalSubstitutions L E LE TE
open import Substitutions L E LE TE
open import LocationContexts L E LE TE
open import LocalContexts L E LE TE
open import GlobalContexts L E LE TE

open Location L
open Language E
open LawfulLanguage LE
open TypedLocalLanguage TE

{-
  Choreographic typing relation of the form
  (Θ , Δ , Γ) ⊢ C : τ
  where Θ is a location context,
  Δ is a local context,
  Γ is a global context,
  C is a choreography,
  and τ is a type.
-}
data _⊢_∶_ : LocCtx × LocalCtx × Ctx → Chor → Typ → Set where
  tyVar : ∀{Θ Δ Γ}
          (Θ⊢Γ : Θ ⊢ Γ) →
          ∀ x →
          (Θ , Δ , Γ) ⊢ Var x ∶ Γ x
  tyDone : ∀{Θ Δ Γ e t ℓ}
           (Θ⊢Γ : Θ ⊢ Γ) →
           (Θ⊢ℓ : Θ ⊢ₗ ℓ) →
           (Δ∣ℓ⊢e∶t : (Δ ∣ ℓ) ⊢ₑ e ∶ t) →
           (Θ , Δ , Γ) ⊢ Done ℓ e ∶ At t ℓ
  tySend : ∀{Θ Δ Γ C t ℓ1 ℓ2}
           (Θ；Δ；Γ⊢C:ℓ1_t : (Θ , Δ , Γ) ⊢ C ∶ At t ℓ1)
           (Θ⊢ℓ2 : Θ ⊢ₗ ℓ2) →
           (Θ , Δ , Γ) ⊢ Send ℓ1 C ℓ2 ∶ At t ℓ2
  tyIf : ∀{Θ Δ Γ C C1 C2 τ ℓ}
          (Θ；Δ；Γ⊢C:ℓ_bool : (Θ , Δ , Γ) ⊢ C ∶ At Boolₑ ℓ)
          (Θ；Δ；Γ⊢C1:τ : (Θ , Δ , Γ) ⊢ C1 ∶ τ)
          (Θ；Δ；Γ⊢C2:τ : (Θ , Δ , Γ) ⊢ C2 ∶ τ) →
          (Θ , Δ , Γ) ⊢ If ℓ C C1 C2 ∶ τ
  tySync : ∀{Θ Δ Γ C τ ℓ1 ℓ2 d}
           (Θ⊢ℓ1 : Θ ⊢ₗ ℓ1) (Θ⊢ℓ2 : Θ ⊢ₗ ℓ2)
           (Θ；Δ；Γ⊢C:τ : (Θ , Δ , Γ) ⊢ C ∶ τ) →
           (Θ , Δ , Γ) ⊢ Sync ℓ1 d ℓ2 C ∶ τ
  tyDefLocal : ∀{Θ Δ Γ C1 C2 t1 ℓ τ2}
               (Θ；Δ；Γ⊢C1:ℓ_t1 : (Θ , Δ , Γ)  ⊢ C1 ∶ At t1 ℓ)
               (Θ；Δ,ℓ_t1；Γ⊢C2:τ2 : (Θ , ((ℓ , t1) ∷ Δ) , Γ) ⊢ C2 ∶ τ2) →
               (Θ , Δ , Γ) ⊢ DefLocal ℓ t1 C1 C2 ∶ τ2
  tyFun : ∀{Θ Δ Γ C τ1 τ2} →
          (Θ；Δ；Γ,τ1⊢C:τ2 : (Θ , Δ , (Γ ,, τ1)) ⊢ C ∶ τ2) →
          (Θ , Δ , Γ) ⊢ Fun τ1 C ∶ Arrow τ1 τ2
  tyFix : ∀{Θ Δ Γ C τ} →
          (Θ；Δ；Γ,τ⊢C:τ : (Θ , Δ , (Γ ,, τ)) ⊢ C ∶ τ) →
          (Θ , Δ , Γ) ⊢ Fix τ C ∶ τ
  tyApp : ∀{Θ Δ Γ C1 C2 τ1 τ2}
          (Θ；Δ；Γ⊢C1:τ1⇒τ2 : (Θ , Δ , Γ)  ⊢ C1 ∶ Arrow τ1 τ2)
          (Θ；Δ；Γ⊢C2:τ1 : (Θ , Δ , Γ) ⊢ C2 ∶ τ1) →
          (Θ , Δ , Γ) ⊢ App C1 C2 ∶ τ2
  tyLocAbs : ∀{Θ Δ Γ C τ}
             (Θ⊢Γ : Θ ⊢ Γ) →
             (↑Θ；↑Δ；↑Γ⊢C∶τ : (↑LocCtx Θ , ↑LocalCtx Δ , ↑Ctx Γ) ⊢ C ∶ τ) →
             (Θ , Δ , Γ) ⊢ LocAbs C ∶ AllLoc τ
  tyLocApp : ∀{Θ Δ Γ C τ ℓ}
             (Θ；Δ；Γ⊢C:∀τ : (Θ , Δ , Γ)  ⊢ C ∶ AllLoc τ) →
             (Θ⊢ℓ : Θ ⊢ₗ ℓ) →
             (Θ , Δ , Γ) ⊢ LocApp C ℓ ∶ subₜ (idSubₗ ▸ₗ ℓ) τ
  tyTellLet : ∀{Θ Δ Γ C1 C2 ρ1 ρ2 ℓ τ} →
              (Θ；Δ；Γ⊢C1:ℓ_t : (Θ , Δ , Γ) ⊢ C1 ∶ At Locₑ ℓ)
              (Θ⊢ρ1 : Θ ⊢ₗₗ ρ1) (Θ⊢ρ2 : Θ ⊢ₗₗ ρ2)
              (Θ⊢τ : Θ ⊢ₜ τ)
              (↑Θ；↑Δ；↑Γ⊢C2:↑τ : (↑LocCtx Θ , ↑LocalCtx Δ , ↑Ctx Γ) ⊢ C2 ∶ ↑ₜ τ) →
              (Θ , Δ , Γ) ⊢ TellLet ℓ ρ1 C1 ρ2 C2 ∶ τ

-- Choreographies have a unique type
tyUniq : ∀{Θ Δ Γ C τ1 τ2} → 
         (Θ , Δ , Γ) ⊢ C ∶ τ1 →
         (Θ , Δ , Γ) ⊢ C ∶ τ2 →
         τ1 ≡ τ2
tyUniq (tyVar Θ⊢Γ x) (tyVar Θ⊢Γ' .x) = refl
tyUniq (tyDone Θ⊢Γ Θ⊢ℓ Δ∣ℓ⊢e∶t1) (tyDone Θ⊢Γ' Θ⊢ℓ' Δ∣ℓ⊢e∶t2) =
  cong₂ At (tyUniqₑ Δ∣ℓ⊢e∶t1 Δ∣ℓ⊢e∶t2) refl
tyUniq (tySend C∶t Θ⊢ℓ2) (tySend C∶t' Θ⊢ℓ2') =
  cong₂ At (At-inj (tyUniq C∶t C∶t') .fst) refl
tyUniq (tyIf C C1 C2) (tyIf C' C1' C2') = tyUniq C1 C1'
tyUniq (tySync _ _ C) (tySync _ _ C') = tyUniq C C'
tyUniq (tyDefLocal C1 C2) (tyDefLocal C1' C2') with tyUniq C1 C1'
... | refl = tyUniq C2 C2'
tyUniq (tyFun C) (tyFun C') = cong₂ Arrow refl (tyUniq C C')
tyUniq (tyFix C) (tyFix C') = tyUniq C C'
tyUniq (tyApp C1 C2) (tyApp C1' C2') = Arrow-inj (tyUniq C1 C1') .snd
tyUniq (tyLocAbs _ C) (tyLocAbs _ C') = cong AllLoc (tyUniq C C')
tyUniq (tyLocApp {τ = τ} {ℓ = ℓ} C Θ⊢ℓ) (tyLocApp {τ = τ'} C' Θ⊢ℓ') = cong₂ subₜ refl τ≡τ'
  where
  τ≡τ' : τ ≡ τ'
  τ≡τ' = AllLoc-inj (tyUniq C C')
tyUniq (tyTellLet C1 Θ⊢ρ1 Θ⊢ρ2 Θ⊢τ C2) (tyTellLet C1' Θ⊢ρ3 Θ⊢ρ4 Θ⊢τ₁ C2') =
  ↑ₜ-pres-inj _ _ (tyUniq C2 C2')

-- The typing relation respects extensional equality
tyExt : ∀{Θ Θ' Δ Γ Γ' C τ} →
        Θ ≈ Θ' → Γ ≈ Γ' →
        (Θ , Δ , Γ) ⊢ C ∶ τ →
        (Θ' , Δ , Γ') ⊢ C ∶ τ
tyExt Θ≈Θ' Γ≈Γ' (tyVar Θ⊢Γ x) =
  subst (λ z → _ ⊢ Var x ∶ z) (sym (Γ≈Γ' x)) (tyVar (wfCtxExt Θ≈Θ' Γ≈Γ' Θ⊢Γ) x)
tyExt Θ≈Θ' Γ≈Γ' (tyDone {ℓ = ℓ} Θ⊢Γ Θ⊢ℓ Δ∣ℓ⊢e∶t) =
  tyDone (wfCtxExt Θ≈Θ' Γ≈Γ' Θ⊢Γ) (wfExtₗ Θ≈Θ' Θ⊢ℓ) (tyExtₑ ≈-refl Δ∣ℓ⊢e∶t)
tyExt Θ≈Θ' Γ≈Γ' (tySend C∶τ Θ⊢ℓ2) =
  tySend (tyExt Θ≈Θ' Γ≈Γ' C∶τ) (wfExtₗ Θ≈Θ' Θ⊢ℓ2)
tyExt Θ≈Θ' Γ≈Γ' (tyIf C∶τ C∶τ1 C∶τ2) =
  tyIf (tyExt Θ≈Θ' Γ≈Γ' C∶τ) (tyExt Θ≈Θ' Γ≈Γ' C∶τ1) (tyExt Θ≈Θ' Γ≈Γ' C∶τ2)
tyExt Θ≈Θ' Γ≈Γ' (tySync Θ⊢ℓ1 Θ⊢ℓ2 C∶τ) =
  tySync (wfExtₗ Θ≈Θ' Θ⊢ℓ1) (wfExtₗ Θ≈Θ' Θ⊢ℓ2) (tyExt Θ≈Θ' Γ≈Γ' C∶τ)
tyExt Θ≈Θ' Γ≈Γ' (tyDefLocal {t1 = t1} {ℓ = ℓ} C∶t1 C∶τ2) =
  tyDefLocal (tyExt Θ≈Θ' Γ≈Γ' C∶t1) (tyExt Θ≈Θ' Γ≈Γ' C∶τ2)
tyExt Θ≈Θ' Γ≈Γ' (tyFun C∶τ2) = tyFun (tyExt Θ≈Θ' (addCtxExt Γ≈Γ') C∶τ2)
tyExt Θ≈Θ' Γ≈Γ' (tyFix C∶τ) = tyFix (tyExt Θ≈Θ' (addCtxExt Γ≈Γ') C∶τ)
tyExt Θ≈Θ' Γ≈Γ' (tyApp C1∶τ1⇒τ2 C2∶τ1) =
  tyApp (tyExt Θ≈Θ' Γ≈Γ' C1∶τ1⇒τ2) (tyExt Θ≈Θ' Γ≈Γ' C2∶τ1)
tyExt Θ≈Θ' Γ≈Γ' (tyLocAbs Θ⊢Γ C∶τ) =
  tyLocAbs (wfCtxExt Θ≈Θ' Γ≈Γ' Θ⊢Γ) (tyExt (↑LocCtxExt Θ≈Θ') (↑CtxExt Γ≈Γ') C∶τ)
tyExt Θ≈Θ' Γ≈Γ' (tyLocApp C∶τ Θ⊢ℓ) = tyLocApp (tyExt Θ≈Θ' Γ≈Γ' C∶τ) (wfExtₗ Θ≈Θ' Θ⊢ℓ)
tyExt Θ≈Θ' Γ≈Γ' (tyTellLet C∶Loc Θ⊢ρ1 Θ⊢ρ2 Θ⊢τ C∶τ) =
  tyTellLet (tyExt Θ≈Θ' Γ≈Γ' C∶Loc) (wfExtₗₗ Θ≈Θ' Θ⊢ρ1) (wfExtₗₗ Θ≈Θ' Θ⊢ρ2)
    (wfExtₜ Θ≈Θ' Θ⊢τ) (tyExt (↑LocCtxExt Θ≈Θ') (↑CtxExt Γ≈Γ') C∶τ)

-- The typing relation has weakening on injective location renamings
tyWkₗ : ∀{Θ Θ' Δ Γ C τ} ξ →
        Injective _≡_ _≡_ ξ →
        Θ ≈ Θ' ∘ ξ →
        (Θ , Δ , Γ) ⊢ C ∶ τ →
        (Θ' , renₗ-LocalCtx ξ Δ , renCtx ξ Γ) ⊢ renₗ ξ C ∶ renₜ ξ τ
tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ (tyVar Θ⊢Γ x) = tyVar (wfCtxWk ξ Θ≈Θ'∘ξ Θ⊢Γ) x
tyWkₗ {Δ = Δ} ξ ξ-inj Θ≈Θ'∘ξ (tyDone {e = e} {t = t} {ℓ = ℓ} Θ⊢Γ Θ⊢ℓ Δ∣ℓ⊢e∶t) =
  tyDone (wfCtxWk ξ Θ≈Θ'∘ξ Θ⊢Γ) (wfWkₗ ξ Θ≈Θ'∘ξ Θ⊢ℓ) (tyExtₑ (projInj Δ ℓ ξ-inj) Δ∣ℓ⊢e∶t)
tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ (tySend C∶τ Θ⊢ℓ2) =
  tySend (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ C∶τ) (wfWkₗ ξ Θ≈Θ'∘ξ Θ⊢ℓ2)
tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ (tyIf C∶Bool C1∶τ C2∶τ) =
  tyIf (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ C∶Bool) (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ C1∶τ) (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ C2∶τ)
tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ (tySync Θ⊢ℓ1 Θ⊢ℓ2 C∶τ) =
  tySync (wfWkₗ ξ Θ≈Θ'∘ξ Θ⊢ℓ1) (wfWkₗ ξ Θ≈Θ'∘ξ Θ⊢ℓ2) (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ C∶τ)
tyWkₗ {Θ} {Θ'} {Δ} {Γ} ξ ξ-inj Θ≈Θ'∘ξ (tyDefLocal {t1 = t1} {ℓ} {τ2} C1∶t1 C2∶τ2) =
  tyDefLocal (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ C1∶t1) (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ C2∶τ2)
tyWkₗ {Θ} {Θ'} {Δ} {Γ} ξ ξ-inj Θ≈Θ'∘ξ (tyFun {τ1 = τ1} C∶τ2) =
  tyFun (tyExt ≈-refl (renCtx,, Γ τ1 ξ) (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ C∶τ2))
tyWkₗ {Θ} {Θ'} {Δ} {Γ} ξ ξ-inj Θ≈Θ'∘ξ (tyFix {τ = τ} C∶τ) =
  tyFix (tyExt ≈-refl (renCtx,, Γ τ ξ) (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ C∶τ))
tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ (tyApp C1∶τ1⇒τ2 C2∶τ2) =
  tyApp (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ C1∶τ1⇒τ2) (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ C2∶τ2)
tyWkₗ {Θ} {Θ'} {Δ} {Γ} ξ ξ-inj Θ≈Θ'∘ξ (tyLocAbs {C = C} {τ = τ} Θ⊢Γ C∶τ) =
  tyLocAbs (wfCtxWk ξ Θ≈Θ'∘ξ Θ⊢Γ) ↑Θ'；↑Δ'；↑Γ'⊢C⟨↑ξ⟩∶τ⟨↑ξ⟩
    where
    open import Relation.Binary.Reasoning.Setoid (≈-Setoid′ ℕ Set)
      
    ↑Θ≈↑Θ'∘↑ξ : ↑LocCtx Θ ≈ ↑LocCtx Θ' ∘ ↑ ξ
    ↑Θ≈↑Θ'∘↑ξ = begin
      ↑LocCtx Θ        ≈⟨ ↑LocCtxExt Θ≈Θ'∘ξ ⟩
      ↑LocCtx (Θ' ∘ ξ) ≈⟨ ↑-distr-∘ Θ' ξ ⟩
      ↑LocCtx Θ' ∘ ↑ ξ ∎

    ↑Θ'；↑Δ⟨↑ξ⟩；[↑Γ]⟨↑ξ⟩⊢C⟨↑ξ⟩∶τ⟨↑ξ⟩ : (↑LocCtx Θ' , renₗ-LocalCtx (↑ ξ) (↑LocalCtx Δ) , renCtx (↑ ξ) (↑Ctx Γ)) ⊢ renₗ (↑ ξ) C ∶ renₜ (↑ ξ) τ
    ↑Θ'；↑Δ⟨↑ξ⟩；[↑Γ]⟨↑ξ⟩⊢C⟨↑ξ⟩∶τ⟨↑ξ⟩ = tyWkₗ (↑ ξ) (↑-pres-inj ξ-inj) ↑Θ≈↑Θ'∘↑ξ C∶τ

    ↑Θ'；↑Δ'；[↑Γ]⟨↑ξ⟩⊢C⟨↑ξ⟩∶τ⟨↑ξ⟩ : (↑LocCtx Θ' , ↑LocalCtx (renₗ-LocalCtx ξ Δ) , renCtx (↑ ξ) (↑Ctx Γ)) ⊢ renₗ (↑ ξ) C ∶ renₜ (↑ ξ) τ
    ↑Θ'；↑Δ'；[↑Γ]⟨↑ξ⟩⊢C⟨↑ξ⟩∶τ⟨↑ξ⟩ = subst (λ x → (_ , x , _) ⊢ _ ∶ _) (sym (↑renₗ-LocalCtx ξ Δ)) ↑Θ'；↑Δ⟨↑ξ⟩；[↑Γ]⟨↑ξ⟩⊢C⟨↑ξ⟩∶τ⟨↑ξ⟩

    ↑Θ'；↑Δ'；↑Γ'⊢C⟨↑ξ⟩∶τ⟨↑ξ⟩ : (↑LocCtx Θ' , ↑LocalCtx (renₗ-LocalCtx ξ Δ) , ↑Ctx (renCtx ξ Γ)) ⊢ renₗ (↑ ξ) C ∶ renₜ (↑ ξ) τ
    ↑Θ'；↑Δ'；↑Γ'⊢C⟨↑ξ⟩∶τ⟨↑ξ⟩ = tyExt ≈-refl (renCtx↑ Γ ξ) ↑Θ'；↑Δ'；[↑Γ]⟨↑ξ⟩⊢C⟨↑ξ⟩∶τ⟨↑ξ⟩
tyWkₗ {Θ} {Θ'} {Δ} {Γ} ξ ξ-inj Θ≈Θ'∘ξ (tyLocApp {C = C} {τ = τ} {ℓ = ℓ} C∶τ Θ⊢ℓ) = Θ'；Δ'；Γ'⊢Cℓ
  where
  open ≡-Reasoning

  Θ'；Δ'；Γ'⊢C : (Θ' , renₗ-LocalCtx ξ Δ , renCtx ξ Γ) ⊢ renₗ ξ C ∶ AllLoc (renₜ (↑ ξ) τ)
  Θ'；Δ'；Γ'⊢C = tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ C∶τ

  Θ'⊢ℓ : Θ' ⊢ₗ renₗ-Loc ξ ℓ
  Θ'⊢ℓ = wfWkₗ ξ Θ≈Θ'∘ξ Θ⊢ℓ

  Θ'；Δ'；Γ'⊢Cℓ' : (Θ' , renₗ-LocalCtx ξ Δ , renCtx ξ Γ) ⊢ LocApp (renₗ ξ C) (renₗ-Loc ξ ℓ) ∶ subₜ (idSubₗ ▸ₗ renₗ-Loc ξ ℓ) (renₜ (↑ ξ) τ)
  Θ'；Δ'；Γ'⊢Cℓ' = tyLocApp Θ'；Δ'；Γ'⊢C Θ'⊢ℓ

  sub-eq : (idSubₗ ▸ₗ renₗ-Loc ξ ℓ) •ₗ ιₗ (↑ ξ) ≈ ιₗ ξ •ₗ (idSubₗ ▸ₗ ℓ)
  sub-eq zero = sym (subιₗ-Loc ξ ℓ)
  sub-eq (suc n) = refl

  ty-eq : subₜ (idSubₗ ▸ₗ renₗ-Loc ξ ℓ) (renₜ (↑ ξ) τ) ≡ renₜ ξ (subₜ (idSubₗ ▸ₗ ℓ) τ)
  ty-eq =
    subₜ (idSubₗ ▸ₗ renₗ-Loc ξ ℓ) (renₜ (↑ ξ) τ)      ≡⟨ cong₂ subₜ refl (sym (subιₜ (↑ ξ) τ)) ⟩
    subₜ (idSubₗ ▸ₗ renₗ-Loc ξ ℓ) (subₜ (ιₗ (↑ ξ)) τ) ≡⟨ sym (subFuseₜ (idSubₗ ▸ₗ renₗ-Loc ξ ℓ) (ιₗ (↑ ξ)) τ) ⟩
    subₜ ((idSubₗ ▸ₗ renₗ-Loc ξ ℓ) •ₗ ιₗ (↑ ξ)) τ     ≡⟨ subExtₜ sub-eq τ ⟩
    subₜ (ιₗ ξ •ₗ (idSubₗ ▸ₗ ℓ)) τ                    ≡⟨ subFuseₜ (ιₗ ξ) (idSubₗ ▸ₗ ℓ) τ ⟩
    subₜ (ιₗ ξ) (subₜ (idSubₗ ▸ₗ ℓ) τ)                ≡⟨ subιₜ ξ (subₜ (idSubₗ ▸ₗ ℓ) τ) ⟩
    renₜ ξ (subₜ (idSubₗ ▸ₗ ℓ) τ)                     ∎

  Θ'；Δ'；Γ'⊢Cℓ : (Θ' , renₗ-LocalCtx ξ Δ , renCtx ξ Γ) ⊢ LocApp (renₗ ξ C) (renₗ-Loc ξ ℓ) ∶ renₜ ξ (subₜ (idSubₗ ▸ₗ ℓ) τ)
  Θ'；Δ'；Γ'⊢Cℓ = subst (λ x → _ ⊢ _ ∶ x) ty-eq Θ'；Δ'；Γ'⊢Cℓ'
tyWkₗ {Θ} {Θ'} {Δ} {Γ} ξ ξ-inj Θ≈Θ'∘ξ (tyTellLet {C2 = C2} {τ = τ} C1∶Loc Θ⊢ρ1 Θ⊢ρ2 Θ⊢τ C2∶↑τ) =
  tyTellLet (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ C1∶Loc) (wfWkₗₗ ξ Θ≈Θ'∘ξ Θ⊢ρ1) (wfWkₗₗ ξ Θ≈Θ'∘ξ Θ⊢ρ2)
    (wfWkₜ ξ Θ≈Θ'∘ξ Θ⊢τ) ↑Θ'；Δ'；Γ'⊢C⟨↑ξ⟩∶↑τ⟨ξ⟩
  where
    module _ where
      open import Relation.Binary.Reasoning.Setoid (≈-Setoid′ ℕ Set)
      
      ↑Θ≈↑Θ'∘↑ξ : ↑LocCtx Θ ≈ ↑LocCtx Θ' ∘ ↑ ξ
      ↑Θ≈↑Θ'∘↑ξ = begin
        ↑LocCtx Θ        ≈⟨ ↑LocCtxExt Θ≈Θ'∘ξ ⟩
        ↑LocCtx (Θ' ∘ ξ) ≈⟨ ↑-distr-∘ Θ' ξ ⟩
        ↑LocCtx Θ' ∘ ↑ ξ ∎

    ↑Θ'；[↑Δ]⟨↑ξ⟩；[↑Γ]⟨↑ξ⟩⊢C2⟨↑ξ⟩∶↑τ⟨↑ξ⟩ : (↑LocCtx Θ' , renₗ-LocalCtx (↑ ξ) (↑LocalCtx Δ) , renCtx (↑ ξ) (↑Ctx Γ)) ⊢ renₗ (↑ ξ) C2 ∶ renₜ (↑ ξ) (↑ₜ τ)
    ↑Θ'；[↑Δ]⟨↑ξ⟩；[↑Γ]⟨↑ξ⟩⊢C2⟨↑ξ⟩∶↑τ⟨↑ξ⟩ = tyWkₗ (↑ ξ) (↑-pres-inj ξ-inj) ↑Θ≈↑Θ'∘↑ξ C2∶↑τ

    ↑Θ'；Δ'；[↑Γ]⟨↑ξ⟩⊢C2⟨↑ξ⟩∶↑τ⟨↑ξ⟩ : (↑LocCtx Θ' , ↑LocalCtx (renₗ-LocalCtx ξ Δ) , renCtx (↑ ξ) (↑Ctx Γ)) ⊢ renₗ (↑ ξ) C2 ∶ renₜ (↑ ξ) (↑ₜ τ)
    ↑Θ'；Δ'；[↑Γ]⟨↑ξ⟩⊢C2⟨↑ξ⟩∶↑τ⟨↑ξ⟩ = subst (λ x → (_ , x , _) ⊢ _ ∶ _) (sym (↑renₗ-LocalCtx ξ Δ)) ↑Θ'；[↑Δ]⟨↑ξ⟩；[↑Γ]⟨↑ξ⟩⊢C2⟨↑ξ⟩∶↑τ⟨↑ξ⟩

    ↑Θ'；Δ'；Γ'⊢C⟨↑ξ⟩∶↑τ⟨↑ξ⟩ : (↑LocCtx Θ' , ↑LocalCtx (renₗ-LocalCtx ξ Δ) , ↑Ctx (renCtx ξ Γ)) ⊢ renₗ (↑ ξ) C2 ∶ renₜ (↑ ξ) (↑ₜ τ)
    ↑Θ'；Δ'；Γ'⊢C⟨↑ξ⟩∶↑τ⟨↑ξ⟩ = tyExt ≈-refl (renCtx↑ Γ ξ) ↑Θ'；Δ'；[↑Γ]⟨↑ξ⟩⊢C2⟨↑ξ⟩∶↑τ⟨↑ξ⟩

    open ≡-Reasoning

    ↑τ⟨↑ξ⟩≡↑τ⟨ξ⟩ : renₜ (↑ ξ) (↑ₜ τ) ≡ ↑ₜ (renₜ ξ τ)
    ↑τ⟨↑ξ⟩≡↑τ⟨ξ⟩ =
      renₜ (↑ ξ) (renₜ suc τ) ≡⟨ sym (renFuseₜ (↑ ξ) suc τ) ⟩
      renₜ (↑ ξ ∘ suc) τ      ≡⟨ renExtₜ (↑∘suc ξ) τ ⟩
      renₜ (suc ∘ ξ) τ        ≡⟨ renFuseₜ suc ξ τ ⟩
      renₜ suc (renₜ ξ τ)     ∎

    ↑Θ'；Δ'；Γ'⊢C⟨↑ξ⟩∶↑τ⟨ξ⟩ : (↑LocCtx Θ' , ↑LocalCtx (renₗ-LocalCtx ξ Δ) , ↑Ctx (renCtx ξ Γ)) ⊢ renₗ (↑ ξ) C2 ∶ ↑ₜ (renₜ ξ τ)
    ↑Θ'；Δ'；Γ'⊢C⟨↑ξ⟩∶↑τ⟨ξ⟩ = subst (λ x → _ ⊢ _ ∶ x) ↑τ⟨↑ξ⟩≡↑τ⟨ξ⟩ ↑Θ'；Δ'；Γ'⊢C⟨↑ξ⟩∶↑τ⟨↑ξ⟩

-- The typing relation has weakening on OPEs of local variables
tyWkₗₑ : ∀{Θ Δ1 Δ2 Γ C τ ξ} →
         OPE ξ Δ1 Δ2 →
         (Θ , Δ1 , Γ) ⊢ C ∶ τ →
         (Θ , Δ2 , Γ) ⊢ renₗₑ ξ C ∶ τ
tyWkₗₑ ξ (tyVar Θ⊢Γ x) = tyVar Θ⊢Γ x
tyWkₗₑ ξ (tyDone Θ⊢Γ Θ⊢ℓ Δ1∣ℓ⊢e∶t) = tyDone Θ⊢Γ Θ⊢ℓ (tyWkOPEₑ ξ Δ1∣ℓ⊢e∶t)
tyWkₗₑ ξ (tySend C∶t Θ⊢ℓ2) = tySend (tyWkₗₑ ξ C∶t) Θ⊢ℓ2
tyWkₗₑ ξ (tyIf C∶bool C1∶τ C2∶τ) = tyIf (tyWkₗₑ ξ C∶bool) (tyWkₗₑ ξ C1∶τ) (tyWkₗₑ ξ C2∶τ)
tyWkₗₑ ξ (tySync Θ⊢ℓ1 Θ⊢ℓ2 C∶τ) = tySync Θ⊢ℓ1 Θ⊢ℓ2 (tyWkₗₑ ξ C∶τ)
tyWkₗₑ ξ (tyDefLocal {t1 = t1} {ℓ} C1∶t1 C2∶τ2) =
  tyDefLocal (tyWkₗₑ ξ C1∶t1) (tyWkₗₑ (KeepOPE ξ ℓ t1) C2∶τ2)
tyWkₗₑ ξ (tyFun C) = tyFun (tyWkₗₑ ξ C)
tyWkₗₑ ξ (tyFix C) = tyFix (tyWkₗₑ ξ C)
tyWkₗₑ ξ (tyApp C1 C2) = tyApp (tyWkₗₑ ξ C1) (tyWkₗₑ ξ C2)
tyWkₗₑ {Θ} {Δ} {Δ'} {Γ} ξ (tyLocAbs {C = C} {τ = τ} Θ⊢Γ C∶τ) =
  tyLocAbs Θ⊢Γ (tyWkₗₑ (renₗ-OPE suc ξ) C∶τ)
tyWkₗₑ ξ (tyLocApp {C = C} {ℓ = ℓ} C∶τ Θ⊢ℓ) = tyLocApp (tyWkₗₑ ξ C∶τ) Θ⊢ℓ
tyWkₗₑ {Θ} {Δ} {Δ'} {Γ} ξ (tyTellLet {C2 = C2} {τ = τ} C1∶Loc Θ⊢ρ1 Θ⊢ρ2 Θ⊢τ C2∶↑τ) =
  tyTellLet (tyWkₗₑ ξ C1∶Loc) Θ⊢ρ1 Θ⊢ρ2 Θ⊢τ (tyWkₗₑ (renₗ-OPE suc ξ) C2∶↑τ) 

{-
  If we have a typing judgment under location context Θ
  and global context Γ, then Γ must be well-formed under Θ
-}
ty⇒wfCtx : ∀{Θ Δ Γ C τ} →
         (Θ , Δ , Γ) ⊢ C ∶ τ →
         Θ ⊢ Γ
ty⇒wfCtx (tyVar Θ⊢Γ x) = Θ⊢Γ
ty⇒wfCtx (tyDone Θ⊢Γ Θ⊢ℓ Δ∣ℓ⊢e∶t) = Θ⊢Γ
ty⇒wfCtx (tySend C∶τ Θ⊢ℓ2) = ty⇒wfCtx C∶τ
ty⇒wfCtx (tyIf C∶bool C1∶τ C2∶τ) = ty⇒wfCtx C∶bool
ty⇒wfCtx (tySync Θ⊢ℓ1 Θ⊢ℓ2 C∶τ) = ty⇒wfCtx C∶τ
ty⇒wfCtx (tyDefLocal C1∶t1 C2∶τ2) = ty⇒wfCtx C1∶t1
ty⇒wfCtx (tyFun C∶τ) = wfCtxTail (ty⇒wfCtx C∶τ)
ty⇒wfCtx (tyFix C∶τ) = wfCtxTail (ty⇒wfCtx C∶τ)
ty⇒wfCtx (tyApp C1 C2) = ty⇒wfCtx C1
ty⇒wfCtx (tyLocAbs Θ⊢Γ C∶τ) = Θ⊢Γ
ty⇒wfCtx (tyLocApp C∶τ Θ⊢ℓ) = ty⇒wfCtx C∶τ
ty⇒wfCtx (tyTellLet C∶τ Θ⊢ρ1 Θ⊢ρ2 Θ⊢τ C∶τ₁) = ty⇒wfCtx C∶τ

{-
  If we have a typing judgment under location context Θ
  with type τ, then τ must be well-formed under Θ
-}
ty⇒wfTy : ∀{Θ Δ Γ C τ} →
         (Θ , Δ , Γ) ⊢ C ∶ τ →
         Θ ⊢ₜ τ
ty⇒wfTy (tyVar Θ⊢Γ x) = Θ⊢Γ x
ty⇒wfTy (tyDone Θ⊢Γ Θ⊢ℓ Δ∣ℓ⊢e∶t) = wfAt Θ⊢ℓ
ty⇒wfTy (tySend C∶τ Θ⊢ℓ2) = wfAt Θ⊢ℓ2
ty⇒wfTy (tyIf C∶bool C1∶τ C2∶τ) = ty⇒wfTy C1∶τ
ty⇒wfTy (tySync Θ⊢ℓ1 Θ⊢ℓ2 C∶τ) = ty⇒wfTy C∶τ
ty⇒wfTy (tyDefLocal C1∶t1 C2∶τ2) = ty⇒wfTy C2∶τ2
ty⇒wfTy (tyFun C∶τ2) = wfArrow (ty⇒wfCtx C∶τ2 0) (ty⇒wfTy C∶τ2)
ty⇒wfTy (tyFix C∶τ) = ty⇒wfTy C∶τ
ty⇒wfTy (tyApp C1∶τ1⇒τ2 C2∶τ1) = wfArrow₂ (ty⇒wfTy C1∶τ1⇒τ2)
ty⇒wfTy (tyLocAbs Θ⊢Γ C∶τ) = wfAllLoc (ty⇒wfTy C∶τ)
ty⇒wfTy {Θ} (tyLocApp C∶τ Θ⊢ℓ) =
  wfSubₜ (▸ₗ⇒ (idSubₗ⇒ Θ) Θ⊢ℓ) (wfAllLocArg (ty⇒wfTy C∶τ))
ty⇒wfTy (tyTellLet C1∶Loc Θ⊢ρ1 Θ⊢ρ2 Θ⊢τ C2∶τ) = Θ⊢τ

-- The typing relation has weakening on global variables
tyWk : ∀{Θ Δ Γ Γ' C τ} ξ →
       Γ ≈ Γ' ∘ ξ →
       Θ ⊢ Γ' →
       (Θ , Δ , Γ) ⊢ C ∶ τ →
       (Θ , Δ , Γ') ⊢ ren ξ C ∶ τ
tyWk {Θ} {Δ} {Γ} {Γ'} ξ Γ≈Γ'∘ξ Θ⊢Γ' (tyVar Θ⊢Γ x) = ξx∶Γx
  where
  ξx∶Γ'[ξx] : (Θ , Δ , Γ') ⊢ Var (ξ x) ∶ Γ' (ξ x)
  ξx∶Γ'[ξx] = tyVar Θ⊢Γ' (ξ x)

  ξx∶Γx : (Θ , Δ , Γ') ⊢ Var (ξ x) ∶ Γ x
  ξx∶Γx = subst (λ z → (Θ , Δ , Γ') ⊢ Var (ξ x) ∶ z) (sym (Γ≈Γ'∘ξ x)) ξx∶Γ'[ξx]
tyWk ξ Γ≈Γ'∘ξ Θ⊢Γ' (tyDone Θ⊢Γ Θ⊢ℓ Δ∣ℓ⊢e∶t) = tyDone Θ⊢Γ' Θ⊢ℓ Δ∣ℓ⊢e∶t
tyWk ξ Γ≈Γ'∘ξ Θ⊢Γ' (tySend C∶τ Θ⊢ℓ2) = tySend (tyWk ξ Γ≈Γ'∘ξ Θ⊢Γ' C∶τ) Θ⊢ℓ2
tyWk ξ Γ≈Γ'∘ξ Θ⊢Γ' (tyIf C∶bool C1∶τ C2∶τ) =
  tyIf (tyWk ξ Γ≈Γ'∘ξ Θ⊢Γ' C∶bool) (tyWk ξ Γ≈Γ'∘ξ Θ⊢Γ' C1∶τ) (tyWk ξ Γ≈Γ'∘ξ Θ⊢Γ' C2∶τ)
tyWk ξ Γ≈Γ'∘ξ Θ⊢Γ' (tySync Θ⊢ℓ1 Θ⊢ℓ2 C∶τ) = tySync Θ⊢ℓ1 Θ⊢ℓ2 (tyWk ξ Γ≈Γ'∘ξ Θ⊢Γ' C∶τ)
tyWk ξ Γ≈Γ'∘ξ Θ⊢Γ' (tyDefLocal C1∶t1 C2∶τ2) =
  tyDefLocal (tyWk ξ Γ≈Γ'∘ξ Θ⊢Γ' C1∶t1) (tyWk ξ Γ≈Γ'∘ξ Θ⊢Γ' C2∶τ2)
tyWk {Θ} {Δ} {Γ} {Γ'} ξ Γ≈Γ'∘ξ Θ⊢Γ' (tyFun {C = C} {τ1 = τ1} {τ2 = τ2} C∶τ2) = tyFun C⟨↑ξ⟩∶τ2
  where
  Γ,,τ1≈[Γ',,τ1]∘↑ξ : Γ ,, τ1 ≈ (Γ' ,, τ1) ∘ (↑ ξ)
  Γ,,τ1≈[Γ',,τ1]∘↑ξ zero = refl
  Γ,,τ1≈[Γ',,τ1]∘↑ξ (suc n) = Γ≈Γ'∘ξ n

  C⟨↑ξ⟩∶τ2 : (Θ , Δ , (Γ' ,, τ1)) ⊢ ren (↑ ξ) C ∶ τ2
  C⟨↑ξ⟩∶τ2 = tyWk (↑ ξ) Γ,,τ1≈[Γ',,τ1]∘↑ξ (wfCtx,, Θ⊢Γ' (ty⇒wfCtx C∶τ2 0)) C∶τ2
tyWk {Θ} {Δ} {Γ} {Γ'} ξ Γ≈Γ'∘ξ Θ⊢Γ' (tyFix {C = C} {τ = τ} C∶τ) = tyFix C⟨↑ξ⟩∶τ
  where
  Γ,,τ≈[Γ',,τ]∘↑ξ : Γ ,, τ ≈ (Γ' ,, τ) ∘ (↑ ξ)
  Γ,,τ≈[Γ',,τ]∘↑ξ zero = refl
  Γ,,τ≈[Γ',,τ]∘↑ξ (suc n) = Γ≈Γ'∘ξ n

  C⟨↑ξ⟩∶τ : (Θ , Δ , (Γ' ,, τ)) ⊢ ren (↑ ξ) C ∶ τ
  C⟨↑ξ⟩∶τ = tyWk (↑ ξ) Γ,,τ≈[Γ',,τ]∘↑ξ (wfCtx,, Θ⊢Γ' (ty⇒wfCtx C∶τ 0)) C∶τ
tyWk ξ Γ≈Γ'∘ξ Θ⊢Γ' (tyApp C1∶τ1⇒τ2 C2∶τ1) =
  tyApp (tyWk ξ Γ≈Γ'∘ξ Θ⊢Γ' C1∶τ1⇒τ2) (tyWk ξ Γ≈Γ'∘ξ Θ⊢Γ' C2∶τ1)
tyWk {Θ} {Δ} {Γ} {Γ'} ξ Γ≈Γ'∘ξ Θ⊢Γ' (tyLocAbs {C = C} Θ⊢Γ C∶τ) =
  tyLocAbs Θ⊢Γ' (tyWk ξ ↑Γ≈↑Γ'∘ξ (wfCtx↑ Θ⊢Γ') C∶τ)
  where
  open import Relation.Binary.Reasoning.Setoid (≈-Setoid′ ℕ Typ)

  ↑Γ≈↑Γ'∘ξ : ↑Ctx Γ ≈ ↑Ctx Γ' ∘ ξ
  ↑Γ≈↑Γ'∘ξ = begin
    ↑Ctx Γ        ≈⟨ ↑CtxExt Γ≈Γ'∘ξ ⟩
    ↑Ctx (Γ' ∘ ξ) ≈⟨ ↑Ctx∘ Γ' ξ ⟩
    ↑Ctx Γ' ∘ ξ   ∎
tyWk {Θ} {Δ} {Γ} {Γ'} ξ Γ≈Γ'∘ξ Θ⊢Γ' (tyLocApp C∶τ Θ⊢ℓ) =
  tyLocApp (tyWk ξ Γ≈Γ'∘ξ Θ⊢Γ' C∶τ) Θ⊢ℓ
tyWk {Θ} {Δ} {Γ} {Γ'} ξ Γ≈Γ'∘ξ Θ⊢Γ' (tyTellLet C1∶Loc Θ⊢ρ1 Θ⊢ρ2 Θ⊢τ C2∶τ) =
  tyTellLet (tyWk ξ Γ≈Γ'∘ξ Θ⊢Γ' C1∶Loc) Θ⊢ρ1 Θ⊢ρ2 Θ⊢τ (tyWk ξ ↑Γ≈↑Γ'∘ξ (wfCtx↑ Θ⊢Γ') C2∶τ)
  where
  open import Relation.Binary.Reasoning.Setoid (≈-Setoid′ ℕ Typ)

  ↑Γ≈↑Γ'∘ξ : ↑Ctx Γ ≈ ↑Ctx Γ' ∘ ξ
  ↑Γ≈↑Γ'∘ξ = begin
    ↑Ctx Γ        ≈⟨ ↑CtxExt Γ≈Γ'∘ξ ⟩
    ↑Ctx (Γ' ∘ ξ) ≈⟨ ↑Ctx∘ Γ' ξ ⟩
    ↑Ctx Γ' ∘ ξ   ∎

{-
  A global substitution σ changes context Γ1 to context Γ2
  if for every variable n, σ assigns n to an expression
  which, under Γ2, has the same type that Γ1 assigns to n.
-}
_∶_⇒_ : LocCtx × LocalCtx × (ℕ → Chor) → (Γ1 Γ2 : ℕ → Typ) → Set
(Θ , Δ , σ) ∶ Γ1 ⇒ Γ2 = ∀ n → (Θ , Δ , Γ2) ⊢ σ n ∶ Γ1 n

-- The identity substitution changes any context to itself
idSub⇒ : ∀ Θ Δ Γ → Θ ⊢ Γ → (Θ , Δ , idSub) ∶ Γ ⇒ Γ
idSub⇒ Θ Δ Γ Θ⊢Γ n = tyVar Θ⊢Γ n

-- Instantiating a well-typed term preserves change in context
▸⇒ : ∀{Θ Δ Γ1 Γ2 σ C τ} →
      (Θ , Δ , σ) ∶ Γ1 ⇒ Γ2 →
      (Θ , Δ , Γ2) ⊢ C ∶ τ →
      (Θ , Δ , σ ▸ C) ∶ Γ1 ,, τ ⇒ Γ2
▸⇒ σ⇒ C∶τ zero = C∶τ
▸⇒ σ⇒ C∶τ (suc n) = σ⇒ n

-- If σ changes Γ1 to Γ2 then Γ2 is well-formed
wfCtx⇒ : ∀{Θ Δ Γ1 Γ2 σ} →
          (Θ , Δ , σ) ∶ Γ1 ⇒ Γ2 →
          Θ ⊢ Γ2
wfCtx⇒ σ = ty⇒wfCtx (σ 0)
  
-- ↑ preserves change in context
↑σ⇒ : ∀{Θ Δ Γ1 Γ2 σ τ} →
      Θ ⊢ₜ τ →
      (Θ , Δ , σ) ∶ Γ1 ⇒ Γ2 →
      (Θ , Δ , ↑σ σ) ∶ Γ1 ,, τ ⇒ (Γ2 ,, τ)
↑σ⇒ Θ⊢τ σ⇒ zero = tyVar (wfCtx,, (wfCtx⇒ σ⇒) Θ⊢τ) 0
↑σ⇒ Θ⊢τ σ⇒ (suc n) = tyWk suc (λ n → refl) (wfCtx,, (wfCtx⇒ σ⇒) Θ⊢τ) (σ⇒ n)

-- Binding a location variable preserves change in context
↑Loc⇒ : ∀{Θ Δ Γ1 Γ2 σ} →
        (Θ , Δ , σ) ∶ Γ1 ⇒ Γ2 →
        (↑LocCtx Θ , renₗ-LocalCtx suc Δ , (λ n → renₗ suc (σ n))) ∶ ↑Ctx Γ1 ⇒ ↑Ctx Γ2
↑Loc⇒ {Θ} {Δ} σ⇒ n = tyWkₗ suc suc-injective Θ≈↑Θ∘suc (σ⇒ n)
  where
  Θ≈↑Θ∘suc : Θ ≈ ↑LocCtx Θ ∘ suc
  Θ≈↑Θ∘suc n = refl

,,[ℓ]⇒ : ∀{Θ Δ Γ1 Γ2 σ} →
          (Θ , Δ , σ) ∶ Γ1 ⇒ Γ2 →
          ∀ ℓ t →
          (Θ , ((ℓ , t) ∷ Δ) , λ x → renₗₑ (Drop Id ℓ t) (σ x)) ∶ Γ1 ⇒ Γ2
,,[ℓ]⇒ {Θ} {Δ} {Γ1} {Γ2} {σ} σ⇒ ℓ t n = tyWkₗₑ (DropOPE IdOPE ℓ t) (σ⇒ n)

-- Typing is closed under context-changing substitutions
tySub : ∀{Θ Δ Γ1 Γ2 C τ σ} →
        (Θ , Δ , σ) ∶ Γ1 ⇒ Γ2 →
        (Θ , Δ , Γ1) ⊢ C ∶ τ →
        (Θ , Δ , Γ2) ⊢ sub σ C ∶ τ
tySub σ (tyVar Θ⊢Γ x) = σ x
tySub σ (tyDone Θ⊢Γ Θ⊢ℓ Δ∣ℓ⊢e∶t) = tyDone (wfCtx⇒ σ) Θ⊢ℓ Δ∣ℓ⊢e∶t
tySub σ (tySend C Θ⊢ℓ2) = tySend (tySub σ C) Θ⊢ℓ2
tySub σ (tyIf C C1 C2) = tyIf (tySub σ C) (tySub σ C1) (tySub σ C2)
tySub σ (tySync Θ⊢ℓ1 Θ⊢ℓ2 C) = tySync Θ⊢ℓ1 Θ⊢ℓ2 (tySub σ C)
tySub σ (tyDefLocal {t1 = t1} {ℓ = ℓ} C1 C2) = 
  tyDefLocal (tySub σ C1) (tySub (,,[ℓ]⇒ σ ℓ t1) C2)
tySub σ (tyFun C) = tyFun (tySub (↑σ⇒ (ty⇒wfCtx C zero) σ) C)
tySub σ (tyFix C) = tyFix (tySub (↑σ⇒ (ty⇒wfCtx C zero) σ) C)
tySub σ (tyApp C1 C2) = tyApp (tySub σ C1) (tySub σ C2)
tySub σ (tyLocAbs Θ⊢Γ C) = tyLocAbs (wfCtx⇒ σ) (tySub (↑Loc⇒ σ) C)
tySub σ (tyLocApp C Θ⊢ℓ) = tyLocApp (tySub σ C) Θ⊢ℓ
tySub σ (tyTellLet C1 Θ⊢ρ1 Θ⊢ρ2 Θ⊢τ C2) =
  tyTellLet (tySub σ C1) Θ⊢ρ1 Θ⊢ρ2 Θ⊢τ (tySub (↑Loc⇒ σ) C2)

subₗ-Ctx,, : ∀ Γ τ σ → subₗ-Ctx σ (Γ ,, τ) ≈ subₗ-Ctx σ Γ ,, subₜ σ τ
subₗ-Ctx,, Γ τ σ zero = refl
subₗ-Ctx,, Γ τ σ (suc n) = refl

open ≡-Reasoning

subₗ-Ctx↑ : ∀ Γ σ → subₗ-Ctx (↑σₗ σ) (↑Ctx Γ) ≈ ↑Ctx (subₗ-Ctx σ Γ)
subₗ-Ctx↑ Γ σ n = 
  subₜ (↑σₗ σ) (renₜ suc (Γ n))      ≡⟨ cong (λ x → subₜ (↑σₗ σ) x) (sym (subιₜ suc (Γ n))) ⟩
  subₜ (↑σₗ σ) (subₜ (ιₗ suc) (Γ n)) ≡⟨ sym (subFuseₜ (↑σₗ σ) (ιₗ suc) (Γ n)) ⟩
  subₜ (↑σₗ σ •ₗ ιₗ suc) (Γ n)       ≡⟨ subExtₜ (λ{ zero → refl ; (suc n) → refl }) (Γ n) ⟩
  subₜ (ιₗ suc •ₗ σ) (Γ n)          ≡⟨ subFuseₜ (ιₗ suc) σ (Γ n) ⟩
  subₜ (ιₗ suc) (subₜ σ (Γ n))      ≡⟨ subιₜ suc (subₜ σ (Γ n)) ⟩
  renₜ suc (subₗ-Ctx σ Γ n)         ∎

subₗ-Loc↑ : ∀ ℓ σ → subₗ-Loc (↑σₗ σ) (renₗ-Loc suc ℓ) ≡ renₗ-Loc suc (subₗ-Loc σ ℓ)
subₗ-Loc↑ ℓ σ = 
  subₗ-Loc (↑σₗ σ) (renₗ-Loc suc ℓ)      ≡⟨ cong (λ x → subₗ-Loc (↑σₗ σ) x) (sym (subιₗ-Loc suc ℓ)) ⟩
  subₗ-Loc (↑σₗ σ) (subₗ-Loc (ιₗ suc) ℓ) ≡⟨ sym (subFuseₗ-Loc (↑σₗ σ) (ιₗ suc) ℓ) ⟩
  subₗ-Loc (↑σₗ σ •ₗ ιₗ suc) ℓ           ≡⟨ subExtₗ-Loc (λ{ zero → refl ; (suc n) → refl }) ℓ ⟩
  subₗ-Loc (ιₗ suc •ₗ σ) ℓ               ≡⟨ subFuseₗ-Loc (ιₗ suc) σ ℓ ⟩
  subₗ-Loc (ιₗ suc) (subₗ-Loc σ ℓ)       ≡⟨ subιₗ-Loc suc (subₗ-Loc σ ℓ) ⟩
  renₗ-Loc suc (subₗ-Loc σ ℓ)            ∎

subₗ-LocalCtx↑ : ∀ σ Δ → subₗ-LocalCtx (↑σₗ σ) (↑LocalCtx Δ) ≡ ↑LocalCtx (subₗ-LocalCtx σ Δ)
subₗ-LocalCtx↑ σ [] = refl
subₗ-LocalCtx↑ σ ((ℓ , t) ∷ Δ) = cong₂ _∷_ (cong₂ _,_ (subₗ-Loc↑ ℓ σ) refl) (subₗ-LocalCtx↑ σ Δ)

subₜ↑ : ∀ τ σ → subₜ (↑σₗ σ) (↑ₜ τ) ≡ ↑ₜ (subₜ σ τ)
subₜ↑ τ σ =
  subₜ (↑σₗ σ) (renₜ suc τ)      ≡⟨ cong (λ x → subₜ (↑σₗ σ) x) (sym (subιₜ suc τ)) ⟩
  subₜ (↑σₗ σ) (subₜ (ιₗ suc) τ) ≡⟨ sym (subFuseₜ (↑σₗ σ) (ιₗ suc) τ) ⟩
  subₜ (↑σₗ σ •ₗ ιₗ suc) τ       ≡⟨ subExtₜ (λ{ zero → refl ; (suc n) → refl }) τ ⟩
  subₜ (ιₗ suc •ₗ σ) τ           ≡⟨ subFuseₜ (ιₗ suc) σ τ ⟩
  subₜ (ιₗ suc) (subₜ σ τ)       ≡⟨ subιₜ suc (subₜ σ τ) ⟩
  renₜ suc (subₜ σ τ)            ∎

-- Typing is closed under context-changing location substitutions
tySubₗ : ∀{Θ1 Θ2 Δ Γ C τ σ} →
         σ ∶ Θ1 ⇒ₗ Θ2 →
         (Θ1 , Δ , Γ) ⊢ C ∶ τ →
         (Θ2 , subₗ-LocalCtx σ Δ , subₗ-Ctx σ Γ) ⊢ subₗ Δ σ C ∶ subₜ σ τ
tySubₗ σ⇒ (tyVar Θ⊢Γ x) = tyVar (wfCtxSub σ⇒ Θ⊢Γ) x
tySubₗ {Δ = Δ} {σ = σ} σ⇒ (tyDone {e = e} {t} {ℓ} Θ⊢Γ Θ⊢ℓ Δ∣ℓ⊢e∶t) =
  tyDone (wfCtxSub σ⇒ Θ⊢Γ) (wfSubₗ σ⇒ Θ⊢ℓ) (tyWkₑ (locSubProj Δ σ ℓ) (locSubProj⇒ Δ σ ℓ) Δ∣ℓ⊢e∶t)
tySubₗ σ⇒ (tySend C∶t Θ⊢ℓ2) = tySend (tySubₗ σ⇒ C∶t) (wfSubₗ σ⇒ Θ⊢ℓ2)
tySubₗ σ⇒ (tyIf C∶bool C1∶τ C2∶τ) = tyIf (tySubₗ σ⇒ C∶bool) (tySubₗ σ⇒ C1∶τ) (tySubₗ σ⇒ C2∶τ)
tySubₗ σ⇒ (tySync Θ⊢ℓ1 Θ⊢ℓ2 C∶τ) = tySync (wfSubₗ σ⇒ Θ⊢ℓ1) (wfSubₗ σ⇒ Θ⊢ℓ2) (tySubₗ σ⇒ C∶τ)
tySubₗ σ⇒ (tyDefLocal {t1 = t1} {ℓ} C1∶t1 C2∶τ2) =
  tyDefLocal (tySubₗ σ⇒ C1∶t1) (tySubₗ σ⇒ C2∶τ2)
tySubₗ {Θ1} {Θ2} {Δ} {Γ} {σ = σ} σ⇒ (tyFun {C = C} {τ1} {τ2} C∶τ2) = tyFun Γ⊢C⟨σ⟩∶τ2⟨σ⟩
  where
  Γ'⊢C⟨σ⟩∶τ2⟨σ⟩ : (Θ2 , subₗ-LocalCtx σ Δ , subₗ-Ctx σ (Γ ,, τ1)) ⊢ subₗ Δ σ C ∶ subₜ σ τ2
  Γ'⊢C⟨σ⟩∶τ2⟨σ⟩ = tySubₗ σ⇒ C∶τ2

  Γ⊢C⟨σ⟩∶τ2⟨σ⟩ : (Θ2 , subₗ-LocalCtx σ Δ , (subₗ-Ctx σ Γ ,, subₜ σ τ1)) ⊢ subₗ Δ σ C ∶ subₜ σ τ2
  Γ⊢C⟨σ⟩∶τ2⟨σ⟩ = tyExt ≈-refl (subₗ-Ctx,, Γ τ1 σ) Γ'⊢C⟨σ⟩∶τ2⟨σ⟩
tySubₗ {Θ1} {Θ2} {Δ} {Γ} {σ = σ} σ⇒ (tyFix {C = C} {τ} C∶τ) = tyFix Γ⊢C⟨σ⟩∶τ⟨σ⟩
  where
  Γ'⊢C⟨σ⟩∶τ⟨σ⟩ : (Θ2 , subₗ-LocalCtx σ Δ , subₗ-Ctx σ (Γ ,, τ)) ⊢ subₗ Δ σ C ∶ subₜ σ τ
  Γ'⊢C⟨σ⟩∶τ⟨σ⟩ = tySubₗ σ⇒ C∶τ

  Γ⊢C⟨σ⟩∶τ⟨σ⟩ : (Θ2 , subₗ-LocalCtx σ Δ , (subₗ-Ctx σ Γ ,, subₜ σ τ)) ⊢ subₗ Δ σ C ∶ subₜ σ τ
  Γ⊢C⟨σ⟩∶τ⟨σ⟩ = tyExt ≈-refl (subₗ-Ctx,, Γ τ σ) Γ'⊢C⟨σ⟩∶τ⟨σ⟩
tySubₗ σ⇒ (tyApp C1∶τ1⇒τ2 C2∶τ1) = tyApp (tySubₗ σ⇒ C1∶τ1⇒τ2) (tySubₗ σ⇒ C2∶τ1)
tySubₗ {Θ1} {Θ2} {Δ} {Γ} {σ = σ} σ⇒ (tyLocAbs {C = C} {τ = τ} Θ⊢Γ C∶τ) = tyLocAbs (wfCtxSub σ⇒ Θ⊢Γ) ↑Δ⟨σ⟩⊢C⟨↑σ⟩∶τ⟨↑σ⟩
  where
  ↑Δ⟨↑σ⟩⊢C⟨↑σ⟩∶τ⟨↑σ⟩ : (↑LocCtx Θ2 , subₗ-LocalCtx (↑σₗ σ) (↑LocalCtx Δ) , ↑Ctx (subₗ-Ctx σ Γ)) ⊢ subₗ (↑LocalCtx Δ) (↑σₗ σ) C ∶ subₜ (↑σₗ σ) τ
  ↑Δ⟨↑σ⟩⊢C⟨↑σ⟩∶τ⟨↑σ⟩ = tyExt ≈-refl (subₗ-Ctx↑ Γ σ) (tySubₗ (↑σₗ⇒ σ⇒) C∶τ)

  ↑Δ⟨σ⟩⊢C⟨↑σ⟩∶τ⟨↑σ⟩ : (↑LocCtx Θ2 , ↑LocalCtx (subₗ-LocalCtx σ Δ) , ↑Ctx (subₗ-Ctx σ Γ)) ⊢ subₗ (↑LocalCtx Δ) (↑σₗ σ) C ∶ subₜ (↑σₗ σ) τ
  ↑Δ⟨σ⟩⊢C⟨↑σ⟩∶τ⟨↑σ⟩ =
    subst (λ x → (↑LocCtx Θ2 , x , ↑Ctx (subₗ-Ctx σ Γ)) ⊢ subₗ (↑LocalCtx Δ) (↑σₗ σ) C ∶ subₜ (↑σₗ σ) τ)
      (subₗ-LocalCtx↑ σ Δ) ↑Δ⟨↑σ⟩⊢C⟨↑σ⟩∶τ⟨↑σ⟩
tySubₗ {Θ1} {Θ2} {Δ} {Γ} {σ = σ} σ⇒ (tyLocApp {C = C} {τ = τ} {ℓ = ℓ} C∶τ Θ⊢ℓ) = Cℓ∶τ⟨id▸ℓ⟩⟨σ⟩
  where
  Cℓ∶τ⟨↑σ⟩⟨id▸ℓ⟨σ⟩⟩ : (Θ2 , subₗ-LocalCtx σ Δ , subₗ-Ctx σ Γ)
                     ⊢ LocApp (subₗ Δ σ C) (subₗ-Loc σ ℓ)
                     ∶ subₜ (idSubₗ ▸ₗ subₗ-Loc σ ℓ) (subₜ (↑σₗ σ) τ)
  Cℓ∶τ⟨↑σ⟩⟨id▸ℓ⟨σ⟩⟩ = tyLocApp (tySubₗ σ⇒ C∶τ) (wfSubₗ σ⇒ Θ⊢ℓ)

  τ⟨↑σ⟩⟨id▸ℓ⟨σ⟩⟩≡τ⟨id▸ℓ⟩⟨σ⟩ : subₜ (idSubₗ ▸ₗ subₗ-Loc σ ℓ) (subₜ (↑σₗ σ) τ) ≡ subₜ σ (subₜ (idSubₗ ▸ₗ ℓ) τ)
  τ⟨↑σ⟩⟨id▸ℓ⟨σ⟩⟩≡τ⟨id▸ℓ⟩⟨σ⟩ = 
    subₜ (idSubₗ ▸ₗ subₗ-Loc σ ℓ) (subₜ (↑σₗ σ) τ)
      ≡⟨ sym (subFuseₜ (idSubₗ ▸ₗ subₗ-Loc σ ℓ) (↑σₗ σ) τ) ⟩
    subₜ ((idSubₗ ▸ₗ subₗ-Loc σ ℓ) •ₗ ↑σₗ σ) τ
      ≡⟨ subExtₜ (λ{ zero → refl ; (suc n) → 
        subₗ-Loc (Var ▸ₗ subₗ-Loc σ ℓ) (subₗ-Loc (Var ∘′ suc) (σ n))
          ≡⟨ sym (subFuseₗ-Loc (Var ▸ₗ subₗ-Loc σ ℓ) (Var ∘′ suc) (σ n)) ⟩
        subₗ-Loc Var (σ n)
          ≡⟨ subIdₗ-Loc (σ n) ⟩
        σ n ∎ }) τ ⟩
    subₜ (σ •ₗ (idSubₗ ▸ₗ ℓ)) τ
      ≡⟨ subFuseₜ σ (idSubₗ ▸ₗ ℓ) τ ⟩
    subₜ σ (subₜ (idSubₗ ▸ₗ ℓ) τ) ∎

  Cℓ∶τ⟨id▸ℓ⟩⟨σ⟩ : (Θ2 , subₗ-LocalCtx σ Δ , subₗ-Ctx σ Γ)
                  ⊢ LocApp (subₗ Δ σ C) (subₗ-Loc σ ℓ)
                  ∶ subₜ σ (subₜ (idSubₗ ▸ₗ ℓ) τ)
  Cℓ∶τ⟨id▸ℓ⟩⟨σ⟩ = subst (λ x → _ ⊢ _ ∶ x) τ⟨↑σ⟩⟨id▸ℓ⟨σ⟩⟩≡τ⟨id▸ℓ⟩⟨σ⟩ Cℓ∶τ⟨↑σ⟩⟨id▸ℓ⟨σ⟩⟩
tySubₗ {Θ1} {Θ2} {Δ} {Γ} {σ = σ} σ⇒ (tyTellLet {C2 = C2} {τ = τ} C1∶Loc Θ⊢ρ1 Θ⊢ρ2 Θ⊢τ C2∶↑τ) =
  tyTellLet (tySubₗ σ⇒ C1∶Loc) (wfSubₗₗ σ⇒ Θ⊢ρ1) (wfSubₗₗ σ⇒ Θ⊢ρ2) (wfSubₜ σ⇒ Θ⊢τ) ↑Δ⟨σ⟩⊢C⟨↑σ⟩∶↑τ⟨σ⟩
  where
  ↑Δ⟨↑σ⟩⊢C⟨↑σ⟩∶τ⟨↑σ⟩ : (↑LocCtx Θ2 , subₗ-LocalCtx (↑σₗ σ) (↑LocalCtx Δ) , ↑Ctx (subₗ-Ctx σ Γ)) ⊢ subₗ (↑LocalCtx Δ) (↑σₗ σ) C2 ∶ subₜ (↑σₗ σ) (↑ₜ τ)
  ↑Δ⟨↑σ⟩⊢C⟨↑σ⟩∶τ⟨↑σ⟩ = tyExt ≈-refl (subₗ-Ctx↑ Γ σ) (tySubₗ (↑σₗ⇒ σ⇒) C2∶↑τ)

  ↑Δ⟨σ⟩⊢C⟨↑σ⟩∶↑τ⟨↑σ⟩ : (↑LocCtx Θ2 , ↑LocalCtx (subₗ-LocalCtx σ Δ) , ↑Ctx (subₗ-Ctx σ Γ)) ⊢ subₗ (↑LocalCtx Δ) (↑σₗ σ) C2 ∶ subₜ (↑σₗ σ) (↑ₜ τ)
  ↑Δ⟨σ⟩⊢C⟨↑σ⟩∶↑τ⟨↑σ⟩ =
    subst (λ x → (↑LocCtx Θ2 , x , ↑Ctx (subₗ-Ctx σ Γ)) ⊢ subₗ (↑LocalCtx Δ) (↑σₗ σ) C2 ∶ subₜ (↑σₗ σ) (↑ₜ τ))
      (subₗ-LocalCtx↑ σ Δ) ↑Δ⟨↑σ⟩⊢C⟨↑σ⟩∶τ⟨↑σ⟩

  ↑Δ⟨σ⟩⊢C⟨↑σ⟩∶↑τ⟨σ⟩ : (↑LocCtx Θ2 , ↑LocalCtx (subₗ-LocalCtx σ Δ) , ↑Ctx (subₗ-Ctx σ Γ)) ⊢ subₗ (↑LocalCtx Δ) (↑σₗ σ) C2 ∶ ↑ₜ (subₜ σ τ)
  ↑Δ⟨σ⟩⊢C⟨↑σ⟩∶↑τ⟨σ⟩ = 
    subst (λ x → (↑LocCtx Θ2 , ↑LocalCtx (subₗ-LocalCtx σ Δ) , ↑Ctx (subₗ-Ctx σ Γ)) ⊢ subₗ (↑LocalCtx Δ) (↑σₗ σ) C2 ∶ x)
      (subₜ↑ τ σ) ↑Δ⟨σ⟩⊢C⟨↑σ⟩∶↑τ⟨↑σ⟩

-- Typing is closed under context-changing local substitutions
tySubₗₑ : ∀{Θ Δ1 Δ2 Γ C τ σ} →
          SUB σ Δ1 Δ2 →
          (Θ , Δ1 , Γ) ⊢ C ∶ τ →
          (Θ , Δ2 , Γ) ⊢ subₗₑ σ C ∶ τ
tySubₗₑ σ (tyVar Θ⊢Γ x) = tyVar Θ⊢Γ x
tySubₗₑ σ (tyDone Θ⊢Γ Θ⊢ℓ e) = tyDone Θ⊢Γ Θ⊢ℓ  (tySUBₑ σ e)
tySubₗₑ σ (tySend C Θ⊢ℓ2) = tySend (tySubₗₑ σ C) Θ⊢ℓ2
tySubₗₑ σ (tyIf C C1 C2) =
  tyIf (tySubₗₑ σ C) (tySubₗₑ σ C1) (tySubₗₑ σ C2)
tySubₗₑ σ (tySync Θ⊢ℓ1 Θ⊢ℓ2 C) = tySync Θ⊢ℓ1 Θ⊢ℓ2 (tySubₗₑ σ C)
tySubₗₑ σ (tyDefLocal {t1 = t1} {ℓ = ℓ} C1 C2) = 
  tyDefLocal (tySubₗₑ σ C1) (tySubₗₑ (keepLocalSUB σ ℓ t1) C2)
tySubₗₑ σ (tyFun C) = tyFun (tySubₗₑ σ C)
tySubₗₑ σ (tyFix C) = tyFix (tySubₗₑ σ C)
tySubₗₑ σ (tyApp C1 C2) = tyApp (tySubₗₑ σ C1) (tySubₗₑ σ C2)
tySubₗₑ σ (tyLocAbs Θ⊢Γ C) = tyLocAbs Θ⊢Γ (tySubₗₑ (renₗ-SUB suc-injective σ) C)
tySubₗₑ σ (tyLocApp C Θ⊢ℓ) = tyLocApp (tySubₗₑ σ C) Θ⊢ℓ
tySubₗₑ σ (tyTellLet C1 Θ⊢ρ1 Θ⊢ρ2 Θ⊢τ C2) =
  tyTellLet (tySubₗₑ σ C1) Θ⊢ρ1 Θ⊢ρ2 Θ⊢τ (tySubₗₑ (renₗ-SUB suc-injective σ) C2) 