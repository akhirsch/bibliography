{-# OPTIONS --safe #-}

open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Nat.Properties
open import Data.List
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
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

open import Choreographies L E LE TE
open import LocalRenamings L E LE TE
open import LocationRenamings L E LE TE
open import Renamings L E LE TE
open import Substitutions L E LE TE
open import Types L E LE TE
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
           (Δ[ℓ]⊢e∶t : Δ ℓ ⊢ₑ e ∶ t) →
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
               (Θ；Δ,ℓ_t1；Γ⊢C2:τ2 : (Θ , (Δ ,,[ ℓ ] t1) , Γ) ⊢ C2 ∶ τ2) →
               (Θ , Δ , Γ) ⊢ DefLocal ℓ C1 C2 ∶ τ2
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
             (↑Θ；↑Δ；↑Γ⊢C∶τ : (↑LocCtx Θ , ↑LocalCtx Δ , ↑Ctx Γ)  ⊢ C ∶ τ) →
             (Θ , Δ , Γ) ⊢ LocAbs C ∶ AllLoc τ
  tyLocApp : ∀{Θ Δ Γ C τ ℓ}
             (Θ；Δ；Γ⊢C:∀τ : (Θ , Δ , Γ)  ⊢ C ∶ AllLoc τ) →
             (Θ⊢ℓ : Θ ⊢ₗ ℓ) →
             (Θ , Δ , Γ) ⊢ LocApp C ℓ ∶ subₜ τ (idSubₗ ▸ₗ ℓ)
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
tyUniq (tyDone Θ⊢Γ Θ⊢ℓ Δ[ℓ]⊢e∶t) (tyDone Θ⊢Γ' Θ⊢ℓ' Δ[ℓ]⊢e∶t') =
  cong₂ At (tyUniqₑ Δ[ℓ]⊢e∶t Δ[ℓ]⊢e∶t') refl
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
tyUniq (tyLocApp {τ = τ} {ℓ = ℓ} C Θ⊢ℓ) (tyLocApp {τ = τ'} C' Θ⊢ℓ') = cong₂ subₜ τ≡τ' refl
  where
  τ≡τ' : τ ≡ τ'
  τ≡τ' = AllLoc-inj (tyUniq C C')
tyUniq (tyTellLet C1 Θ⊢ρ1 Θ⊢ρ2 Θ⊢τ C2) (tyTellLet C1' Θ⊢ρ3 Θ⊢ρ4 Θ⊢τ₁ C2') =
  ↑ₜ-pres-inj _ _ (tyUniq C2 C2')

-- The typing relation respects extensional equality
tyExt : ∀{Θ Θ' Δ Δ' Γ Γ' C τ} →
        Θ ≈ Θ' → Δ ≈₂ Δ' → Γ ≈ Γ' →
        (Θ , Δ , Γ) ⊢ C ∶ τ →
        (Θ' , Δ' , Γ') ⊢ C ∶ τ
tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' (tyVar Θ⊢Γ x) =
  subst (λ z → _ ⊢ Var x ∶ z) (sym (Γ≈Γ' x)) (tyVar (wfCtxExt Θ≈Θ' Γ≈Γ' Θ⊢Γ) x)
tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' (tyDone {ℓ = ℓ} Θ⊢Γ Θ⊢ℓ Δ[ℓ]⊢e∶t) =
  tyDone (wfCtxExt Θ≈Θ' Γ≈Γ' Θ⊢Γ) (wfExtₗ Θ≈Θ' Θ⊢ℓ) (tyExtₑ (Δ≈Δ' ℓ) Δ[ℓ]⊢e∶t)
tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' (tySend C∶τ Θ⊢ℓ2) =
  tySend (tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' C∶τ) (wfExtₗ Θ≈Θ' Θ⊢ℓ2)
tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' (tyIf C∶τ C∶τ1 C∶τ2) =
  tyIf (tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' C∶τ) (tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' C∶τ1) (tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' C∶τ2)
tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' (tySync Θ⊢ℓ1 Θ⊢ℓ2 C∶τ) =
  tySync (wfExtₗ Θ≈Θ' Θ⊢ℓ1) (wfExtₗ Θ≈Θ' Θ⊢ℓ2) (tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' C∶τ)
tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' (tyDefLocal {t1 = t1} {ℓ = ℓ} C∶t1 C∶τ2) =
  tyDefLocal (tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' C∶t1) (tyExt Θ≈Θ' (addLocalCtxExt Δ≈Δ' ℓ t1) Γ≈Γ' C∶τ2)
tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' (tyFun C∶τ2) = tyFun (tyExt Θ≈Θ' Δ≈Δ' (addCtxExt Γ≈Γ') C∶τ2)
tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' (tyFix C∶τ) = tyFix (tyExt Θ≈Θ' Δ≈Δ' (addCtxExt Γ≈Γ') C∶τ)
tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' (tyApp C1∶τ1⇒τ2 C2∶τ1) =
  tyApp (tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' C1∶τ1⇒τ2) (tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' C2∶τ1)
tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' (tyLocAbs Θ⊢Γ C∶τ) =
  tyLocAbs (wfCtxExt Θ≈Θ' Γ≈Γ' Θ⊢Γ) (tyExt (↑LocCtxExt Θ≈Θ') (↑LocalCtxExt Δ≈Δ') (↑CtxExt Γ≈Γ') C∶τ)
tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' (tyLocApp C∶τ Θ⊢ℓ) = tyLocApp (tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' C∶τ) (wfExtₗ Θ≈Θ' Θ⊢ℓ)
tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' (tyTellLet C∶Loc Θ⊢ρ1 Θ⊢ρ2 Θ⊢τ C∶τ) =
  tyTellLet (tyExt Θ≈Θ' Δ≈Δ' Γ≈Γ' C∶Loc) (wfExtₗₗ Θ≈Θ' Θ⊢ρ1) (wfExtₗₗ Θ≈Θ' Θ⊢ρ2)
    (wfExtₜ Θ≈Θ' Θ⊢τ) (tyExt (↑LocCtxExt Θ≈Θ') (↑LocalCtxExt Δ≈Δ') (↑CtxExt Γ≈Γ') C∶τ)

-- The typing relation has weakening on locations
tyWkₗ : ∀{Θ Θ' Δ Δ' Γ C τ} ξ →
        Injective _≡_ _≡_ ξ →
        Θ ≈ Θ' ∘ ξ →
        Δ ≈₂ Δ' ∘ₗ ξ →
        (Θ , Δ , Γ) ⊢ C ∶ τ →
        (Θ' , Δ' , renCtx Γ ξ) ⊢ renₗ C ξ ∶ renₜ τ ξ
tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ (tyVar Θ⊢Γ x) = tyVar (wfCtxWk ξ Θ≈Θ'∘ξ Θ⊢Γ) x
tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ (tyDone {e = e} {t = t} {ℓ = ℓ} Θ⊢Γ Θ⊢ℓ Δ[ℓ]⊢e:t) =
  tyDone (wfCtxWk ξ Θ≈Θ'∘ξ Θ⊢Γ) (wfWkₗ ξ Θ≈Θ'∘ξ Θ⊢ℓ) (tyExtₑ (Δ≈Δ'∘ξ ℓ) Δ[ℓ]⊢e:t)
tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ (tySend C∶τ Θ⊢ℓ2) =
  tySend (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ C∶τ) (wfWkₗ ξ Θ≈Θ'∘ξ Θ⊢ℓ2)
tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ (tyIf C∶Bool C1∶τ C2∶τ) =
  tyIf (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ C∶Bool) (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ C1∶τ) (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ C2∶τ)
tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ (tySync Θ⊢ℓ1 Θ⊢ℓ2 C∶τ) =
  tySync (wfWkₗ ξ Θ≈Θ'∘ξ Θ⊢ℓ1) (wfWkₗ ξ Θ≈Θ'∘ξ Θ⊢ℓ2) (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ C∶τ)
tyWkₗ {Θ} {Θ'} {Δ} {Δ'} {Γ} ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ (tyDefLocal {t1 = t1} {ℓ} {τ2} C1∶t1 C2∶τ2) =
  tyDefLocal (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ C1∶t1) (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ eq C2∶τ2)
    where
    open import Relation.Binary.Reasoning.Setoid (≈₂-Setoid′ Loc ℕ Typₑ)
    
    eq : (Δ ,,[ ℓ ] t1) ≈₂ ((Δ' ,,[ renₗ-Loc ℓ ξ ] t1) ∘ₗ ξ)
    eq = begin
      Δ ,,[ ℓ ] t1                    ≈⟨ addLocalCtxExt Δ≈Δ'∘ξ ℓ t1 ⟩
      (Δ' ∘ₗ ξ) ,,[ ℓ ] t1            ≈⟨ ∘ₗ,, Δ' ξ ℓ t1 ξ-inj ⟩
      (Δ' ,,[ renₗ-Loc ℓ ξ ] t1) ∘ₗ ξ ∎
tyWkₗ {Θ} {Θ'} {Δ} {Δ'} {Γ} ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ (tyFun {τ1 = τ1} C∶τ2) =
  tyFun (tyExt ≈-refl ≈₂-refl (renCtx,, Γ τ1 ξ) (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ C∶τ2))
tyWkₗ {Θ} {Θ'} {Δ} {Δ'} {Γ} ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ (tyFix {τ = τ} C∶τ) =
  tyFix (tyExt ≈-refl ≈₂-refl (renCtx,, Γ τ ξ) (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ C∶τ))
tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ (tyApp C1∶τ1⇒τ2 C2∶τ2) =
  tyApp (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ C1∶τ1⇒τ2) (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ C2∶τ2)
tyWkₗ {Θ} {Θ'} {Δ} {Δ'} {Γ} ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ (tyLocAbs {C = C} {τ = τ} Θ⊢Γ C∶τ) =
  tyLocAbs (wfCtxWk ξ Θ≈Θ'∘ξ Θ⊢Γ) ↑Θ'；↑Δ'；↑[Γ⟨ξ⟩]⊢C⟨↑ξ⟩∶τ⟨↑ξ⟩
    where
    module _ where
      open import Relation.Binary.Reasoning.Setoid (≈-Setoid′ ℕ Set)
      
      ↑Θ≈↑Θ'∘↑ξ : ↑LocCtx Θ ≈ ↑LocCtx Θ' ∘ ↑ ξ
      ↑Θ≈↑Θ'∘↑ξ = begin
        ↑LocCtx Θ        ≈⟨ ↑LocCtxExt Θ≈Θ'∘ξ ⟩
        ↑LocCtx (Θ' ∘ ξ) ≈⟨ ↑-distr-∘ Θ' ξ ⟩
        ↑LocCtx Θ' ∘ ↑ ξ ∎

    module _ where
      open import Relation.Binary.Reasoning.Setoid (≈₂-Setoid′ Loc ℕ Typₑ)

      ↑Δ≈↑Δ'∘↑ξ : ↑LocalCtx Δ ≈₂ ↑LocalCtx Δ' ∘ₗ ↑ ξ
      ↑Δ≈↑Δ'∘↑ξ = begin
        ↑LocalCtx Δ         ≈⟨ ↑LocalCtxExt Δ≈Δ'∘ξ ⟩
        ↑LocalCtx (Δ' ∘ₗ ξ) ≈⟨ ↑LocalCtx-distr-∘ₗ Δ' ξ ⟩
        ↑LocalCtx Δ' ∘ₗ ↑ ξ ∎

    ↑Θ'；↑Δ'；[↑Γ]⟨↑ξ⟩⊢C⟨↑ξ⟩∶τ⟨↑ξ⟩ : (↑LocCtx Θ' , ↑LocalCtx Δ' , renCtx (↑Ctx Γ) (↑ ξ)) ⊢ renₗ C (↑ ξ) ∶ renₜ τ (↑ ξ)
    ↑Θ'；↑Δ'；[↑Γ]⟨↑ξ⟩⊢C⟨↑ξ⟩∶τ⟨↑ξ⟩ = tyWkₗ (↑ ξ) (↑-pres-inj ξ-inj) ↑Θ≈↑Θ'∘↑ξ ↑Δ≈↑Δ'∘↑ξ C∶τ

    ↑Θ'；↑Δ'；↑[Γ⟨ξ⟩]⊢C⟨↑ξ⟩∶τ⟨↑ξ⟩ : (↑LocCtx Θ' , ↑LocalCtx Δ' , ↑Ctx (renCtx Γ ξ)) ⊢ renₗ C (↑ ξ) ∶ renₜ τ (↑ ξ)
    ↑Θ'；↑Δ'；↑[Γ⟨ξ⟩]⊢C⟨↑ξ⟩∶τ⟨↑ξ⟩ = tyExt ≈-refl ≈₂-refl (renCtx↑ Γ ξ) ↑Θ'；↑Δ'；[↑Γ]⟨↑ξ⟩⊢C⟨↑ξ⟩∶τ⟨↑ξ⟩
tyWkₗ {Θ} {Θ'} {Δ} {Δ'} {Γ} ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ (tyLocApp {C = C} {τ = τ} {ℓ = ℓ} C∶τ Θ⊢ℓ) = Θ'；Δ'；Γ⟨ξ⟩⊢Cℓ
  where
  open ≡-Reasoning

  Θ'；Δ'；Γ⟨ξ⟩⊢C : (Θ' , Δ' , renCtx Γ ξ) ⊢ renₗ C ξ ∶ AllLoc (renₜ τ (↑ ξ))
  Θ'；Δ'；Γ⟨ξ⟩⊢C = tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ C∶τ

  Θ'⊢ℓ : Θ' ⊢ₗ renₗ-Loc ℓ ξ
  Θ'⊢ℓ = wfWkₗ ξ Θ≈Θ'∘ξ Θ⊢ℓ

  Θ'；Δ'；Γ⟨ξ⟩⊢Cℓ' : (Θ' , Δ' , renCtx Γ ξ) ⊢ LocApp (renₗ C ξ) (renₗ-Loc ℓ ξ) ∶ subₜ (renₜ τ (↑ ξ)) (idSubₗ ▸ₗ renₗ-Loc ℓ ξ)
  Θ'；Δ'；Γ⟨ξ⟩⊢Cℓ' = tyLocApp Θ'；Δ'；Γ⟨ξ⟩⊢C Θ'⊢ℓ

  sub-eq : (idSubₗ ▸ₗ renₗ-Loc ℓ ξ) •ₗ ιₗ (↑ ξ) ≈ ιₗ ξ •ₗ (idSubₗ ▸ₗ ℓ)
  sub-eq zero = sym (subιₗ-Loc ξ ℓ)
  sub-eq (suc n) = refl

  ty-eq : subₜ (renₜ τ (↑ ξ)) (idSubₗ ▸ₗ renₗ-Loc ℓ ξ) ≡ renₜ (subₜ τ (idSubₗ ▸ₗ ℓ)) ξ
  ty-eq =
    subₜ (renₜ τ (↑ ξ)) (idSubₗ ▸ₗ renₗ-Loc ℓ ξ)      ≡⟨ cong₂ subₜ (sym (subιₜ (↑ ξ) τ)) refl ⟩
    subₜ (subₜ τ (ιₗ (↑ ξ))) (idSubₗ ▸ₗ renₗ-Loc ℓ ξ) ≡⟨ sym (subFuseₜ (idSubₗ ▸ₗ renₗ-Loc ℓ ξ) (ιₗ (↑ ξ)) τ) ⟩
    subₜ τ ((idSubₗ ▸ₗ renₗ-Loc ℓ ξ) •ₗ ιₗ (↑ ξ))     ≡⟨ subExtₜ sub-eq τ ⟩
    subₜ τ (ιₗ ξ •ₗ (idSubₗ ▸ₗ ℓ))                    ≡⟨ subFuseₜ (ιₗ ξ) (idSubₗ ▸ₗ ℓ) τ ⟩
    subₜ (subₜ τ (idSubₗ ▸ₗ ℓ)) (ιₗ ξ)                ≡⟨ subιₜ ξ (subₜ τ (idSubₗ ▸ₗ ℓ)) ⟩
    renₜ (subₜ τ (idSubₗ ▸ₗ ℓ)) ξ                     ∎

  Θ'；Δ'；Γ⟨ξ⟩⊢Cℓ : (Θ' , Δ' , renCtx Γ ξ) ⊢ LocApp (renₗ C ξ) (renₗ-Loc ℓ ξ) ∶ renₜ (subₜ τ (idSubₗ ▸ₗ ℓ)) ξ
  Θ'；Δ'；Γ⟨ξ⟩⊢Cℓ = subst (λ x → (Θ' , Δ' , renCtx Γ ξ) ⊢ LocApp (renₗ C ξ) (renₗ-Loc ℓ ξ) ∶ x) ty-eq Θ'；Δ'；Γ⟨ξ⟩⊢Cℓ'
tyWkₗ {Θ} {Θ'} {Δ} {Δ'} {Γ} ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ (tyTellLet {C2 = C2} {τ = τ} C1∶Loc Θ⊢ρ1 Θ⊢ρ2 Θ⊢τ C2∶↑τ) =
  tyTellLet (tyWkₗ ξ ξ-inj Θ≈Θ'∘ξ Δ≈Δ'∘ξ C1∶Loc) (wfWkₗₗ ξ Θ≈Θ'∘ξ Θ⊢ρ1) (wfWkₗₗ ξ Θ≈Θ'∘ξ Θ⊢ρ2)
    (wfWkₜ ξ Θ≈Θ'∘ξ Θ⊢τ) ↑Θ'；↑Δ'；↑[Γ⟨ξ⟩]⊢C⟨↑ξ⟩∶↑τ⟨ξ⟩
  where
    module _ where
      open import Relation.Binary.Reasoning.Setoid (≈-Setoid′ ℕ Set)
      
      ↑Θ≈↑Θ'∘↑ξ : ↑LocCtx Θ ≈ ↑LocCtx Θ' ∘ ↑ ξ
      ↑Θ≈↑Θ'∘↑ξ = begin
        ↑LocCtx Θ        ≈⟨ ↑LocCtxExt Θ≈Θ'∘ξ ⟩
        ↑LocCtx (Θ' ∘ ξ) ≈⟨ ↑-distr-∘ Θ' ξ ⟩
        ↑LocCtx Θ' ∘ ↑ ξ ∎

    module _ where
      open import Relation.Binary.Reasoning.Setoid (≈₂-Setoid′ Loc ℕ Typₑ)

      ↑Δ≈↑Δ'∘↑ξ : ↑LocalCtx Δ ≈₂ ↑LocalCtx Δ' ∘ₗ ↑ ξ
      ↑Δ≈↑Δ'∘↑ξ = begin
        ↑LocalCtx Δ         ≈⟨ ↑LocalCtxExt Δ≈Δ'∘ξ ⟩
        ↑LocalCtx (Δ' ∘ₗ ξ) ≈⟨ ↑LocalCtx-distr-∘ₗ Δ' ξ ⟩
        ↑LocalCtx Δ' ∘ₗ ↑ ξ ∎

    ↑Θ'；↑Δ'；[↑Γ]⟨↑ξ⟩⊢C2⟨↑ξ⟩∶↑τ⟨↑ξ⟩ : (↑LocCtx Θ' , ↑LocalCtx Δ' , renCtx (↑Ctx Γ) (↑ ξ)) ⊢ renₗ C2 (↑ ξ) ∶ renₜ (↑ₜ τ) (↑ ξ)
    ↑Θ'；↑Δ'；[↑Γ]⟨↑ξ⟩⊢C2⟨↑ξ⟩∶↑τ⟨↑ξ⟩ = tyWkₗ (↑ ξ) (↑-pres-inj ξ-inj) ↑Θ≈↑Θ'∘↑ξ ↑Δ≈↑Δ'∘↑ξ C2∶↑τ

    ↑Θ'；↑Δ'；↑[Γ⟨ξ⟩]⊢C⟨↑ξ⟩∶↑τ⟨↑ξ⟩ : (↑LocCtx Θ' , ↑LocalCtx Δ' , ↑Ctx (renCtx Γ ξ)) ⊢ renₗ C2 (↑ ξ) ∶ renₜ (↑ₜ τ) (↑ ξ)
    ↑Θ'；↑Δ'；↑[Γ⟨ξ⟩]⊢C⟨↑ξ⟩∶↑τ⟨↑ξ⟩ = tyExt ≈-refl ≈₂-refl (renCtx↑ Γ ξ) ↑Θ'；↑Δ'；[↑Γ]⟨↑ξ⟩⊢C2⟨↑ξ⟩∶↑τ⟨↑ξ⟩

    open ≡-Reasoning

    ↑τ⟨↑ξ⟩≡↑τ⟨ξ⟩ : renₜ (↑ₜ τ) (↑ ξ) ≡ ↑ₜ (renₜ τ ξ)
    ↑τ⟨↑ξ⟩≡↑τ⟨ξ⟩ =
      renₜ (renₜ τ suc) (↑ ξ) ≡⟨ sym (renFuseₜ suc (↑ ξ) τ) ⟩
      renₜ τ (↑ ξ ∘ suc)      ≡⟨ renExtₜ (↑∘suc ξ) τ ⟩
      renₜ τ (suc ∘ ξ)        ≡⟨ renFuseₜ ξ suc τ ⟩
      renₜ (renₜ τ ξ) suc     ∎

    ↑Θ'；↑Δ'；↑[Γ⟨ξ⟩]⊢C⟨↑ξ⟩∶↑τ⟨ξ⟩ : (↑LocCtx Θ' , ↑LocalCtx Δ' , ↑Ctx (renCtx Γ ξ)) ⊢ renₗ C2 (↑ ξ) ∶ ↑ₜ (renₜ τ ξ)
    ↑Θ'；↑Δ'；↑[Γ⟨ξ⟩]⊢C⟨↑ξ⟩∶↑τ⟨ξ⟩ = subst (λ x → (↑LocCtx Θ' , ↑LocalCtx Δ' , ↑Ctx (renCtx Γ ξ)) ⊢ renₗ C2 (↑ ξ) ∶ x)
        ↑τ⟨↑ξ⟩≡↑τ⟨ξ⟩ ↑Θ'；↑Δ'；↑[Γ⟨ξ⟩]⊢C⟨↑ξ⟩∶↑τ⟨↑ξ⟩

-- The typing relation has weakening on local variables
tyWkₗₑ : ∀{Θ Δ Δ' Γ C τ} ξ →
         Δ ≈₂ Δ' ∘ₗₑ ξ →
         (Θ , Δ , Γ) ⊢ C ∶ τ →
         (Θ , Δ' , Γ) ⊢ renₗₑ C ξ ∶ τ
tyWkₗₑ ξ Δ≈Δ'∘ξ (tyVar Θ⊢Γ x) = tyVar Θ⊢Γ x
tyWkₗₑ ξ Δ≈Δ'∘ξ (tyDone {ℓ = ℓ} Θ⊢Γ Θ⊢ℓ Δ[ℓ]⊢e∶t) =
  tyDone Θ⊢Γ Θ⊢ℓ (tyWkₑ (ξ ℓ) (Δ≈Δ'∘ξ ℓ) Δ[ℓ]⊢e∶t)
tyWkₗₑ ξ Δ≈Δ'∘ξ (tySend C∶t Θ⊢ℓ2) = tySend (tyWkₗₑ ξ Δ≈Δ'∘ξ C∶t) Θ⊢ℓ2
tyWkₗₑ ξ Δ≈Δ'∘ξ (tyIf C∶bool C1∶τ C2∶τ) =
  tyIf (tyWkₗₑ ξ Δ≈Δ'∘ξ C∶bool) (tyWkₗₑ ξ Δ≈Δ'∘ξ C1∶τ) (tyWkₗₑ ξ Δ≈Δ'∘ξ C2∶τ)
tyWkₗₑ ξ Δ≈Δ'∘ξ (tySync Θ⊢ℓ1 Θ⊢ℓ2 C∶τ) = tySync Θ⊢ℓ1 Θ⊢ℓ2 (tyWkₗₑ ξ Δ≈Δ'∘ξ C∶τ)
tyWkₗₑ {Δ = Δ} {Δ'} ξ Δ≈Δ'∘ξ (tyDefLocal {t1 = t1} {ℓ = ℓ} C1∶t1 C2∶τ2) =
  tyDefLocal (tyWkₗₑ ξ Δ≈Δ'∘ξ C1∶t1) (tyWkₗₑ (↑[ ℓ ] ξ) ctx-eq C2∶τ2)
  where
  open import Relation.Binary.Reasoning.Setoid (≈₂-Setoid′ Loc ℕ Typₑ)

  ctx-eq : Δ ,,[ ℓ ] t1 ≈₂ (Δ' ,,[ ℓ ] t1) ∘ₗₑ ↑[ ℓ ] ξ
  ctx-eq = begin
    Δ ,,[ ℓ ] t1                 ≈⟨ addLocalCtxExt Δ≈Δ'∘ξ ℓ t1 ⟩
    (Δ' ∘ₗₑ ξ) ,,[ ℓ ] t1        ≈⟨ ∘ₗₑ,, Δ' ξ ℓ t1 ⟩
    (Δ' ,,[ ℓ ] t1) ∘ₗₑ ↑[ ℓ ] ξ ∎
tyWkₗₑ ξ Δ≈Δ'∘ξ (tyFun C∶τ) = tyFun (tyWkₗₑ ξ Δ≈Δ'∘ξ C∶τ)
tyWkₗₑ ξ Δ≈Δ'∘ξ (tyFix C∶τ) = tyFix (tyWkₗₑ ξ Δ≈Δ'∘ξ C∶τ)
tyWkₗₑ ξ Δ≈Δ'∘ξ (tyApp C1∶τ1⇒τ2 C2∶τ1) = tyApp (tyWkₗₑ ξ Δ≈Δ'∘ξ C1∶τ1⇒τ2) (tyWkₗₑ ξ Δ≈Δ'∘ξ C2∶τ1)
tyWkₗₑ {Θ} {Δ} {Δ'} {Γ} ξ Δ≈Δ'∘ξ (tyLocAbs {C = C} {τ = τ} Θ⊢Γ C∶τ) = tyLocAbs Θ⊢Γ C⟨↑ξ⟩∶τ
  where
  open import Relation.Binary.Reasoning.Setoid (≈₂-Setoid′ Loc ℕ Typₑ)

  ctx-eq : ↑LocalCtx Δ ≈₂ ↑LocalCtx Δ' ∘ₗₑ ↑ₗₑ ξ
  ctx-eq = begin
    ↑LocalCtx Δ            ≈⟨ ↑LocalCtxExt Δ≈Δ'∘ξ ⟩
    ↑LocalCtx (Δ' ∘ₗₑ ξ)   ≈⟨ ↑LocalCtx-distr-∘ₗₑ Δ' ξ ⟩
    ↑LocalCtx Δ' ∘ₗₑ ↑ₗₑ ξ ∎

  C⟨↑ξ⟩∶τ : (↑LocCtx Θ , ↑LocalCtx Δ' , ↑Ctx Γ) ⊢ renₗₑ C (↑ₗₑ ξ) ∶ τ
  C⟨↑ξ⟩∶τ = tyWkₗₑ (↑ₗₑ ξ) ctx-eq C∶τ
tyWkₗₑ ξ Δ≈Δ'∘ξ (tyLocApp C∶Loc Θ⊢ℓ) = tyLocApp (tyWkₗₑ ξ Δ≈Δ'∘ξ C∶Loc) Θ⊢ℓ
tyWkₗₑ {Θ} {Δ} {Δ'} {Γ} ξ Δ≈Δ'∘ξ (tyTellLet {C2 = C2} {τ = τ} C1∶Loc Θ⊢ρ1 Θ⊢ρ2 Θ⊢τ C2∶τ) =
  tyTellLet (tyWkₗₑ ξ Δ≈Δ'∘ξ C1∶Loc) Θ⊢ρ1 Θ⊢ρ2 Θ⊢τ C2⟨↑ξ⟩∶↑τ 
  where
  open import Relation.Binary.Reasoning.Setoid (≈₂-Setoid′ Loc ℕ Typₑ)

  ctx-eq : ↑LocalCtx Δ ≈₂ ↑LocalCtx Δ' ∘ₗₑ ↑ₗₑ ξ
  ctx-eq = begin
    ↑LocalCtx Δ            ≈⟨ ↑LocalCtxExt Δ≈Δ'∘ξ ⟩
    ↑LocalCtx (Δ' ∘ₗₑ ξ)   ≈⟨ ↑LocalCtx-distr-∘ₗₑ Δ' ξ ⟩
    ↑LocalCtx Δ' ∘ₗₑ ↑ₗₑ ξ ∎

  C2⟨↑ξ⟩∶↑τ : (↑LocCtx Θ , ↑LocalCtx Δ' , ↑Ctx Γ) ⊢ renₗₑ C2 (↑ₗₑ ξ) ∶ ↑ₜ τ
  C2⟨↑ξ⟩∶↑τ = tyWkₗₑ (↑ₗₑ ξ) ctx-eq C2∶τ

{-
  If we have a typing judgment under location context Θ
  and global context Γ, then Γ must be well-formed under Θ
-}
ty⇒wfCtx : ∀{Θ Δ Γ C τ} →
         (Θ , Δ , Γ) ⊢ C ∶ τ →
         Θ ⊢ Γ
ty⇒wfCtx (tyVar Θ⊢Γ x) = Θ⊢Γ
ty⇒wfCtx (tyDone Θ⊢Γ Θ⊢ℓ Δ[ℓ]⊢e∶t) = Θ⊢Γ
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

-- The typing relation has weakening on global variables
tyWk : ∀{Θ Δ Γ Γ' C τ} ξ →
       Γ ≈ Γ' ∘ ξ →
       Θ ⊢ Γ' →
       (Θ , Δ , Γ) ⊢ C ∶ τ →
       (Θ , Δ , Γ') ⊢ ren C ξ ∶ τ
tyWk {Θ} {Δ} {Γ} {Γ'} ξ Γ≈Γ'∘ξ Θ⊢Γ' (tyVar Θ⊢Γ x) = ξx∶Γx
  where
  ξx∶Γ'[ξx] : (Θ , Δ , Γ') ⊢ Var (ξ x) ∶ Γ' (ξ x)
  ξx∶Γ'[ξx] = tyVar Θ⊢Γ' (ξ x)

  ξx∶Γx : (Θ , Δ , Γ') ⊢ Var (ξ x) ∶ Γ x
  ξx∶Γx = subst (λ z → (Θ , Δ , Γ') ⊢ Var (ξ x) ∶ z) (sym (Γ≈Γ'∘ξ x)) ξx∶Γ'[ξx]
tyWk ξ Γ≈Γ'∘ξ Θ⊢Γ' (tyDone Θ⊢Γ Θ⊢ℓ Δ[ℓ]⊢e∶t) = tyDone Θ⊢Γ' Θ⊢ℓ Δ[ℓ]⊢e∶t
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

  C⟨↑ξ⟩∶τ2 : (Θ , Δ , (Γ' ,, τ1)) ⊢ ren C (↑ ξ) ∶ τ2
  C⟨↑ξ⟩∶τ2 = tyWk (↑ ξ) Γ,,τ1≈[Γ',,τ1]∘↑ξ (wfCtx,, Θ⊢Γ' (ty⇒wfCtx C∶τ2 0)) C∶τ2
tyWk {Θ} {Δ} {Γ} {Γ'} ξ Γ≈Γ'∘ξ Θ⊢Γ' (tyFix {C = C} {τ = τ} C∶τ) = tyFix C⟨↑ξ⟩∶τ
  where
  Γ,,τ≈[Γ',,τ]∘↑ξ : Γ ,, τ ≈ (Γ' ,, τ) ∘ (↑ ξ)
  Γ,,τ≈[Γ',,τ]∘↑ξ zero = refl
  Γ,,τ≈[Γ',,τ]∘↑ξ (suc n) = Γ≈Γ'∘ξ n

  C⟨↑ξ⟩∶τ : (Θ , Δ , (Γ' ,, τ)) ⊢ ren C (↑ ξ) ∶ τ
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
