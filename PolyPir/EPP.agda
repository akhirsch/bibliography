{-# OPTIONS --safe #-}

open import Level renaming (zero to ℓ-zero; suc to ℓ-suc; _⊔_ to ℓ-max)
open import Data.Empty
open import Data.Bool
open import Data.List
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map; _<*>_)
open import Data.Maybe renaming (map to mmap)
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr) hiding (map)
open import Relation.Nullary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality
open import Function

open ≡-Reasoning

open import Common
open import Common
open import KindSignatures
open import TypeSignatures
open import TypeContexts
open import Types
open import Terms
open import Kinding
open import PolyPir.LocalLang

module PolyPir.EPP
  -- Location values
  (Loc : Set)
  -- Locations should have decidable equality
  (≡-dec-Loc : DecidableEquality Loc)

  -- Local language
  (𝕃 : LocalLang Loc)
  where

open import PolyPir.ChorTypes Loc ≡-dec-Loc 𝕃
open import PolyPir.TypeOperations Loc ≡-dec-Loc 𝕃
open import PolyPir.ChorTerms Loc ≡-dec-Loc 𝕃
open import PolyPir.TermOperations Loc ≡-dec-Loc 𝕃
open import PolyPir.ChorEquality Loc ≡-dec-Loc 𝕃
open import PolyPir.CtrlLang Loc ≡-dec-Loc 𝕃

data _∈ₛ_ (L : Loc) : CTy → Set where
  ∈Sng : L ∈ₛ Sng (LitLoc L)
  ∈Union₁ : ∀{ρ1} → L ∈ₛ ρ1 → (ρ2 : CTy) → L ∈ₛ Union ρ1 ρ2
  ∈Union₂ : ∀{ρ2} → (ρ1 : CTy) → L ∈ₛ ρ2 → L ∈ₛ Union ρ1 ρ2

_?∈ₛ_ : (L : Loc) (ρ : CTy) → Dec (L ∈ₛ ρ)
L ?∈ₛ tyVar x = no λ ()
L ?∈ₛ tyConstr (EmbLocalTyS sₑ) ts = no λ ()
L ?∈ₛ tyConstr (LocalS κₑ) ts = no λ ()
L ?∈ₛ tyConstr AtS ts = no λ ()
L ?∈ₛ tyConstr FunS ts = no λ ()
L ?∈ₛ tyConstr (AllS κ ∀κ) ts = no λ ()
L ?∈ₛ tyConstr (LitLocS L') ts = no λ ()
L ?∈ₛ tyConstr EmpS ts = no λ ()
L ?∈ₛ tyConstr SngS [] = no λ ()
L ?∈ₛ tyConstr SngS ((t , zero) ∷ []) with ≡-dec-CTy (LitLoc L) t
... | yes refl = yes ∈Sng
... | no  ¬p   = no λ{ ∈Sng → ¬p refl }
L ?∈ₛ tyConstr SngS ((t , suc k) ∷ []) = no λ ()
L ?∈ₛ tyConstr SngS (tk1 ∷ tk2 ∷ ts) = no λ ()
L ?∈ₛ tyConstr UnionS [] = no λ ()
L ?∈ₛ tyConstr UnionS (tk1 ∷ []) = no λ ()
L ?∈ₛ tyConstr UnionS ((t1 , 0) ∷ (t2 , 0) ∷ []) with L ?∈ₛ t1 | L ?∈ₛ t2
... | yes p | _     = yes (∈Union₁ p t2)
... | no ¬p | yes q = yes (∈Union₂ t1 q)
... | no ¬p | no ¬q = no λ{ (∈Union₁ p ρ2) → ¬p p
                          ; (∈Union₂ ρ1 q) → ¬q q }
L ?∈ₛ tyConstr UnionS ((t1 , 0) ∷ (t2 , suc x) ∷ []) = no λ ()
L ?∈ₛ tyConstr UnionS ((t1 , suc x) ∷ (t2 , k2) ∷ []) = no λ ()
L ?∈ₛ tyConstr UnionS (tk1 ∷ tk2 ∷ tk3 ∷ ts) = no λ ()

{-
Endpoint projection

⟦ C ⟧ σ Γ Δ L

Projects the choreography C⟨σ⟩ with type variables from Γ
and variables from Δ to the location L

σ is a type substitution which maps type variables in C
to types with variables from Γ

We need to allow for the type substitution
because we need to be able to project terms of
the form ⟦C[α ↦ L]⟧L which would otherwise
not be strictly structurally recursive
-}
⟦_⟧ : CTm → TySub C⅀ₖ → List ChorKnd → List CTyp → Loc → Maybe Ctrl
⟦ var x ⟧ σ Γ Δ L = just $ var x
⟦ constr DoneS ((tₑ , 0) ∷ (ℓ , 0) ∷ []) ((e , 0 , 0) ∷ []) ⟧ σ Γ Δ L
  with ≡-dec-CTy (LitLoc L) (subTy C⅀ₖ σ ℓ)
... | yes L≡ℓ = just $ Ret (proj (map isLocKnd Γ) (map (?isLocalTy (LitLoc L)) Δ) (tySub C⅀ σ e))
... | no  L≢ℓ = just Unit
⟦ constr LamS ((τ1 , 0) ∷ (τ2 , 0) ∷ []) ((C , 0 , 1) ∷ []) ⟧ σ Γ Δ L =
  ⦇ CtrlLam (⟦ C ⟧ σ Γ ((* , τ1) ∷ Δ) L) ⦈
⟦ constr FixS ((τ , 0) ∷ []) ((C , 0 , 1) ∷ []) ⟧ σ Γ Δ L =
  ⦇ CtrlFix (⟦ C ⟧ σ Γ ((* , τ) ∷ Δ) L) ⦈
⟦ constr AppS ((τ1 , 0) ∷ (τ2 , 0) ∷ []) ((F , 0 , 0) ∷ (C , 0 , 0) ∷ []) ⟧ σ Γ Δ L =
  ⦇ CtrlApp (⟦ F ⟧ σ Γ Δ L) (⟦ C ⟧ σ Γ Δ L) ⦈
⟦ constr (AbsS (LocKnd κₑ) tt) ((τ , 1) ∷ []) ((C , 1 , 0) ∷ []) ⟧ σ Γ Δ L =
  ⦇ CtrlTAbs (⟦ C ⟧ (TyKeepSub C⅀ₖ σ) (*ₑ ∷ Γ) (renCtx C⅀ₖ suc Δ) L) ⦈
⟦ constr (AbsS * tt) ((τ , 1) ∷ []) ((C , 1 , 0) ∷ []) ⟧ σ Γ Δ L =
  ⦇ CtrlTAbs (⟦ C ⟧ (TyKeepSub C⅀ₖ σ) (* ∷ Γ) (renCtx C⅀ₖ suc Δ) L) ⦈
⟦ constr (AbsS *ₗ tt) ((τ , 1) ∷ []) ((C , 1 , 0) ∷ []) ⟧ σ Γ Δ L =
  do E[L] ← ⟦ C ⟧ (σ ▸ LitLoc L) Γ Δ L
     E ← ⟦ C ⟧ (TyKeepSub C⅀ₖ σ) (*ₗ ∷ Γ) (renCtx C⅀ₖ suc Δ) L
     just $ CtrlTAbs (AmI (tyVar 0) (tyRenCtrl suc E[L]) E)
⟦ constr (AbsS *ₛ tt) ((τ , 1) ∷ []) ((C , 1 , 0) ∷ []) ⟧ σ Γ Δ L =
  do E[L] ← ⟦ C ⟧ (σ ▸ LitLoc L) Γ Δ L
     E ← ⟦ C ⟧ (TyKeepSub C⅀ₖ σ) (*ₛ ∷ Γ) (renCtx C⅀ₖ suc Δ) L
     just $ CtrlTAbs (AmIIn (tyVar 0) (tyRenCtrl suc E[L]) E)
⟦ constr (AppTyS κ ∀κ) ((τ , 1) ∷ (t , 0) ∷ []) ((C , 0 , 0) ∷ []) ⟧ σ Γ Δ L =
  ⦇ (flip CtrlTApp t) (⟦ C ⟧ σ Γ Δ L) ⦈
⟦ constr SendS ((ℓ1 , 0) ∷ (ℓ2 , 0) ∷ (tₑ , 0) ∷ []) ((C , 0 , 0) ∷ []) ⟧ σ Γ Δ L
  with ≡-dec-CTy (LitLoc L) (subTy C⅀ₖ σ ℓ1)
     | ≡-dec-CTy (LitLoc L) (subTy C⅀ₖ σ ℓ2)
     | ≡-dec-CTy (subTy C⅀ₖ σ ℓ1) (subTy C⅀ₖ σ ℓ2)
... | yes L≡ℓ1 | yes L≡ℓ2 | yes ℓ1≡ℓ2 = ⟦ C ⟧ σ Γ Δ L
... | yes L≡ℓ1 | yes L≡ℓ2 | no  ℓ1≢ℓ2 = ⊥-elim $ ℓ1≢ℓ2 (sym L≡ℓ1 ∙ L≡ℓ2)
... | yes L≡ℓ1 | no  L≢ℓ2 | yes ℓ1≡ℓ2 = ⊥-elim $ L≢ℓ2 (L≡ℓ1 ∙ ℓ1≡ℓ2)
... | yes L≡ℓ1 | no  L≢ℓ2 | no  ℓ1≢ℓ2 = ⦇ (flip SendTo ℓ2) (⟦ C ⟧ σ Γ Δ L) ⦈
... | no  L≢ℓ1 | yes L≡ℓ2 | no  ℓ1≢ℓ2 = just $ Recv ℓ1
... | no  L≢ℓ1 | yes L≡ℓ2 | yes ℓ1≡ℓ2 = ⊥-elim $ L≢ℓ1 (L≡ℓ2 ∙ sym ℓ1≡ℓ2)
... | no  L≢ℓ1 | no  L≢ℓ2 | _ = ⟦ C ⟧ σ Γ Δ L
⟦ constr (SyncS d) ((ℓ1 , 0) ∷ (ℓ2 , 0) ∷ (τ , 0) ∷ []) ((C , 0 , 0) ∷ []) ⟧ σ Γ Δ L
  with ≡-dec-CTy (LitLoc L) (subTy C⅀ₖ σ ℓ1)
     | ≡-dec-CTy (LitLoc L) (subTy C⅀ₖ σ ℓ2)
     | ≡-dec-CTy (subTy C⅀ₖ σ ℓ1) (subTy C⅀ₖ σ ℓ2)
... | yes L≡ℓ1 | yes L≡ℓ2 | yes ℓ1≡ℓ2 = ⟦ C ⟧ σ Γ Δ L
... | yes L≡ℓ1 | yes L≡ℓ2 | no  ℓ1≢ℓ2 = ⊥-elim $ ℓ1≢ℓ2 (sym L≡ℓ1 ∙ L≡ℓ2)
... | yes L≡ℓ1 | no  L≢ℓ2 | yes ℓ1≡ℓ2 = ⊥-elim $ L≢ℓ2 (L≡ℓ1 ∙ ℓ1≡ℓ2)
... | yes L≡ℓ1 | no  L≢ℓ2 | no  ℓ1≢ℓ2 = ⦇ (Choose d ℓ2) (⟦ C ⟧ σ Γ Δ L) ⦈
... | no  L≢ℓ1 | yes L≡ℓ2 | no  ℓ1≢ℓ2 = just $ Recv ℓ1
... | no  L≢ℓ1 | yes L≡ℓ2 | yes ℓ1≡ℓ2 =
  if d
  then ⦇ (λ x → Allow ℓ1 (′ x) ？) (⟦ C ⟧ σ Γ Δ L) ⦈
  else (⦇ (λ x → Allow ℓ1 ？ (′ x)) (⟦ C ⟧ σ Γ Δ L) ⦈)
... | no  L≢ℓ1 | no  L≢ℓ2 | _ = ⟦ C ⟧ σ Γ Δ L
⟦ constr ITES ((ℓ , 0) ∷ (τ , 0) ∷ []) ((C1 , 0 , 0) ∷ (C2 , 0 , 0) ∷ (C3 , 0 , 0) ∷ []) ⟧ σ Γ Δ L
  with ≡-dec-CTy (LitLoc L) (subTy C⅀ₖ σ ℓ)
... | yes L≡ℓ = ⦇ CtrlITE (⟦ C1 ⟧ σ Γ Δ L) (⟦ C2 ⟧ σ Γ Δ L) (⟦ C3 ⟧ σ Γ Δ L) ⦈
... | no  L≢ℓ =
  do E1 ← ⟦ C1 ⟧ σ Γ Δ L
     E2 ← ⟦ C2 ⟧ σ Γ Δ L
     E3 ← ⟦ C3 ⟧ σ Γ Δ L
     E2⊔E3 ← E2 ⊔ E3
     just $ Seq E1 E2⊔E3
⟦ constr LocalLetS ((ℓ , 0) ∷ (tₑ , 0) ∷ (τ , 0) ∷ []) ((C1 , 0 , 0) ∷ (C2 , 0 , 1) ∷ []) ⟧ σ Γ Δ L =
  ⦇ LetRet (⟦ C1 ⟧ σ Γ Δ L) (⟦ C2 ⟧ σ Γ ((Bnd *ₑ' , Local *ₑ' tₑ ℓ) ∷ Δ) L) ⦈
⟦ constr TellTyS ((ℓ , 0) ∷ (ρ , 0) ∷ (τ , 0) ∷ []) ((C1 , 0 , 0) ∷ (C2 , 1 , 0) ∷ []) ⟧ σ Γ Δ L
  with ≡-dec-CTy (LitLoc L) (subTy C⅀ₖ σ ℓ) | L ?∈ₛ (subTy C⅀ₖ σ ρ)
... | yes L≡ℓ | _ =
  do E1 ← ⟦ C1 ⟧ σ Γ Δ L
     E2 ← ⟦ C2 ⟧ (TyKeepSub C⅀ₖ σ) (*ₑ ∷ Γ) (renCtx C⅀ₖ suc Δ) L
     just $ SendTy *ₑ E1 ρ E2
... | no L≢ℓ | yes L∈ρ =
  do E1 ← ⟦ C1 ⟧ σ Γ Δ L
     E2 ← ⟦ C2 ⟧ (TyKeepSub C⅀ₖ σ) (*ₑ ∷ Γ) (renCtx C⅀ₖ suc Δ) L
     just $ Seq E1 (RecvTy *ₑ ℓ E2)
... | no L≢ℓ | no  L∉ρ =
  do E1 ← ⟦ C1 ⟧ σ Γ Δ L
     E2 ← ⟦ C2 ⟧ (TyKeepSub C⅀ₖ σ) (*ₑ ∷ Γ) (renCtx C⅀ₖ suc Δ) L
     if ?notFreeTyInCtrl 0 E2 .does
      then just $ Seq E1 (tyRenCtrl pred E2)
      else nothing
⟦ constr TellLocS ((ℓ , 0) ∷ (ρ , 0) ∷ (τ , 0) ∷ []) ((C1 , 0 , 0) ∷ (C2 , 1 , 0) ∷ []) ⟧ σ Γ Δ L
  with ≡-dec-CTy (LitLoc L) (subTy C⅀ₖ σ ℓ) | L ?∈ₛ (subTy C⅀ₖ σ ρ)
... | yes L≡ℓ | _ =
  do E1 ← ⟦ C1 ⟧ σ Γ Δ L
     E2 ← ⟦ C2 ⟧ (TyKeepSub C⅀ₖ σ) (*ₗ ∷ Γ) (renCtx C⅀ₖ suc Δ) L
     E2[L] ← ⟦ C2 ⟧ (σ ▸ LitLoc L) Γ Δ L
     just $ SendTy *ₗ E1 ρ (AmI (tyVar 0) (tyRenCtrl suc E2[L]) E2)
... | no L≢ℓ | yes L∈ρ =
  do E1 ← ⟦ C1 ⟧ σ Γ Δ L
     E2 ← ⟦ C2 ⟧ (TyKeepSub C⅀ₖ σ) (*ₗ ∷ Γ) (renCtx C⅀ₖ suc Δ) L
     E2[L] ← ⟦ C2 ⟧ (σ ▸ LitLoc L) Γ Δ L
     just $ Seq E1 (RecvTy *ₗ ℓ (AmI (tyVar 0) (tyRenCtrl suc E2[L]) E2))
... | no L≢ℓ | no L∉ρ =
  do E1 ← ⟦ C1 ⟧ σ Γ Δ L
     E2 ← ⟦ C2 ⟧ (TyKeepSub C⅀ₖ σ) (*ₗ ∷ Γ) (renCtx C⅀ₖ suc Δ) L
     if ?notFreeTyInCtrl 0 E2 .does
      then just $ Seq E1 (tyRenCtrl pred E2)
      else nothing
⟦ _ ⟧ σ Γ Δ L = nothing
