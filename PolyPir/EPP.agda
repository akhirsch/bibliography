{-# OPTIONS --safe #-}

open import Level renaming (zero to ℓ-zero; suc to ℓ-suc; _⊔_ to ℓ-max)
open import Data.Empty
open import Data.Unit
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

with-dec : ∀{a b} {A : Set a} {B : Set b} →
          Dec A →
          (A → B) →
          (¬ A → B) →
          B
with-dec (yes x) f g = f x
with-dec (no ¬x) f g = g ¬x

Handler : ∀{a} → List (Set a) → Set a → Set a
Handler [] B = B
Handler (A ∷ A*) B = (A → Handler A* B) × (¬ A → Handler A* B)

data HVec {a ℓ} {A : Set a} (P : A → Set ℓ) : List A → Set (ℓ-max a ℓ) where
  [] : HVec P []
  _∷_ : ∀{x xs} → P x → HVec P xs → HVec P (x ∷ xs)

with-dec*-impl : ∀{a} {A* : List (Set a)} {B : Set a} →
                  HVec Dec A* →
                  Handler A* B →
                  B
with-dec*-impl {A* = []} [] y = y
with-dec*-impl {A* = A ∷ A*} (A-Dec ∷ A*-Dec) (f , g) =
  with-dec A-Dec
    (λ x → with-dec*-impl A*-Dec (f x))
    (λ ¬x → with-dec*-impl A*-Dec (g ¬x))

HVec-++ : ∀{a ℓ} {A : Set a} {P : A → Set ℓ} {xs ys : List A} →
          HVec P (xs ++ ys) →
          HVec P xs × HVec P ys
HVec-++ {xs = []} {ys} Pys = [] , Pys
HVec-++ {xs = x ∷ xs} {ys} (Px ∷ Pxs++ys) =
  let (Pxs , Pys) = HVec-++ {xs = xs} {ys} Pxs++ys
  in Px ∷ Pxs , Pys

Handlers : ∀{a} → List (Set a) → Set a → List (Set a)
Handlers [] B = B ∷ []
Handlers (A ∷ A*) B =
  let Hs = Handlers A* B
  in map (λ H → A → H) Hs ++ map (λ H → ¬ A → H) Hs

ap-HVec : ∀{a} {A : Set a}
          {Ts : List (Set a)} →
          HVec id (map (λ X → A → X) Ts) →
          A → HVec id Ts
ap-HVec {Ts = []} [] x = []
ap-HVec {Ts = T ∷ Ts} (f ∷ fs) x = f x ∷ ap-HVec fs x

Handlers⇒Handler : ∀{a} {A* : List (Set a)} {B : Set a} →
                   HVec id (Handlers A* B) → Handler A* B
Handlers⇒Handler {A* = []} (y ∷ []) = y
Handlers⇒Handler {A* = A ∷ A*} {B} Hs =
  (λ x → Handlers⇒Handler {A* = A*} $
          ap-HVec
          (HVec-++
            {xs = map (λ H → A → H) (Handlers A* B)}
            {map (λ H → ¬ A → H) (Handlers A* B)}
            Hs .fst)
          x) ,
  λ ¬x → Handlers⇒Handler {A* = A*} $
          ap-HVec
          (HVec-++
            {xs = map (λ H → A → H) (Handlers A* B)}
            {map (λ H → ¬ A → H) (Handlers A* B)}
            Hs .snd)
          ¬x

with-dec* : ∀{a} {A* : List (Set a)} {B : Set a} →
            HVec Dec A* →
            HVec id (Handlers A* B) →
            B
with-dec* {A* = A*} A*-dec Hs =
  with-dec*-impl A*-dec (Handlers⇒Handler {A* = A*} Hs)

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
⟦ constr DoneS ((tₑ , 0) ∷ (ℓ , 0) ∷ []) ((e , 0 , 0) ∷ []) ⟧ σ Γ Δ L =
  with-dec (≡-dec-CTy (LitLoc L) (subTy C⅀ₖ σ ℓ))
    (λ L≡ℓ → just $ Ret (proj (map isLocKnd Γ) (map (?isLocalTy (LitLoc L)) Δ) (tySub C⅀ σ e)))
    (λ L≢ℓ → just Unit)
⟦ constr LamS ((τ1 , 0) ∷ (τ2 , 0) ∷ []) ((C , 0 , 1) ∷ []) ⟧ σ Γ Δ L =
  ⦇ CtrlLam (⟦ C ⟧ σ Γ ((* , τ1) ∷ Δ) L) ⦈
⟦ constr FixS ((τ , 0) ∷ []) ((C , 0 , 1) ∷ []) ⟧ σ Γ Δ L =
  ⦇ CtrlFix (⟦ C ⟧ σ Γ ((* , τ) ∷ Δ) L) ⦈
⟦ constr AppS ((τ1 , 0) ∷ (τ2 , 0) ∷ []) ((F , 0 , 0) ∷ (C , 0 , 0) ∷ []) ⟧ σ Γ Δ L =
  ⦇ CtrlApp (⟦ F ⟧ σ Γ Δ L) (⟦ C ⟧ σ Γ Δ L) ⦈
⟦ constr (AbsS (LocKnd κₑ) tt) ((τ , 1) ∷ []) ((C , 1 , 0) ∷ []) ⟧ σ Γ Δ L =
  ⦇ CtrlTAbs (⟦ C ⟧ (TyKeepSub C⅀ₖ σ) (LocKnd κₑ ∷ Γ) (renCtx C⅀ₖ suc Δ) L) ⦈
⟦ constr (AbsS * tt) ((τ , 1) ∷ []) ((C , 1 , 0) ∷ []) ⟧ σ Γ Δ L =
  ⦇ CtrlTAbs (⟦ C ⟧ (TyKeepSub C⅀ₖ σ) (* ∷ Γ) (renCtx C⅀ₖ suc Δ) L) ⦈
⟦ constr (AbsS *ₗ tt) ((τ , 1) ∷ []) ((C , 1 , 0) ∷ []) ⟧ σ Γ Δ L =
  do E[L] ← ⟦ C ⟧ (σ ▸ LitLoc L) Γ Δ L
     E    ← ⟦ C ⟧ (TyKeepSub C⅀ₖ σ) (*ₗ ∷ Γ) (renCtx C⅀ₖ suc Δ) L
     just $ CtrlTAbs (AmI (tyVar 0) (tyRenCtrl suc E[L]) E)
⟦ constr (AbsS *ₛ tt) ((τ , 1) ∷ []) ((C , 1 , 0) ∷ []) ⟧ σ Γ Δ L =
  do E[L] ← ⟦ C ⟧ (σ ▸ LitLoc L) Γ Δ L
     E    ← ⟦ C ⟧ (TyKeepSub C⅀ₖ σ) (*ₛ ∷ Γ) (renCtx C⅀ₖ suc Δ) L
     just $ CtrlTAbs (AmIIn (tyVar 0) (tyRenCtrl suc E[L]) E)
⟦ constr (AppTyS κ ∀κ) ((τ , 1) ∷ (t , 0) ∷ []) ((C , 0 , 0) ∷ []) ⟧ σ Γ Δ L =
  ⦇ (flip CtrlTApp (subTy C⅀ₖ σ t)) (⟦ C ⟧ σ Γ Δ L) ⦈
⟦ constr SendS ((ℓ1 , 0) ∷ (ℓ2 , 0) ∷ (tₑ , 0) ∷ []) ((C , 0 , 0) ∷ []) ⟧ σ Γ Δ L =
  with-dec* (≡-dec-CTy (LitLoc L) (subTy C⅀ₖ σ ℓ1) ∷
             ≡-dec-CTy (LitLoc L) (subTy C⅀ₖ σ ℓ2) ∷ []) $
    (λ L≡ℓ1 L≡ℓ2 → ⟦ C ⟧ σ Γ Δ L) ∷
    (λ L≡ℓ1 L≢ℓ2 → ⦇ (flip SendTo (subTy C⅀ₖ σ ℓ2)) (⟦ C ⟧ σ Γ Δ L) ⦈) ∷ 
    (λ L≢ℓ1 L≡ℓ2 → ⦇ Seq (⟦ C ⟧ σ Γ Δ L) (just $ Recv (subTy C⅀ₖ σ ℓ1)) ⦈) ∷
    (λ L≢ℓ1 L≢ℓ2 → ⟦ C ⟧ σ Γ Δ L) ∷ []
⟦ constr (SyncS d) ((ℓ1 , 0) ∷ (ℓ2 , 0) ∷ (τ , 0) ∷ []) ((C , 0 , 0) ∷ []) ⟧ σ Γ Δ L =
  with-dec* (≡-dec-CTy (LitLoc L) (subTy C⅀ₖ σ ℓ1) ∷
             ≡-dec-CTy (LitLoc L) (subTy C⅀ₖ σ ℓ2) ∷ []) $
    (λ L≡ℓ1 L≡ℓ2 → ⟦ C ⟧ σ Γ Δ L) ∷
    (λ L≡ℓ1 L≢ℓ2 → ⦇ (Choose d (subTy C⅀ₖ σ ℓ2)) (⟦ C ⟧ σ Γ Δ L) ⦈) ∷
    (λ L≢ℓ1 L≡ℓ2 →
      if d
        then ⦇ (λ x → Allow (subTy C⅀ₖ σ ℓ1) (′ x) ？) (⟦ C ⟧ σ Γ Δ L) ⦈
        else ⦇ (λ x → Allow (subTy C⅀ₖ σ ℓ1) ？ (′ x)) (⟦ C ⟧ σ Γ Δ L) ⦈) ∷
    (λ L≢ℓ1 L≢ℓ2 → ⟦ C ⟧ σ Γ Δ L) ∷ []
⟦ constr ITES ((ℓ , 0) ∷ (τ , 0) ∷ []) ((C1 , 0 , 0) ∷ (C2 , 0 , 0) ∷ (C3 , 0 , 0) ∷ []) ⟧ σ Γ Δ L =
  with-dec (≡-dec-CTy (LitLoc L) (subTy C⅀ₖ σ ℓ))
    (λ L≡ℓ → ⦇ CtrlITE (⟦ C1 ⟧ σ Γ Δ L) (⟦ C2 ⟧ σ Γ Δ L) (⟦ C3 ⟧ σ Γ Δ L) ⦈)
    (λ L≢ℓ → 
      do E1    ← ⟦ C1 ⟧ σ Γ Δ L
         E2    ← ⟦ C2 ⟧ σ Γ Δ L
         E3    ← ⟦ C3 ⟧ σ Γ Δ L
         E2⊔E3 ← E2 ⊔ E3
         just $ Seq E1 E2⊔E3)
⟦ constr LocalLetS ((ℓ , 0) ∷ (tₑ , 0) ∷ (τ , 0) ∷ []) ((C1 , 0 , 0) ∷ (C2 , 0 , 1) ∷ []) ⟧ σ Γ Δ L =
  with-dec (≡-dec-CTy (LitLoc L) (subTy C⅀ₖ σ ℓ))
    (λ L≡ℓ → ⦇ LetRet (⟦ C1 ⟧ σ Γ Δ L) (⟦ C2 ⟧ σ Γ ((Bnd *ₑ' , Local *ₑ' tₑ ℓ) ∷ Δ) L) ⦈)
    (λ L≢ℓ → ⦇ Seq (⟦ C1 ⟧ σ Γ Δ L) (⟦ C2 ⟧ σ Γ ((Bnd *ₑ' , Local *ₑ' tₑ ℓ) ∷ Δ) L) ⦈)
⟦ constr TellTyS ((ℓ , 0) ∷ (ρ , 0) ∷ (τ , 0) ∷ []) ((C1 , 0 , 0) ∷ (C2 , 1 , 0) ∷ []) ⟧ σ Γ Δ L =
  with-dec* (≡-dec-CTy (LitLoc L) (subTy C⅀ₖ σ ℓ) ∷
             L ?∈ₛ (subTy C⅀ₖ σ ρ) ∷ []) $
    (λ L≡ℓ _ →
        do E1 ← ⟦ C1 ⟧ σ Γ Δ L
           E2 ← ⟦ C2 ⟧ (TyKeepSub C⅀ₖ σ) (*ₑ ∷ Γ) (renCtx C⅀ₖ suc Δ) L
           just $ SendTy *ₑ E1 (subTy C⅀ₖ σ ρ) E2) ∷
    (λ L≡ℓ _ → 
        do E1 ← ⟦ C1 ⟧ σ Γ Δ L
           E2 ← ⟦ C2 ⟧ (TyKeepSub C⅀ₖ σ) (*ₑ ∷ Γ) (renCtx C⅀ₖ suc Δ) L
           just $ SendTy *ₑ E1 (subTy C⅀ₖ σ ρ) E2) ∷
    (λ L≢ℓ L∈ρ →
        do E1 ← ⟦ C1 ⟧ σ Γ Δ L
           E2 ← ⟦ C2 ⟧ (TyKeepSub C⅀ₖ σ) (*ₑ ∷ Γ) (renCtx C⅀ₖ suc Δ) L
           just $ Seq E1 (RecvTy *ₑ (subTy C⅀ₖ σ ℓ) E2)) ∷
    (λ L≢ℓ L∉ρ →
        do E1 ← ⟦ C1 ⟧ σ Γ Δ L
           E2 ← ⟦ C2 ⟧ (TyKeepSub C⅀ₖ σ) (*ₑ ∷ Γ) (renCtx C⅀ₖ suc Δ) L
           if ?notFreeTyInCtrl 0 E2 .does
            then just $ Seq E1 (tyRenCtrl pred E2)
            else nothing) ∷ []
⟦ constr TellLocS ((ℓ , 0) ∷ (ρ , 0) ∷ (τ , 0) ∷ []) ((C1 , 0 , 0) ∷ (C2 , 1 , 0) ∷ []) ⟧ σ Γ Δ L =
  with-dec* (≡-dec-CTy (LitLoc L) (subTy C⅀ₖ σ ℓ) ∷
            L ?∈ₛ (subTy C⅀ₖ σ ρ) ∷ []) $
  (λ L≡ℓ _ →
      do E1    ← ⟦ C1 ⟧ σ Γ Δ L
         E2    ← ⟦ C2 ⟧ (TyKeepSub C⅀ₖ σ) (*ₗ ∷ Γ) (renCtx C⅀ₖ suc Δ) L
         E2[L] ← ⟦ C2 ⟧ (σ ▸ LitLoc L) Γ Δ L
         just $ SendTy *ₗ E1 (subTy C⅀ₖ σ ρ) (AmI (tyVar 0) (tyRenCtrl suc E2[L]) E2)) ∷
  (λ L≡ℓ _ → 
      do E1    ← ⟦ C1 ⟧ σ Γ Δ L
         E2    ← ⟦ C2 ⟧ (TyKeepSub C⅀ₖ σ) (*ₗ ∷ Γ) (renCtx C⅀ₖ suc Δ) L
         E2[L] ← ⟦ C2 ⟧ (σ ▸ LitLoc L) Γ Δ L
         just $ SendTy *ₗ E1 (subTy C⅀ₖ σ ρ) (AmI (tyVar 0) (tyRenCtrl suc E2[L]) E2)) ∷
  (λ L≢ℓ L∈ρ →
      do E1    ← ⟦ C1 ⟧ σ Γ Δ L
         E2    ← ⟦ C2 ⟧ (TyKeepSub C⅀ₖ σ) (*ₗ ∷ Γ) (renCtx C⅀ₖ suc Δ) L
         E2[L] ← ⟦ C2 ⟧ (σ ▸ LitLoc L) Γ Δ L
         just $ Seq E1 (RecvTy *ₗ (subTy C⅀ₖ σ ℓ) (AmI (tyVar 0) (tyRenCtrl suc E2[L]) E2))) ∷
  (λ L≢ℓ L∉ρ →
      do E1 ← ⟦ C1 ⟧ σ Γ Δ L
         E2 ← ⟦ C2 ⟧ (TyKeepSub C⅀ₖ σ) (*ₗ ∷ Γ) (renCtx C⅀ₖ suc Δ) L
         if ?notFreeTyInCtrl 0 E2 .does
          then just $ Seq E1 (tyRenCtrl pred E2)
          else nothing) ∷ []
⟦ _ ⟧ σ Γ Δ L = nothing
  