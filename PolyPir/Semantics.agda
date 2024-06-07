{-# OPTIONS --safe #-}

open import Level renaming (zero to ℓ-zero; suc to ℓ-suc)
open import Data.Empty
open import Data.Unit
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map)
open import Data.Product.Properties
open import Data.Bool
open import Data.Nat
open import Data.List
open import Data.List.Properties
open import Data.Maybe renaming (map to mmap)
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr) hiding (map)
open import Relation.Nullary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality
open import Function
open import Function.Bundles

open ≡-Reasoning

open import Common
open import SecondOrderSignatures
open import ThirdOrderSignatures
open import SecondOrderSolverMacro
open import LanguageMorphism
open import ThirdOrderLanguage

open import PolyPir.LocalLang

module PolyPir.Semantics
  -- Location values
  (Loc : Set)
  -- Locations should have decidable equality
  (≡-dec-Loc : DecidableEquality Loc)

  -- Local language
  (𝕃 : LocalLang Loc)

  where

open import PolyPir.PolyPir Loc ≡-dec-Loc 𝕃 public
open import ThirdOrderLanguage C⅀ as C
open import SecondOrderLanguageUntyped C⅀₂ as UC

-- Process names in types
tyProcessNames : ∀{Γ κ} → C.Ty Γ κ → C.Ty Γ *ₗ → Set
tyProcessNames (tyVar x) ℓ' = ⊥
tyProcessNames (tyConstr (LocalTy sₑ) es) ℓ' = ⊥
tyProcessNames (tyConstr At (ℓ ∷ t ∷ [])) ℓ' = ℓ' ≡ ℓ
tyProcessNames (tyConstr Fun (s ∷ t ∷ [])) ℓ' =
  tyProcessNames s ℓ' ⊎ tyProcessNames t ℓ'
tyProcessNames (tyConstr (All (LocKnd κₑ)) (t ∷ [])) ℓ' =
  tyProcessNames t (C.tyWk ℓ')
tyProcessNames (tyConstr (All *) (t ∷ [])) ℓ' = ⊤
tyProcessNames (tyConstr (All *ₗ) (t ∷ [])) ℓ' = ⊤
tyProcessNames (tyConstr (All *ₛ) (t ∷ [])) ℓ' = ⊤
tyProcessNames (tyConstr (LitLoc L) []) ℓ' = ℓ' ≡ C.tyConstr (LitLoc L) C.[]
tyProcessNames (tyConstr Emp []) ℓ' = ⊥
tyProcessNames (tyConstr Sng (ℓ ∷ [])) ℓ' = ℓ' ≡ ℓ
tyProcessNames (tyConstr Union (ρ1 ∷ ρ2 ∷ [])) ℓ' =
  tyProcessNames ρ1 ℓ' ⊎ tyProcessNames ρ2 ℓ'

-- Process names in terms
processNames : ∀{Γ Δ t} → C.Tm Γ Δ t → C.Ty Γ *ₗ → Set
processNames (var x) ℓ' = ⊥
processNames (constr (Local sₑ) (ℓ ∷ ts) es) ℓ' = ℓ' ≡ ℓ
processNames (constr Done (ℓ ∷ t ∷ []) (e ∷ [])) ℓ' = ℓ' ≡ ℓ
processNames (constr Lam (s ∷ t ∷ []) (C ∷ [])) ℓ' =
  tyProcessNames s ℓ' ⊎ processNames C ℓ'
processNames (constr Fix (t ∷ []) (C ∷ [])) ℓ' =
  tyProcessNames t ℓ' ⊎ processNames C ℓ'
processNames (constr App (s ∷ t ∷ []) (C1 ∷ C2 ∷ [])) ℓ' =
  processNames C1 ℓ' ⊎ processNames C2 ℓ'
processNames (constr (Abs (LocKnd κₑ)) (t ∷ []) (C ∷ [])) ℓ' =
  tyProcessNames t (C.tyWk ℓ') ⊎ processNames C (C.tyWk ℓ')
processNames (constr (Abs *) (t ∷ []) (C ∷ [])) ℓ' = ⊤
processNames (constr (Abs *ₗ) (t ∷ []) (C ∷ [])) ℓ' = ⊤
processNames (constr (Abs *ₛ) (t ∷ []) (C ∷ [])) ℓ' = ⊤
processNames (constr (AppTy (LocKnd κₑ)) (t ∷ v ∷ []) (C ∷ [])) ℓ' =
  tyProcessNames t (C.tyWk ℓ') ⊎ tyProcessNames v ℓ' ⊎ processNames C ℓ'
processNames (constr (AppTy *) (t ∷ v ∷ []) (C ∷ [])) ℓ' = {! v  !}
processNames (constr (AppTy *ₗ) (t ∷ v ∷ []) (C ∷ [])) ℓ' = {!   !}
processNames (constr (AppTy *ₛ) (t ∷ v ∷ []) (C ∷ [])) ℓ' = {!   !}
processNames (constr Send (ℓ1 ∷ ℓ2 ∷ t ∷ []) (C ∷ [])) ℓ' =
  ℓ' ≡ ℓ1 ⊎ ℓ' ≡ ℓ2 ⊎ processNames C ℓ'
processNames (constr (Sync d) (ℓ1 ∷ ℓ2 ∷ t ∷ []) (C ∷ [])) ℓ' =
  ℓ' ≡ ℓ1 ⊎ ℓ' ≡ ℓ2 ⊎ processNames C ℓ'
processNames (constr ITE (ℓ ∷ t ∷ []) (C1 ∷ C2 ∷ C3 ∷ [])) ℓ' =
  ℓ' ≡ ℓ ⊎ processNames C1 ℓ' ⊎ processNames C2 ℓ' ⊎ processNames C3 ℓ'
processNames (constr LocalLet (ℓ ∷ t ∷ s ∷ []) (e ∷ C ∷ [])) ℓ' =
  ℓ' ≡ ℓ ⊎ tyProcessNames s ℓ' ⊎ processNames C ℓ'
processNames (constr (LocalLetTy κₑ) ts es) ℓ' = {!   !}
processNames (constr LocalLetLoc ts es) ℓ' = {!   !}

{-
Choreography rewriting relation

[AbsR]
-----------------------------
(λx.C1) C2 C3 ⇝ (λx.C1 C3) C2

[AbsL]
---------------------------------
C1 ((λx.C2) C3) ⇝ (λx.(C1 C2)) C3
-}
data _⇝_ : ∀{Γ Δ t} → C.Tm Γ Δ t → C.Tm Γ Δ t → Set where
  AbsR : ∀{Γ Δ} {t2 t3 s : C.Ty Γ *} →
          (C1 : C.Tm Γ ((* , t2) ∷ Δ) (* , TyFun t3 s))
          (C2 : C.Tm Γ Δ (* , t2))
          (C3 : C.Tm Γ Δ (* , t3)) →
          TmApp (TmApp (TmLam C1) C2) C3 ⇝ TmApp (TmLam (TmApp C1 (C.ren (C.Drop C.IdRen) C3))) C2

  AbsL : ∀{Γ Δ} {t2 t3 s : C.Ty Γ *} →
          -- spn(C1) ∩ pn(C2) ≡ ∅
          {!   !} →
          (C1 : C.Tm Γ Δ (* , TyFun t2 s))
          (C2 : C.Tm Γ ((* , t3) ∷ Δ) (* , t2))
          (C3 : C.Tm Γ Δ (* , t3)) →
          TmApp C1 (TmApp (TmLam C2) C3) ⇝ TmApp (TmLam (TmApp (C.ren (C.Drop C.IdRen) C1) C2)) C3

data _⇝*_ {Γ Δ t} : C.Tm Γ Δ t → C.Tm Γ Δ t → Set where
  ⇝*Z : ∀{C} → C ⇝* C
  ⇝*S : ∀{C1 C2 C3} → C1 ⇝ C2 → C2 ⇝* C3 → C1 ⇝* C3

data ProcLabel (Γ : List CKnd) : Set where
  ∅ : ProcLabel Γ
  Comm : C.Ty Γ *ₗ → C.Ty Γ *ₗ → ProcLabel Γ

data AbsLabel : Set where
  ƛ : AbsLabel
  τ : AbsLabel

{-
Choreography semantics

[Str]
C1 ⇝* C2
C2 ⇒[τ,P] C3
-------------
C1 ⇒[τ,P] C3
-}
data _⇒[_,_]_ : ∀{Γ Δ t} → C.Tm Γ Δ t → AbsLabel → ProcLabel Γ → C.Tm Γ Δ t → Set where
  Str : ∀{Γ Δ t P} {C1 C2 C3 : C.Tm Γ Δ t} →
        C1 ⇝* C2 →
        C2 ⇒[ τ , P ] C3 →
        C1 ⇒[ τ , P ] C3
   