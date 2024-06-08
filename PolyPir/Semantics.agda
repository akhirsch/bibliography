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

{-
Values

V ::= x | λx.C

TODO: Finish definition
TODO: Verify definition
-}
data Val : ∀{Γ Δ t} → C.Tm Γ Δ t → Set where
  VarVal : ∀{Γ Δ t} (x : C.Var Γ Δ t) → Val (C.var x)
  LamVal : ∀{Γ Δ s t} (C : C.Tm Γ ((* , s) ∷ Δ) (* , t)) → Val (TmLam C)

{-
Process names in types

pn(X) = ∅
pn(tₑ) = ∅
pn(t @ ℓ) = {ℓ}
pn(τ1 → τ2) = pn(τ1) ∪ pn(τ2)
pn(∀x:*ₑ.τ) = pn(τ)
pn(∀x:*.τ) = ℒ
pn(∀x:*ₗ.τ) = ℒ
pn(∀x:*ₛ.τ) = ℒ
pn(L) = {L}
pn(∅) = ∅
pn({ℓ}) = {ℓ}
pn(ρ1 ∪ ρ2) = pn(ρ1) ∪ pn(ρ2)

TODO: Verify definition
-}
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

{-
Process names in terms

pn(x) = ∅
pn(e) = ∅
pn(ℓ.e) = {ℓ}
pn(λx:τ.C) = pn(τ) ∪ pn(C)
pn(μx:τ.C) = pn(τ) ∪ pn(C)
pn(C1 C2) = pn(C1) ∪ pn(C2)
pn(ΛX:κ.C) = pn(ty(C)) ∪ pn(C)
pn(C [T]) = pn(ty(C)) ∪ pn(C) ∪ pn(T)
pn(ℓ1.C ↝ ℓ2) = {ℓ1,ℓ2} ∪ pn(C)
pn(ℓ1[d] ↝ ℓ2; C) = {ℓ1,ℓ2} ∪ pn(C)
pn(ℓ.if C1 then C2 else C3) = {ℓ} ∪ pn(C1) ∪ pn(C2) ∪ pn(C3)
pn(let ℓ.x := C1 in C2) = {ℓ1} ∪ pn(C1) ∪ pn(C2)
pn(let X := ℓ.C1 ↝ ρ in C2) = {ℓ} ∪ pn(ρ) ∪ pn(C1) ∪ pn(C2)

TODO: Verify definition
-}
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
processNames (constr (Abs κ) (t ∷ []) (C ∷ [])) ℓ' =
  tyProcessNames t (C.tyWk ℓ') ⊎ processNames C (C.tyWk ℓ')
processNames (constr (AppTy κ) (t ∷ v ∷ []) (C ∷ [])) ℓ' =
  tyProcessNames t (C.tyWk ℓ') ⊎ tyProcessNames v ℓ' ⊎ processNames C ℓ'
processNames (constr Send (ℓ1 ∷ ℓ2 ∷ t ∷ []) (C ∷ [])) ℓ' =
  ℓ' ≡ ℓ1 ⊎ ℓ' ≡ ℓ2 ⊎ processNames C ℓ'
processNames (constr (Sync d) (ℓ1 ∷ ℓ2 ∷ t ∷ []) (C ∷ [])) ℓ' =
  ℓ' ≡ ℓ1 ⊎ ℓ' ≡ ℓ2 ⊎ processNames C ℓ'
processNames (constr ITE (ℓ ∷ t ∷ []) (C1 ∷ C2 ∷ C3 ∷ [])) ℓ' =
  ℓ' ≡ ℓ ⊎ processNames C1 ℓ' ⊎ processNames C2 ℓ' ⊎ processNames C3 ℓ'
processNames (constr LocalLet (ℓ ∷ t ∷ s ∷ []) (e ∷ C ∷ [])) ℓ' =
  ℓ' ≡ ℓ ⊎ tyProcessNames s ℓ' ⊎ processNames e ℓ' ⊎ processNames C ℓ'
processNames (constr (LocalLetTy κₑ) (ℓ ∷ ρ ∷ t ∷ []) (C1 ∷ C2 ∷ [])) ℓ' =
  ℓ' ≡ ℓ ⊎ tyProcessNames ρ ℓ' ⊎ tyProcessNames t ℓ'
  ⊎ processNames C1 ℓ' ⊎ processNames C2 (C.tyWk ℓ')
processNames (constr LocalLetLoc (ℓ ∷ ρ ∷ t ∷ []) (C1 ∷ C2 ∷ [])) ℓ' =
  ℓ' ≡ ℓ ⊎ tyProcessNames ρ ℓ' ⊎ tyProcessNames t ℓ'
  ⊎ processNames C1 ℓ' ⊎ processNames C2 (C.tyWk ℓ')

{-
Synchronizing process names in terms

spn(x) = ∅
spn(e) = ∅
spn(ℓ.e) = ∅
spn(λx:τ.C) = spn(C)
spn(μx:τ.C) = spn(C)
spn(C1 C2) = spn(C1) ∪ spn(C2)
spn(ΛX:κ.C) = spn(C)
spn(C [T]) = spn(C)
spn(ℓ1.C ↝ ℓ2) = {ℓ1,ℓ2} ∪ spn(C)
spn(ℓ1[d] ↝ ℓ2; C) = {ℓ1,ℓ2} ∪ spn(C)
spn(ℓ.if C1 then C2 else C3) = spn(C1) ∪ spn(C2) ∪ spn(C3)
spn(let ℓ.x := C1 in C2) = spn(C1) ∪ spn(C2)
spn(let X := ℓ.C1 ↝ ρ in C2) = {ℓ} ∪ pn(ρ) ∪ spn(C1) ∪ spn(C2)

TODO: Verify definition
-}
syncProcessNames : ∀{Γ Δ t} → C.Tm Γ Δ t → C.Ty Γ *ₗ → Set
syncProcessNames (var x) ℓ' = ⊥
syncProcessNames (constr (Local sₑ) (ℓ ∷ ts) es) ℓ' = ⊥
syncProcessNames (constr Done (ℓ ∷ t ∷ []) (e ∷ [])) ℓ' = ⊥
syncProcessNames (constr Lam (s ∷ t ∷ []) (C ∷ [])) ℓ' =
  syncProcessNames C ℓ'
syncProcessNames (constr Fix (t ∷ []) (C ∷ [])) ℓ' =
  syncProcessNames C ℓ'
syncProcessNames (constr App (s ∷ t ∷ []) (C1 ∷ C2 ∷ [])) ℓ' =
  syncProcessNames C1 ℓ' ⊎ syncProcessNames C2 ℓ'
syncProcessNames (constr (Abs κ) (t ∷ []) (C ∷ [])) ℓ' =
  syncProcessNames C (C.tyWk ℓ')
syncProcessNames (constr (AppTy κ) (t ∷ v ∷ []) (C ∷ [])) ℓ' =
  syncProcessNames C ℓ'
syncProcessNames (constr Send (ℓ1 ∷ ℓ2 ∷ t ∷ []) (C ∷ [])) ℓ' =
  ℓ' ≡ ℓ1 ⊎ ℓ' ≡ ℓ2 ⊎ syncProcessNames C ℓ'
syncProcessNames (constr (Sync d) (ℓ1 ∷ ℓ2 ∷ t ∷ []) (C ∷ [])) ℓ' =
  ℓ' ≡ ℓ1 ⊎ ℓ' ≡ ℓ2 ⊎ syncProcessNames C ℓ'
syncProcessNames (constr ITE (ℓ ∷ t ∷ []) (C1 ∷ C2 ∷ C3 ∷ [])) ℓ' =
  syncProcessNames C1 ℓ' ⊎ syncProcessNames C2 ℓ' ⊎ syncProcessNames C3 ℓ'
syncProcessNames (constr LocalLet (ℓ ∷ t ∷ s ∷ []) (e ∷ C ∷ [])) ℓ' =
  syncProcessNames C ℓ'
syncProcessNames (constr (LocalLetTy κₑ) (ℓ ∷ ρ ∷ t ∷ []) (C1 ∷ C2 ∷ [])) ℓ' =
  ℓ' ≡ ℓ ⊎ tyProcessNames ρ ℓ'
  ⊎ syncProcessNames C1 ℓ' ⊎ syncProcessNames C2 (C.tyWk ℓ')
syncProcessNames (constr LocalLetLoc (ℓ ∷ ρ ∷ t ∷ []) (C1 ∷ C2 ∷ [])) ℓ' =
  ℓ' ≡ ℓ ⊎ tyProcessNames ρ ℓ'
  ⊎ syncProcessNames C1 ℓ' ⊎ syncProcessNames C2 (C.tyWk ℓ')

{-
Choreography rewriting relation

[AbsR]
-----------------------------
(λx.C1) C2 C3 ⇝ (λx.C1 C3) C2

[AbsL]
spn(C1) ∩ pn(C2) ≡ ∅
---------------------------------
C1 ((λx.C2) C3) ⇝ (λx.(C1 C2)) C3

TODO: Finish definition
TODO: Verify definition
-}
data _⇝_ : ∀{Γ Δ t} → C.Tm Γ Δ t → C.Tm Γ Δ t → Set where
  AbsR : ∀{Γ Δ} {t2 t3 s : C.Ty Γ *} →
          (C1 : C.Tm Γ ((* , t2) ∷ Δ) (* , TyFun t3 s))
          (C2 : C.Tm Γ Δ (* , t2))
          (C3 : C.Tm Γ Δ (* , t3)) →
          TmApp (TmApp (TmLam C1) C2) C3 ⇝ TmApp (TmLam (TmApp C1 (C.ren (C.Drop C.IdRen) C3))) C2

  AbsL : ∀{Γ Δ} {t2 t3 s : C.Ty Γ *} →
          (C1 : C.Tm Γ Δ (* , TyFun t2 s))
          (C2 : C.Tm Γ ((* , t3) ∷ Δ) (* , t2))
          (C3 : C.Tm Γ Δ (* , t3)) →
          (∀ ℓ → syncProcessNames C1 ℓ → processNames C2 ℓ → ⊥) →
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

TODO: Finish definition
TODO: Verify definition
-}
data _⇒[_,_]_ : ∀{Γ Δ t} → C.Tm Γ Δ t → AbsLabel → ProcLabel Γ → C.Tm Γ Δ t → Set where
  Str : ∀{Γ Δ t P} {C1 C2 C3 : C.Tm Γ Δ t} →
        C1 ⇝* C2 →
        C2 ⇒[ τ , P ] C3 →
        C1 ⇒[ τ , P ] C3
     