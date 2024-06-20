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

open ≡-Reasoning

open import Common
open import Common
open import KindSignatures
open import TypeSignatures
open import TypeContexts
open import Types
open import Kinding
open import Terms
open import TypeContexts
open import Typing

open import PolyPir.LocalLang

module PolyPir.ChorTerms
  -- Location values
  (Loc : Set)
  -- Locations should have decidable equality
  (≡-dec-Loc : DecidableEquality Loc)

  -- Local language
  (𝕃 : LocalLang Loc)
  where

open import PolyPir.ChorTypes Loc ≡-dec-Loc 𝕃
open import PolyPir.TypeOperations Loc ≡-dec-Loc 𝕃

ChorCtx = Ctx C⅀ₖ
Ctxₑ = Ctx ⅀ₑₖ

TmSymbₑ  = 𝕃 .⅀ₑ .TmSymb
TmTySigₑ = 𝕃 .⅀ₑ .TmTySig
TmSigₑ   = 𝕃 .⅀ₑ .TmSig

-------------------------
-- CHOREOGRAPHIC TERMS --
-------------------------

{-
Choreographic term syntax

C ::= X | e | ℓ.e
    | λX:τ.C | μX:τ.C | C1 C2
    | Λα:κ.C | C [T]
    | ℓ1.C ⇝ ℓ2 | ℓ1[d] ⇝ ℓ2 ; C
    | if C1 then C2 else C3
    | let ℓ.x := C1 in C2
    | ℓ.tell α : *ₑ := C1 to ρ in C2
    | ℓ.tell α : *ₗ := C1 to ρ in C2
-}
data ChorTmSymb : Set where
  -- Embedding of local terms
  LocalTmS : (sₑ : TmSymbₑ) → ChorTmSymb
  -- Choreographic local terms
  DoneS : ChorTmSymb

  -- Lambda abstraction
  LamS : ChorTmSymb
  -- Fixpoint
  FixS : ChorTmSymb
  -- FunSction application
  AppS : ChorTmSymb
  -- Type abstraction
  AbsS : (κ : ChorKnd) (∀κ : canAbstract κ) → ChorTmSymb
  -- Type application
  AppTyS : (κ : ChorKnd) (∀κ : canAbstract κ) → ChorTmSymb
  -- Send operation
  SendS : ChorTmSymb
  -- Synchronization operation
  SyncS : (d : Bool) → ChorTmSymb
  -- If-then-else
  ITES : ChorTmSymb

  -- Binding local values
  LocalLetS : ChorTmSymb
  -- Binding local types
  TellTyS : ChorTmSymb
  -- Binding local locations
  TellLocS : ChorTmSymb

LocalTmS-inj : ∀{sₑ sₑ'} → LocalTmS sₑ ≡ LocalTmS sₑ' → sₑ ≡ sₑ'
LocalTmS-inj refl = refl

-- Type annotations for terms
ChorTmTySig : ChorTmSymb → List (List (C⅀ₖ .Knd) × C⅀ₖ .Knd)
ChorTmTySig (LocalTmS sₑ) =
  ([] , *ₗ) ∷ map LocKndΣ (TmTySigₑ sₑ)
ChorTmTySig DoneS = ([] , *ₑ) ∷ ([] , *ₗ) ∷ []
ChorTmTySig LamS = ([] , *) ∷ ([] , *) ∷ []
ChorTmTySig FixS = ([] , *) ∷ []
ChorTmTySig AppS = ([] , *) ∷ ([] , *) ∷ []
ChorTmTySig (AbsS κ ∀κ) = (κ ∷ [] , *) ∷ []
ChorTmTySig (AppTyS κ ∀κ) = (κ ∷ [] , *) ∷ ([] , κ) ∷ []
ChorTmTySig SendS = ([] , *ₗ) ∷ ([] , *ₗ) ∷ ([] , *ₑ) ∷ []
ChorTmTySig (SyncS d) = ([] , *ₗ) ∷ ([] , *ₗ) ∷ ([] , *) ∷ []
ChorTmTySig ITES = ([] , *ₗ) ∷ ([] , *) ∷ []
ChorTmTySig LocalLetS = ([] , *ₗ) ∷ ([] , *ₑ) ∷ ([] , *) ∷ []
ChorTmTySig TellTyS = ([] , *ₗ) ∷ ([] , *ₛ) ∷ ([] , *) ∷ []
ChorTmTySig TellLocS = ([] , *ₗ) ∷ ([] , *ₛ) ∷ ([] , *) ∷ []

TypFun : (Γ : ChorKndCtx) (ℓ : CTy) (Γₑ' : KndCtxₑ) →
         Typ ⅀ₑₖ → Typ C⅀ₖ
TypFun Γ ℓ Γₑ' (κₑ , tₑ) =
  Bnd κₑ ,
  Local κₑ
    (regainTy (replicate (length Γₑ') true ++ map isLocKnd Γ) (injTy tₑ))
    (renTy C⅀ₖ (Drop* id (length (injKndCtx Γₑ'))) ℓ)

⊢TypFun : ∀{Γ ℓ Γₑ' tₑ} →
           Γ c⊢ₜ ℓ ∶ *ₗ →
           wfTyp ⅀ₑₖ (Γₑ' ++ projKndCtx Γ) tₑ →
           wfTyp C⅀ₖ (injKndCtx Γₑ' ++ Γ) (TypFun Γ ℓ Γₑ' tₑ)
⊢TypFun {Γ} {ℓ} {Γₑ'} {κₑ , tₑ} ⊢ℓ ⊢tₑ =
  let eq1 : map isLocKnd (injKndCtx Γₑ' ++ Γ)
            ≡ replicate (length Γₑ') true ++ map isLocKnd Γ
      eq1 =
        map isLocKnd (injKndCtx Γₑ' ++ Γ)
          ≡⟨ map-++-commute isLocKnd (injKndCtx Γₑ') Γ ⟩
        map isLocKnd (injKndCtx Γₑ') ++ map isLocKnd Γ
          ≡⟨ cong (_++ map isLocKnd Γ) (isLocKnd∘injKndCtx≡true Γₑ') ⟩
        replicate (length Γₑ') true ++ map isLocKnd Γ ∎
      eq2 : Γₑ' ++ projKndCtx Γ ≡ projKndCtx (injKndCtx Γₑ' ++ Γ)
      eq2 =
        Γₑ' ++ projKndCtx Γ
          ≡⟨ cong (_++ projKndCtx Γ) (sym $ proj∘injKndCtx≗id Γₑ') ⟩
        projKndCtx (injKndCtx Γₑ') ++ projKndCtx Γ
          ≡⟨ (sym $ projKndCtx-++ (injKndCtx Γₑ') Γ) ⟩
        projKndCtx (injKndCtx Γₑ' ++ Γ) ∎
  in ⊢Local
    (subst (λ x → (injKndCtx Γₑ' ++ Γ) c⊢ₜ regainTy x (injTy tₑ) ∶ LocKnd κₑ)
        eq1
        (⊢regainTy (⊢injTy
          (subst (λ x → x e⊢ₜ tₑ ∶ κₑ)
              eq2
              ⊢tₑ))))
    (⊢renTy C⅀ₖ (⊢TyDrop* C⅀ₖ (⊢TyIdRen C⅀ₖ) (injKndCtx Γₑ')) ⊢ℓ)

⊢TypFun⁻ : ∀{Γ ℓ Γₑ' tₑ} →
           wfTyp C⅀ₖ (injKndCtx Γₑ' ++ Γ) (TypFun Γ ℓ Γₑ' tₑ) →
           Γ c⊢ₜ ℓ ∶ *ₗ ×
           wfTyp ⅀ₑₖ (Γₑ' ++ projKndCtx Γ) tₑ
⊢TypFun⁻ {Γ} {ℓ} {Γₑ'} {κₑ , tₑ} ⊢Local-tₑ with ⊢Local⁻ ⊢Local-tₑ
... | (⊢tₑ , ⊢ℓ) =
  let eq1 : map isLocKnd (injKndCtx Γₑ' ++ Γ)
            ≡ replicate (length Γₑ') true ++ map isLocKnd Γ
      eq1 =
        map isLocKnd (injKndCtx Γₑ' ++ Γ)
          ≡⟨ map-++-commute isLocKnd (injKndCtx Γₑ') Γ ⟩
        map isLocKnd (injKndCtx Γₑ') ++ map isLocKnd Γ
          ≡⟨ cong (_++ map isLocKnd Γ) (isLocKnd∘injKndCtx≡true Γₑ') ⟩
        replicate (length Γₑ') true ++ map isLocKnd Γ ∎
      eq2 : Γₑ' ++ projKndCtx Γ ≡ projKndCtx (injKndCtx Γₑ' ++ Γ)
      eq2 =
        Γₑ' ++ projKndCtx Γ
          ≡⟨ cong (_++ projKndCtx Γ) (sym $ proj∘injKndCtx≗id Γₑ') ⟩
        projKndCtx (injKndCtx Γₑ') ++ projKndCtx Γ
          ≡⟨ (sym $ projKndCtx-++ (injKndCtx Γₑ') Γ) ⟩
        projKndCtx (injKndCtx Γₑ' ++ Γ) ∎
  in ⊢renTy⁻ C⅀ₖ (⊢TyDrop⁻* C⅀ₖ (⊢TyIdRen⁻ C⅀ₖ) (injKndCtx Γₑ')) ⊢ℓ ,
    (⊢injTy⁻ $
      subst (λ x → injKndCtx x c⊢ₜ injTy tₑ ∶ LocKnd κₑ)
        (sym eq2) $
      ⊢regainTy⁻ $
      subst (λ x → (map LocKnd Γₑ' ++ Γ) c⊢ₜ regainTy x (injTy tₑ) ∶ LocKnd κₑ)
        (sym eq1)
        ⊢tₑ)

BinderFun : (Γ : ChorKndCtx) (ℓ : CTy) → Binder ⅀ₑₖ → Binder C⅀ₖ
BinderFun Γ ℓ (Γₑ' , Δₑ' , tₑ) =
  injKndCtx Γₑ' ,
  map (TypFun Γ ℓ Γₑ') Δₑ' ,
  TypFun Γ ℓ Γₑ' tₑ

⊢BinderFun : ∀{Γ ℓ Σ} →
             Γ c⊢ₜ ℓ ∶ *ₗ →
             wfBinder ⅀ₑₖ (projKndCtx Γ) Σ →
             wfBinder C⅀ₖ Γ (BinderFun Γ ℓ Σ)
⊢BinderFun {Γ} {ℓ} {Γₑ' , Δₑ' , κₑ , tₑ} ⊢ℓ (⊢Δₑ' , ⊢tₑ) =
  let eq1 : map isLocKnd (injKndCtx Γₑ' ++ Γ)
           ≡ replicate (length Γₑ') true ++ map isLocKnd Γ
      eq1 = 
        map isLocKnd (injKndCtx Γₑ' ++ Γ)
          ≡⟨ map-++-commute isLocKnd (injKndCtx Γₑ') Γ ⟩
        map isLocKnd (injKndCtx Γₑ') ++ map isLocKnd Γ
          ≡⟨ cong (_++ map isLocKnd Γ) (isLocKnd∘injKndCtx≡true Γₑ') ⟩
        replicate (length Γₑ') true ++ map isLocKnd Γ ∎
      eq2 : Γₑ' ++ projKndCtx Γ ≡ projKndCtx (injKndCtx Γₑ' ++ Γ)
      eq2 =
        Γₑ' ++ projKndCtx Γ
          ≡⟨ cong (_++ projKndCtx Γ) (sym $ proj∘injKndCtx≗id Γₑ') ⟩
        projKndCtx (injKndCtx Γₑ') ++ projKndCtx Γ
          ≡⟨ (sym $ projKndCtx-++ (injKndCtx Γₑ') Γ) ⟩
        projKndCtx (injKndCtx Γₑ' ++ Γ) ∎
  in
  map-AllElems
      (wfTyp ⅀ₑₖ (Γₑ' ++ projKndCtx Γ))
      (wfTyp C⅀ₖ (injKndCtx Γₑ' ++ Γ))
      (TypFun Γ ℓ Γₑ')
      (λ tₑ ⊢tₑ → ⊢TypFun ⊢ℓ ⊢tₑ)
      ⊢Δₑ' ,
  ⊢Local
    (subst (λ x → (injKndCtx Γₑ' ++ Γ) c⊢ₜ regainTy x (injTy tₑ) ∶ LocKnd κₑ)
      eq1
      (⊢regainTy (⊢injTy
        (subst (λ x → x e⊢ₜ tₑ ∶ κₑ)
          eq2
          ⊢tₑ))))
    (⊢renTy C⅀ₖ (⊢TyDrop* C⅀ₖ (⊢TyIdRen C⅀ₖ) (injKndCtx Γₑ')) ⊢ℓ)

⊢BinderFun⁻ : ∀{Γ ℓ Σ} →
             wfBinder C⅀ₖ Γ (BinderFun Γ ℓ Σ) →
             Γ c⊢ₜ ℓ ∶ *ₗ ×
             wfBinder ⅀ₑₖ (projKndCtx Γ) Σ
⊢BinderFun⁻ {Γ} {ℓ} {Γₑ' , Δₑ' , κₑ , tₑ} (⊢Δₑ' , ⊢tₑ) =
  let eq1 : map isLocKnd (injKndCtx Γₑ' ++ Γ)
           ≡ replicate (length Γₑ') true ++ map isLocKnd Γ
      eq1 = 
        map isLocKnd (injKndCtx Γₑ' ++ Γ)
          ≡⟨ map-++-commute isLocKnd (injKndCtx Γₑ') Γ ⟩
        map isLocKnd (injKndCtx Γₑ') ++ map isLocKnd Γ
          ≡⟨ cong (_++ map isLocKnd Γ) (isLocKnd∘injKndCtx≡true Γₑ') ⟩
        replicate (length Γₑ') true ++ map isLocKnd Γ ∎
      eq2 : Γₑ' ++ projKndCtx Γ ≡ projKndCtx (injKndCtx Γₑ' ++ Γ)
      eq2 =
        Γₑ' ++ projKndCtx Γ
          ≡⟨ cong (_++ projKndCtx Γ) (sym $ proj∘injKndCtx≗id Γₑ') ⟩
        projKndCtx (injKndCtx Γₑ') ++ projKndCtx Γ
          ≡⟨ (sym $ projKndCtx-++ (injKndCtx Γₑ') Γ) ⟩
        projKndCtx (injKndCtx Γₑ' ++ Γ) ∎
  in ⊢TypFun⁻ {Γ} {ℓ} {Γₑ'} {κₑ , tₑ} ⊢tₑ .fst ,
    (map-AllElems⁻
      (wfTyp ⅀ₑₖ (Γₑ' ++ projKndCtx Γ))
      (wfTyp C⅀ₖ (injKndCtx Γₑ' ++ Γ))
      (TypFun Γ ℓ Γₑ')
      (λ tₑ ⊢tₑ → ⊢TypFun⁻ {Γ} {ℓ} {Γₑ'} {tₑ} ⊢tₑ .snd)
      ⊢Δₑ' , 
    (subst (_e⊢ₜ tₑ ∶ κₑ)
      (sym eq2) $
    ⊢injTy⁻ $
    ⊢regainTy⁻ $
    subst
      (λ x → (map LocKnd Γₑ' ++ Γ)
             c⊢ₜ regainTy x (injTy tₑ)
             ∶ LocKnd κₑ)
    (sym eq1) $
    ⊢Local⁻ ⊢tₑ .fst))

{-
Choreographic term typing judgments

If
⊢ e1ₑ : t1ₑ
…
⊢ enₑ : tnₑ
--------------------
⊢ sₑ e1ₑ … enₑ : tₑ
holds in the local language, then
⊢ e1ₑ : ℓ.t1ₑ
…
⊢ enₑ : ℓ.tnₑ
---------------------
⊢ sₑ e1ₑ … enₑ : ℓ.tₑ

⊢ ℓ : *ₗ
⊢ e : ℓ.tₑ
-----------------
⊢ ℓ.e : tₑ @ ℓ

⊢ τ1, τ2 : *
x : τ1 ⊢ e : τ2
-------------------
⊢ λx:τ1.e : τ1 → τ2

⊢ τ : *
x : τ ⊢ e : τ
--------------
⊢ μx:τ.e : τ

⊢ τ1, τ2 : *
⊢ f : τ1 → τ2
⊢ e : τ1
-------------------
⊢ f e : τ2

x : κ ⊢ τ : *
x : κ ⊢ e : τ
-----------------
⊢ Λx:κ.e : ∀x:κ.τ

x : κ ⊢ τ : *
⊢ f : ∀x:κ.τ
⊢ t : κ
------------------
⊢ f [t] : τ[x ↦ t]

⊢ tₑ : *ₑ
⊢ ℓ1, ℓ2 : *ₗ
⊢ C : tₑ @ ℓ1
---------------------
⊢ ℓ1.C ⇝ ℓ2 : tₑ @ ℓ2

⊢ ℓ1, ℓ2 : *ₗ
⊢ τ : *
⊢ C : τ
--------------------
⊢ ℓ1[d] ⇝ ℓ2 ; C : τ

⊢ ℓ : *ₗ
⊢ τ : *
⊢ C1 : Boolₑ @ ℓ
⊢ C2, C3 : τ
---------------------------
⊢ if C1 then C2 else C3 : τ

⊢ ℓ : *ₗ
⊢ t : *ₑ
⊢ τ : *
⊢ C1 : t @ ℓ
x : ℓ.t ⊢ C2 : τ
-------------------------
⊢ let ℓ.x := C1 in C2 : τ

⊢ ℓ : *ₗ
⊢ ρ : *ₛ
⊢ τ : *
⊢ C1 : Typₑ @ ℓ
α : *ₑ ⊢ C2 : τ
--------------------------------------
ℓ.tell α : *ₑ := C1 to ρ in C2

⊢ ℓ : *ₗ
⊢ ρ : *ₛ
⊢ τ : *
⊢ C1 : Locₑ @ ℓ
α : *ₗ ⊢ C2 : τ
--------------------------------------
ℓ.tell α : *ₗ := C1 to ρ in C2
-}
ChorTmSig : (s : ChorTmSymb) (Γ : ChorKndCtx) (ts : TyVec C⅀ₖ) → Binders C⅀ₖ × Typ C⅀ₖ
ChorTmSig (LocalTmS sₑ) Γ ((ℓ , 0) ∷ ts) =
  let Σκtₑ : Binders ⅀ₑₖ × Typ ⅀ₑₖ
      Σκtₑ = TmSigₑ sₑ (projKndCtx Γ) (projTyVec (map isLocKnd Γ) ts)
  in map (BinderFun Γ ℓ) (Σκtₑ .fst) ,
     Bnd (Σκtₑ .snd .fst) ,
     Local (Σκtₑ .snd .fst) (regainTy (map isLocKnd Γ) (injTy (Σκtₑ .snd .snd))) ℓ
ChorTmSig DoneS Γ ((tₑ , 0) ∷ (ℓ , 0) ∷ []) =
  ([] , [] , Bnd *ₑ' , Local *ₑ' tₑ ℓ) ∷ [] ,
  * ,
  At tₑ ℓ
ChorTmSig LamS Γ ((τ1 , 0) ∷ (τ2 , 0) ∷ []) =
  ([] , (* , τ1) ∷ [] , * , τ2) ∷ [] ,
  * ,
  Fun τ1 τ2
ChorTmSig FixS Γ ((τ , 0) ∷ []) =
  ([] , (* , τ) ∷ [] , * , τ) ∷ [] ,
  * ,
  τ
ChorTmSig AppS Γ ((τ1 , 0) ∷ (τ2 , 0) ∷ []) =
  ([] , [] , * , Fun τ1 τ2) ∷ ([] , [] , * , τ1) ∷ [] ,
  * ,
  τ2
ChorTmSig (AbsS κ ∀κ) Γ ((τ , 1) ∷ []) =
  (κ ∷ [] , [] , * , τ) ∷ [] ,
  * ,
  All ∀κ τ
ChorTmSig (AppTyS κ ∀κ) Γ ((τ , 1) ∷ (T , 0) ∷ []) =
  ([] , [] , * , All ∀κ τ) ∷ [] ,
  * ,
  subTy C⅀ₖ (addTySub C⅀ₖ tyVar T) τ
ChorTmSig SendS Γ ((ℓ1 , 0) ∷ (ℓ2 , 0) ∷ (tₑ , 0) ∷ []) =
  ([] , [] , * , At tₑ ℓ1) ∷ [] ,
  * ,
  At tₑ ℓ2
ChorTmSig (SyncS d) Γ ((ℓ1 , 0) ∷ (ℓ2 , 0) ∷ (τ , 0) ∷ []) =
  ([] , [] , * , τ) ∷ [] ,
  * ,
  τ
ChorTmSig ITES Γ ((ℓ , 0) ∷ (τ , 0) ∷ []) =
  let Bool = renTy C⅀ₖ (Drop* id (length Γ)) (injTy (𝕃 .Boolₑ)) in
  ([] , [] , * , At Bool ℓ)
    ∷ ([] , [] , * , τ)
    ∷ ([] , [] , * , τ)
    ∷ [] ,
  * ,
  τ
ChorTmSig LocalLetS Γ ((ℓ , 0) ∷ (tₑ , 0) ∷ (τ , 0) ∷ []) =
  (([] , [] , * , At tₑ ℓ)
    ∷ ([] , (Bnd *ₑ' , Local *ₑ' tₑ ℓ) ∷ [] , * , τ)
    ∷ []) ,
  * ,
  τ
ChorTmSig TellTyS Γ ((ℓ , 0) ∷ (ρ , 0) ∷ (τ , 0) ∷ []) =
  let TyRep = renTy C⅀ₖ (Drop* id (length Γ)) (injTy (𝕃 .TyRepₑ)) in
  (([] , [] , * , At TyRep ℓ)
    ∷ (*ₑ ∷ [] , [] , * , renTy C⅀ₖ (Drop id) τ)
    ∷ []) ,
  * ,
  τ
ChorTmSig TellLocS Γ ((ℓ , 0) ∷ (ρ , 0) ∷ (τ , 0) ∷ []) =
  let Loc = renTy C⅀ₖ (Drop* id (length Γ)) (injTy (𝕃 .Locₑ)) in
  (([] , [] , * , At Loc ℓ)
    ∷ (*ₗ ∷ [] , [] , * , renTy C⅀ₖ (Drop id) τ)
    ∷ []) ,
  * ,
  τ
ChorTmSig _ _ _ = [] , * , tyVar zero

⊢ChorTmSig-fst : ∀{Γ ts} (s : ChorTmSymb) →
                  vecKinded C⅀ₖ Γ ts (ChorTmTySig s) →
                  wfBinders C⅀ₖ Γ (ChorTmSig s Γ ts .fst)
⊢ChorTmSig-fst {Γ} {(ℓ , 0) ∷ ts} (LocalTmS sₑ) (⊢ℓ ⊢ₜ∷ ⊢ts) =
  map-AllElems
    (wfBinder ⅀ₑₖ (projKndCtx Γ))
    (wfBinder C⅀ₖ Γ)
    (BinderFun Γ ℓ)
    (λ Σ → ⊢BinderFun ⊢ℓ)
    (𝕃 .⅀ₑ .⊢TmSig-fst sₑ (⊢projTyVec ⊢ts))
⊢ChorTmSig-fst DoneS (tₑ ⊢ₜ∷ ℓ ⊢ₜ∷ ⊢ₜ[]) =
  (tt , ⊢Local tₑ ℓ) ,
  tt
⊢ChorTmSig-fst LamS (τ1 ⊢ₜ∷ τ2 ⊢ₜ∷ ⊢ₜ[]) =
  ((τ1 , tt) , τ2) ,
  tt
⊢ChorTmSig-fst FixS (τ ⊢ₜ∷ ⊢ₜ[]) =
  ((τ , tt) , τ) ,
  tt
⊢ChorTmSig-fst AppS (τ1 ⊢ₜ∷ τ2 ⊢ₜ∷ ⊢ₜ[]) =
  (tt , ⊢Fun τ1 τ2) ,
  (tt , τ1) ,
  tt
⊢ChorTmSig-fst (AbsS κ ∀κ) (τ ⊢ₜ∷ ⊢ₜ[]) =
  (tt , τ) ,
  tt
⊢ChorTmSig-fst (AppTyS κ ∀κ) (τ ⊢ₜ∷ T ⊢ₜ∷ ⊢ₜ[]) =
  (tt , ⊢All ∀κ τ) ,
  tt
⊢ChorTmSig-fst SendS (ℓ1 ⊢ₜ∷ ℓ2 ⊢ₜ∷ tₑ ⊢ₜ∷ ⊢ₜ[]) =
  (tt , ⊢At tₑ ℓ1) ,
  tt
⊢ChorTmSig-fst (SyncS d) (ℓ1 ⊢ₜ∷ ℓ2 ⊢ₜ∷ τ ⊢ₜ∷ ⊢ₜ[]) =
  (tt , τ) ,
  tt
⊢ChorTmSig-fst {Γ} ITES (ℓ ⊢ₜ∷ τ ⊢ₜ∷ ⊢ₜ[]) =
  let Bool = renTy C⅀ₖ (Drop* id (length Γ)) (injTy (𝕃 .Boolₑ))
      ⊢ξ : TYREN C⅀ₖ (Drop* id (length Γ)) [] Γ
      ⊢ξ = subst (TYREN C⅀ₖ (Drop* id (length Γ)) [])
            (++-identityʳ Γ) $
            ⊢TyDrop* C⅀ₖ (⊢TyIdRen C⅀ₖ) Γ
      ⊢Bool : Γ c⊢ₜ Bool ∶ *ₑ
      ⊢Bool = ⊢renTy C⅀ₖ ⊢ξ (⊢injTy (𝕃 .⊢Boolₑ))
  in
  (tt , ⊢At ⊢Bool ℓ) ,
  (tt , τ) ,
  (tt , τ) ,
  tt
⊢ChorTmSig-fst LocalLetS (ℓ ⊢ₜ∷ tₑ ⊢ₜ∷ τ ⊢ₜ∷ ⊢ₜ[]) =
  (tt , ⊢At tₑ ℓ) ,
  ((⊢Local tₑ ℓ , tt) , τ) ,
  tt
⊢ChorTmSig-fst {Γ} TellTyS (ℓ ⊢ₜ∷ ρ ⊢ₜ∷ τ ⊢ₜ∷ ⊢ₜ[]) =
  let TyRep = renTy C⅀ₖ (Drop* id (length Γ)) (injTy (𝕃 .TyRepₑ))
      ⊢ξ : TYREN C⅀ₖ (Drop* id (length Γ)) [] Γ
      ⊢ξ = subst (TYREN C⅀ₖ (Drop* id (length Γ)) [])
            (++-identityʳ Γ) $
            ⊢TyDrop* C⅀ₖ (⊢TyIdRen C⅀ₖ) Γ
      ⊢TyRep : Γ c⊢ₜ TyRep ∶ *ₑ
      ⊢TyRep = ⊢renTy C⅀ₖ ⊢ξ (⊢injTy (𝕃 .⊢TyRepₑ))
  in
  (tt , ⊢At ⊢TyRep ℓ) ,
  (tt , ⊢renTy C⅀ₖ (⊢TyDrop C⅀ₖ (⊢TyIdRen C⅀ₖ)) τ) ,
  tt
⊢ChorTmSig-fst {Γ} TellLocS (ℓ ⊢ₜ∷ ρ ⊢ₜ∷ τ ⊢ₜ∷ ⊢ₜ[]) =
  let Loc = renTy C⅀ₖ (Drop* id (length Γ)) (injTy (𝕃 .Locₑ))
      ⊢ξ : TYREN C⅀ₖ (Drop* id (length Γ)) [] Γ
      ⊢ξ = subst (TYREN C⅀ₖ (Drop* id (length Γ)) [])
            (++-identityʳ Γ) $
            ⊢TyDrop* C⅀ₖ (⊢TyIdRen C⅀ₖ) Γ
      ⊢Loc : Γ c⊢ₜ Loc ∶ *ₑ
      ⊢Loc = ⊢renTy C⅀ₖ ⊢ξ (⊢injTy (𝕃 .⊢Locₑ))
  in
  (tt , ⊢At ⊢Loc ℓ) ,
  (tt , ⊢renTy C⅀ₖ (⊢TyDrop C⅀ₖ (⊢TyIdRen C⅀ₖ)) τ) ,
  tt

⊢ChorTmSig-snd : ∀{Γ ts} (s : ChorTmSymb) →
                vecKinded C⅀ₖ Γ ts (ChorTmTySig s) →
                wfTyp C⅀ₖ Γ (ChorTmSig s Γ ts .snd)
⊢ChorTmSig-snd (LocalTmS sₑ) (ℓ ⊢ₜ∷ ts) =
  ⊢Local (⊢regainTy (⊢injTy (𝕃 .⅀ₑ .⊢TmSig-snd sₑ (⊢projTyVec ts)))) ℓ
⊢ChorTmSig-snd DoneS (tₑ ⊢ₜ∷ ℓ ⊢ₜ∷ ⊢ₜ[]) = ⊢At tₑ ℓ
⊢ChorTmSig-snd LamS (τ1 ⊢ₜ∷ τ2 ⊢ₜ∷ ⊢ₜ[]) = ⊢Fun τ1 τ2
⊢ChorTmSig-snd FixS (τ ⊢ₜ∷ ⊢ₜ[]) = τ
⊢ChorTmSig-snd AppS (τ1 ⊢ₜ∷ τ2 ⊢ₜ∷ ⊢ₜ[]) = τ2
⊢ChorTmSig-snd (AbsS κ ∀κ) (τ ⊢ₜ∷ ⊢ₜ[]) = ⊢All ∀κ τ
⊢ChorTmSig-snd (AppTyS κ ∀κ) (τ ⊢ₜ∷ T ⊢ₜ∷ ⊢ₜ[]) =
  ⊢subTy C⅀ₖ (⊢▸ₜ C⅀ₖ (⊢TyIdSub C⅀ₖ) T) τ
⊢ChorTmSig-snd SendS (ℓ1 ⊢ₜ∷ ℓ2 ⊢ₜ∷ tₑ ⊢ₜ∷ ⊢ₜ[]) = ⊢At tₑ ℓ2
⊢ChorTmSig-snd (SyncS d) (ℓ1 ⊢ₜ∷ ℓ2 ⊢ₜ∷ τ ⊢ₜ∷ ⊢ₜ[]) = τ
⊢ChorTmSig-snd ITES (ℓ ⊢ₜ∷ τ ⊢ₜ∷ ⊢ₜ[]) = τ
⊢ChorTmSig-snd LocalLetS (ℓ ⊢ₜ∷ tₑ ⊢ₜ∷ τ ⊢ₜ∷ ⊢ₜ[]) = τ
⊢ChorTmSig-snd {Γ} TellTyS (ℓ ⊢ₜ∷ ρ ⊢ₜ∷ τ ⊢ₜ∷ ⊢ₜ[]) = τ
⊢ChorTmSig-snd {Γ} TellLocS (ℓ ⊢ₜ∷ ρ ⊢ₜ∷ τ ⊢ₜ∷ ⊢ₜ[]) = τ

sub-comm-ChorTmSig-fst-helper
  : ∀{κ} (Γ1 Γ2 : ChorKndCtx) σ t → [] e⊢ₜ t ∶ κ →
    renTy C⅀ₖ (Drop* id (length Γ2)) (injTy t) ≡
    subTy C⅀ₖ σ (renTy C⅀ₖ (Drop* id (length Γ1)) (injTy t))
sub-comm-ChorTmSig-fst-helper Γ1 Γ2 σ t ⊢t =
  renTy C⅀ₖ (Drop* id (length Γ2)) (injTy t)
    ≡⟨ ⊢renTyε C⅀ₖ (Drop* id (length Γ2)) (⊢injTy ⊢t) ⟩
  injTy t
    ≡⟨ (sym $ ⊢subTyε C⅀ₖ (σ c◦•ₜ Drop* id (length Γ1)) (⊢injTy ⊢t)) ⟩
  subTy C⅀ₖ (σ c◦•ₜ Drop* id (length Γ1)) (injTy t)
    ≡⟨ (sym $ subTy◦•ₜ C⅀ₖ σ (Drop* id (length Γ1)) (injTy t)) ⟩
  subTy C⅀ₖ σ (renTy C⅀ₖ (Drop* id (length Γ1)) (injTy t)) ∎

sub-comm-TypFun
  : ∀{Γ1 Γ2 Γₑ' tₑ σ ℓ} →
    TYSUB C⅀ₖ σ Γ1 Γ2 →
    Γ1 c⊢ₜ ℓ ∶ *ₗ →
    wfTyp ⅀ₑₖ (Γₑ' ++ projKndCtx Γ1) tₑ →
    TypFun Γ2 (subTy C⅀ₖ σ ℓ) Γₑ' (subTyp ⅀ₑₖ (TyKeepSub* ⅀ₑₖ (projTySub Γ1 Γ2 σ) (length Γₑ')) tₑ)
    ≡ subTyp C⅀ₖ (TyKeepSub* C⅀ₖ σ (length (map LocKnd Γₑ'))) (TypFun Γ1 ℓ Γₑ' tₑ)
sub-comm-TypFun {Γ1} {Γ2} {Γₑ'} {κₑ , tₑ} {σ} {ℓ} ⊢σ ⊢ℓ ⊢tₑ =
  let eq1 : Γₑ' ++ projKndCtx Γ1 ≡ projKndCtx (injKndCtx Γₑ' ++ Γ1)
      eq1 =
        Γₑ' ++ projKndCtx Γ1
          ≡⟨ (sym $ cong (_++ projKndCtx Γ1) $ proj∘injKndCtx≗id Γₑ') ⟩
        projKndCtx (injKndCtx Γₑ') ++ projKndCtx Γ1
          ≡⟨ (sym $ projKndCtx-++ (injKndCtx Γₑ') Γ1) ⟩
        projKndCtx (injKndCtx Γₑ' ++ Γ1) ∎
      eq2 : ∀ Γ → replicate (length Γₑ') true ++ map isLocKnd Γ ≡
            map isLocKnd (injKndCtx Γₑ' ++ Γ)
      eq2 Γ =
        replicate (length Γₑ') true ++ map isLocKnd Γ
          ≡⟨ (sym $ cong (_++ map isLocKnd Γ) $ isLocKnd∘injKndCtx≡true Γₑ') ⟩
        map isLocKnd (injKndCtx Γₑ') ++ map isLocKnd Γ
          ≡⟨ (sym $ map-++-commute isLocKnd (injKndCtx Γₑ') Γ) ⟩
        map isLocKnd (injKndCtx Γₑ' ++ Γ) ∎
  in
  cong (Bnd κₑ ,_) $
  cong₂ (λ x y → tyConstr (LocalS κₑ) ((x , 0) ∷ (y , 0) ∷ []))
    (regainTy (replicate (length Γₑ') true ++ map isLocKnd Γ2)
      (injTy (subTy ⅀ₑₖ (TyKeepSub* ⅀ₑₖ (projTySub Γ1 Γ2 σ) (length Γₑ')) tₑ))
      ≡⟨ (cong (λ x → regainTy (replicate (length Γₑ') true ++ map isLocKnd Γ2)
            (injTy (subTy ⅀ₑₖ (TyKeepSub* ⅀ₑₖ (projTySub Γ1 Γ2 σ) x) tₑ))) $
            sym $ length-map LocKnd Γₑ') ⟩
    regainTy (replicate (length Γₑ') true ++ map isLocKnd Γ2)
      (injTy (subTy ⅀ₑₖ (TyKeepSub* ⅀ₑₖ (projTySub Γ1 Γ2 σ) (length (injKndCtx Γₑ'))) tₑ))
      ≡⟨ (sym $ cong (λ x → regainTy (replicate (length Γₑ') true ++ map isLocKnd Γ2)
            (injTy x)) $
            ⊢subTy-≗TySub ⅀ₑₖ (Keep*-projTySub ⊢σ Γₑ') ⊢tₑ) ⟩
    regainTy (replicate (length Γₑ') true ++ map isLocKnd Γ2)
      (injTy (subTy ⅀ₑₖ
        (projTySub (injKndCtx Γₑ' ++ Γ1) (injKndCtx Γₑ' ++ Γ2)
          (TyKeepSub* C⅀ₖ σ (length (injKndCtx Γₑ'))))
        tₑ))
      ≡⟨ (cong (λ x → regainTy x
          (injTy (subTy ⅀ₑₖ
            (projTySub (injKndCtx Γₑ' ++ Γ1) (injKndCtx Γₑ' ++ Γ2)
              (TyKeepSub* C⅀ₖ σ (length (injKndCtx Γₑ'))))
            tₑ))) $ eq2 Γ2) ⟩
    regainTy (map isLocKnd (injKndCtx Γₑ' ++ Γ2))
      (injTy (subTy ⅀ₑₖ
        (projTySub (injKndCtx Γₑ' ++ Γ1) (injKndCtx Γₑ' ++ Γ2)
          (TyKeepSub* C⅀ₖ σ (length (injKndCtx Γₑ'))))
        tₑ))
      ≡⟨ regain∘inj∘projSub≗sub∘regain∘inj
            (⊢TyKeepSub* C⅀ₖ ⊢σ (injKndCtx Γₑ'))
            (subst (λ x → x e⊢ₜ tₑ ∶ κₑ) eq1 ⊢tₑ) ⟩
    subTy C⅀ₖ (TyKeepSub* C⅀ₖ σ (length (injKndCtx Γₑ')))
      (renTy C⅀ₖ
        (regainTyVar (map isLocKnd (injKndCtx Γₑ' ++ Γ1)))
        (injTy tₑ))
      ≡⟨ (sym $ cong (λ x → subTy C⅀ₖ (TyKeepSub* C⅀ₖ σ (length (injKndCtx Γₑ')))
          (renTy C⅀ₖ
            (regainTyVar x)
            (injTy tₑ))) $ eq2 Γ1) ⟩
    subTy C⅀ₖ (TyKeepSub* C⅀ₖ σ (length (injKndCtx Γₑ')))
      (renTy C⅀ₖ
        (regainTyVar (replicate (length Γₑ') true ++ map isLocKnd Γ1))
        (injTy tₑ)) ∎)
    (renTy C⅀ₖ (Drop* id (length (injKndCtx Γₑ'))) (subTy C⅀ₖ σ ℓ)
      ≡⟨ subTy•◦ₜ C⅀ₖ (Drop* id (length (injKndCtx Γₑ'))) σ ℓ ⟩
    subTy C⅀ₖ (Drop* id (length (injKndCtx Γₑ')) c•◦ₜ σ) ℓ
      ≡⟨ subTy-ext C⅀ₖ (Drop*-id•◦≗DropSub* C⅀ₖ σ (length (injKndCtx Γₑ'))) ℓ ⟩
    subTy C⅀ₖ (TyDropSub* C⅀ₖ σ (length (injKndCtx Γₑ'))) ℓ
      ≡⟨ (sym $ subTy-ext C⅀ₖ (Keep*◦•ₜDrop* C⅀ₖ σ id (length (injKndCtx Γₑ'))) ℓ) ⟩
    subTy C⅀ₖ
      (TyKeepSub* C⅀ₖ σ (length (injKndCtx Γₑ')) c◦•ₜ Drop* id (length (injKndCtx Γₑ')))
      ℓ
      ≡⟨ (sym $ subTy◦•ₜ C⅀ₖ (TyKeepSub* C⅀ₖ σ (length (map LocKnd Γₑ')))
            (Drop* id (length (injKndCtx Γₑ'))) ℓ) ⟩
    subTy C⅀ₖ (TyKeepSub* C⅀ₖ σ (length (map LocKnd Γₑ')))
      (renTy C⅀ₖ (Drop* id (length (injKndCtx Γₑ'))) ℓ) ∎)

sub-comm-BinderFun
  : ∀{Γ1 Γ2 σ ℓ Σ} →
    TYSUB C⅀ₖ σ Γ1 Γ2 →
    Γ1 c⊢ₜ ℓ ∶ *ₗ →
    wfBinder ⅀ₑₖ (projKndCtx Γ1) Σ →
    BinderFun Γ2 (subTy C⅀ₖ σ ℓ) (subBinder ⅀ₑₖ (projTySub Γ1 Γ2 σ) Σ) ≡
    subBinder C⅀ₖ σ (BinderFun Γ1 ℓ Σ)
sub-comm-BinderFun {Γ1} {Γ2} {σ} {ℓ} {Γₑ' , Δₑ' , κₑ , tₑ} ⊢σ ⊢ℓ (⊢Δₑ' , ⊢tₑ) =
  cong₂ (λ x y → map LocKnd Γₑ' , x , y)
    (map (TypFun Γ2 (subTy C⅀ₖ σ ℓ) Γₑ')
      (map (subTyp ⅀ₑₖ
        (TyKeepSub* ⅀ₑₖ (projTySub Γ1 Γ2 σ) (length Γₑ')))
        Δₑ')
      ≡⟨ (sym $ map-compose {g = TypFun Γ2 (subTy C⅀ₖ σ ℓ) Γₑ'}
          {subTyp ⅀ₑₖ (TyKeepSub* ⅀ₑₖ (projTySub Γ1 Γ2 σ) (length Γₑ'))}
          Δₑ') ⟩
    map (TypFun Γ2 (subTy C⅀ₖ σ ℓ) Γₑ'
        ∘ subTyp ⅀ₑₖ (TyKeepSub* ⅀ₑₖ (projTySub Γ1 Γ2 σ) (length Γₑ')))
      Δₑ'
      ≡⟨ ⊢Ctx-map-cong ⅀ₑₖ (sub-comm-TypFun ⊢σ ⊢ℓ) ⊢Δₑ' ⟩
    map (subTyp C⅀ₖ (TyKeepSub* C⅀ₖ σ (length (map LocKnd Γₑ'))) ∘ TypFun Γ1 ℓ Γₑ') Δₑ'
      ≡⟨ map-compose {g = subTyp C⅀ₖ (TyKeepSub* C⅀ₖ σ (length (map LocKnd Γₑ')))}
          {TypFun Γ1 ℓ Γₑ'}
          Δₑ' ⟩
    map (subTyp C⅀ₖ (TyKeepSub* C⅀ₖ σ (length (map LocKnd Γₑ'))))
      (map (TypFun Γ1 ℓ Γₑ') Δₑ') ∎)
    (sub-comm-TypFun ⊢σ ⊢ℓ ⊢tₑ)

sub-comm-ChorTmSig-fst : ∀{Γ1 Γ2 σ ts} (s : ChorTmSymb) →
                          TYSUB C⅀ₖ σ Γ1 Γ2 →
                          vecKinded C⅀ₖ Γ1 ts (ChorTmTySig s) →
                          ChorTmSig s Γ2 (subTyVec C⅀ₖ σ ts) .fst ≡
                          subBinders C⅀ₖ σ (ChorTmSig s Γ1 ts .fst)
sub-comm-ChorTmSig-fst {Γ1} {Γ2} {σ} {(ℓ , 0) ∷ ts} (LocalTmS sₑ) ⊢σ (⊢ℓ ⊢ₜ∷ ⊢ts) =
  map (BinderFun Γ2 (subTy C⅀ₖ σ ℓ))
    (TmSigₑ sₑ (projKndCtx Γ2) (projTyVec (map isLocKnd Γ2) (subTyVec C⅀ₖ σ ts)) .fst)
    ≡⟨ (cong (λ x → map (BinderFun Γ2 (subTy C⅀ₖ σ ℓ))
            (TmSigₑ sₑ (projKndCtx Γ2) x .fst)) $ 
        proj∘sub≗projSub∘projTyVec ⊢σ ⊢ts) ⟩
  map (BinderFun Γ2 (subTy C⅀ₖ σ ℓ))
    (TmSigₑ sₑ (projKndCtx Γ2)
      (subTyVec ⅀ₑₖ (projTySub Γ1 Γ2 σ) (projTyVec (map isLocKnd Γ1) ts)) .fst)
    ≡⟨ (cong (map (BinderFun Γ2 (subTy C⅀ₖ σ ℓ))) $
          sub-comm-TmSig-fst (𝕃 .⅀ₑ) sₑ (⊢projTySub ⊢σ) (⊢projTyVec ⊢ts)) ⟩
  map (BinderFun Γ2 (subTy C⅀ₖ σ ℓ))
    (map (subBinder ⅀ₑₖ (projTySub Γ1 Γ2 σ))
      (TmSigₑ sₑ (projKndCtx Γ1) (projTyVec (map isLocKnd Γ1) ts) .fst))
    ≡⟨ (sym $ map-compose {g = BinderFun Γ2 (subTy C⅀ₖ σ ℓ)} {subBinder ⅀ₑₖ (projTySub Γ1 Γ2 σ)} 
          (TmSigₑ sₑ (projKndCtx Γ1) (projTyVec (map isLocKnd Γ1) ts) .fst)) ⟩
  map (BinderFun Γ2 (subTy C⅀ₖ σ ℓ) ∘ subBinder ⅀ₑₖ (projTySub Γ1 Γ2 σ))
    (TmSigₑ sₑ (projKndCtx Γ1) (projTyVec (map isLocKnd Γ1) ts) .fst)
    ≡⟨ ⊢Binders-map-cong ⅀ₑₖ (sub-comm-BinderFun ⊢σ ⊢ℓ)
        (⊢TmSig-fst (𝕃 .⅀ₑ) sₑ (⊢projTyVec ⊢ts)) ⟩
  map (subBinder C⅀ₖ σ ∘ BinderFun Γ1 ℓ)
    (TmSigₑ sₑ (projKndCtx Γ1) (projTyVec (map isLocKnd Γ1) ts) .fst)
    ≡⟨ map-compose {g = subBinder C⅀ₖ σ} {BinderFun Γ1 ℓ}
        (TmSigₑ sₑ (projKndCtx Γ1) (projTyVec (map isLocKnd Γ1) ts) .fst) ⟩
  map (subBinder C⅀ₖ σ) (map (BinderFun Γ1 ℓ)
    (TmSigₑ sₑ (projKndCtx Γ1) (projTyVec (map isLocKnd Γ1) ts) .fst)) ∎
sub-comm-ChorTmSig-fst DoneS ⊢σ (tₑ ⊢ₜ∷ ℓ ⊢ₜ∷ ⊢ₜ[]) = refl
sub-comm-ChorTmSig-fst LamS ⊢σ(τ1 ⊢ₜ∷ τ2 ⊢ₜ∷ ⊢ₜ[]) = refl
sub-comm-ChorTmSig-fst FixS ⊢σ (τ ⊢ₜ∷ ⊢ₜ[]) = refl
sub-comm-ChorTmSig-fst AppS ⊢σ (τ1 ⊢ₜ∷ τ2 ⊢ₜ∷ ⊢ₜ[]) = refl
sub-comm-ChorTmSig-fst (AbsS κ ∀κ) ⊢σ (τ ⊢ₜ∷ ⊢ₜ[]) = refl
sub-comm-ChorTmSig-fst (AppTyS κ ∀κ) ⊢σ (τ ⊢ₜ∷ T ⊢ₜ∷ ⊢ₜ[]) = refl
sub-comm-ChorTmSig-fst SendS ⊢σ (ℓ1 ⊢ₜ∷ ℓ2 ⊢ₜ∷ tₑ ⊢ₜ∷ ⊢ₜ[]) = refl
sub-comm-ChorTmSig-fst (SyncS d) ⊢σ (ℓ1 ⊢ₜ∷ ℓ2 ⊢ₜ∷ τ ⊢ₜ∷ ⊢ₜ[]) = refl
sub-comm-ChorTmSig-fst {Γ1} {Γ2} {σ} {(ℓ , 0) ∷ (τ , 0) ∷ []}
  ITES ⊢σ (⊢ℓ ⊢ₜ∷ ⊢τ ⊢ₜ∷ ⊢ₜ[]) =
  cong (λ x → 
    ([] , [] , * , tyConstr AtS ((x , 0) ∷ (subTy C⅀ₖ σ ℓ , 0) ∷ []))
    ∷ ([] , [] , * , subTy C⅀ₖ σ τ)
    ∷ ([] , [] , * , subTy C⅀ₖ σ τ)
    ∷ []) $ sub-comm-ChorTmSig-fst-helper Γ1 Γ2 σ (𝕃 .Boolₑ) (𝕃 .⊢Boolₑ)
sub-comm-ChorTmSig-fst LocalLetS ⊢σ (ℓ ⊢ₜ∷ tₑ ⊢ₜ∷ τ ⊢ₜ∷ ⊢ₜ[]) = refl
sub-comm-ChorTmSig-fst {Γ1} {Γ2} {σ} {(ℓ , 0) ∷ (ρ , 0) ∷ (τ , 0) ∷ []}
  TellTyS ⊢σ (⊢ℓ ⊢ₜ∷ ⊢ρ ⊢ₜ∷ ⊢τ ⊢ₜ∷ ⊢ₜ[]) =
    cong₂ (λ x y →
      ([] , [] , * , tyConstr AtS ((x , 0) ∷ (subTy C⅀ₖ σ ℓ , 0) ∷ []))
      ∷ (*ₑ ∷ [] , [] , * , y)
      ∷ [])
    (sub-comm-ChorTmSig-fst-helper Γ1 Γ2 σ (𝕃 .TyRepₑ) (𝕃 .⊢TyRepₑ)) $
    renTy C⅀ₖ (Drop id) (subTy C⅀ₖ σ τ)
      ≡⟨ subTy•◦ₜ C⅀ₖ (Drop id) σ τ ⟩
    subTy C⅀ₖ (TyDropSub C⅀ₖ σ) τ
      ≡⟨ (sym $ subTy◦•ₜ C⅀ₖ(TyKeepSub C⅀ₖ σ) (Drop id) τ) ⟩
    subTy C⅀ₖ (TyKeepSub C⅀ₖ σ) (renTy C⅀ₖ (Drop id) τ) ∎
sub-comm-ChorTmSig-fst {Γ1} {Γ2} {σ} {(ℓ , 0) ∷ (ρ , 0) ∷ (τ , 0) ∷ []}
  TellLocS ⊢σ (⊢ℓ ⊢ₜ∷ ⊢ρ ⊢ₜ∷ ⊢τ ⊢ₜ∷ ⊢ₜ[]) =
    cong₂ (λ x y →
      ([] , [] , * , tyConstr AtS ((x , 0) ∷ (subTy C⅀ₖ σ ℓ , 0) ∷ []))
      ∷ (*ₗ ∷ [] , [] , * , y)
      ∷ [])
    (sub-comm-ChorTmSig-fst-helper Γ1 Γ2 σ (𝕃 .Locₑ) (𝕃 .⊢Locₑ)) $
    renTy C⅀ₖ (Drop id) (subTy C⅀ₖ σ τ)
      ≡⟨ subTy•◦ₜ C⅀ₖ (Drop id) σ τ ⟩
    subTy C⅀ₖ (TyDropSub C⅀ₖ σ) τ
      ≡⟨ (sym $ subTy◦•ₜ C⅀ₖ(TyKeepSub C⅀ₖ σ) (Drop id) τ) ⟩
    subTy C⅀ₖ (TyKeepSub C⅀ₖ σ) (renTy C⅀ₖ (Drop id) τ) ∎

sub-comm-ChorTmSig-snd : ∀{Γ1 Γ2 σ ts} (s : ChorTmSymb) →
                          TYSUB C⅀ₖ σ Γ1 Γ2 →
                          vecKinded C⅀ₖ Γ1 ts (ChorTmTySig s) →
                          ChorTmSig s Γ2 (subTyVec C⅀ₖ σ ts) .snd ≡
                          subTyp C⅀ₖ σ (ChorTmSig s Γ1 ts .snd)
sub-comm-ChorTmSig-snd {Γ1} {Γ2} {σ} {(ℓ , 0) ∷ ts} (LocalTmS sₑ) ⊢σ (⊢ℓ ⊢ₜ∷ ⊢ts) =
  let eq : TmSigₑ sₑ (projKndCtx Γ2) (projTyVec (map isLocKnd Γ2) (subTyVec C⅀ₖ σ ts)) .snd
            ≡ subTyp ⅀ₑₖ (projTySub Γ1 Γ2 σ)
                (TmSig (𝕃 .⅀ₑ) sₑ (projKndCtx Γ1) (projTyVec (map isLocKnd Γ1) ts) .snd)
      eq =
        TmSigₑ sₑ (projKndCtx Γ2)
          (projTyVec (map isLocKnd Γ2) (subTyVec C⅀ₖ σ ts)) .snd
          ≡⟨ (cong (λ x → TmSigₑ sₑ (projKndCtx Γ2) x .snd) $
                proj∘sub≗projSub∘projTyVec ⊢σ ⊢ts) ⟩
        TmSigₑ sₑ (projKndCtx Γ2)
          (subTyVec ⅀ₑₖ (projTySub Γ1 Γ2 σ) (projTyVec (map isLocKnd Γ1) ts)) .snd
          ≡⟨ 𝕃 .⅀ₑ .sub-comm-TmSig-snd sₑ (⊢projTySub ⊢σ) (⊢projTyVec ⊢ts) ⟩
        subTyp ⅀ₑₖ (projTySub Γ1 Γ2 σ)
          (TmSig (𝕃 .⅀ₑ) sₑ (projKndCtx Γ1) (projTyVec (map isLocKnd Γ1) ts) .snd) ∎
  in cong₂ _,_
    (cong Bnd $ cong fst eq)
    (cong₂ tyConstr
      (cong LocalS $ cong fst eq)
      (cong (λ x → (x , 0) ∷ (subTy C⅀ₖ σ ℓ , 0) ∷ []) $
        regainTy (map isLocKnd Γ2)
          (injTy (TmSigₑ sₑ (projKndCtx Γ2)
            (projTyVec (map isLocKnd Γ2) (subTyVec C⅀ₖ σ ts)) .snd .snd))
          ≡⟨ (cong (λ x → regainTy (map isLocKnd Γ2) (injTy x)) $ cong snd eq) ⟩
        regainTy (map isLocKnd Γ2)
          (injTy (subTy ⅀ₑₖ (projTySub Γ1 Γ2 σ)
            (TmSig (𝕃 .⅀ₑ) sₑ (projKndCtx Γ1) (projTyVec (map isLocKnd Γ1) ts) .snd .snd)))
          ≡⟨ regain∘inj∘projSub≗sub∘regain∘inj ⊢σ
              (⊢TmSig-snd (𝕃 .⅀ₑ) sₑ (⊢projTyVec ⊢ts)) ⟩
        subTy C⅀ₖ σ (regainTy (map isLocKnd Γ1)
          (injTy (TmSigₑ sₑ (projKndCtx Γ1) (projTyVec (map isLocKnd Γ1) ts) .snd .snd))) ∎))
sub-comm-ChorTmSig-snd DoneS ⊢σ (tₑ ⊢ₜ∷ ℓ ⊢ₜ∷ ⊢ₜ[]) = refl
sub-comm-ChorTmSig-snd LamS ⊢σ(τ1 ⊢ₜ∷ τ2 ⊢ₜ∷ ⊢ₜ[]) = refl
sub-comm-ChorTmSig-snd FixS ⊢σ (τ ⊢ₜ∷ ⊢ₜ[]) = refl
sub-comm-ChorTmSig-snd AppS ⊢σ (τ1 ⊢ₜ∷ τ2 ⊢ₜ∷ ⊢ₜ[]) = refl
sub-comm-ChorTmSig-snd (AbsS κ ∀κ) ⊢σ (τ ⊢ₜ∷ ⊢ₜ[]) = refl
sub-comm-ChorTmSig-snd {Γ1} {Γ2} {σ} {(τ , 1) ∷ (T , 0) ∷ []} (AppTyS κ ∀κ) ⊢σ (⊢τ ⊢ₜ∷ ⊢T ⊢ₜ∷ ⊢ₜ[]) =
  cong (* ,_) $
  subTy C⅀ₖ (addTySub C⅀ₖ tyVar (subTy C⅀ₖ σ T)) (subTy C⅀ₖ (TyKeepSub C⅀ₖ σ) τ)
    ≡⟨ subTy◦ₜ C⅀ₖ (addTySub C⅀ₖ tyVar (subTy C⅀ₖ σ T)) (TyKeepSub C⅀ₖ σ) τ ⟩
  subTy C⅀ₖ (_◦ₜ_ C⅀ₖ (addTySub C⅀ₖ tyVar (subTy C⅀ₖ σ T)) (TyKeepSub C⅀ₖ σ)) τ
    ≡⟨ subTy-ext C⅀ₖ (▸ₜ-◦ₜ-Keep C⅀ₖ tyVar (subTy C⅀ₖ σ T) σ) τ ⟩
  subTy C⅀ₖ (addTySub C⅀ₖ (_◦ₜ_ C⅀ₖ tyVar σ) (subTy C⅀ₖ σ T)) τ
    ≡⟨ subTy-ext C⅀ₖ (▸ₜ-ext C⅀ₖ (Id◦ₜ C⅀ₖ σ) refl) τ ⟩
  subTy C⅀ₖ (addTySub C⅀ₖ σ (subTy C⅀ₖ σ T)) τ
    ≡⟨ subTy-ext C⅀ₖ (sym ∘ ◦ₜ-▸ₜ C⅀ₖ σ tyVar T) τ ⟩
  subTy C⅀ₖ (_◦ₜ_ C⅀ₖ σ (addTySub C⅀ₖ tyVar T)) τ
    ≡⟨ (sym $ subTy◦ₜ C⅀ₖ σ (addTySub C⅀ₖ tyVar T) τ) ⟩
  subTy C⅀ₖ σ (subTy C⅀ₖ (addTySub C⅀ₖ tyVar T) τ) ∎
sub-comm-ChorTmSig-snd SendS ⊢σ (ℓ1 ⊢ₜ∷ ℓ2 ⊢ₜ∷ tₑ ⊢ₜ∷ ⊢ₜ[]) = refl
sub-comm-ChorTmSig-snd (SyncS d) ⊢σ (ℓ1 ⊢ₜ∷ ℓ2 ⊢ₜ∷ τ ⊢ₜ∷ ⊢ₜ[]) = refl
sub-comm-ChorTmSig-snd ITES ⊢σ (⊢ℓ ⊢ₜ∷ ⊢τ ⊢ₜ∷ ⊢ₜ[]) = refl
sub-comm-ChorTmSig-snd LocalLetS ⊢σ (ℓ ⊢ₜ∷ tₑ ⊢ₜ∷ τ ⊢ₜ∷ ⊢ₜ[]) = refl
sub-comm-ChorTmSig-snd {Γ} TellTyS ⊢σ (ℓ ⊢ₜ∷ ρ ⊢ₜ∷ τ ⊢ₜ∷ ⊢ₜ[]) = refl
sub-comm-ChorTmSig-snd {Γ} TellLocS ⊢σ (ℓ ⊢ₜ∷ ρ ⊢ₜ∷ τ ⊢ₜ∷ ⊢ₜ[]) = refl

C⅀ : TypeSignature
⅀ₖ C⅀ = C⅀ₖ
TmSymb C⅀ = ChorTmSymb
TmTySig C⅀ = ChorTmTySig
TmSig C⅀ = ChorTmSig
⊢TmSig-fst C⅀ = ⊢ChorTmSig-fst
⊢TmSig-snd C⅀ = ⊢ChorTmSig-snd
sub-comm-TmSig-snd C⅀ = sub-comm-ChorTmSig-snd
sub-comm-TmSig-fst C⅀ = sub-comm-ChorTmSig-fst

CTm : Set
CTm = Tm C⅀

CTmVec : Set
CTmVec = TmVec C⅀

CTyp : Set
CTyp = Typ C⅀ₖ

Tmₑ : Set
Tmₑ = Tm (𝕃 .⅀ₑ)

TmVecₑ : Set
TmVecₑ = TmVec (𝕃 .⅀ₑ)

Typₑ : Set
Typₑ = Typ ⅀ₑₖ

_⨾_c⊢var_∶_ : ChorKndCtx → ChorCtx → ℕ → CTyp → Set
_⨾_c⊢var_∶_ = varTyped C⅀

_⨾_c⊢_∶_ : ChorKndCtx → ChorCtx → CTm → CTyp → Set
_⨾_c⊢_∶_ = typed C⅀

_⨾_c⊢vec_∶_ : ChorKndCtx → ChorCtx → CTmVec → Binders C⅀ₖ → Set
_⨾_c⊢vec_∶_ = vecTyped C⅀

_c⊢ctx_ : ChorKndCtx → ChorCtx → Set
_c⊢ctx_ = wfCtx C⅀ₖ

_⨾_e⊢var_∶_ : KndCtxₑ → Ctxₑ → ℕ → Typₑ → Set
_⨾_e⊢var_∶_ = varTyped (𝕃 .⅀ₑ)

_e⊢ctx_ : KndCtxₑ → Ctxₑ → Set
_e⊢ctx_ = wfCtx ⅀ₑₖ

_⨾_e⊢_∶_ : KndCtxₑ → Ctxₑ → Tmₑ → Typₑ → Set
_⨾_e⊢_∶_ = typed (𝕃 .⅀ₑ)

_⨾_e⊢vec_∶_ : KndCtxₑ → Ctxₑ → TmVecₑ → Binders ⅀ₑₖ → Set
_⨾_e⊢vec_∶_ = vecTyped (𝕃 .⅀ₑ)

⊢renId : ∀{Γ Δ C t} →
          Γ ⨾ Δ c⊢ C ∶ t →
          Γ ⨾ renCtx C⅀ₖ id Δ c⊢ C ∶ t
⊢renId {Γ} {Δ} {C} {t} ⊢C =
  subst (λ x → Γ ⨾ x c⊢ C ∶ t)
    (sym $ renCtxId C⅀ₖ Δ)
    ⊢C

⊢renId⁻ : ∀{Γ Δ C t} →
          Γ ⨾ renCtx C⅀ₖ id Δ c⊢ C ∶ t →
          Γ ⨾ Δ c⊢ C ∶ t
⊢renId⁻ {Γ} {Δ} {C} {t} ⊢C =
  subst (λ x → Γ ⨾ x c⊢ C ∶ t)
    (renCtxId C⅀ₖ Δ)
    ⊢C

-- Aliases for each term constructor
EmbLocalTm : (sₑ : TmSymbₑ) (ℓ : CTy) (ts : CTyVec) (es : CTmVec) → CTm
EmbLocalTm sₑ ℓ ts es = constr (LocalTmS sₑ) ((ℓ , 0) ∷ ts) es

Done : (tₑ : CTy) (ℓ : CTy) (e : CTm) → CTm
Done tₑ ℓ e = constr DoneS ((tₑ , 0) ∷ (ℓ , 0) ∷ []) ((e , 0 , 0) ∷ [])

⊢Done : ∀{Γ Δ tₑ ℓ e} →
         Γ c⊢ₜ ℓ ∶ *ₗ →
         Γ ⨾ Δ c⊢ e ∶ (Bnd *ₑ' , Local *ₑ' tₑ ℓ) →
         Γ ⨾ Δ c⊢ Done tₑ ℓ e ∶ (* , At tₑ ℓ)
⊢Done ⊢ℓ ⊢e =
  ⊢constr DoneS
    (⊢Local⁻ (⊢⇒⊢typ C⅀ ⊢e) .fst ⊢ₜ∷ ⊢ℓ ⊢ₜ∷ ⊢ₜ[])
    (⊢renId ⊢e ⊢∷ ⊢[] (⊢⇒⊢ctx C⅀ ⊢e))

Lam : (τ1 τ2 : CTy) (C : CTm) → CTm
Lam τ1 τ2 C = constr LamS ((τ1 , 0) ∷ (τ2 , 0) ∷ []) ((C , 0 , 1) ∷ [])

⊢Lam : ∀{Γ Δ τ1 τ2 C} →
        Γ ⨾ ((* , τ1) ∷ Δ) c⊢ C ∶ (* , τ2) →
        Γ ⨾ Δ c⊢ Lam τ1 τ2 C ∶ (* , Fun τ1 τ2)
⊢Lam {Γ} {Δ} {τ1} {τ2} {C} ⊢C =
  let ⊢C' : Γ ⨾ (* , τ1) ∷ renCtx C⅀ₖ id Δ c⊢ C ∶ (* , τ2)
      ⊢C' = subst (λ x → Γ ⨾ (* , τ1) ∷ x c⊢ C ∶ (* , τ2))
              (sym $ renCtxId C⅀ₖ Δ)
              ⊢C
  in ⊢constr LamS
    (⊢⇒⊢ctx C⅀ ⊢C .fst ⊢ₜ∷ ⊢⇒⊢typ C⅀ ⊢C ⊢ₜ∷ ⊢ₜ[])
    (⊢C' ⊢∷ ⊢[] (⊢⇒⊢ctx C⅀ ⊢C .snd))

⊢Lam⁻ : ∀{Γ Δ τ1 τ2 κ τ C} →
        Γ ⨾ Δ c⊢ Lam τ1 τ2 C ∶ (κ , τ) →
        κ ≡ * ×
        τ ≡ Fun τ1 τ2 ×
        Γ ⨾ ((* , τ1) ∷ Δ) c⊢ C ∶ (* , τ2)
⊢Lam⁻ {Γ} {Δ} {τ1} {τ2} {C = C} (⊢constr LamS (⊢τ1 ⊢ₜ∷ ⊢τ2 ⊢ₜ∷ ⊢ₜ[]) (⊢C ⊢∷ ⊢[] ⊢Δ)) =
  refl , refl , subst (λ x → Γ ⨾ (* , τ1) ∷ x c⊢ C ∶ (* , τ2)) (renCtxId C⅀ₖ Δ) ⊢C

Fix : (τ : CTy) (C : CTm) → CTm
Fix τ C = constr FixS ((τ , 0) ∷ []) ((C , 0 , 1) ∷ [])

⊢Fix : ∀{Γ Δ τ C} →
        Γ ⨾ ((* , τ) ∷ Δ) c⊢ C ∶ (* , τ) →
        Γ ⨾ Δ c⊢ Fix τ C ∶ (* , τ)
⊢Fix {Γ} {Δ} {τ} {C} ⊢C =
  let ⊢C' : Γ ⨾ (* , τ) ∷ renCtx C⅀ₖ id Δ c⊢ C ∶ (* , τ)
      ⊢C' = subst (λ x → Γ ⨾ (* , τ) ∷ x c⊢ C ∶ (* , τ))
              (sym $ renCtxId C⅀ₖ Δ)
              ⊢C
  in ⊢constr FixS
    (⊢⇒⊢typ C⅀ ⊢C ⊢ₜ∷ ⊢ₜ[])
    (⊢C' ⊢∷ ⊢[] (⊢⇒⊢ctx C⅀ ⊢C .snd))

App : (τ1 τ2 : CTy) (F : CTm) (C : CTm) → CTm
App τ1 τ2 F C = constr AppS ((τ1 , 0) ∷ (τ2 , 0) ∷ []) ((F , 0 , 0) ∷ (C , 0 , 0) ∷ [])

⊢App : ∀{Γ Δ τ1 τ2 F C} →
        Γ ⨾ Δ c⊢ F ∶ (* , Fun τ1 τ2) →
        Γ ⨾ Δ c⊢ C ∶ (* , τ1) →
        Γ ⨾ Δ c⊢ App τ1 τ2 F C ∶ (* , τ2)
⊢App ⊢F ⊢C =
  ⊢constr AppS
    ((fst $ ⊢Fun⁻ $ ⊢⇒⊢typ C⅀ ⊢F) ⊢ₜ∷ (snd $ ⊢Fun⁻ $ ⊢⇒⊢typ C⅀ ⊢F) ⊢ₜ∷ ⊢ₜ[])
    (⊢renId ⊢F ⊢∷ ⊢renId ⊢C ⊢∷ ⊢[] (⊢⇒⊢ctx C⅀ ⊢F))

⊢App⁻ : ∀{Γ Δ τ1 κ τ2 τ2' F C} →
        Γ ⨾ Δ c⊢ App τ1 τ2' F C ∶ (κ , τ2) →
        κ ≡ * ×
        τ2' ≡ τ2 ×
        Γ ⨾ Δ c⊢ F ∶ (* , Fun τ1 τ2) ×
        Γ ⨾ Δ c⊢ C ∶ (* , τ1)
⊢App⁻ (⊢constr AppS (⊢τ1 ⊢ₜ∷ ⊢τ2 ⊢ₜ∷ ⊢ₜ[]) (⊢F ⊢∷ ⊢C ⊢∷ ⊢[] ⊢Δ)) =
  refl , refl , ⊢renId⁻ ⊢F , ⊢renId⁻ ⊢C

Abs : ∀{κ} (∀κ : canAbstract κ) (τ : CTy) (C : CTm) → CTm
Abs {κ} ∀κ τ C = constr (AbsS κ ∀κ) ((τ , 1) ∷ []) ((C , 1 , 0) ∷ [])

⊢Abs : ∀{Γ Δ C κ τ} (∀κ : canAbstract κ) →
       Γ c⊢ctx Δ →
       (κ ∷ Γ) ⨾ renCtx C⅀ₖ (Drop id) Δ c⊢ C ∶ (* , τ) →
       Γ ⨾ Δ c⊢ Abs ∀κ τ C ∶ (* , All ∀κ τ)
⊢Abs {κ = κ} ∀κ ⊢Δ ⊢C =
  ⊢constr (AbsS κ ∀κ) (⊢⇒⊢typ C⅀ ⊢C ⊢ₜ∷ ⊢ₜ[]) (⊢C ⊢∷ ⊢[] ⊢Δ)

AppTy : ∀{κ} (∀κ : canAbstract κ) (C : CTm) (τ : CTy) (T : CTy) → CTm
AppTy {κ} ∀κ C τ T =
  constr (AppTyS κ ∀κ) ((τ , 1) ∷ (T , 0) ∷ []) ((C , 0 , 0) ∷ [])

⊢AppTy : ∀{Γ Δ κ C τ T} (∀κ : canAbstract κ) →
         Γ ⨾ Δ c⊢ C ∶ (* , All ∀κ τ) →
         Γ c⊢ₜ T ∶ κ →
         Γ ⨾ Δ c⊢ AppTy ∀κ C τ T ∶ (* , subTy C⅀ₖ (addTySub C⅀ₖ tyVar T) τ)
⊢AppTy {Γ} {Δ} {κ} {C} {τ} {T} ∀κ ⊢C ⊢T =
  ⊢constr (AppTyS κ ∀κ)
    ((⊢All⁻ $ ⊢⇒⊢typ C⅀ ⊢C) ⊢ₜ∷ ⊢T ⊢ₜ∷ ⊢ₜ[])
    (⊢renId ⊢C ⊢∷ ⊢[] (⊢⇒⊢ctx C⅀ ⊢C))

Send : (ℓ1 : CTy) (C : CTm) (tₑ : CTy) (ℓ2 : CTy) → CTm
Send ℓ1 C tₑ ℓ2 =
  constr SendS
    ((ℓ1 , 0) ∷ (ℓ2 , 0) ∷ (tₑ , 0) ∷ [])
    ((C , 0 , 0) ∷ [])

⊢Send : ∀{Γ Δ ℓ1 C tₑ ℓ2} →
        Γ ⨾ Δ c⊢ C ∶ (* , At tₑ ℓ1) →
        Γ c⊢ₜ ℓ2 ∶ *ₗ →
        Γ ⨾ Δ c⊢ Send ℓ1 C tₑ ℓ2 ∶ (* , At tₑ ℓ2)
⊢Send ⊢C ⊢ℓ2 =
  ⊢constr SendS
    ((snd $ ⊢At⁻ $ ⊢⇒⊢typ C⅀ ⊢C) ⊢ₜ∷ ⊢ℓ2 ⊢ₜ∷ (fst $ ⊢At⁻ $ ⊢⇒⊢typ C⅀ ⊢C) ⊢ₜ∷ ⊢ₜ[])
    (⊢renId ⊢C ⊢∷ ⊢[] (⊢⇒⊢ctx C⅀ ⊢C))

Sync : (ℓ1 : CTy) (d : Bool) (ℓ2 : CTy) (C : CTm) (τ : CTy) → CTm
Sync ℓ1 d ℓ2 C τ =
  constr (SyncS d)
    ((ℓ1 , 0) ∷ (ℓ2 , 0) ∷ (τ , 0) ∷ [])
    ((C , 0 , 0) ∷ [])

⊢Sync : ∀{Γ Δ d ℓ1 ℓ2 C τ} →
        Γ c⊢ₜ ℓ1 ∶ *ₗ →
        Γ c⊢ₜ ℓ2 ∶ *ₗ →
        Γ ⨾ Δ c⊢ C ∶ (* , τ) →
        Γ ⨾ Δ c⊢ Sync ℓ1 d ℓ2 C τ ∶ (* , τ)
⊢Sync {d = d} ⊢ℓ1 ⊢ℓ2 ⊢C =
  ⊢constr (SyncS d)
    (⊢ℓ1 ⊢ₜ∷ ⊢ℓ2 ⊢ₜ∷ ⊢⇒⊢typ C⅀ ⊢C ⊢ₜ∷ ⊢ₜ[])
    (⊢renId ⊢C ⊢∷ ⊢[] (⊢⇒⊢ctx C⅀ ⊢C))

ITE : (ℓ : CTy) (C1 C2 C3 : CTm) (τ : CTy) → CTm
ITE ℓ C1 C2 C3 τ = 
  constr ITES
    ((ℓ , 0) ∷ (τ , 0) ∷ [])
    ((C1 , 0 , 0) ∷ (C2 , 0 , 0) ∷ (C3 , 0 , 0) ∷ [])

⊢ITE : ∀{Γ Δ ℓ C1 C2 C3 τ} →
       Γ ⨾ Δ c⊢ C1 ∶ (* , At (renTy C⅀ₖ (Drop* id (length Γ)) $ injTy (𝕃 .Boolₑ)) ℓ) →
       Γ ⨾ Δ c⊢ C2 ∶ (* , τ) →
       Γ ⨾ Δ c⊢ C3 ∶ (* , τ) →
       Γ ⨾ Δ c⊢ ITE ℓ C1 C2 C3 τ ∶ (* , τ)
⊢ITE ⊢C1 ⊢C2 ⊢C3 =
  ⊢constr ITES
    ((snd $ ⊢At⁻ $ ⊢⇒⊢typ C⅀ ⊢C1) ⊢ₜ∷ ⊢⇒⊢typ C⅀ ⊢C2 ⊢ₜ∷ ⊢ₜ[])
    (⊢renId ⊢C1 ⊢∷ ⊢renId ⊢C2 ⊢∷ ⊢renId ⊢C3 ⊢∷ ⊢[] (⊢⇒⊢ctx C⅀ ⊢C1))

LocalLet : (ℓ : CTy) (C1 : CTm) (tₑ : CTy) (C2 : CTm) (τ : CTy)  → CTm
LocalLet ℓ C1 tₑ C2 τ = 
  constr LocalLetS
    ((ℓ , 0) ∷ (tₑ , 0) ∷ (τ , 0) ∷ [])
    ((C1 , 0 , 0) ∷ (C2 , 0 , 1) ∷ [])

⊢LocalLet : ∀{Γ Δ ℓ tₑ τ C1 C2} →
            Γ ⨾ Δ c⊢ C1 ∶ (* , At tₑ ℓ) →
            Γ ⨾ ((Bnd *ₑ' , Local *ₑ' tₑ ℓ)) ∷ Δ c⊢ C2 ∶ (* , τ) →
            Γ ⨾ Δ c⊢ LocalLet ℓ C1 tₑ C2 τ ∶ (* , τ)
⊢LocalLet {Γ} {Δ} {ℓ} {tₑ} {τ} {C1} {C2} ⊢C1 ⊢C2 =
  let ⊢C2' : Γ ⨾ (Bnd *ₑ' , Local *ₑ' tₑ ℓ) ∷ renCtx C⅀ₖ id Δ c⊢ C2 ∶ (* , τ)
      ⊢C2' = subst (λ x → Γ ⨾ (Bnd *ₑ' , Local *ₑ' tₑ ℓ) ∷ x c⊢ C2 ∶ (* , τ))
              (sym $ renCtxId C⅀ₖ Δ)
              ⊢C2
  in ⊢constr LocalLetS
    ((snd $ ⊢At⁻ $ ⊢⇒⊢typ C⅀ ⊢C1) ⊢ₜ∷ ((fst $ ⊢At⁻ $ ⊢⇒⊢typ C⅀ ⊢C1) ⊢ₜ∷ ⊢⇒⊢typ C⅀ ⊢C2 ⊢ₜ∷ ⊢ₜ[]))
    (⊢renId ⊢C1 ⊢∷ ⊢C2' ⊢∷ ⊢[] (⊢⇒⊢ctx C⅀ ⊢C1))

TellTy : (ℓ : CTy) (C1 : CTm) (ρ : CTy) (C2 : CTm) (τ : CTy) → CTm
TellTy ℓ C1 ρ C2 τ =
  constr TellTyS
    ((ℓ , 0) ∷ (ρ , 0) ∷ (τ , 0) ∷ [])
    ((C1 , 0 , 0) ∷ (C2 , 1 , 0) ∷ [])

⊢TellTy : ∀{Γ Δ ℓ ρ τ C1 C2} →
          Γ ⨾ Δ c⊢ C1 ∶ (* , At (renTy C⅀ₖ (Drop* id (length Γ)) (injTy (𝕃 .TyRepₑ))) ℓ) →
          Γ c⊢ₜ ρ ∶ *ₛ →
          Γ c⊢ₜ τ ∶ * →
          (*ₑ ∷ Γ) ⨾ renCtx C⅀ₖ (Drop id) Δ c⊢ C2 ∶ (* , renTy C⅀ₖ (Drop id) τ) →
          Γ ⨾ Δ c⊢ TellTy ℓ C1 ρ C2 τ ∶ (* , τ)
⊢TellTy {Γ} {Δ} {ℓ} {ρ} {τ} {C1} {C2} ⊢C1 ⊢ρ ⊢τ ⊢C2 =
  ⊢constr TellTyS
    ((snd $ ⊢At⁻ $ ⊢⇒⊢typ C⅀ ⊢C1) ⊢ₜ∷ ⊢ρ ⊢ₜ∷ ⊢τ ⊢ₜ∷ ⊢ₜ[])
    (⊢renId ⊢C1 ⊢∷ ⊢C2 ⊢∷ ⊢[] (⊢⇒⊢ctx C⅀ ⊢C1))

TellLoc : (ℓ : CTy) (C1 : CTm) (ρ : CTy) (C2 : CTm) (τ : CTy) → CTm
TellLoc ℓ C1 ρ C2 τ =
  constr TellLocS
    ((ℓ , 0) ∷ (ρ , 0) ∷ (τ , 0) ∷ [])
    ((C1 , 0 , 0) ∷ (C2 , 1 , 0) ∷ [])

⊢TellLoc : ∀{Γ Δ ℓ ρ τ C1 C2} →
          Γ ⨾ Δ c⊢ C1 ∶ (* , At (renTy C⅀ₖ (Drop* id (length Γ)) (injTy (𝕃 .Locₑ))) ℓ) →
          Γ c⊢ₜ ρ ∶ *ₛ →
          Γ c⊢ₜ τ ∶ * →
          (*ₗ ∷ Γ) ⨾ renCtx C⅀ₖ (Drop id) Δ c⊢ C2 ∶ (* , renTy C⅀ₖ (Drop id) τ) →
          Γ ⨾ Δ c⊢ TellLoc ℓ C1 ρ C2 τ ∶ (* , τ)
⊢TellLoc {Γ} {Δ} {ℓ} {ρ} {τ} {C1} {C2} ⊢C1 ⊢ρ ⊢τ ⊢C2 =
  ⊢constr TellLocS
    ((snd $ ⊢At⁻ $ ⊢⇒⊢typ C⅀ ⊢C1) ⊢ₜ∷ ⊢ρ ⊢ₜ∷ ⊢τ ⊢ₜ∷ ⊢ₜ[])
    (⊢renId ⊢C1 ⊢∷ ⊢C2 ⊢∷ ⊢[] (⊢⇒⊢ctx C⅀ ⊢C1))
 