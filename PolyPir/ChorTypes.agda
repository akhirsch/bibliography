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
-- open import TypeMorphism
open import PolyPir.LocalLang

module PolyPir.ChorTypes
  -- Location values
  (Loc : Set)
  -- Locations should have decidable equality
  (≡-dec-Loc : DecidableEquality Loc)

  -- Local language
  (𝕃 : LocalLang Loc)
  where

⅀ₑₖ      = 𝕃 .⅀ₑ .⅀ₖ
Kndₑ     = ⅀ₑₖ .Knd
*ₑ'      = 𝕃 .TyKnd
KndCtxₑ  = List Kndₑ
TySymbₑ  = ⅀ₑₖ .TySymb
TySigₑ   = ⅀ₑₖ .TySig

_e⊢ₜvar_∶_ : List Kndₑ → ℕ → Kndₑ → Set
_e⊢ₜvar_∶_ = varKinded ⅀ₑₖ

_e⊢ₜ_∶_ : List Kndₑ → Ty ⅀ₑₖ → Kndₑ → Set
_e⊢ₜ_∶_ = kinded ⅀ₑₖ

_e⊢ₜvec_∶_ : List Kndₑ → TyVec ⅀ₑₖ → List (KndCtxₑ × Kndₑ) → Set
_e⊢ₜvec_∶_ = vecKinded ⅀ₑₖ

-------------------------
-- CHOREOGRAPHIC KINDS --
-------------------------

{-
Choreographic kind syntax

κ ::= κₑ | ?.κₑ | * | *ₗ | *ₛ
-}
data ChorKnd : Set where
  -- Embedding of local kinds
  LocKnd : (κₑ : Kndₑ) → ChorKnd
  -- Kind of locally bound types
  Bnd : (κₑ : Kndₑ) → ChorKnd
  -- Kind of choreographic types
  * : ChorKnd
  -- Kind of locations
  *ₗ : ChorKnd
  -- Kind of sets of locations
  *ₛ : ChorKnd

*ₑ = LocKnd *ₑ'

ChorKndCtx = List ChorKnd

-- Whether we are allowed to abstract over a given kind
canAbstract : ChorKnd → Set
canAbstract (LocKnd κₑ) = ⊤
canAbstract (Bnd κₑ) = ⊥
canAbstract * = ⊤
canAbstract *ₗ = ⊤
canAbstract *ₛ = ⊤

canAbstract-isProp : (κ : ChorKnd) → isProp (canAbstract κ)
canAbstract-isProp (LocKnd κₑ) = ⊤-isProp
canAbstract-isProp (Bnd κₑ) = ⊥-isProp
canAbstract-isProp * = ⊤-isProp
canAbstract-isProp *ₗ = ⊤-isProp
canAbstract-isProp *ₛ = ⊤-isProp

-- Basic properties
LocKnd-inj : Injective _≡_ _≡_ LocKnd
LocKnd-inj refl = refl

LocKndΣ : List Kndₑ × Kndₑ → List ChorKnd × ChorKnd
LocKndΣ (Δₑ , κₑ) = map LocKnd Δₑ , LocKnd κₑ

LocKndΣ-inj : Injective _≡_ _≡_ LocKndΣ
LocKndΣ-inj {Δ1 , κ1} {Δ2 , κ2} p =
  cong₂ _,_
    (map-injective LocKnd-inj (,-injective p .fst))
    (LocKnd-inj (,-injective p .snd))

{-
Context projection

Projects a choreographic kinding context to a local kinding context
by filtering all non-local kinds.

proj [] = []
proj (κₑ ∷ Γ) = κₑ ∷ proj Γ
proj (κ ∷ Γ) = proj Γ
-}
projKndCtx : ChorKndCtx → KndCtxₑ
projKndCtx [] = []
projKndCtx (LocKnd κₑ ∷ Γ) = κₑ ∷ projKndCtx Γ
projKndCtx (Bnd κₑ ∷ Γ) = projKndCtx Γ
projKndCtx (* ∷ Γ) = projKndCtx Γ
projKndCtx (*ₗ ∷ Γ) = projKndCtx Γ
projKndCtx (*ₛ ∷ Γ) = projKndCtx Γ

-- Projecting distributes over concatenation
projKndCtx-++ : (Γ1 Γ2 : ChorKndCtx) →
                projKndCtx (Γ1 ++ Γ2) ≡ (projKndCtx Γ1) ++ (projKndCtx Γ2)
projKndCtx-++ [] Γ2 = refl
projKndCtx-++ (LocKnd κₑ ∷ Γ1) Γ2 = cong (κₑ ∷_) (projKndCtx-++ Γ1 Γ2)
projKndCtx-++ (Bnd κₑ ∷ Γ1) Γ2 = projKndCtx-++ Γ1 Γ2
projKndCtx-++ (* ∷ Γ1) Γ2 = projKndCtx-++ Γ1 Γ2
projKndCtx-++ (*ₗ ∷ Γ1) Γ2 = projKndCtx-++ Γ1 Γ2
projKndCtx-++ (*ₛ ∷ Γ1) Γ2 = projKndCtx-++ Γ1 Γ2

{-
Context injection

Injects a local kinding context to a choreographic kinding context.
Essentially just the identity but needed for bookkeeping.

inj [] = []
inj (κₑ ∷ Γ) = κₑ ∷ inj Γ
-}
injKndCtx : KndCtxₑ → ChorKndCtx
injKndCtx = map LocKnd

-- Injecting distributes over concatenation
injKndCtx-++ : (Γ1 Γ2 : KndCtxₑ) → injKndCtx (Γ1 ++ Γ2) ≡ (injKndCtx Γ1) ++ (injKndCtx Γ2)
injKndCtx-++ Γ1 Γ2 = map-++-commute LocKnd Γ1 Γ2

-- Projecting after injecting a kinding context has no effect
proj∘injKndCtx≗id : projKndCtx ∘ injKndCtx ≗ id
proj∘injKndCtx≗id [] = refl
proj∘injKndCtx≗id (κₑ ∷ Γₑ) = cong (κₑ ∷_) (proj∘injKndCtx≗id Γₑ)

-- Determine if a given kind is from the local language
isLocKnd : ChorKnd → Bool
isLocKnd (LocKnd κₑ) = true
isLocKnd _ = false

-- An injected context only contains local kinds
isLocKnd∘injKndCtx≡true : (Γₑ : KndCtxₑ) →
                          map isLocKnd (injKndCtx Γₑ) ≡
                          replicate (length Γₑ) true
isLocKnd∘injKndCtx≡true Γₑ =
  map isLocKnd (injKndCtx Γₑ)
    ≡⟨ (sym $ map-compose {g = isLocKnd} {LocKnd} Γₑ) ⟩
  map (λ _ → true) Γₑ
    ≡⟨ map-const true Γₑ ⟩
  replicate (length Γₑ) true ∎

-------------------------
-- CHOREOGRAPHIC TYPES --
-------------------------

{-
Choreographic type syntax

T, τ, ℓ, ρ ::= α | tₑ | ℓ.tₑ | tₑ @ ℓ | τ1 → τ2 | ∀α:κ.τ
             | L | ∅ | {ℓ} | ρ1 ∪ ρ2
-}
data ChorTySymb : Set where 
  -- Embedding of local type constructors
  EmbLocalTyS : (sₑ : TySymbₑ) → ChorTySymb
  
  -- Type of locally-bound values
  LocalS : (κₑ : Kndₑ) → ChorTySymb
  -- Type of located values
  AtS : ChorTySymb
  -- Choreographic function type
  FunS : ChorTySymb
  -- Kind quantification
  AllS : (κ : ChorKnd) (∀κ : canAbstract κ) → ChorTySymb

  -- Literal locations
  LitLocS : (L : Loc) → ChorTySymb
  -- Empty location set
  EmpS : ChorTySymb
  -- Singleton location set
  SngS : ChorTySymb
  -- UnionS of location sets
  UnionS : ChorTySymb

{-
Choreographic type kinding judgments

If it holds in the local language, then
⊢ t1ₑ : κ1ₑ
…
⊢ tnₑ : κnₑ
-------------------
⊢ sₑ t1ₑ … tnₑ : κₑ

⊢ tₑ : κₑ
⊢ ℓ : *ₗ
-------------
⊢ ℓ.tₑ : ?.κₑ

⊢ tₑ : *ₑ
⊢ ℓ : *ₗ
------------
⊢ tₑ @ ℓ : *

⊢ τ1 : *
⊢ τ2 : *
-------------
⊢ τ1 → τ2 : *

α : κ ⊢ τ : *
-------------
⊢ ∀α:κ.τ : *

L ∈ ℒ
--------
⊢ L : *ₗ

--------
⊢ ∅ : *ₛ

⊢ ℓ : *ₗ
----------
⊢ {ℓ} : *ₛ

⊢ ρ1 : *ₛ
⊢ ρ2 : *ₛ
--------------
⊢ ρ1 ∪ ρ2 : *ₛ
-}
ChorTySig : ChorTySymb → List (List ChorKnd × ChorKnd) × ChorKnd
ChorTySig (EmbLocalTyS sₑ) =
  map LocKndΣ (TySigₑ sₑ .fst) ,
  LocKnd (TySigₑ sₑ .snd)
ChorTySig (LocalS κₑ) =
  ([] , LocKnd κₑ) ∷ ([] , *ₗ) ∷ [] , 
  Bnd κₑ
ChorTySig AtS =
  ([] , *ₑ) ∷ ([] , *ₗ) ∷ [] , 
  *
ChorTySig FunS =
  ([] , *) ∷ ([] , *) ∷ [] , 
  *
ChorTySig (AllS κ ∀κ) =
  (κ ∷ [] , *) ∷ [] ,
  *
ChorTySig (LitLocS L) = [] , *ₗ
ChorTySig EmpS = [] , *ₛ
ChorTySig SngS =
  ([] , *ₗ) ∷ [] , 
  *ₛ
ChorTySig UnionS =
  ([] , *ₛ) ∷ ([] , *ₛ) ∷ [] , 
  *ₛ

C⅀ₖ : KindSignature
Knd    C⅀ₖ = ChorKnd
TySymb C⅀ₖ = ChorTySymb
TySig  C⅀ₖ = ChorTySig

CTy : Set
CTy = Ty C⅀ₖ

CTyVec : Set
CTyVec = TyVec C⅀ₖ

_c⊢ₜvar_∶_ : List ChorKnd → ℕ → ChorKnd → Set
_c⊢ₜvar_∶_ = varKinded C⅀ₖ

_c⊢ₜ_∶_ : List ChorKnd → CTy → ChorKnd → Set
_c⊢ₜ_∶_ = kinded C⅀ₖ

_c⊢ₜvec_∶_ : List ChorKnd → CTyVec → List (ChorKndCtx × ChorKnd) → Set
_c⊢ₜvec_∶_ = vecKinded C⅀ₖ

-- Aliases for each type constructor
EmbLocalTy : (sₑ : TySymbₑ) (ts : CTyVec) → CTy
EmbLocalTy sₑ ts = tyConstr (EmbLocalTyS sₑ) ts

⊢EmbLocalTy : ∀{Γ ts} (sₑ : TySymbₑ) →
           Γ c⊢ₜvec ts ∶ map LocKndΣ (TySigₑ sₑ .fst) →
           Γ c⊢ₜ EmbLocalTy sₑ ts ∶ LocKnd (TySigₑ sₑ .snd)
⊢EmbLocalTy sₑ ⊢ts = ⊢ₜtyConstr (EmbLocalTyS sₑ) ⊢ts           

Local : (κₑ : Kndₑ) (tₑ : CTy) (ℓ : CTy) → CTy
Local κₑ tₑ ℓ = tyConstr (LocalS κₑ) ((tₑ , 0) ∷ (ℓ , 0) ∷ [])

⊢Local : ∀{Γ κₑ tₑ ℓ} →
      Γ c⊢ₜ tₑ ∶ LocKnd κₑ →
      Γ c⊢ₜ ℓ ∶ *ₗ →
      Γ c⊢ₜ Local κₑ tₑ ℓ ∶ Bnd κₑ
⊢Local {κₑ = κₑ} ⊢tₑ ⊢ℓ = ⊢ₜtyConstr (LocalS κₑ) (⊢tₑ ⊢ₜ∷ ⊢ℓ ⊢ₜ∷ ⊢ₜ[])

At : (tₑ : CTy) (ℓ : CTy) → CTy
At tₑ ℓ = tyConstr AtS ((tₑ , 0) ∷ (ℓ , 0) ∷ [])

⊢At : ∀{Γ tₑ ℓ} →
      Γ c⊢ₜ tₑ ∶ *ₑ →
      Γ c⊢ₜ ℓ ∶ *ₗ →
      Γ c⊢ₜ At tₑ ℓ ∶ *
⊢At ⊢tₑ ⊢ℓ = ⊢ₜtyConstr AtS (⊢tₑ ⊢ₜ∷ ⊢ℓ ⊢ₜ∷ ⊢ₜ[])

Fun : (τ1 τ2 : CTy) → CTy
Fun τ1 τ2 = tyConstr FunS ((τ1 , 0) ∷ (τ2 , 0) ∷ [])

⊢Fun : ∀{Γ τ1 τ2} →
        Γ c⊢ₜ τ1 ∶ * →
        Γ c⊢ₜ τ2 ∶ * →
        Γ c⊢ₜ Fun τ1 τ2 ∶ *
⊢Fun ⊢τ1 ⊢τ2 = ⊢ₜtyConstr FunS (⊢τ1 ⊢ₜ∷ ⊢τ2 ⊢ₜ∷ ⊢ₜ[])

All : ∀{κ} (∀κ : canAbstract κ) (τ : CTy) → CTy
All {κ} ∀κ τ = tyConstr (AllS κ ∀κ) ((τ , 1) ∷ [])

⊢All : ∀{Γ κ τ} →
      (∀κ : canAbstract κ) →
      (κ ∷ Γ) c⊢ₜ τ ∶ * →
      Γ c⊢ₜ All ∀κ τ ∶ *
⊢All {κ = κ} ∀κ ⊢τ =
  ⊢ₜtyConstr (AllS κ ∀κ) (⊢τ ⊢ₜ∷ ⊢ₜ[])

LitLoc : (L : Loc) → CTy
LitLoc L = tyConstr (LitLocS L) []

⊢LitLoc : ∀{Γ} (L : Loc) → Γ c⊢ₜ LitLoc L ∶ *ₗ
⊢LitLoc L = ⊢ₜtyConstr (LitLocS L) ⊢ₜ[]

Emp : CTy
Emp = tyConstr EmpS []

⊢Emp : ∀{Γ} → Γ c⊢ₜ Emp ∶ *ₛ
⊢Emp = ⊢ₜtyConstr EmpS ⊢ₜ[]

Sng : (ℓ : CTy) → CTy
Sng ℓ = tyConstr SngS ((ℓ , 0) ∷ [])

⊢Sng : ∀{Γ ℓ} →
       Γ c⊢ₜ ℓ ∶ *ₗ →
       Γ c⊢ₜ Sng ℓ ∶ *ₛ
⊢Sng ⊢ℓ = ⊢ₜtyConstr SngS (⊢ℓ ⊢ₜ∷ ⊢ₜ[])

Union : (ρ1 ρ2 : CTy) → CTy
Union ρ1 ρ2 = tyConstr UnionS ((ρ1 , 0) ∷ (ρ2 , 0) ∷ [])

⊢Union : ∀{Γ ρ1 ρ2} →
        Γ c⊢ₜ ρ1 ∶ *ₛ →
        Γ c⊢ₜ ρ2 ∶ *ₛ →
        Γ c⊢ₜ Union ρ1 ρ2 ∶ *ₛ
⊢Union ⊢ρ1 ⊢ρ2 = ⊢ₜtyConstr UnionS (⊢ρ1 ⊢ₜ∷ ⊢ρ2 ⊢ₜ∷ ⊢ₜ[])

---------------------
-- TYPE PROJECTION --
---------------------

{-
Type projection

If a choreographic type t is well-kinded with kind κₑ
Γ ⊢ t ∶ κₑ
then there is a corresponding local type
proj Γ ⊢ proj t : κₑ
in the projected context
-}
projTyVar : (Γ : List Bool) → Ren
projTyVar [] x = x
projTyVar (true ∷ Γ) = Keep (projTyVar Γ)
projTyVar (false ∷ Γ) zero = zero
projTyVar (false ∷ Γ) (suc x) = projTyVar Γ x

⊢projTyVar : ∀{Γ κₑ x} →
             Γ c⊢ₜvar x ∶ LocKnd κₑ →
             projKndCtx Γ e⊢ₜvar projTyVar (map isLocKnd Γ) x ∶ κₑ
⊢projTyVar ⊢ₜ0 = ⊢ₜ0
⊢projTyVar {LocKnd κₑ ∷ Γ} (⊢ₜS ⊢x) = ⊢ₜS (⊢projTyVar ⊢x)
⊢projTyVar {Bnd κₑ ∷ Γ} (⊢ₜS ⊢x) = ⊢projTyVar ⊢x
⊢projTyVar {* ∷ Γ} (⊢ₜS ⊢x) = ⊢projTyVar ⊢x
⊢projTyVar {*ₗ ∷ Γ} (⊢ₜS ⊢x) = ⊢projTyVar ⊢x
⊢projTyVar {*ₛ ∷ Γ} (⊢ₜS ⊢x) = ⊢projTyVar ⊢x

projTy : (Γ : List Bool) → CTy → Ty ⅀ₑₖ
projTyVec : (Γ : List Bool) → CTyVec → TyVec ⅀ₑₖ

projTy Γ (tyVar x) = tyVar (projTyVar Γ x)
projTy Γ (tyConstr (EmbLocalTyS sₑ) es) =
  tyConstr sₑ (projTyVec Γ es)
projTy Γ _ = tyVar zero

projTyVec Γ [] = []
projTyVec Γ ((e , k) ∷ es) =
  (projTy (replicate k true ++ Γ) e , k) ∷ projTyVec Γ es

⊢projTy : ∀{Γ κₑ t} →
            Γ c⊢ₜ t ∶ LocKnd κₑ →
            projKndCtx Γ e⊢ₜ projTy (map isLocKnd Γ) t ∶ κₑ
⊢projTyVec : ∀{Γ Σₑ ts} →
            Γ c⊢ₜvec ts ∶ map LocKndΣ Σₑ →
            projKndCtx Γ e⊢ₜvec projTyVec (map isLocKnd Γ) ts ∶ Σₑ

⊢projTy {t = tyVar x} (⊢ₜvar ⊢x) = ⊢ₜvar (⊢projTyVar ⊢x)
⊢projTy {t = tyConstr (EmbLocalTyS sₑ) es} (⊢ₜtyConstr .(EmbLocalTyS sₑ) ⊢ts) =
  ⊢ₜtyConstr sₑ (⊢projTyVec ⊢ts)

⊢projTyVec {Σₑ = []} {[]} ⊢ₜ[] = ⊢ₜ[]
⊢projTyVec {Γ} {(Γₑ' , κₑ) ∷ Σₑ} {(e , .(length (map LocKnd Γₑ'))) ∷ ts} (⊢t ⊢ₜ∷ ⊢ts) =
  ⊢ₜ∷' ⅀ₑₖ
    (⊢projTy ⊢t)
    (⊢projTyVec ⊢ts)
    (projKndCtx-++ (injKndCtx Γₑ') Γ
      ∙ cong (_++ projKndCtx Γ) (proj∘injKndCtx≗id Γₑ'))
    (length-map LocKnd Γₑ')
    (cong (flip projTy e) $
      map-++-commute isLocKnd (injKndCtx Γₑ') Γ
      ∙ cong (_++ map isLocKnd Γ)
        (sym (map-compose {g = isLocKnd} {LocKnd} Γₑ')
          ∙ map-const true Γₑ'
          ∙ cong (flip replicate true)
            (sym $ length-map LocKnd Γₑ')))

--------------------
-- TYPE INJECTION --
--------------------

{-
Type injection

If a local type t is well-kinded with
kind κₑ in a local context Γₑ
Γₑ ⊢ t ∶ κₑ
then there is a corresponding choreographic type
inj Γₑ ⊢ inj t : κₑ
in the injected context
-}
injTy : Ty ⅀ₑₖ → CTy
injTyVec : TyVec ⅀ₑₖ → CTyVec

injTy (tyVar x) = tyVar x
injTy (tyConstr sₑ ts) =
  tyConstr (EmbLocalTyS sₑ) (injTyVec ts)

injTyVec [] = []
injTyVec ((t , k) ∷ ts) =
  (injTy t , k) ∷ injTyVec ts

⊢injTyVar : ∀{Γₑ κₑ x} →
            Γₑ e⊢ₜvar x ∶ κₑ →
            injKndCtx Γₑ c⊢ₜvar x ∶ LocKnd κₑ
⊢injTyVar ⊢ₜ0 = ⊢ₜ0
⊢injTyVar (⊢ₜS ⊢x) = ⊢ₜS (⊢injTyVar ⊢x)

⊢injTy : ∀{Γₑ κₑ t} →
         Γₑ e⊢ₜ t ∶ κₑ →
         injKndCtx Γₑ c⊢ₜ injTy t ∶ LocKnd κₑ
⊢injTyVec : ∀{Γₑ Σₑ ts} →
            Γₑ e⊢ₜvec ts ∶ Σₑ →
            injKndCtx Γₑ c⊢ₜvec injTyVec ts ∶ map LocKndΣ Σₑ

⊢injTy (⊢ₜvar ⊢x) = ⊢ₜvar (⊢injTyVar ⊢x)
⊢injTy (⊢ₜtyConstr sₑ ⊢ts) =
  ⊢ₜtyConstr (EmbLocalTyS sₑ) (⊢injTyVec ⊢ts)

⊢injTyVec ⊢ₜ[] = ⊢ₜ[]
⊢injTyVec {Γₑ} (_⊢ₜ∷_ {Δ = Δ} ⊢t ⊢ts) =
  ⊢ₜ∷' C⅀ₖ
  (⊢injTy ⊢t)
  (⊢injTyVec ⊢ts)
  (injKndCtx-++ Δ Γₑ)
  (sym $ length-map LocKnd Δ)
  refl

--------------------
-- TYPE REGAINING --
--------------------

{-
There is a canonical renaming from a projected and
then injected kind context back to itself.
We need to match up the index of variables in
the projected context with their index in
the original context.

Γ      = (x0 : *), (x1 : *ₑ), (x2 : *), (x3 : *ₗ), (x4 : *ₑ)
proj Γ =           (x0 : *ₑ),                      (x1 : *ₑ)

regain : proj Γ → Γ
regain = [x0 ↦ x1, x1 ↦ x4]
-}
regainTyVar : (Γ : List Bool) → Ren
regainTyVar [] = id
regainTyVar (true ∷ Γ) = Keep (regainTyVar Γ)
regainTyVar (false ∷ Γ) = Drop (regainTyVar Γ)

⊢regainTyVar : {Γ : ChorKndCtx} →
               TYREN C⅀ₖ (regainTyVar (map isLocKnd Γ))
                (injKndCtx (projKndCtx Γ))
                Γ
⊢regainTyVar {[]} = ⊢TyIdRen C⅀ₖ
⊢regainTyVar {LocKnd κₑ ∷ Γ} = ⊢TyKeep C⅀ₖ ⊢regainTyVar
⊢regainTyVar {Bnd κₑ ∷ Γ} = ⊢TyDrop C⅀ₖ ⊢regainTyVar
⊢regainTyVar {* ∷ Γ} = ⊢TyDrop C⅀ₖ ⊢regainTyVar
⊢regainTyVar {*ₗ ∷ Γ} = ⊢TyDrop C⅀ₖ ⊢regainTyVar
⊢regainTyVar {*ₛ ∷ Γ} = ⊢TyDrop C⅀ₖ ⊢regainTyVar

regainTyVar-++ : (Γ : List Bool) (n : ℕ) →
                  regainTyVar (replicate n true ++ Γ)
                  ≗ Keep* (regainTyVar Γ) n
regainTyVar-++ Γ zero = ≗-refl
regainTyVar-++ Γ (suc n) = Keep-ext (regainTyVar-++ Γ n)

regainTyVar-true≗id : (n : ℕ) → regainTyVar (replicate n true) ≗ id
regainTyVar-true≗id zero = ≗-refl
regainTyVar-true≗id (suc n) x =
  Keep-ext (regainTyVar-true≗id n) x ∙ Keep-id x

regainTyVar∘injKndCtx≗id : (Γₑ : KndCtx ⅀ₑₖ) →
                           regainTyVar (map isLocKnd (injKndCtx Γₑ)) ≗ id
regainTyVar∘injKndCtx≗id Γₑ x =
  regainTyVar (map isLocKnd (injKndCtx Γₑ)) x
    ≡⟨ (cong (flip regainTyVar x) $ isLocKnd∘injKndCtx≡true Γₑ) ⟩
  regainTyVar (replicate (length Γₑ) true) x
    ≡⟨ regainTyVar-true≗id (length Γₑ) x ⟩
  x ∎

regainTy : (Γ : List Bool) → CTy → CTy
regainTy Γ = renTy C⅀ₖ (regainTyVar Γ)

⊢regainTy : ∀{Γ κ t} →
           injKndCtx (projKndCtx Γ) c⊢ₜ t ∶ κ →
           Γ c⊢ₜ regainTy (map isLocKnd Γ) t ∶ κ
⊢regainTy ⊢t = ⊢renTy C⅀ₖ ⊢regainTyVar ⊢t

regainTyVec : (Γ : List Bool) → CTyVec → CTyVec
regainTyVec Γ = renTyVec C⅀ₖ (regainTyVar Γ)

⊢regainTyVec : ∀{Γ Σ ts} →
              injKndCtx (projKndCtx Γ) c⊢ₜvec ts ∶ Σ →
              Γ c⊢ₜvec regainTyVec (map isLocKnd Γ) ts ∶ Σ
⊢regainTyVec ⊢ts = ⊢renTyVec C⅀ₖ ⊢regainTyVar ⊢ts

-- Project a renaming
projTyRen : (Γ1 Γ2 : ChorKndCtx) → Ren → Ren
projTyRen Γ1 Γ2 ξ = projTyVar (map isLocKnd Γ2) ∘ ξ ∘ regainTyVar (map isLocKnd Γ1)

⊢projTyRen : ∀{Γ1 Γ2 ξ} →
             TYREN C⅀ₖ ξ Γ1 Γ2 →
             TYREN ⅀ₑₖ
              (projTyRen Γ1 Γ2 ξ)
              (projKndCtx Γ1)
              (projKndCtx Γ2)
⊢projTyRen {Γ1} {Γ2} ⊢ξ = ⊢projTyVar ∘ ⊢ξ ∘ ⊢regainTyVar ∘ ⊢injTyVar

projTyRenId : (Γ : ChorKndCtx) → projTyRen Γ Γ id ≗ id
projTyRenId [] x = refl
projTyRenId (LocKnd κₑ ∷ Γ) zero = refl
projTyRenId (LocKnd κₑ ∷ Γ) (suc x) = cong suc (projTyRenId Γ x)
projTyRenId (Bnd κₑ ∷ Γ) x = projTyRenId Γ x
projTyRenId (* ∷ Γ) x = projTyRenId Γ x
projTyRenId (*ₗ ∷ Γ) x = projTyRenId Γ x
projTyRenId (*ₛ ∷ Γ) x = projTyRenId Γ x

-- Project a substitution
projTySub : (Γ1 Γ2 : ChorKndCtx) → TySub C⅀ₖ → TySub ⅀ₑₖ
projTySub Γ1 Γ2 σ = projTy (map isLocKnd Γ2) ∘ σ ∘ regainTyVar (map isLocKnd Γ1)

⊢projTySub : ∀{Γ1 Γ2 σ} →
             TYSUB C⅀ₖ σ Γ1 Γ2 →
             TYSUB ⅀ₑₖ
              (projTySub Γ1 Γ2 σ)
              (projKndCtx Γ1)
              (projKndCtx Γ2)
⊢projTySub {Γ1} {Γ2} ⊢σ = ⊢projTy ∘ ⊢σ ∘ ⊢regainTyVar ∘ ⊢injTyVar

-- Inject a renaming
injTyRen : (Γ1 Γ2 : KndCtxₑ) → Ren → Ren
injTyRen Γ1 Γ2 ξ = ξ ∘ projTyVar (map isLocKnd (injKndCtx Γ1))

⊢injTyRen : ∀{Γ1 Γ2 ξ x κₑ} →
             TYREN ⅀ₑₖ ξ Γ1 Γ2 →
             injKndCtx Γ1 c⊢ₜvar x ∶ LocKnd κₑ →
             injKndCtx Γ2 c⊢ₜvar injTyRen Γ1 Γ2 ξ x ∶ LocKnd κₑ
⊢injTyRen {Γ1} {x = x} {κₑ} ⊢ξ ⊢x =
  let ⊢projx : Γ1 e⊢ₜvar projTyVar (map isLocKnd (injKndCtx Γ1)) x ∶ κₑ
      ⊢projx = subst (λ y → y e⊢ₜvar projTyVar (map isLocKnd (injKndCtx Γ1)) x ∶ κₑ)
                  (proj∘injKndCtx≗id Γ1)
                  (⊢projTyVar ⊢x)
  in ⊢injTyVar (⊢ξ ⊢projx)

injTyRenId : (Γ : KndCtxₑ) → injTyRen Γ Γ id ≗ id
injTyRenId [] x = refl
injTyRenId (κₑ ∷ Γ) zero = refl
injTyRenId (κₑ ∷ Γ) (suc x) = cong suc (injTyRenId Γ x)

-- Inject a substitution
injTySub : (Γ1 Γ2 : KndCtxₑ) → TySub ⅀ₑₖ → TySub C⅀ₖ
injTySub Γ1 Γ2 σ = injTy ∘ σ ∘ projTyVar (map isLocKnd (injKndCtx Γ1))

⊢injTySub : ∀{Γ1 Γ2 σ x κₑ} →
             TYSUB ⅀ₑₖ σ Γ1 Γ2 →
             injKndCtx Γ1 c⊢ₜvar x ∶ LocKnd κₑ →
             injKndCtx Γ2 c⊢ₜ injTySub Γ1 Γ2 σ x ∶ LocKnd κₑ
⊢injTySub {Γ1} {x = x} {κₑ} ⊢σ ⊢x =
  let ⊢projx : Γ1 e⊢ₜvar projTyVar (map isLocKnd (injKndCtx Γ1)) x ∶ κₑ
      ⊢projx = subst (λ y → y e⊢ₜvar projTyVar (map isLocKnd (injKndCtx Γ1)) x ∶ κₑ)
                  (proj∘injKndCtx≗id Γ1)
                  (⊢projTyVar ⊢x)
  in ⊢injTy (⊢σ ⊢projx)

---------------------------
-- TYPE OPERATION LEMMAS --
---------------------------

{-
proj ∘ inj ≗ id

Injecting and then projecting a type has no effect
-}
proj∘injTyVar≗id : (n : ℕ) → projTyVar (replicate n true) ≗ id
proj∘injTyVar≗id zero x = refl
proj∘injTyVar≗id (suc n) zero = refl
proj∘injTyVar≗id (suc n) (suc x) = cong suc (proj∘injTyVar≗id n x)

proj∘injTy≗id : (n : ℕ) → projTy (replicate n true) ∘ injTy ≗ id
proj∘injTyVec≗id : (n : ℕ) → projTyVec (replicate n true) ∘ injTyVec ≗ id

proj∘injTy≗id n (tyVar x) = cong tyVar (proj∘injTyVar≗id n x)
proj∘injTy≗id n (tyConstr sₑ ts) = cong (tyConstr sₑ) (proj∘injTyVec≗id n ts)

proj∘injTyVec≗id n [] = refl
proj∘injTyVec≗id n ((t , k) ∷ ts) =
  cong₂ (λ x y → (x , k) ∷ y)
    (subst (λ x → projTy x (injTy t) ≡ t)
      (replicate-++ k n true)
      (proj∘injTy≗id (k + n) t))
    (proj∘injTyVec≗id n ts)

{-
regain ∘ inj ∘ proj ≗ id

Projecting, then injecting, then regaining lost
variables has no effect on a type
-}
regain∘inj∘projTyVar≗id : ∀{Γ x κₑ} →
                          Γ c⊢ₜvar x ∶ LocKnd κₑ →
                          regainTyVar (map isLocKnd Γ) (projTyVar (map isLocKnd Γ) x) ≡ x
regain∘inj∘projTyVar≗id ⊢ₜ0 = refl
regain∘inj∘projTyVar≗id (⊢ₜS {κ2 = LocKnd κₑ} ⊢x) =
  cong suc (regain∘inj∘projTyVar≗id ⊢x)
regain∘inj∘projTyVar≗id (⊢ₜS {κ2 = Bnd κₑ} ⊢x) =
  cong suc (regain∘inj∘projTyVar≗id ⊢x)
regain∘inj∘projTyVar≗id (⊢ₜS {κ2 = *} ⊢x) =
  cong suc (regain∘inj∘projTyVar≗id ⊢x)
regain∘inj∘projTyVar≗id (⊢ₜS {κ2 = *ₗ} ⊢x) =
  cong suc (regain∘inj∘projTyVar≗id ⊢x)
regain∘inj∘projTyVar≗id (⊢ₜS {κ2 = *ₛ} ⊢x) =
  cong suc (regain∘inj∘projTyVar≗id ⊢x)

regain∘inj∘projTy≗id : ∀{Γ t κₑ} →
                        Γ c⊢ₜ t ∶ LocKnd κₑ →
                        regainTy (map isLocKnd Γ)
                          (injTy (projTy (map isLocKnd Γ) t))
                        ≡ t
regain∘inj∘projTyVec≗id : ∀{Γ ts Σₑ} →
                          Γ c⊢ₜvec ts ∶ map LocKndΣ Σₑ →
                          regainTyVec (map isLocKnd Γ)
                            (injTyVec (projTyVec (map isLocKnd Γ) ts))
                          ≡ ts

regain∘inj∘projTy≗id {t = tyVar x} (⊢ₜvar ⊢x) =
  cong tyVar $ regain∘inj∘projTyVar≗id ⊢x
regain∘inj∘projTy≗id {t = tyConstr (EmbLocalTyS sₑ) ts} (⊢ₜtyConstr .(EmbLocalTyS sₑ) ⊢ts) =
  cong (tyConstr (EmbLocalTyS sₑ)) (regain∘inj∘projTyVec≗id ⊢ts)

regain∘inj∘projTyVec≗id {ts = []} ⊢ts = refl
regain∘inj∘projTyVec≗id {Γ} {(t , k) ∷ ts} {(Γₑ' , κₑ) ∷ Σₑ} (⊢t ⊢ₜ∷ ⊢ts) =
  let eq : replicate (length (map LocKnd Γₑ')) true ++ map isLocKnd Γ
            ≡ map isLocKnd (map LocKnd Γₑ' ++ Γ)
      eq =
        replicate (length (map LocKnd Γₑ')) true ++ map isLocKnd Γ
          ≡⟨ (cong (λ x → replicate x true ++ map isLocKnd Γ) $
                length-map LocKnd Γₑ') ⟩
        replicate (length Γₑ') true ++ map isLocKnd Γ
          ≡⟨ cong (_++ map isLocKnd Γ) $
             sym $ isLocKnd∘injKndCtx≡true Γₑ' ⟩
        map isLocKnd (map LocKnd Γₑ') ++ map isLocKnd Γ
          ≡⟨ (sym $ map-++-commute isLocKnd (map LocKnd Γₑ') Γ) ⟩
        map isLocKnd (map LocKnd Γₑ' ++ Γ) ∎
  in cong₂ (λ x y → (x , k) ∷ y)
    (renTy C⅀ₖ (Keep* (regainTyVar (map isLocKnd Γ)) (length (map LocKnd Γₑ')))
        (injTy (projTy (replicate (length (map LocKnd Γₑ')) true ++ map isLocKnd Γ) t))
      ≡⟨ (sym $ renTy-ext C⅀ₖ (regainTyVar-++ (map isLocKnd Γ) (length (map LocKnd Γₑ')))
            (injTy (projTy (replicate (length (map LocKnd Γₑ')) true ++ map isLocKnd Γ) t))) ⟩
    renTy C⅀ₖ (regainTyVar (replicate (length (map LocKnd Γₑ')) true ++ map isLocKnd Γ))
        (injTy (projTy (replicate (length (map LocKnd Γₑ')) true ++ map isLocKnd Γ) t))
      ≡⟨ cong (λ x → renTy C⅀ₖ (regainTyVar x) (injTy (projTy x t))) eq ⟩
    renTy C⅀ₖ (regainTyVar (map isLocKnd (map LocKnd Γₑ' ++ Γ)))
        (injTy (projTy (map isLocKnd (map LocKnd Γₑ' ++ Γ)) t))
      ≡⟨ regain∘inj∘projTy≗id ⊢t ⟩
    t ∎)
    (regain∘inj∘projTyVec≗id ⊢ts)

-- Projection distributes over composing renamings
projTyRen• : ∀{Γ1 Γ2 Γ3 ξ1 ξ2} →
             TYREN C⅀ₖ ξ1 Γ2 Γ3 → 
             TYREN C⅀ₖ ξ2 Γ1 Γ2 →
             ≗TyRen ⅀ₑₖ (projKndCtx Γ1)
              (projTyRen Γ1 Γ3 (ξ1 • ξ2))
              (projTyRen Γ2 Γ3 ξ1 • projTyRen Γ1 Γ2 ξ2)
projTyRen• {Γ1} {Γ2} {Γ3} {ξ1} {ξ2} ⊢ξ1 ⊢ξ2 {x = x} ⊢x =
  projTyVar (map isLocKnd Γ3) (ξ1 (ξ2 (regainTyVar (map isLocKnd Γ1) x)))
    ≡⟨ (cong (λ x → projTyVar (map isLocKnd Γ3) (ξ1 x)) $
          sym $ regain∘inj∘projTyVar≗id $
          ⊢ξ2 (⊢regainTyVar (⊢injTyVar ⊢x))) ⟩
  projTyVar (map isLocKnd Γ3)
    (ξ1 (regainTyVar (map isLocKnd Γ2) (projTyVar (map isLocKnd Γ2)
      (ξ2 (regainTyVar (map isLocKnd Γ1) x))))) ∎

Drop-projTyRen : ∀{Γ1 Γ2 ξ κₑ'} →
                TYREN C⅀ₖ ξ Γ1 Γ2 →
                ≗TyRen ⅀ₑₖ (projKndCtx Γ1)
                  (projTyRen Γ1 (LocKnd κₑ' ∷ Γ2) (Drop ξ))
                  (Drop (projTyRen Γ1 Γ2 ξ))
Drop-projTyRen {Γ1} {Γ2} {ξ} {κₑ'} ⊢ξ {x} {κₑ} ⊢x =
  projTyRen Γ1 (LocKnd κₑ' ∷ Γ2) (Drop ξ) x
    ≡⟨ projTyRen• {Γ3 = LocKnd κₑ' ∷ Γ2} {suc} {ξ} ⊢ₜS ⊢ξ ⊢x ⟩
  suc (projTyVar (map isLocKnd Γ2)
    (regainTyVar (map isLocKnd Γ2)
      (projTyVar (map isLocKnd Γ2)
        (ξ (regainTyVar (map isLocKnd Γ1) x)))))
    ≡⟨ (cong (λ x → suc (projTyVar (map isLocKnd Γ2) x)) $
         regain∘inj∘projTyVar≗id (⊢ξ (⊢regainTyVar (⊢injTyVar ⊢x)))) ⟩
  suc (projTyVar (map isLocKnd Γ2)
    (ξ (regainTyVar (map isLocKnd Γ1) x))) ∎

Keep-projTyRen : ∀{Γ1 Γ2 ξ κₑ'} →
                TYREN C⅀ₖ ξ Γ1 Γ2 →
                ≗TyRen ⅀ₑₖ (κₑ' ∷ projKndCtx Γ1)
                  (projTyRen (LocKnd κₑ' ∷ Γ1) (LocKnd κₑ' ∷ Γ2) (Keep ξ))
                  (Keep (projTyRen Γ1 Γ2 ξ))
Keep-projTyRen ⊢ξ ⊢ₜ0 = refl
Keep-projTyRen {κₑ' = κₑ'} ⊢ξ (⊢ₜS ⊢x) = Drop-projTyRen {κₑ' = κₑ'} ⊢ξ ⊢x

Keep*-projTyRen : ∀{Γ1 Γ2 ξ} →
                  TYREN C⅀ₖ ξ Γ1 Γ2 →
                  (Γₑ' : KndCtxₑ) →
                  ≗TyRen ⅀ₑₖ (Γₑ' ++ projKndCtx Γ1)
                    (projTyRen (map LocKnd Γₑ' ++ Γ1) (map LocKnd Γₑ' ++ Γ2) (Keep* ξ (length (map LocKnd Γₑ'))))
                    (Keep* (projTyRen Γ1 Γ2 ξ) (length (map LocKnd Γₑ')))
Keep*-projTyRen ⊢ξ [] ⊢x = refl
Keep*-projTyRen ⊢ξ (κₑ' ∷ Γₑ') ⊢ₜ0 = refl
Keep*-projTyRen ⊢ξ (κₑ' ∷ Γₑ') (⊢ₜS ⊢x) =
  cong suc $ Keep*-projTyRen ⊢ξ Γₑ' ⊢x

{-
proj ∘ ⟨ξ⟩ ≗ ⟨proj ξ⟩ ∘ proj

Renaming and then projecting is identical
to first projecting, and then renaming
on the projected renaming
-}
proj∘ren≗projRen∘projTyVar
  : ∀{x κₑ} (Γ1 Γ2 : ChorKndCtx) (ξ : Ren) →
    Γ1 c⊢ₜvar x ∶ LocKnd κₑ →
    projTyVar (map isLocKnd Γ2) (ξ x) ≡
    projTyRen Γ1 Γ2 ξ (projTyVar (map isLocKnd Γ1) x)
proj∘ren≗projRen∘projTyVar {x} Γ1 Γ2 ξ ⊢x =
  projTyVar (map isLocKnd Γ2) (ξ x)
    ≡⟨ (sym $ cong (λ x → projTyVar (map isLocKnd Γ2) (ξ x)) $
          regain∘inj∘projTyVar≗id ⊢x) ⟩
  projTyVar (map isLocKnd Γ2)
    (ξ (regainTyVar (map isLocKnd Γ1) (projTyVar (map isLocKnd Γ1) x))) ∎

proj∘ren≗projRen∘projTy
  : ∀{Γ1 Γ2 ξ t κₑ} →
    TYREN C⅀ₖ ξ Γ1 Γ2 →
    Γ1 c⊢ₜ t ∶ LocKnd κₑ →
    projTy (map isLocKnd Γ2) (renTy C⅀ₖ ξ t) ≡
    renTy ⅀ₑₖ (projTyRen Γ1 Γ2 ξ) (projTy (map isLocKnd Γ1) t)
proj∘ren≗projRen∘projTyVec
  : ∀{Γ1 Γ2 ξ ts Σₑ} →
    TYREN C⅀ₖ ξ Γ1 Γ2 →
    Γ1 c⊢ₜvec ts ∶ map LocKndΣ Σₑ →
    projTyVec (map isLocKnd Γ2) (renTyVec C⅀ₖ ξ ts) ≡
    renTyVec ⅀ₑₖ (projTyRen Γ1 Γ2 ξ) (projTyVec (map isLocKnd Γ1) ts)

proj∘ren≗projRen∘projTy {Γ1} {Γ2} {ξ} {tyVar x} ⊢ξ (⊢ₜvar ⊢x) =
  cong tyVar (proj∘ren≗projRen∘projTyVar Γ1 Γ2 ξ ⊢x)
proj∘ren≗projRen∘projTy {t = tyConstr (EmbLocalTyS sₑ) ts} ⊢ξ (⊢ₜtyConstr .(EmbLocalTyS sₑ) ⊢ts) =
  cong (tyConstr sₑ) (proj∘ren≗projRen∘projTyVec ⊢ξ ⊢ts)

proj∘ren≗projRen∘projTyVec {ts = []} {[]} ⊢ξ ⊢ₜ[] = refl
proj∘ren≗projRen∘projTyVec {Γ1} {Γ2} {ξ} {(t , .(length (map LocKnd Γₑ'))) ∷ ts} {(Γₑ' , κₑ) ∷ Σₑ} ⊢ξ (⊢t ⊢ₜ∷ ⊢ts) =
  let eq1 : ∀ Γ → replicate (length (map LocKnd Γₑ')) true ++ map isLocKnd Γ
            ≡ map isLocKnd (map LocKnd Γₑ' ++ Γ)
      eq1 Γ =
        replicate (length (injKndCtx Γₑ')) true ++ map isLocKnd Γ
          ≡⟨ cong (λ x → replicate x true ++ map isLocKnd Γ) (length-map LocKnd Γₑ') ⟩
        replicate (length Γₑ') true ++ map isLocKnd Γ
          ≡⟨ cong (_++ map isLocKnd Γ) (sym $ isLocKnd∘injKndCtx≡true Γₑ') ⟩
        map isLocKnd (injKndCtx Γₑ') ++ map isLocKnd Γ
          ≡⟨ (sym $ map-++-commute isLocKnd (injKndCtx Γₑ') Γ) ⟩
        map isLocKnd (injKndCtx Γₑ' ++ Γ) ∎
      eq2 : projKndCtx (map LocKnd Γₑ' ++ Γ1) ≡ Γₑ' ++ projKndCtx Γ1
      eq2 =
        projKndCtx (map LocKnd Γₑ' ++ Γ1)
          ≡⟨ projKndCtx-++ (map LocKnd Γₑ') Γ1 ⟩
        projKndCtx (injKndCtx Γₑ') ++ projKndCtx Γ1
          ≡⟨ cong (_++ projKndCtx Γ1) (proj∘injKndCtx≗id Γₑ') ⟩
        Γₑ' ++ projKndCtx Γ1 ∎
  in cong₂ (λ x y → (x , length (map LocKnd Γₑ')) ∷ y)
    (projTy (replicate (length (map LocKnd Γₑ')) true ++ map isLocKnd Γ2)
      (renTy C⅀ₖ (Keep* ξ (length (map LocKnd Γₑ'))) t)
      ≡⟨ (cong (flip projTy (renTy C⅀ₖ (Keep* ξ (length (map LocKnd Γₑ'))) t)) (eq1 Γ2)) ⟩
    projTy (map isLocKnd (map LocKnd Γₑ' ++ Γ2))
      (renTy C⅀ₖ (Keep* ξ (length (map LocKnd Γₑ'))) t)
      ≡⟨ proj∘ren≗projRen∘projTy (⊢TyKeep* C⅀ₖ ⊢ξ (map LocKnd Γₑ')) ⊢t ⟩
    renTy ⅀ₑₖ
      (projTyRen (map LocKnd Γₑ' ++ Γ1) (map LocKnd Γₑ' ++ Γ2)
        (Keep* ξ (length (map LocKnd Γₑ'))))
      (projTy (map isLocKnd (map LocKnd Γₑ' ++ Γ1)) t)
      ≡⟨ cong (λ x → renTy ⅀ₑₖ
      (projTyRen (map LocKnd Γₑ' ++ Γ1) (map LocKnd Γₑ' ++ Γ2)
        (Keep* ξ (length (map LocKnd Γₑ'))))
      (projTy x t)) (sym $ eq1 Γ1) ⟩
    renTy ⅀ₑₖ
      (projTyRen (map LocKnd Γₑ' ++ Γ1) (map LocKnd Γₑ' ++ Γ2)
        (Keep* ξ (length (map LocKnd Γₑ'))))
      (projTy (replicate (length (map LocKnd Γₑ')) true ++ map isLocKnd Γ1) t)
      ≡⟨ ⊢renTy-≗TyRen ⅀ₑₖ
            (Keep*-projTyRen ⊢ξ Γₑ')
            (subst₂ (λ x y → x e⊢ₜ projTy y t ∶ κₑ)
                eq2
                (sym (eq1 Γ1))
                (⊢projTy ⊢t)) ⟩
    renTy ⅀ₑₖ
      (Keep* (projTyRen Γ1 Γ2 ξ) (length (map LocKnd Γₑ')))
      (projTy (replicate (length (map LocKnd Γₑ')) true ++ map isLocKnd Γ1) t) ∎)
    (proj∘ren≗projRen∘projTyVec ⊢ξ ⊢ts)

-- Injection distributes over composing renamings
injTyRen• : (Γ1 Γ2 Γ3 : KndCtxₑ) (ξ1 ξ2 : Ren) →
            injTyRen Γ1 Γ3 (ξ1 • ξ2) ≗
            injTyRen Γ2 Γ3 ξ1 • injTyRen Γ1 Γ2 ξ2
injTyRen• Γ1 Γ2 Γ3 ξ1 ξ2 x =
  ξ1 (ξ2 (projTyVar (map isLocKnd (map LocKnd Γ1)) x))
    ≡⟨ (sym $ cong ξ1 $ proj∘injTyVar≗id (length Γ2) $
          (ξ2 (projTyVar (map isLocKnd (map LocKnd Γ1)) x))) ⟩
  ξ1 (projTyVar (replicate (length Γ2) true)
    (ξ2 (projTyVar (map isLocKnd (map LocKnd Γ1)) x)))
    ≡⟨ (cong (λ y → ξ1 (projTyVar y
          (ξ2 (projTyVar (map isLocKnd (map LocKnd Γ1)) x)))) $
      sym $ isLocKnd∘injKndCtx≡true Γ2) ⟩
  ξ1 (projTyVar (map isLocKnd (map LocKnd Γ2))
    (ξ2 (projTyVar (map isLocKnd (map LocKnd Γ1)) x))) ∎

Drop-injTyRen : ∀{κₑ} (Γ1 Γ2 : KndCtxₑ) (ξ : Ren) →
                injTyRen Γ1 (κₑ ∷ Γ2) (Drop ξ) ≗
                Drop (injTyRen Γ1 Γ2 ξ)
Drop-injTyRen {κₑ} Γ1 Γ2 ξ x = 
  injTyRen Γ1 (κₑ ∷ Γ2) (suc • ξ) x
    ≡⟨ injTyRen• Γ1 Γ2 (κₑ ∷ Γ2) suc ξ x ⟩
  suc (projTyVar (map isLocKnd (injKndCtx Γ2))
    (ξ (projTyVar (map isLocKnd (injKndCtx Γ1)) x)))
    ≡⟨ cong (λ y → suc (projTyVar y (ξ (projTyVar (map isLocKnd (injKndCtx Γ1)) x))))
        (isLocKnd∘injKndCtx≡true Γ2) ⟩
  suc (projTyVar (replicate (length Γ2) true)
    (ξ (projTyVar (map isLocKnd (injKndCtx Γ1)) x)))
    ≡⟨ (cong suc $ proj∘injTyVar≗id (length Γ2) $
        ξ (projTyVar (map isLocKnd (injKndCtx Γ1)) x)) ⟩
  suc (ξ (projTyVar (map isLocKnd (injKndCtx Γ1)) x)) ∎

Keep-injTyRen : ∀{κₑ} (Γ1 Γ2 : KndCtxₑ) (ξ : Ren) →
                injTyRen (κₑ ∷ Γ1) (κₑ ∷ Γ2) (Keep ξ) ≗
                Keep (injTyRen Γ1 Γ2 ξ)
Keep-injTyRen Γ1 Γ2 ξ zero = refl
Keep-injTyRen {κₑ} Γ1 Γ2 ξ (suc x) =
  Drop-injTyRen {κₑ} Γ1 Γ2 ξ x

Keep*-injTyRen : (Γ1 Γ2 : KndCtxₑ) (ξ : Ren) →
                 (Γₑ' : KndCtxₑ) →
                 injTyRen (Γₑ' ++ Γ1) (Γₑ' ++ Γ2) (Keep* ξ (length Γₑ')) ≗
                 Keep* (injTyRen Γ1 Γ2 ξ) (length Γₑ')
Keep*-injTyRen Γ1 Γ2 ξ [] x = refl
Keep*-injTyRen Γ1 Γ2 ξ (κₑ' ∷ Γₑ') x =
  injTyRen (κₑ' ∷ Γₑ' ++ Γ1) (κₑ' ∷ Γₑ' ++ Γ2)
    (Keep (Keep* ξ (length Γₑ'))) x
    ≡⟨ Keep-injTyRen {κₑ'} (Γₑ' ++ Γ1) (Γₑ' ++ Γ2) (Keep* ξ (length Γₑ')) x ⟩
  Keep (injTyRen (Γₑ' ++ Γ1) (Γₑ' ++ Γ2) (Keep* ξ (length Γₑ'))) x
    ≡⟨ Keep-ext (Keep*-injTyRen Γ1 Γ2 ξ Γₑ') x ⟩
  Keep (Keep* (injTyRen Γ1 Γ2 ξ) (length Γₑ')) x ∎

{-
inj ∘ ⟨ξ⟩ ≗ ⟨inj ξ⟩ ∘ inj

Renaming and then injecting is identical
to first injecting, and then renaming
on the injected renaming
-}
inj∘ren≗injRen∘injTyVar
  : ∀{Γ1 Γ2 x κₑ} →
    (ξ : Ren) →
    Γ1 e⊢ₜvar x ∶ κₑ →
    ξ x ≡ injTyRen Γ1 Γ2 ξ x
inj∘ren≗injRen∘injTyVar {κₑ ∷ Γ1} {Γ2} {0} ξ ⊢ₜ0 = refl
inj∘ren≗injRen∘injTyVar {κₑ ∷ Γ1} {Γ2} {suc x} ξ (⊢ₜS ⊢x) =
  inj∘ren≗injRen∘injTyVar {Γ1} {Γ2} (ξ ∘ suc) ⊢x

inj∘ren≗injRen∘injTyVar'
  : ∀{Γ1 Γ2} →
    (ξ : Ren) →
    ξ ≗ injTyRen Γ1 Γ2 ξ
inj∘ren≗injRen∘injTyVar' {[]} {Γ2} ξ x = refl
inj∘ren≗injRen∘injTyVar' {κₑ ∷ Γ1} {Γ2} ξ zero = refl
inj∘ren≗injRen∘injTyVar' {κₑ ∷ Γ1} {Γ2} ξ (suc x) =
  cong (ξ ∘ suc) (inj∘ren≗injRen∘injTyVar' {Γ1} {Γ2} id x)

inj∘ren≗injRen∘injTy
  : ∀{Γ1 Γ2 ξ t κₑ} →
    TYREN ⅀ₑₖ ξ Γ1 Γ2 →
    Γ1 e⊢ₜ t ∶ κₑ →
    injTy (renTy ⅀ₑₖ ξ t) ≡ renTy C⅀ₖ (injTyRen Γ1 Γ2 ξ) (injTy t)
inj∘ren≗injRen∘injTyVec
  : ∀{Γ1 Γ2 ξ ts Σₑ} →
    TYREN ⅀ₑₖ ξ Γ1 Γ2 →
    Γ1 e⊢ₜvec ts ∶ Σₑ →
    injTyVec (renTyVec ⅀ₑₖ ξ ts) ≡ renTyVec C⅀ₖ (injTyRen Γ1 Γ2 ξ) (injTyVec ts)

inj∘ren≗injRen∘injTy {Γ1} {Γ2} {ξ = ξ} ⊢ξ (⊢ₜvar ⊢x) =
  cong tyVar (inj∘ren≗injRen∘injTyVar {Γ1} {Γ2} ξ ⊢x)
inj∘ren≗injRen∘injTy ⊢ξ (⊢ₜtyConstr s ⊢ts) =
  cong (tyConstr (EmbLocalTyS s)) (inj∘ren≗injRen∘injTyVec ⊢ξ ⊢ts)

inj∘ren≗injRen∘injTyVec ⊢ξ ⊢ₜ[] = refl
inj∘ren≗injRen∘injTyVec {Γ1} {Γ2} {ξ} {(t , _) ∷ ts} {(Δₑ , κₑ) ∷ Σₑ} ⊢ξ (⊢t ⊢ₜ∷ ⊢ts) =
  cong₂ (λ x y → (x , length Δₑ) ∷ y)
    (injTy (renTy ⅀ₑₖ (Keep* ξ (length Δₑ)) t)
      ≡⟨ inj∘ren≗injRen∘injTy (⊢TyKeep* ⅀ₑₖ ⊢ξ Δₑ) ⊢t ⟩
    renTy C⅀ₖ (injTyRen (Δₑ ++ Γ1) (Δₑ ++ Γ2) (Keep* ξ (length Δₑ))) (injTy t)
      ≡⟨ renTy-ext C⅀ₖ (Keep*-injTyRen Γ1 Γ2 ξ Δₑ) (injTy t) ⟩
    renTy C⅀ₖ (Keep* (injTyRen Γ1 Γ2 ξ) (length Δₑ)) (injTy t) ∎)
    (inj∘ren≗injRen∘injTyVec ⊢ξ ⊢ts)

_e•◦ₜ_ = _•◦ₜ_ ⅀ₑₖ
_c•◦ₜ_ = _•◦ₜ_ C⅀ₖ
_c◦•ₜ_ = _◦•ₜ_ C⅀ₖ

-- Projection distributes over composing renamings after substitutions
projTySub•◦ : ∀{Γ1 Γ2 Γ3 σ ξ x κₑ} →
              TYREN C⅀ₖ ξ Γ2 Γ3 →
              TYSUB C⅀ₖ σ Γ1 Γ2 →
              projKndCtx Γ1 e⊢ₜvar x ∶ κₑ →
              projTySub Γ1 Γ3 (ξ c•◦ₜ σ) x
              ≡ (projTyRen Γ2 Γ3 ξ e•◦ₜ projTySub Γ1 Γ2 σ) x
projTySub•◦ {Γ1} {Γ2} {Γ3} {σ} {ξ} {x} ⊢ξ ⊢σ ⊢x =
  projTy (map isLocKnd Γ3)
    (renTy C⅀ₖ ξ (σ (regainTyVar (map isLocKnd Γ1) x)))
    ≡⟨ proj∘ren≗projRen∘projTy ⊢ξ (⊢σ (⊢regainTyVar (⊢injTyVar ⊢x))) ⟩
    renTy ⅀ₑₖ (projTyVar (map isLocKnd Γ3) ∘ ξ ∘ regainTyVar (map isLocKnd Γ2))
      (projTy (map isLocKnd Γ2) (σ (regainTyVar (map isLocKnd Γ1) x))) ∎

Drop-projTySub : ∀{Γ1 Γ2 σ κₑ'} →
                TYSUB C⅀ₖ σ Γ1 Γ2 →
                ≗TySub ⅀ₑₖ (projKndCtx Γ1)
                  (projTySub Γ1 (LocKnd κₑ' ∷ Γ2) (TyDropSub C⅀ₖ σ))
                  (TyDropSub ⅀ₑₖ (projTySub Γ1 Γ2 σ))
Drop-projTySub {Γ1} {Γ2} {σ} {κₑ'} ⊢σ {x} {κₑ} ⊢x =
  projTySub Γ1 (LocKnd κₑ' ∷ Γ2) (suc c•◦ₜ σ) x
    ≡⟨ projTySub•◦ (⊢ₜS {κ2 = LocKnd κₑ'}) ⊢σ ⊢x ⟩
  renTy ⅀ₑₖ (projTyRen Γ2 (LocKnd κₑ' ∷ Γ2) (Drop id)) (projTySub Γ1 Γ2 σ x)
    ≡⟨ ⊢renTy-≗TyRen ⅀ₑₖ (Drop-projTyRen {κₑ' = κₑ'} (⊢TyIdRen C⅀ₖ {Γ2})) (⊢projTySub ⊢σ ⊢x) ⟩
  renTy ⅀ₑₖ (Drop (projTyRen Γ2 Γ2 id)) (projTySub Γ1 Γ2 σ x)
    ≡⟨ renTy-ext ⅀ₑₖ (Drop-ext (projTyRenId Γ2)) (projTySub Γ1 Γ2 σ x) ⟩
  renTy ⅀ₑₖ suc (projTySub Γ1 Γ2 σ x) ∎

Keep-projTySub : ∀{Γ1 Γ2 σ κₑ'} →
                TYSUB C⅀ₖ σ Γ1 Γ2 →
                ≗TySub ⅀ₑₖ (κₑ' ∷ projKndCtx Γ1)
                  (projTySub (LocKnd κₑ' ∷ Γ1) (LocKnd κₑ' ∷ Γ2) (TyKeepSub C⅀ₖ σ))
                  (TyKeepSub ⅀ₑₖ (projTySub Γ1 Γ2 σ))
Keep-projTySub ⊢σ ⊢ₜ0 = refl
Keep-projTySub {κₑ' = κₑ'} ⊢σ (⊢ₜS ⊢x) = Drop-projTySub {κₑ' = κₑ'} ⊢σ ⊢x

Keep*-projTySub : ∀{Γ1 Γ2 σ} →
                  TYSUB C⅀ₖ σ Γ1 Γ2 →
                  (Γₑ' : KndCtxₑ) →
                  ≗TySub ⅀ₑₖ (Γₑ' ++ projKndCtx Γ1)
                    (projTySub (map LocKnd Γₑ' ++ Γ1) (map LocKnd Γₑ' ++ Γ2) (TyKeepSub* C⅀ₖ σ (length (map LocKnd Γₑ'))))
                    (TyKeepSub* ⅀ₑₖ (projTySub Γ1 Γ2 σ) (length (map LocKnd Γₑ')))
Keep*-projTySub ⊢σ [] ⊢x = refl
Keep*-projTySub {Γ1} {Γ2} {σ} ⊢σ (κₑ' ∷ Γₑ') {x = x} {κₑ} ⊢x =
  let eq : ∀ Γ → Γₑ' ++ projKndCtx Γ ≡ projKndCtx (map LocKnd Γₑ' ++ Γ)
      eq Γ =
        Γₑ' ++ projKndCtx Γ
          ≡⟨ cong (_++ projKndCtx Γ) (sym $ proj∘injKndCtx≗id Γₑ') ⟩
        projKndCtx (injKndCtx Γₑ') ++ projKndCtx Γ
          ≡⟨ (sym $ projKndCtx-++ (injKndCtx Γₑ') Γ) ⟩
        projKndCtx (injKndCtx Γₑ' ++ Γ) ∎
  in
  projTySub
    (LocKnd κₑ' ∷ map LocKnd Γₑ' ++ Γ1)
    (LocKnd κₑ' ∷ map LocKnd Γₑ' ++ Γ2)
    (TyKeepSub C⅀ₖ (TyKeepSub* C⅀ₖ σ (length (map LocKnd Γₑ'))))
    x
    ≡⟨ Keep-projTySub (⊢TyKeepSub* C⅀ₖ ⊢σ (map LocKnd Γₑ')) $
        subst (λ y → y e⊢ₜvar x ∶ κₑ)
            (cong (κₑ' ∷_) (eq Γ1))
            ⊢x ⟩
  TyKeepSub ⅀ₑₖ
    (projTySub
      (map LocKnd Γₑ' ++ Γ1)
      (map LocKnd Γₑ' ++ Γ2)
      (TyKeepSub* C⅀ₖ σ (length (map LocKnd Γₑ'))))
    x
    ≡⟨ Keep-≗TySub ⅀ₑₖ (Keep*-projTySub ⊢σ Γₑ') ⊢x ⟩
  TyKeepSub ⅀ₑₖ
    (TyKeepSub* ⅀ₑₖ (projTySub Γ1 Γ2 σ) (length (map LocKnd Γₑ')))
    x ∎

{-
proj ∘ ⟨σ⟩ ≗ ⟨proj σ⟩ ∘ proj

Substituting and then projecting is identical
to first projecting, and then substituting
on the projected substitution
-}
proj∘sub≗projSub∘projTyVar
  : ∀{x κₑ} (Γ1 Γ2 : ChorKndCtx) (σ : TySub C⅀ₖ) →
    Γ1 c⊢ₜvar x ∶ LocKnd κₑ →
    projTy (map isLocKnd Γ2) (σ x) ≡
    projTySub Γ1 Γ2 σ (projTyVar (map isLocKnd Γ1) x)
proj∘sub≗projSub∘projTyVar {x} Γ1 Γ2 σ ⊢x =
  projTy (map isLocKnd Γ2) (σ x)
    ≡⟨ (sym $ cong (λ x → projTy (map isLocKnd Γ2) (σ x)) $
          regain∘inj∘projTyVar≗id ⊢x) ⟩
  projTy (map isLocKnd Γ2)
    (σ (regainTyVar (map isLocKnd Γ1) (projTyVar (map isLocKnd Γ1) x))) ∎

proj∘sub≗projSub∘projTy
  : ∀{Γ1 Γ2 σ t κₑ} →
    TYSUB C⅀ₖ σ Γ1 Γ2 →
    Γ1 c⊢ₜ t ∶ LocKnd κₑ →
    projTy (map isLocKnd Γ2) (subTy C⅀ₖ σ t) ≡
    subTy ⅀ₑₖ (projTySub Γ1 Γ2 σ) (projTy (map isLocKnd Γ1) t)
proj∘sub≗projSub∘projTyVec
  : ∀{Γ1 Γ2 σ ts Σₑ} →
    TYSUB C⅀ₖ σ Γ1 Γ2 →
    Γ1 c⊢ₜvec ts ∶ map LocKndΣ Σₑ →
    projTyVec (map isLocKnd Γ2) (subTyVec C⅀ₖ σ ts) ≡
    subTyVec ⅀ₑₖ (projTySub Γ1 Γ2 σ) (projTyVec (map isLocKnd Γ1) ts)

proj∘sub≗projSub∘projTy {Γ1} {Γ2} {σ} {tyVar x} ⊢σ (⊢ₜvar ⊢x) =
  proj∘sub≗projSub∘projTyVar Γ1 Γ2 σ ⊢x
proj∘sub≗projSub∘projTy {t = tyConstr (EmbLocalTyS sₑ) ts} ⊢σ (⊢ₜtyConstr .(EmbLocalTyS sₑ) ⊢ts) =
  cong (tyConstr sₑ) (proj∘sub≗projSub∘projTyVec ⊢σ ⊢ts)

proj∘sub≗projSub∘projTyVec {ts = []} {[]} ⊢σ ⊢ₜ[] = refl
proj∘sub≗projSub∘projTyVec {Γ1} {Γ2} {σ} {(t , .(length (map LocKnd Γₑ'))) ∷ ts} {(Γₑ' , κₑ) ∷ Σₑ} ⊢σ (⊢t ⊢ₜ∷ ⊢ts) =
  let eq1 : ∀ Γ → replicate (length (map LocKnd Γₑ')) true ++ map isLocKnd Γ
            ≡ map isLocKnd (map LocKnd Γₑ' ++ Γ)
      eq1 Γ =
        replicate (length (injKndCtx Γₑ')) true ++ map isLocKnd Γ
          ≡⟨ cong (λ x → replicate x true ++ map isLocKnd Γ) (length-map LocKnd Γₑ') ⟩
        replicate (length Γₑ') true ++ map isLocKnd Γ
          ≡⟨ cong (_++ map isLocKnd Γ) (sym $ isLocKnd∘injKndCtx≡true Γₑ') ⟩
        map isLocKnd (injKndCtx Γₑ') ++ map isLocKnd Γ
          ≡⟨ (sym $ map-++-commute isLocKnd (injKndCtx Γₑ') Γ) ⟩
        map isLocKnd (injKndCtx Γₑ' ++ Γ) ∎
      eq2 : projKndCtx (map LocKnd Γₑ' ++ Γ1) ≡ Γₑ' ++ projKndCtx Γ1
      eq2 =
        projKndCtx (map LocKnd Γₑ' ++ Γ1)
          ≡⟨ projKndCtx-++ (map LocKnd Γₑ') Γ1 ⟩
        projKndCtx (injKndCtx Γₑ') ++ projKndCtx Γ1
          ≡⟨ cong (_++ projKndCtx Γ1) (proj∘injKndCtx≗id Γₑ') ⟩
        Γₑ' ++ projKndCtx Γ1 ∎
  in cong₂ (λ x y → (x , length (map LocKnd Γₑ')) ∷ y)
    (projTy (replicate (length (map LocKnd Γₑ')) true ++ map isLocKnd Γ2)
      (subTy C⅀ₖ (TyKeepSub* C⅀ₖ σ (length (map LocKnd Γₑ'))) t)
      ≡⟨ (cong (flip projTy (subTy C⅀ₖ (TyKeepSub* C⅀ₖ σ (length (map LocKnd Γₑ'))) t)) (eq1 Γ2)) ⟩
    projTy (map isLocKnd (map LocKnd Γₑ' ++ Γ2))
      (subTy C⅀ₖ (TyKeepSub* C⅀ₖ σ (length (map LocKnd Γₑ'))) t)
      ≡⟨ proj∘sub≗projSub∘projTy (⊢TyKeepSub* C⅀ₖ ⊢σ (map LocKnd Γₑ')) ⊢t ⟩
    subTy ⅀ₑₖ
      (projTySub (map LocKnd Γₑ' ++ Γ1) (map LocKnd Γₑ' ++ Γ2)
        (TyKeepSub* C⅀ₖ σ (length (map LocKnd Γₑ'))))
      (projTy (map isLocKnd (map LocKnd Γₑ' ++ Γ1)) t)
      ≡⟨ cong (λ x → subTy ⅀ₑₖ
      (projTySub (map LocKnd Γₑ' ++ Γ1) (map LocKnd Γₑ' ++ Γ2)
        (TyKeepSub* C⅀ₖ σ (length (map LocKnd Γₑ'))))
      (projTy x t)) (sym $ eq1 Γ1) ⟩
    subTy ⅀ₑₖ
      (projTySub (map LocKnd Γₑ' ++ Γ1) (map LocKnd Γₑ' ++ Γ2)
        (TyKeepSub* C⅀ₖ σ (length (map LocKnd Γₑ'))))
      (projTy (replicate (length (map LocKnd Γₑ')) true ++ map isLocKnd Γ1) t)
      ≡⟨ ⊢subTy-≗TySub ⅀ₑₖ
            (Keep*-projTySub ⊢σ Γₑ')
            (subst₂ (λ x y → x e⊢ₜ projTy y t ∶ κₑ)
                eq2
                (sym (eq1 Γ1))
                (⊢projTy ⊢t)) ⟩
    subTy ⅀ₑₖ
      (TyKeepSub* ⅀ₑₖ (projTySub Γ1 Γ2 σ) (length (map LocKnd Γₑ')))
      (projTy (replicate (length (map LocKnd Γₑ')) true ++ map isLocKnd Γ1) t) ∎)
    (proj∘sub≗projSub∘projTyVec ⊢σ ⊢ts)

-- Injection distributes over composing renamings with substitutions
injTySub•◦ : ∀{Γ1 Γ2 Γ3 ξ σ x κₑ} →
             TYREN ⅀ₑₖ ξ Γ2 Γ3 →
             TYSUB ⅀ₑₖ σ Γ1 Γ2 →
             injKndCtx Γ1 c⊢ₜvar x ∶ LocKnd κₑ →
             injTySub Γ1 Γ3 (ξ e•◦ₜ σ) x ≡
            (injTyRen Γ2 Γ3 ξ c•◦ₜ injTySub Γ1 Γ2 σ) x
injTySub•◦ {Γ1} {Γ2} {Γ3} {ξ} {σ} {x} {κₑ} ⊢ξ ⊢σ ⊢x =
  injTy (renTy ⅀ₑₖ ξ (σ (projTyVar (map isLocKnd (injKndCtx Γ1)) x)))
    ≡⟨ inj∘ren≗injRen∘injTy ⊢ξ (⊢σ $
      (subst (λ y → y e⊢ₜvar projTyVar (map isLocKnd (injKndCtx Γ1)) x ∶ κₑ)
          (proj∘injKndCtx≗id Γ1)
          (⊢projTyVar ⊢x))) ⟩
  renTy C⅀ₖ (injTyRen Γ2 Γ3 ξ)
    (injTySub Γ1 Γ2 σ x) ∎

Drop-injTySub : ∀{Γ1 Γ2 κₑ' σ x κₑ} →
                TYSUB ⅀ₑₖ σ Γ1 Γ2 →
                injKndCtx Γ1 c⊢ₜvar x ∶ LocKnd κₑ →
                injTySub Γ1 (κₑ' ∷ Γ2) (TyDropSub ⅀ₑₖ σ) x ≡
                TyDropSub C⅀ₖ (injTySub Γ1 Γ2 σ) x
Drop-injTySub {Γ1} {Γ2} {κₑ'} {σ} {x} {κₑ} ⊢σ ⊢x =
  injTySub Γ1 (κₑ' ∷ Γ2) (suc e•◦ₜ σ) x
    ≡⟨ injTySub•◦ (⊢TyDrop ⅀ₑₖ {κ = κₑ'} (⊢TyIdRen ⅀ₑₖ {Γ2})) ⊢σ ⊢x ⟩
  renTy C⅀ₖ (injTyRen Γ2 (κₑ' ∷ Γ2) suc) (injTySub Γ1 Γ2 σ x)
    ≡⟨ renTy-ext C⅀ₖ (Drop-injTyRen {κₑ'} Γ2 Γ2 id) (injTySub Γ1 Γ2 σ x) ⟩
  renTy C⅀ₖ (Drop (injTyRen Γ2 Γ2 id)) (injTySub Γ1 Γ2 σ x)
    ≡⟨ renTy-ext C⅀ₖ (Drop-ext (injTyRenId Γ2)) (injTySub Γ1 Γ2 σ x) ⟩
  renTy C⅀ₖ suc (injTySub Γ1 Γ2 σ x) ∎

Keep-injTySub : ∀{Γ1 Γ2 κₑ' σ x κₑ} →
                TYSUB ⅀ₑₖ σ Γ1 Γ2 →
                (LocKnd κₑ' ∷ injKndCtx Γ1) c⊢ₜvar x ∶ LocKnd κₑ →
                injTySub (κₑ' ∷ Γ1) (κₑ' ∷ Γ2) (TyKeepSub ⅀ₑₖ σ) x ≡
                TyKeepSub C⅀ₖ (injTySub Γ1 Γ2 σ) x
Keep-injTySub ⊢σ ⊢ₜ0 = refl
Keep-injTySub {κₑ' = κₑ'} ⊢σ (⊢ₜS ⊢x) = Drop-injTySub {κₑ' = κₑ'} ⊢σ ⊢x

Keep*-injTySub : ∀{Γ1 Γ2 σ x κₑ} →
                 TYSUB ⅀ₑₖ σ Γ1 Γ2 →
                 (Γₑ' : KndCtxₑ) →
                 (injKndCtx Γₑ' ++ injKndCtx Γ1) c⊢ₜvar x ∶ LocKnd κₑ →
                 injTySub (Γₑ' ++ Γ1) (Γₑ' ++ Γ2) (TyKeepSub* ⅀ₑₖ σ (length Γₑ')) x ≡
                 TyKeepSub* C⅀ₖ (injTySub Γ1 Γ2 σ) (length Γₑ') x
Keep*-injTySub ⊢σ [] ⊢x = refl
Keep*-injTySub {Γ1} {Γ2} {σ} {zero} {.κₑ'} ⊢σ (κₑ' ∷ Γₑ') ⊢ₜ0 = refl
Keep*-injTySub {Γ1} {Γ2} {σ} {suc x} {κₑ} ⊢σ (κₑ' ∷ Γₑ') (⊢ₜS ⊢x) =
  injTySub (κₑ' ∷ Γₑ' ++ Γ1) (κₑ' ∷ Γₑ' ++ Γ2)
    (TyKeepSub ⅀ₑₖ (TyKeepSub* ⅀ₑₖ σ (length Γₑ'))) (suc x)
    ≡⟨ (Keep-injTySub {κₑ' = κₑ'} (⊢TyKeepSub* ⅀ₑₖ ⊢σ Γₑ') $
        subst (λ y → y c⊢ₜvar suc x ∶ LocKnd κₑ)
          (sym $ cong (LocKnd κₑ' ∷_) $ injKndCtx-++ Γₑ' Γ1)
          (⊢ₜS ⊢x)) ⟩
  renTy C⅀ₖ suc (injTySub (Γₑ' ++ Γ1) (Γₑ' ++ Γ2) (TyKeepSub* ⅀ₑₖ σ (length Γₑ')) x)
    ≡⟨ cong (renTy C⅀ₖ suc) (Keep*-injTySub ⊢σ Γₑ' ⊢x) ⟩
  renTy C⅀ₖ suc (TyKeepSub* C⅀ₖ (injTySub Γ1 Γ2 σ) (length Γₑ') x) ∎

{-
inj ∘ ⟨σ⟩ ≗ ⟨inj σ⟩ ∘ inj

Substituting and then injecting is identical
to first injecting, and then substituting
on the injected substitution
-}
inj∘sub≗injSub∘injTyVar
  : ∀{Γ1 Γ2 x κₑ} →
    (σ : TySub ⅀ₑₖ) →
    Γ1 e⊢ₜvar x ∶ κₑ →
    injTy (σ x) ≡ injTySub Γ1 Γ2 σ x
inj∘sub≗injSub∘injTyVar {κₑ ∷ Γ1} {Γ2} σ ⊢ₜ0 = refl
inj∘sub≗injSub∘injTyVar {κₑ ∷ Γ1} {Γ2} {suc x} σ (⊢ₜS ⊢x) =
  inj∘sub≗injSub∘injTyVar {Γ1} {Γ2} (σ ∘ suc) ⊢x

-- Every type variable in an injected context can only have a local kind
var∈injCtx : ∀{Γ x κ} →
             injKndCtx Γ c⊢ₜvar x ∶ κ →
             Σ[ κₑ ∈ _ ] κ ≡ LocKnd κₑ
var∈injCtx {Γ = κₑ ∷ Γ} ⊢ₜ0 = κₑ , refl
var∈injCtx {Γ = κₑ ∷ Γ} (⊢ₜS ⊢x) = var∈injCtx ⊢x

inj∘sub≗injSub∘injTy
  : ∀{Γ1 Γ2 σ t κₑ} →
    TYSUB ⅀ₑₖ σ Γ1 Γ2 →
    Γ1 e⊢ₜ t ∶ κₑ →
    injTy (subTy ⅀ₑₖ σ t) ≡ subTy C⅀ₖ (injTySub Γ1 Γ2 σ) (injTy t)
inj∘sub≗injSub∘injTyVec
  : ∀{Γ1 Γ2 σ ts Σₑ} →
    TYSUB ⅀ₑₖ σ Γ1 Γ2 →
    Γ1 e⊢ₜvec ts ∶ Σₑ →
    injTyVec (subTyVec ⅀ₑₖ σ ts) ≡ subTyVec C⅀ₖ (injTySub Γ1 Γ2 σ) (injTyVec ts)

inj∘sub≗injSub∘injTy {Γ1} {Γ2} {σ = σ} ⊢σ (⊢ₜvar ⊢x) =
  inj∘sub≗injSub∘injTyVar {Γ1} {Γ2} σ ⊢x
inj∘sub≗injSub∘injTy ⊢σ (⊢ₜtyConstr s ⊢ts) =
  cong (tyConstr (EmbLocalTyS s)) (inj∘sub≗injSub∘injTyVec ⊢σ ⊢ts)

inj∘sub≗injSub∘injTyVec ⊢σ ⊢ₜ[] = refl
inj∘sub≗injSub∘injTyVec {Γ1} {Γ2} {σ} {(t , _) ∷ ts} {(Δₑ , κₑ) ∷ Σₑ} ⊢σ (⊢t ⊢ₜ∷ ⊢ts) =
  cong₂ (λ x y → (x , length Δₑ) ∷ y)
    (injTy (subTy ⅀ₑₖ (TyKeepSub* ⅀ₑₖ σ (length Δₑ)) t)
      ≡⟨ inj∘sub≗injSub∘injTy (⊢TyKeepSub* ⅀ₑₖ ⊢σ Δₑ) ⊢t ⟩
    subTy C⅀ₖ (injTySub (Δₑ ++ Γ1) (Δₑ ++ Γ2) (TyKeepSub* ⅀ₑₖ σ (length Δₑ))) (injTy t)
      ≡⟨ ⊢subTy-≗TySub C⅀ₖ
          (λ {x} {κ} ⊢x → Keep*-injTySub ⊢σ Δₑ $
            subst₂ (λ y z → y c⊢ₜvar x ∶ z)
              (injKndCtx-++ Δₑ Γ1)
              (var∈injCtx ⊢x .snd)
              ⊢x)
          (⊢injTy ⊢t) ⟩
    subTy C⅀ₖ (TyKeepSub* C⅀ₖ (injTySub Γ1 Γ2 σ) (length Δₑ)) (injTy t) ∎)
    (inj∘sub≗injSub∘injTyVec ⊢σ ⊢ts)

-- regain ∘ inj ∘ ⟨proj σ⟩ ≗ ⟨σ⟩ ∘ regain ∘ inj
regain∘inj∘projSub≗sub∘regain∘inj
  : ∀{Γ1 Γ2 σ t κₑ} →
    TYSUB C⅀ₖ σ Γ1 Γ2 →
    projKndCtx Γ1 e⊢ₜ t ∶ κₑ →
    regainTy (map isLocKnd Γ2) (injTy (subTy ⅀ₑₖ (projTySub Γ1 Γ2 σ) t)) ≡
    subTy C⅀ₖ σ (regainTy (map isLocKnd Γ1) (injTy t))
regain∘inj∘projSub≗sub∘regain∘inj {Γ1} {Γ2} {σ} {t} {κₑ} ⊢σ ⊢t =
  regainTy (map isLocKnd Γ2)
    (injTy (subTy ⅀ₑₖ (projTySub Γ1 Γ2 σ) t))
    ≡⟨ (cong (regainTy (map isLocKnd Γ2)) $
        inj∘sub≗injSub∘injTy (⊢projTySub ⊢σ) ⊢t) ⟩
  renTy C⅀ₖ (regainTyVar (map isLocKnd Γ2))
    (subTy C⅀ₖ
      (injTySub (projKndCtx Γ1) (projKndCtx Γ2)
        (projTySub Γ1 Γ2 σ))
    (injTy t))
    ≡⟨ subTy•◦ₜ C⅀ₖ (regainTyVar (map isLocKnd Γ2))
        (injTySub (projKndCtx Γ1) (projKndCtx Γ2)
          (projTySub Γ1 Γ2 σ))
        (injTy t) ⟩
  subTy C⅀ₖ
    (regainTy (map isLocKnd Γ2) ∘ injTy ∘ projTy (map isLocKnd Γ2)
      ∘ σ ∘ regainTyVar (map isLocKnd Γ1) ∘ projTyVar (map isLocKnd (injKndCtx (projKndCtx Γ1))))
    (injTy t)
    ≡⟨ ⊢subTy-≗TySub C⅀ₖ
        (λ {x} {κ} ⊢x → regain∘inj∘projTy≗id {κₑ = var∈injCtx ⊢x .fst} $
          ⊢σ $ ⊢regainTyVar $ ⊢injTyVar $
          subst (λ y → y e⊢ₜvar projTyVar (map isLocKnd (injKndCtx (projKndCtx Γ1))) x ∶ fst (var∈injCtx ⊢x))
            (proj∘injKndCtx≗id (projKndCtx Γ1)) $
            ⊢projTyVar $ subst (λ y → injKndCtx (projKndCtx Γ1) c⊢ₜvar x ∶ y)
                (var∈injCtx ⊢x .snd)
                ⊢x)
        (⊢injTy ⊢t) ⟩
  subTy C⅀ₖ
    (σ ∘ regainTyVar (map isLocKnd Γ1) ∘ projTyVar (map isLocKnd (injKndCtx (projKndCtx Γ1))))
    (injTy t)
    ≡⟨ (cong (λ x → subTy C⅀ₖ (σ ∘ regainTyVar (map isLocKnd Γ1) ∘ projTyVar x) (injTy t)) $
        isLocKnd∘injKndCtx≡true (projKndCtx Γ1)) ⟩
  subTy C⅀ₖ
    (σ ∘ regainTyVar (map isLocKnd Γ1) ∘ projTyVar (replicate (length (projKndCtx Γ1)) true))
    (injTy t)
    ≡⟨ subTy-ext C⅀ₖ
        (λ x → cong (σ ∘ regainTyVar (map isLocKnd Γ1)) $ 
            proj∘injTyVar≗id (length (projKndCtx Γ1)) x)
        (injTy t) ⟩
  subTy C⅀ₖ
    (σ ∘ regainTyVar (map isLocKnd Γ1))
    (injTy t)
    ≡⟨ (sym $ subTy◦•ₜ C⅀ₖ σ (regainTyVar (map isLocKnd Γ1)) (injTy t)) ⟩
  subTy C⅀ₖ σ (regainTy (map isLocKnd Γ1) (injTy t)) ∎

