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
Tyₑ      = Ty ⅀ₑₖ

_e⊢ₜvar_∶_ : List Kndₑ → ℕ → Kndₑ → Set
_e⊢ₜvar_∶_ = varKinded ⅀ₑₖ

_e⊢ₜ_∶_ : List Kndₑ → Tyₑ → Kndₑ → Set
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

LocalS-inj : ∀{κₑ κₑ'} → LocalS κₑ ≡ LocalS κₑ' → κₑ ≡ κₑ'
LocalS-inj refl = refl

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

⊢Local⁻ : ∀{Γ κₑ tₑ ℓ} →
          Γ c⊢ₜ Local κₑ tₑ ℓ ∶ Bnd κₑ →
          Γ c⊢ₜ tₑ ∶ LocKnd κₑ ×
          Γ c⊢ₜ ℓ ∶ *ₗ
⊢Local⁻ {κₑ = κₑ} (⊢ₜtyConstr .(LocalS κₑ) (⊢tₑ ⊢ₜ∷ ⊢ℓ ⊢ₜ∷ ⊢ₜ[])) = ⊢tₑ , ⊢ℓ

At : (tₑ : CTy) (ℓ : CTy) → CTy
At tₑ ℓ = tyConstr AtS ((tₑ , 0) ∷ (ℓ , 0) ∷ [])

⊢At : ∀{Γ tₑ ℓ} →
      Γ c⊢ₜ tₑ ∶ *ₑ →
      Γ c⊢ₜ ℓ ∶ *ₗ →
      Γ c⊢ₜ At tₑ ℓ ∶ *
⊢At ⊢tₑ ⊢ℓ = ⊢ₜtyConstr AtS (⊢tₑ ⊢ₜ∷ ⊢ℓ ⊢ₜ∷ ⊢ₜ[])

⊢At⁻ : ∀{Γ tₑ ℓ} →
        Γ c⊢ₜ At tₑ ℓ ∶ * →
        Γ c⊢ₜ tₑ ∶ *ₑ × Γ c⊢ₜ ℓ ∶ *ₗ
⊢At⁻ (⊢ₜtyConstr AtS (⊢tₑ ⊢ₜ∷ ⊢ℓ ⊢ₜ∷ ⊢ₜ[])) =
  ⊢tₑ , ⊢ℓ

Fun : (τ1 τ2 : CTy) → CTy
Fun τ1 τ2 = tyConstr FunS ((τ1 , 0) ∷ (τ2 , 0) ∷ [])

⊢Fun : ∀{Γ τ1 τ2} →
        Γ c⊢ₜ τ1 ∶ * →
        Γ c⊢ₜ τ2 ∶ * →
        Γ c⊢ₜ Fun τ1 τ2 ∶ *
⊢Fun ⊢τ1 ⊢τ2 = ⊢ₜtyConstr FunS (⊢τ1 ⊢ₜ∷ ⊢τ2 ⊢ₜ∷ ⊢ₜ[])

⊢Fun⁻ : ∀{Γ τ1 τ2} →
        Γ c⊢ₜ Fun τ1 τ2 ∶ * →
        Γ c⊢ₜ τ1 ∶ * × Γ c⊢ₜ τ2 ∶ *
⊢Fun⁻ (⊢ₜtyConstr .FunS (⊢τ1 ⊢ₜ∷ ⊢τ2 ⊢ₜ∷ ⊢ₜ[])) =
  ⊢τ1 , ⊢τ2

All : ∀{κ} (∀κ : canAbstract κ) (τ : CTy) → CTy
All {κ} ∀κ τ = tyConstr (AllS κ ∀κ) ((τ , 1) ∷ [])

⊢All : ∀{Γ κ τ} →
      (∀κ : canAbstract κ) →
      (κ ∷ Γ) c⊢ₜ τ ∶ * →
      Γ c⊢ₜ All ∀κ τ ∶ *
⊢All {κ = κ} ∀κ ⊢τ =
  ⊢ₜtyConstr (AllS κ ∀κ) (⊢τ ⊢ₜ∷ ⊢ₜ[])

⊢All⁻ : ∀{Γ κ ∀κ τ} →
        Γ c⊢ₜ All {κ} ∀κ τ ∶ * →
        (κ ∷ Γ) c⊢ₜ τ ∶ *
⊢All⁻ (⊢ₜtyConstr (AllS κ ∀κ) (⊢τ ⊢ₜ∷ ⊢ₜ[])) = ⊢τ

LitLoc : (L : Loc) → CTy
LitLoc L = tyConstr (LitLocS L) []

⊢LitLoc : ∀{Γ} (L : Loc) → Γ c⊢ₜ LitLoc L ∶ *ₗ
⊢LitLoc L = ⊢ₜtyConstr (LitLocS L) ⊢ₜ[]

LitLoc-inj : Injective _≡_ _≡_ LitLoc
LitLoc-inj refl = refl

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

LitSet : (ρ : List Loc) → CTy
LitSet [] = Emp
LitSet (L ∷ ρ) =
  Union
    (Sng (LitLoc L))
    (LitSet ρ)

⊢LitSet : ∀{Γ} (ρ : List Loc) → Γ c⊢ₜ LitSet ρ ∶ *ₛ
⊢LitSet [] = ⊢Emp
⊢LitSet (L ∷ ρ) =
  ⊢Union
    (⊢Sng (⊢LitLoc L))
    (⊢LitSet ρ)
