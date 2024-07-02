{-# OPTIONS --safe #-}

open import Level renaming (zero to ℓ-zero; suc to ℓ-suc)
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map)
open import Data.Product.Properties
open import Data.Bool
open import Data.Nat
open import Data.Nat.Properties
open import Data.List
open import Data.List.Properties
open import Data.Maybe renaming (map to mmap)
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr) hiding (map)
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
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
open import Typing
open import TypeEquality
open import PolyPir.LocalLang

module PolyPir.Semantics
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

_⇒ₑ_ = 𝕃 .Stepₑ

{-
Choreography values

V ::= L.v | λX:τ.C | Λα:κ.C
-}
data Val (Γ : ChorKndCtx) : Tm C⅀ → Set where
  ValDone : (tₑ : Tyₑ) (L : Loc) (v : Tmₑ) → 
            (v-Val : 𝕃 .Valₑ v) →
            Val Γ (Done (injTy tₑ) (LitLoc L)
              (inj (regainTyVar (map isLocKnd Γ)) (LitLoc L) v))
  ValLam : (τ1 τ2 : CTy) (C : CTm) →
           Val Γ (Lam τ1 τ2 C)
  ValAbs : ∀{κ} (∀κ : canAbstract κ) (τ : CTy) (C : CTm) →
           Val Γ (Abs ∀κ τ C)

{-
Redices

R ::= L.(e1 ⇒ e2) | Arg(R) | Fun(R) | App | Rec
    | R {L}↝ | L1.v ↝ L2 | L1[d] ↝ L2
    | if L R | if L true | if L false
    | TFun(R) | TApp
    | let L := v | L.tell t to ρ | L.tell L' to ρ
-}
data Redex : Set where
  LocR : (L : Loc) (e1 e2 : Tmₑ) → Redex
  ArgR FunR TFunR : (R : Redex) → Redex
  AppR RecR TAppR : Redex
  SendR : (R : Redex) (L : Loc) → Redex
  SendVR : (L1 : Loc) (v : Tmₑ) (L2 : Loc) → Redex
  SyncR : (L1 : Loc) (d : Bool) (L2 : Loc) → Redex
  IfR : (L : Loc) (R : Redex) → Redex
  IfTrueR IfFalseR : (L : Loc) → Redex
  LetR : (L : Loc) (v : Tmₑ) → Redex
  TellTyR : (L : Loc) (t : Tyₑ) (ρ : List Loc) → Redex
  TellLocR : (L : Loc) (L' : Loc) (ρ : List Loc) → Redex

_∈_ : {A : Set} →
      A → List A → Set
x ∈ [] = ⊥
x ∈ (y ∷ ys) = x ≡ y ⊎ x ∈ ys

_∈loc_ : Loc → Redex → Set
L ∈loc LocR L' e1 e2 = L ≡ L'
L ∈loc ArgR R = L ∈loc R
L ∈loc FunR R = L ∈loc R
L ∈loc TFunR R = L ∈loc R
L ∈loc AppR = ⊤
L ∈loc RecR = ⊤
L ∈loc TAppR = ⊤
L ∈loc SendR R L' = L ≡ L' ⊎ L ∈loc R
L ∈loc SendVR L1 v L2 = L ≡ L1 ⊎ L ≡ L2
L ∈loc SyncR L1 d L2 = L ≡ L1 ⊎ L ≡ L2
L ∈loc IfR L' R = L ∈loc R
L ∈loc IfTrueR L' = L ≡ L'
L ∈loc IfFalseR L' = L ≡ L'
L ∈loc LetR L' v = L ≡ L'
L ∈loc TellTyR L' t ρ = L ≡ L' ⊎ (L ∈ ρ)
L ∈loc TellLocR L' L'' ρ = L ≡ L' ⊎ (L ∈ ρ)

{-
Operational semantics

-}
data _⇒[_⨾_⨾_]_ : (C1 : CTm) (Γ : ChorKndCtx) (Δ : ChorCtx) (R : Redex) (C2 : CTm) → Set where
  DoneStep : ∀{Γ Δ tₑ L e1 e2} →
            (e1⇒e2 : e1 ⇒ₑ e2) →
            Done (injTy tₑ) (LitLoc L)
              (inj (regainTyVar (map isLocKnd Γ)) (LitLoc L) e1)
              ⇒[ Γ ⨾ Δ ⨾ LocR L e1 e2 ]
            Done (injTy tₑ) (LitLoc L)
              (inj (regainTyVar (map isLocKnd Γ)) (LitLoc L) e2)

  AppFunStep : ∀{Γ Δ τ1 τ2 C1 C1' C2 R} →
                C1 ⇒[ Γ ⨾ Δ ⨾ R ] C1' →
                App τ1 τ2 C1 C2
                ⇒[ Γ ⨾ Δ ⨾ FunR R ]
                App τ1 τ2 C1' C2

  AppArgStep : ∀{Γ Δ τ1 τ2 C1 C2 C2' R} →
                C2 ⇒[ Γ ⨾ Δ ⨾ R ] C2' →
                App τ1 τ2 C1 C2
                  ⇒[ Γ ⨾ Δ ⨾ ArgR R ]
                App τ1 τ2 C1 C2'

  AppStep : ∀{Γ Δ τ1 τ2 C V} →
            (V-Val : Val Γ V) →
            App τ1 τ2 (Lam τ1 τ2 C) V
              ⇒[ Γ ⨾ Δ ⨾ AppR ]
            sub C⅀ (addSub C⅀ var V) C

  RecStep : ∀{Γ Δ τ C} →
            Fix τ C
              ⇒[ Γ ⨾ Δ ⨾ RecR ]
            sub C⅀ (addSub C⅀ var (Fix τ C)) C

  SendStep : ∀{Γ Δ L1 L2 tₑ C C' R} →
            C ⇒[ Γ ⨾ Δ ⨾ R ] C' →
            Send (LitLoc L1) C tₑ (LitLoc L2)
              ⇒[ Γ ⨾ Δ ⨾ SendR R L1 ]
            Send (LitLoc L1) C' tₑ (LitLoc L2)

  SendVStep : ∀{Γ Δ L1 L2 tₑ v} →
              (v-Val : 𝕃 .Valₑ v) →
              Send (LitLoc L1)
                (Done (injTy tₑ) (LitLoc L1) (inj (regainTyVar (map isLocKnd Γ)) (LitLoc L1) v))
                (injTy tₑ) (LitLoc L2)
                ⇒[ Γ ⨾ Δ ⨾ SendVR L1 v L2 ]
              Done (injTy tₑ) (LitLoc L2) (inj (regainTyVar (map isLocKnd Γ)) (LitLoc L2) v)

  SyncIStep : ∀{Γ Δ L1 L2 d C C' R τ} →
              C ⇒[ Γ ⨾ Δ ⨾ R ] C' →
              Sync (LitLoc L1) d (LitLoc L2) C τ
                ⇒[ Γ ⨾ Δ ⨾ R ]
              Sync (LitLoc L1) d (LitLoc L2) C' τ

  SyncStep : ∀{Γ Δ L1 L2 d C τ} →
              Sync (LitLoc L1) d (LitLoc L2) C τ
                ⇒[ Γ ⨾ Δ ⨾ SyncR L1 d L2 ]
              C

  IfStep : ∀{Γ Δ L C C' C1 C2 τ R} →
            C ⇒[ Γ ⨾ Δ ⨾ R ] C' →
            ITE (LitLoc L) C C1 C2 τ
              ⇒[ Γ ⨾ Δ ⨾ IfR L R ]
            ITE (LitLoc L) C' C1 C2 τ

  IfIStep : ∀{Γ Δ L C C1 C1' C2 C2' τ R} →
            ¬ (L ∈loc R) →
            C1 ⇒[ Γ ⨾ Δ ⨾ R ] C1' →
            C2 ⇒[ Γ ⨾ Δ ⨾ R ] C2' →
            ITE (LitLoc L) C C1 C2 τ
              ⇒[ Γ ⨾ Δ ⨾ IfR L R ]
            ITE (LitLoc L) C C1' C2' τ

  IfTrueStep : ∀{Γ Δ L C1 C2 τ} →
                ITE (LitLoc L)
                  (Done (injTy (𝕃 .Boolₑ)) (LitLoc L)
                    (inj (regainTyVar (map isLocKnd Γ)) (LitLoc L) (𝕃 .ttₑ)))
                  C1 C2 τ
                  ⇒[ Γ ⨾ Δ ⨾ IfTrueR L ]
                C1

  IfFalseStep : ∀{Γ Δ L C1 C2 τ} →
              ITE (LitLoc L)
                (Done (injTy (𝕃 .Boolₑ)) (LitLoc L)
                  (inj (regainTyVar (map isLocKnd Γ)) (LitLoc L) (𝕃 .ffₑ)))
                C1 C2 τ
                ⇒[ Γ ⨾ Δ ⨾ IfTrueR L ]
              C2

  TAppFunStep : ∀{Γ Δ κ C C' τ t R} {∀κ : canAbstract κ} →
                C ⇒[ Γ ⨾ Δ ⨾ R ] C' →
                AppTy ∀κ C τ t
                  ⇒[ Γ ⨾ Δ ⨾ FunR R ]
                AppTy ∀κ C' τ t

  TAppStep : ∀{Γ Δ κ C τ t} {∀κ : canAbstract κ} →
              AppTy ∀κ (Abs ∀κ τ C) τ t
                ⇒[ Γ ⨾ Δ ⨾ TAppR ]
              tySub C⅀ (addTySub C⅀ₖ tyVar t) C

  LocalLetArgStep : ∀{Γ Δ L C1 C1' tₑ C2 τ R} →
                    C1 ⇒[ Γ ⨾ Δ ⨾ R ] C1' →
                    LocalLet (LitLoc L) C1 (injTy tₑ) C2 τ
                      ⇒[ Γ ⨾ Δ ⨾ ArgR R ]
                    LocalLet (LitLoc L) C1' (injTy tₑ) C2 τ

  LocalLetIStep : ∀{Γ Δ L C1 tₑ C2 C2' τ R} →
                  ¬ (L ∈loc R) →
                  C2 ⇒[ Γ ⨾ (Bnd *ₑ' , Local *ₑ' (injTy tₑ) (LitLoc L)) ∷ Δ ⨾ R ] C2' →
                  LocalLet (LitLoc L) C1 (injTy tₑ) C2 τ
                    ⇒[ Γ ⨾ Δ ⨾ R ]
                  LocalLet (LitLoc L) C1 (injTy tₑ) C2' τ

  LocalLetStep : ∀{Γ Δ L v tₑ C τ} →
                  (v-Val : 𝕃 .Valₑ v) →
                  LocalLet (LitLoc L)
                    (Done (injTy tₑ) (LitLoc L) (inj (regainTyVar (map isLocKnd Γ)) (LitLoc L) v))
                    (injTy tₑ) C τ
                    ⇒[ Γ ⨾ Δ ⨾ LetR L v ]
                  sub C⅀ (addSub C⅀ var (inj (regainTyVar (map isLocKnd Γ)) (LitLoc L) v)) C

  TellLetTyArgStep : ∀{Γ Δ L C1 C1' ρ C2 τ R} →
                    C1 ⇒[ Γ ⨾ Δ ⨾ R ] C1' →
                    TellTy (LitLoc L) C1 (LitSet ρ) C2 τ
                      ⇒[ Γ ⨾ Δ ⨾ ArgR R ]
                    TellTy (LitLoc L) C1' (LitSet ρ) C2 τ

  TellLetTyIStep : ∀{Γ Δ L C1 ρ C2 C2' τ R} →
                    ¬ (L ∈loc R) →
                    (∀ L' → L' ∈ ρ → L' ∈loc R → ⊥) →
                    C2 ⇒[ *ₑ ∷ Γ ⨾ renCtx C⅀ₖ (Drop id) Δ ⨾ R ] C2' →
                    TellTy (LitLoc L) C1 (LitSet ρ) C2 τ
                      ⇒[ Γ ⨾ Δ ⨾ R ]
                    TellTy (LitLoc L) C1 (LitSet ρ) C2' τ

  TellLetTyStep : ∀{Γ Δ L tₑ ρ C2 τ} →
                  TellTy (LitLoc L) (inj (regainTyVar (map isLocKnd Γ)) (LitLoc L) tₑ) (LitSet ρ) C2 τ
                    ⇒[ Γ ⨾ Δ ⨾ TellTyR L (𝕃 .Elₑ tₑ) ρ ]
                  tySub C⅀ (addTySub C⅀ₖ tyVar (injTy (𝕃 .Elₑ tₑ))) C2

  TellLetLocArgStep : ∀{Γ Δ L C1 C1' ρ C2 τ R} →
                    C1 ⇒[ Γ ⨾ Δ ⨾ R ] C1' →
                    TellLoc (LitLoc L) C1 (LitSet ρ) C2 τ
                      ⇒[ Γ ⨾ Δ ⨾ ArgR R ]
                    TellLoc (LitLoc L) C1' (LitSet ρ) C2 τ

  TellLetLocIStep : ∀{Γ Δ L C1 ρ C2 C2' τ R} →
                    ¬ (L ∈loc R) →
                    (∀ L' → L' ∈ ρ → L' ∈loc R → ⊥) →
                    C2 ⇒[ *ₗ ∷ Γ ⨾ renCtx C⅀ₖ (Drop id) Δ ⨾ R ] C2' →
                    TellLoc (LitLoc L) C1 (LitSet ρ) C2 τ
                      ⇒[ Γ ⨾ Δ ⨾ R ]
                    TellLoc (LitLoc L) C1 (LitSet ρ) C2' τ
                    
  TellLetLocStep : ∀{Γ Δ L L' ρ C2 τ} →
                  TellLoc (LitLoc L) (inj (regainTyVar (map isLocKnd Γ)) (LitLoc L) (𝕃 .litLocₑ L')) (LitSet ρ) C2 τ
                    ⇒[ Γ ⨾ Δ ⨾  TellLocR L L' ρ ]
                  tySub C⅀ (addTySub C⅀ₖ tyVar (LitLoc L')) C2

Done-inj : ∀{t1ₑ ℓ1 e1 t2ₑ ℓ2 e2} →
           Done t1ₑ ℓ1 e1 ≡ Done t2ₑ ℓ2 e2 →
           t1ₑ ≡ t2ₑ ×
           ℓ1 ≡ ℓ2 ×
           e1 ≡ e2
Done-inj refl = refl , refl , refl

regainTyVar-inj : (Γ : List Bool) →
                  Injective _≡_ _≡_ (regainTyVar Γ)
regainTyVar-inj [] = id
regainTyVar-inj (true ∷ Γ) = Keep-inj (regainTyVar-inj Γ)
regainTyVar-inj (false ∷ Γ) = Drop-inj (regainTyVar-inj Γ)

Val-Done-elim : ∀{Γ C tₑ L v} →
                Val Γ C →
                C ≡ Done (injTy tₑ) (LitLoc L)
                      (inj (regainTyVar (map isLocKnd Γ)) (LitLoc L) v) →
                𝕃 .Valₑ v
Val-Done-elim {Γ} (ValDone tₑ L v v-Val) p with Done-inj p
... | _ , refl , q =
  subst (𝕃 .Valₑ)
    (inj-injective (regainTyVar-inj (map isLocKnd Γ)) (tyConstr (LitLocS L) []) q)
    v-Val

-- Values cannot step
valNoStep : ∀{Γ Δ R C1 C2} → Val Γ C1 → ¬ (C1 ⇒[ Γ ⨾ Δ ⨾ R ] C2)
valNoStep C1-Val (DoneStep e1⇒e2) =
  𝕃 .valNoStepₑ (Val-Done-elim C1-Val refl) e1⇒e2

Preservation : ∀{Γ Δ C1 C2 t R} →
               Γ ⨾ Δ c⊢ C1 ∶ t →
               C1 ⇒[ Γ ⨾ Δ ⨾ R ] C2 →
               Γ ⨾ Δ c⊢ C2 ∶ t
Preservation (⊢constr DoneS (⊢tₑ ⊢ₜ∷ ⊢L ⊢ₜ∷ ⊢ₜ[]) (⊢e1 ⊢∷ ⊢[] ⊢Δ)) (DoneStep e1⇒e2) =
  ⊢constr DoneS (⊢tₑ ⊢ₜ∷ ⊢L ⊢ₜ∷ ⊢ₜ[]) ({! ⊢injTy⁻  !} ⊢∷ ⊢[] ⊢Δ)
{-
⊢e1 : Γ ⨾ renCtx (C⅀ .⅀ₖ) id Δ
      inj (regainTyVar (map isLocKnd Γ)) (LitLoc L) e1
      ∶ (Bnd *ₑ' , Local *ₑ' (injTy tₑ) (tyConstr (LitLocS L) []))

? : Γ ⨾ renCtx (C⅀ .⅀ₖ) id Δ
    ⊢ inj (regainTyVar (map isLocKnd Γ)) (LitLoc L) e2
    ∶ (Bnd *ₑ' , Local *ₑ' (injTy tₑ) (tyConstr (LitLocS L) []))
-}
Preservation {Γ} {Δ} (⊢constr AppS (⊢τ1 ⊢ₜ∷ ⊢τ2 ⊢ₜ∷ ⊢ₜ[]) (⊢C1 ⊢∷ ⊢C2 ⊢∷ ⊢[] ⊢Δ))
  (AppFunStep {C1 = C1} {C1'} {R = R} C1⇒C1') =
  let step = subst (λ x → C1 ⇒[ Γ ⨾ x ⨾ R ] C1') (sym $ renCtxId C⅀ₖ Δ) C1⇒C1'
  in ⊢constr AppS (⊢τ1 ⊢ₜ∷ ⊢τ2 ⊢ₜ∷ ⊢ₜ[]) (Preservation ⊢C1 step ⊢∷ ⊢C2 ⊢∷ ⊢[] ⊢Δ)
Preservation {Γ} {Δ} (⊢constr AppS (⊢τ1 ⊢ₜ∷ ⊢τ2 ⊢ₜ∷ ⊢ₜ[]) (⊢C1 ⊢∷ ⊢C2 ⊢∷ ⊢[] ⊢Δ))
  (AppArgStep {C2 = C2} {C2'} {R = R} C2⇒C2') =
  let step = subst (λ x → C2 ⇒[ Γ ⨾ x ⨾ R ] C2') (sym $ renCtxId C⅀ₖ Δ) C2⇒C2'
  in ⊢constr AppS (⊢τ1 ⊢ₜ∷ ⊢τ2 ⊢ₜ∷ ⊢ₜ[]) (⊢C1 ⊢∷ Preservation ⊢C2 step ⊢∷ ⊢[] ⊢Δ)
Preservation {Γ} {Δ} (⊢constr AppS (⊢τ1 ⊢ₜ∷ ⊢τ2 ⊢ₜ∷ ⊢ₜ[]) (⊢C ⊢∷ ⊢V ⊢∷ ⊢[] ⊢Δ))
  (AppStep {τ1 = τ1} {V = V} V-Val) =
    ⊢sub C⅀
      (⊢▸ ≗-refl
        (subst (λ x → SUB C⅀ var Γ x Δ) (sym $ renCtxId C⅀ₖ Δ) $ ⊢IdSub C⅀ ⊢Δ)
        (subst (λ x → Γ ⨾ x c⊢ V ∶ (* , τ1)) (renCtxId C⅀ₖ Δ) ⊢V))
      (⊢Lam⁻ ⊢C .snd .snd)
Preservation {Γ} {Δ} ⊢μC@(⊢constr FixS (⊢τ1 ⊢ₜ∷ ⊢ₜ[]) (⊢C ⊢∷ ⊢[] ⊢Δ)) RecStep =
  ⊢sub C⅀
    (⊢▸ ≗-refl
      (subst (λ x → SUB C⅀ var Γ x Δ) (sym $ renCtxId C⅀ₖ Δ) $ ⊢IdSub C⅀ ⊢Δ)
      ⊢μC)
    ⊢C
Preservation {Γ} {Δ} (⊢constr SendS (⊢L1 ⊢ₜ∷ ⊢L2 ⊢ₜ∷ ⊢tₑ ⊢ₜ∷ ⊢ₜ[]) (⊢C ⊢∷ ⊢[] ⊢Δ))
  (SendStep {C = C} {C'} {R} C⇒C') =
  let step = subst (λ x → C ⇒[ Γ ⨾ x ⨾ R ] C') (sym $ renCtxId C⅀ₖ Δ) C⇒C'
  in ⊢constr SendS (⊢L1 ⊢ₜ∷ ⊢L2 ⊢ₜ∷ ⊢tₑ ⊢ₜ∷ ⊢ₜ[]) (Preservation ⊢C step ⊢∷ ⊢[] ⊢Δ)
Preservation (⊢constr .SendS (⊢L1 ⊢ₜ∷ ⊢L2 ⊢ₜ∷ ⊢ts) (⊢e ⊢∷ ⊢[] ⊢Δ))
  (SendVStep v-Val) = ⊢Done ⊢L2 {!   !}
{-
? : Γ ⨾ Δ
    c⊢ inj (regainTyVar (map isLocKnd Γ)) (LitLoc L2) v
    ∶ (Bnd *ₑ' , Local *ₑ' (injTy tₑ) (tyConstr (LitLocS L2) []))

⊢Done⁻ ⊢e .snd
  : Γ ⨾ renCtx (C⅀ .⅀ₖ) id Δ
    c⊢ inj (regainTyVar (map isLocKnd Γ)) (LitLoc L1) v
    ∶ (Bnd *ₑ' , Local *ₑ' (injTy tₑ) (tyConstr (LitLocS L1) []))
    -}
Preservation ⊢C1 (SyncIStep C1⇒C2) = {!   !}
Preservation ⊢C1 SyncStep = {!   !}
Preservation ⊢C1 (IfStep C1⇒C2) = {!   !}
Preservation ⊢C1 (IfIStep L∉R C1⇒C2 C1⇒C3) = {!   !}
Preservation ⊢C1 IfTrueStep = {!   !}
Preservation ⊢C1 IfFalseStep = {!   !}
Preservation ⊢C1 (TAppFunStep C1⇒C2) = {!   !}
Preservation ⊢C1 TAppStep = {!   !}
Preservation ⊢C1 (LocalLetArgStep C1⇒C2) = {!   !}
Preservation ⊢C1 (LocalLetIStep L∉R C1⇒C2) = {!   !}
Preservation ⊢C1 (LocalLetStep v-Val) = {! x !}
Preservation ⊢C1 (TellLetTyArgStep C1⇒C2) = {!   !}
Preservation ⊢C1 (TellLetTyIStep L∉R ρ∉R C1⇒C2) = {!   !}
Preservation ⊢C1 TellLetTyStep = {!   !}
Preservation ⊢C1 (TellLetLocArgStep C1⇒C2) = {!   !}
Preservation ⊢C1 (TellLetLocIStep L∉R ρ∉R C1⇒C2) = {!   !}
Preservation ⊢C1 TellLetLocStep = {!   !}  
 