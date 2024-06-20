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
open import Typing
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

{-
Values

V ::= X | ℓ.v | λX:τ.C | Λα:κ.C
-}
data Val : Tm C⅀ → Set where
  ValVar : (x : ℕ) → Val (var x)
  ValDone : (tₑ : CTy) (ℓ : CTy) (v : CTm) → 
            𝕃 .Valₑ {!   !} →
            Val (Done tₑ ℓ v)
  ValLam : (τ1 τ2 : CTy) (C : CTm) → Val (Lam τ1 τ2 C)
  ValAbs : ∀{κ} (∀κ : canAbstract κ) (τ : CTy) (C : CTm) → Val (Abs ∀κ τ C)

{-
Process names in types

pn(α) = ∅
pn(tₑ) = ∅
pn(t @ ℓ) = {ℓ}
pn(τ1 → τ2) = pn(τ1) ∪ pn(τ2)
pn(∀α:*ₑ.τ) = pn(τ)
pn(∀α:*.τ) = ℒ
pn(∀α:*ₗ.τ) = ℒ
pn(∀α:*ₛ.τ) = ℒ
pn(L) = {L}
pn(∅) = ∅
pn({ℓ}) = {ℓ}
pn(ρ1 ∪ ρ2) = pn(ρ1) ∪ pn(ρ2)

TODO: Verify definition
-}
tyProcessNames : CTy → CTy → Set
tyProcessNames (tyVar x) ℓ' = ⊥
tyProcessNames (tyConstr (EmbLocalTyS sₑ) ts) ℓ' = ⊥
tyProcessNames (tyConstr (LocalS κₑ) ((tₑ , 0) ∷ (ℓ , 0) ∷ [])) ℓ' = ℓ' ≡ ℓ
tyProcessNames (tyConstr AtS ((tₑ , 0) ∷ (ℓ , 0) ∷ [])) ℓ' = ℓ' ≡ ℓ
tyProcessNames (tyConstr FunS ((τ1 , 0) ∷ (τ2 , 0) ∷ [])) ℓ' =
  tyProcessNames τ1 ℓ' ⊎ tyProcessNames τ2 ℓ'
tyProcessNames (tyConstr (AllS (LocKnd κₑ) tt) ((τ , 1) ∷ [])) ℓ' = 
  tyProcessNames τ (renTy C⅀ₖ (Drop id) ℓ')
tyProcessNames (tyConstr (AllS * tt) ((τ , 1) ∷ [])) ℓ' = ⊤
tyProcessNames (tyConstr (AllS *ₗ tt) ((τ , 1) ∷ [])) ℓ' = ⊤
tyProcessNames (tyConstr (AllS *ₛ tt) ((τ , 1) ∷ [])) ℓ' = ⊤
tyProcessNames (tyConstr (LitLocS L) []) ℓ' = ℓ' ≡ tyConstr (LitLocS L) []
tyProcessNames (tyConstr EmpS []) ℓ' = ⊥
tyProcessNames (tyConstr SngS ((ℓ , 0) ∷ [])) ℓ' = tyProcessNames ℓ ℓ'
tyProcessNames (tyConstr UnionS ((ρ1 , 0) ∷ (ρ2 , 0) ∷ [])) ℓ' =
  tyProcessNames ρ1 ℓ' ⊎ tyProcessNames ρ2 ℓ'
tyProcessNames _ _ = ⊥

{-
Process names in terms

pn(X) = ∅
pn(e) = ∅
pn(ℓ.e) = {ℓ}
pn(λX:τ.C) = pn(τ) ∪ pn(C)
pn(μX:τ.C) = pn(τ) ∪ pn(C)
pn(C1 C2) = pn(C1) ∪ pn(C2)
pn(Λα:*ₑ.C) = pn(C)
pn(Λα:*.C) = ℒ
pn(Λα:*ₗ.C) = ℒ
pn(Λα:*ₛ.C) = ℒ
pn(C [T]) = pn(C) ∪ pn(T)
pn(ℓ1.C ↝ ℓ2) = {ℓ1,ℓ2} ∪ pn(C)
pn(ℓ1[d] ↝ ℓ2; C) = {ℓ1,ℓ2} ∪ pn(C)
pn(ℓ.if C1 then C2 else C3) = {ℓ} ∪ pn(C1) ∪ pn(C2) ∪ pn(C3)
pn(let ℓ.x := C1 in C2) = {ℓ1} ∪ pn(C1) ∪ pn(C2)
pn(ℓ.tell α : *ₑ := C1 to ρ in C2) = {ℓ} ∪ pn(ρ) ∪ pn(C1) ∪ pn(C2)
pn(ℓ.tell α : *ₗ := C1 to ρ in C2) = {ℓ} ∪ pn(ρ) ∪ pn(C1) ∪ pn(C2)

TODO: Verify definition
-}
processNames : CTm → CTy → Set
processNames (var x) ℓ' = ⊥ 
processNames (constr (LocalS sₑ) ((ℓ , 0) ∷ ts) es) ℓ' = ℓ' ≡ ℓ
processNames (constr DoneS ((tₑ , 0) ∷ (ℓ , 0) ∷ []) ((e , 0 , 0) ∷ [])) ℓ' = ℓ' ≡ ℓ
processNames (constr LamS ((τ1 , 0) ∷ (τ2 , 0) ∷ []) ((C , 0 , 1) ∷ [])) ℓ' =
  tyProcessNames τ1 ℓ' ⊎ processNames C ℓ'
processNames (constr FixS ((τ , 0) ∷ []) ((C , 0 , 1) ∷ [])) ℓ' =
  tyProcessNames τ ℓ' ⊎ processNames C ℓ'
processNames (constr AppS ((τ1 , 0) ∷ (τ2 , 0) ∷ []) ((C1 , 0 , 0) ∷ (C2 , 0 , 0) ∷ [])) ℓ' =
  processNames C1 ℓ' ⊎ processNames C2 ℓ'
processNames (constr (AbsS (LocKnd κₑ) tt) ((τ , 1) ∷ []) ((C , 1 , 0) ∷ [])) ℓ' =
  processNames C (renTy C⅀ₖ (Drop id) ℓ')
processNames (constr (AbsS * tt) ((τ , 1) ∷ []) ((C , 1 , 0) ∷ [])) ℓ' = ⊤
processNames (constr (AbsS *ₗ tt) ((τ , 1) ∷ []) ((C , 1 , 0) ∷ [])) ℓ' = ⊤
processNames (constr (AbsS *ₛ tt) ((τ , 1) ∷ []) ((C , 1 , 0) ∷ [])) ℓ' = ⊤
processNames (constr (AppTyS κ ∀κ) ((τ , 1) ∷ (T , 0) ∷ []) ((C , 0 , 0) ∷ [])) ℓ' =
  processNames C ℓ' ⊎ tyProcessNames T ℓ'
processNames (constr SendS ((ℓ1 , 0) ∷ (ℓ2 , 0) ∷ (tₑ , 0) ∷ []) ((C , 0 , 0) ∷ [])) ℓ' =
  ℓ' ≡ ℓ1 ⊎ ℓ' ≡ ℓ2 ⊎ processNames C ℓ'
processNames (constr (SyncS d) ((ℓ1 , 0) ∷ (ℓ2 , 0) ∷ (τ , 0) ∷ []) ((C , 0 , 0) ∷ [])) ℓ' =
  ℓ' ≡ ℓ1 ⊎ ℓ' ≡ ℓ2 ⊎ processNames C ℓ'
processNames (constr ITES ((ℓ , 0) ∷ (τ , 0) ∷ []) ((C1 , 0 , 0) ∷ (C2 , 0 , 0) ∷ (C3 , 0 , 0) ∷ [])) ℓ' =
  ℓ' ≡ ℓ ⊎ processNames C1 ℓ' ⊎ processNames C2 ℓ' ⊎ processNames C3 ℓ'
processNames (constr LocalLetS ((ℓ , 0) ∷ (tₑ , 0) ∷ (τ , 0) ∷ []) ((C1 , 0 , 0) ∷ (C2 , 0 , 1) ∷ [])) ℓ' =
  ℓ' ≡ ℓ ⊎ processNames C1 ℓ' ⊎ processNames C2 ℓ'
processNames (constr TellTyS ((ℓ , 0) ∷ (ρ , 0) ∷ (τ , 0) ∷ []) ((C1 , 0 , 0) ∷ (C2 , 1 , 0) ∷ [])) ℓ' =
  ℓ' ≡ ℓ ⊎ tyProcessNames τ ℓ' ⊎ processNames C1 ℓ' ⊎ processNames C2 ℓ'
processNames (constr TellLocS ((ℓ , 0) ∷ (ρ , 0) ∷ (τ , 0) ∷ []) ((C1 , 0 , 0) ∷ (C2 , 1 , 0) ∷ [])) ℓ' =
  ℓ' ≡ ℓ ⊎ tyProcessNames τ ℓ' ⊎ processNames C1 ℓ' ⊎ processNames C2 ℓ'
processNames _ _ = ⊥

{-
Synchronizing process names in terms

spn(X) = ∅
spn(e) = ∅
spn(ℓ.e) = ∅
spn(λX:τ.C) = spn(C)
spn(μX:τ.C) = spn(C)
spn(C1 C2) = spn(C1) ∪ spn(C2)
spn(Λα:κ.C) = spn(C)
spn(C [T]) = spn(C)
spn(ℓ1.C ↝ ℓ2) = {ℓ1,ℓ2} ∪ spn(C)
spn(ℓ1[d] ↝ ℓ2; C) = {ℓ1,ℓ2} ∪ spn(C)
spn(ℓ.if C1 then C2 else C3) = spn(C1) ∪ spn(C2) ∪ spn(C3)
spn(let ℓ.x := C1 in C2) = spn(C1) ∪ spn(C2)
spn(ℓ.tell α : *ₑ := C1 to ρ in C2) = {ℓ} ∪ pn(ρ) ∪ spn(C1) ∪ spn(C2)
spn(ℓ.tell α : *ₗ := C1 to ρ in C2) = {ℓ} ∪ pn(ρ) ∪ spn(C1) ∪ spn(C2)

TODO: Verify definition
-}
syncProcessNames : CTm → CTy → Set
syncProcessNames (var x) ℓ' = ⊥ 
syncProcessNames (constr (LocalS sₑ) ((ℓ , 0) ∷ ts) es) ℓ' = ⊥
syncProcessNames (constr DoneS ((tₑ , 0) ∷ (ℓ , 0) ∷ []) ((e , 0 , 0) ∷ [])) ℓ' = ⊥
syncProcessNames (constr LamS ((τ1 , 0) ∷ (τ2 , 0) ∷ []) ((C , 0 , 1) ∷ [])) ℓ' =
  syncProcessNames C ℓ'
syncProcessNames (constr FixS ((τ , 0) ∷ []) ((C , 0 , 1) ∷ [])) ℓ' =
  syncProcessNames C ℓ'
syncProcessNames (constr AppS ((τ1 , 0) ∷ (τ2 , 0) ∷ []) ((C1 , 0 , 0) ∷ (C2 , 0 , 0) ∷ [])) ℓ' =
  syncProcessNames C2 ℓ'
syncProcessNames (constr (AbsS κ ∀κ) ((τ , 1) ∷ []) ((C , 1 , 0) ∷ [])) ℓ' = 
  syncProcessNames C (renTy C⅀ₖ (Drop id) ℓ')
syncProcessNames (constr (AppTyS κ ∀κ) ((τ , 1) ∷ (T , 0) ∷ []) ((C , 0 , 0) ∷ [])) ℓ' =
  syncProcessNames C ℓ'
syncProcessNames (constr SendS ((ℓ1 , 0) ∷ (ℓ2 , 0) ∷ (tₑ , 0) ∷ []) ((C , 0 , 0) ∷ [])) ℓ' =
  ℓ' ≡ ℓ1 ⊎ ℓ' ≡ ℓ2 ⊎ syncProcessNames C ℓ'
syncProcessNames (constr (SyncS d) ((ℓ1 , 0) ∷ (ℓ2 , 0) ∷ (τ , 0) ∷ []) ((C , 0 , 0) ∷ [])) ℓ' =
  ℓ' ≡ ℓ1 ⊎ ℓ' ≡ ℓ2 ⊎ syncProcessNames C ℓ'
syncProcessNames (constr ITES ((ℓ , 0) ∷ (τ , 0) ∷ []) ((C1 , 0 , 0) ∷ (C2 , 0 , 0) ∷ (C3 , 0 , 0) ∷ [])) ℓ' =
  syncProcessNames C1 ℓ' ⊎ syncProcessNames C2 ℓ' ⊎ syncProcessNames C3 ℓ'
syncProcessNames (constr LocalLetS ((ℓ , 0) ∷ (tₑ , 0) ∷ (τ , 0) ∷ []) ((C1 , 0 , 0) ∷ (C2 , 0 , 1) ∷ [])) ℓ' =
  syncProcessNames C1 ℓ' ⊎ syncProcessNames C2 ℓ'
syncProcessNames (constr TellTyS ((ℓ , 0) ∷ (ρ , 0) ∷ (τ , 0) ∷ []) ((C1 , 0 , 0) ∷ (C2 , 1 , 0) ∷ [])) ℓ' =
  ℓ' ≡ ℓ ⊎ tyProcessNames τ ℓ' ⊎ syncProcessNames C1 ℓ' ⊎ syncProcessNames C2 ℓ'
syncProcessNames (constr TellLocS ((ℓ , 0) ∷ (ρ , 0) ∷ (τ , 0) ∷ []) ((C1 , 0 , 0) ∷ (C2 , 1 , 0) ∷ [])) ℓ' =
  ℓ' ≡ ℓ ⊎ tyProcessNames τ ℓ' ⊎ syncProcessNames C1 ℓ' ⊎ syncProcessNames C2 ℓ'
syncProcessNames _ _ = ⊥

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
data _⇝_ : CTm → CTm → Set where
  AbsR : {τ2 τ3 s : CTy} (C1 C2 C3 : CTm) →
          App τ3 s (App τ2 (Fun τ3 s) (Lam τ2 (Fun τ3 s) C1) C2) C3 ⇝
          App τ2 s (Lam τ2 s (App τ3 s C1 (ren C⅀ (Drop id) C3))) C2

  AbsL : ∀{τ2 τ3 s : CTy} (C1 C2 C3 : CTm) →
         (∀ ℓ → syncProcessNames C1 ℓ → processNames C2 ℓ → ⊥) →
         App τ2 s C1 (App τ3 τ2 (Lam τ3 τ2 C2) C3) ⇝
         App τ3 s (Lam τ3 s (App τ2 s (ren C⅀ (Drop id) C1) C2)) C3

⊢⇝ : ∀{Γ Δ C1 C2 t} →
      Γ ⨾ Δ c⊢ C1 ∶ t →
      C1 ⇝ C2 →
      Γ ⨾ Δ c⊢ C2 ∶ t
⊢⇝ ⊢C123 (AbsR {τ2} {τ3} {s} C1 C2 C3) with ⊢App⁻ ⊢C123
... | refl , refl , ⊢C12 , ⊢C3 with ⊢App⁻ ⊢C12
... | refl , refl , ⊢λC1 , ⊢C2 with ⊢Lam⁻ ⊢λC1
... | refl , refl , ⊢C1 =
  ⊢App (⊢Lam (⊢App ⊢C1 (⊢ren C⅀ (⊢Drop C⅀ (⊢IdRen C⅀ (⊢⇒⊢ctx C⅀ ⊢C2)) (⊢⇒⊢typ C⅀ ⊢C2)) ⊢C3))) ⊢C2
⊢⇝ ⊢C123 (AbsL {τ2} {τ3} {s} C1 C2 C3 spn-pn-disj) with ⊢App⁻ ⊢C123
... | refl , refl , ⊢C1 , ⊢C23 with ⊢App⁻ ⊢C23
... | refl , refl , ⊢λC2 , ⊢C3 with ⊢Lam⁻ ⊢λC2
... | refl , refl , ⊢C2 =
  ⊢App (⊢Lam (⊢App (⊢ren C⅀ (⊢Drop C⅀ (⊢IdRen C⅀ (⊢⇒⊢ctx C⅀ ⊢C1)) (⊢⇒⊢typ C⅀ ⊢C3)) ⊢C1) ⊢C2)) ⊢C3

data _⇝*_ : CTm → CTm → Set where
  ⇝*Z : ∀{C} → C ⇝* C
  ⇝*S : ∀{C1 C2 C3} → C1 ⇝ C2 → C2 ⇝* C3 → C1 ⇝* C3

⊢⇝* : ∀{Γ Δ C1 C2 t} →
      Γ ⨾ Δ c⊢ C1 ∶ t →
      C1 ⇝* C2 →
      Γ ⨾ Δ c⊢ C2 ∶ t
⊢⇝* ⊢C1 ⇝*Z = ⊢C1
⊢⇝* ⊢C1 (⇝*S C1⇝C2 C2⇝*C3) =
  ⊢⇝* (⊢⇝ ⊢C1 C1⇝C2) C2⇝*C3

data ProcLabel : Set where
  ∅ : ProcLabel
  Comm : CTy → CTy → ProcLabel

labelDisjoint : ProcLabel → (CTy → Set) → Set
labelDisjoint ∅ P = ⊤
labelDisjoint (Comm ℓ1 ℓ2) P = ¬ (P ℓ1) × ¬ (P ℓ2)

data AbsLabel : Set where
  ƛ : AbsLabel
  τℓ : AbsLabel

{-
Choreography semantics

[AppAbs]
(λx:τ1.C1) C2 ⇒[τ,∅] C1[x ↦ C2]

[InAbs]
C ⇒[ℓ,P] C'
-----------------------
λx:τ1.C ⇒[ƛ,P] λx:τ1.C'

[App1]
C1 ⇒[ℓ,P] C1'
ℓ = ƛ ⇒ P ∩ pn(C2) ≡ ∅
----------------------
C1 C2 ⇒[τ,P] C1' C2

[App2]
Val V1
C2 ⇒[τ,P] C2'
-------------------
V1 C2 ⇒[τ,P] V1 C2'

[App3]
C2 ⇒[τ,P] C2'
P ∩ pn(C1) ≡ ∅
-------------------
C1 C2 ⇒[τ,P] C1 C2'

[FixAbs]
μx:τ.C ⇒[τ,∅] C[x ↦ μx:τ.C]

[SendAbs]
ℓ1.v ⇝ ℓ2 ⇒[τ,{ℓ1,ℓ2}] ℓ2.v

[ITEAbsT]
ITE ℓ1.true C1 C2 ⇒[τ,∅] C1

[ITEAbsF]
ITE ℓ1.false C1 C2 ⇒[τ,∅] C2

[Str]
C1 ⇝* C2
C2 ⇒[τ,P] C3
-------------
C1 ⇒[τ,P] C3

TODO: Finish definition
TODO: Verify definition
-}
data _⇒[_,_]_ : CTm → AbsLabel → ProcLabel → CTm → Set where
  AppAbs : ∀{C1 C2 τ1 τ2} →
           App τ1 τ2 (Lam τ1 τ2 C1) C2
            ⇒[ τℓ , ∅ ]
           sub C⅀ (addSub C⅀ var C2) C1

  InAbs : ∀{C C' τ1 τ2 ℓ P} →
          C ⇒[ ℓ , P ] C' →
          Lam τ1 τ2 C ⇒[ ƛ , P ] Lam τ1 τ2 C'

  App1 : ∀{C1 C1' C2 τ1 τ2 ℓ P} →
          (ℓ ≡ ƛ → labelDisjoint P (processNames C2)) →
          C1 ⇒[ ℓ , P ] C1' →
          App τ1 τ2 C1 C2 ⇒[ τℓ , P ] App τ1 τ2 C1' C2

  App2 : ∀{V1 C2 C2' τ1 τ2 P} →
          Val V1 →
          C2 ⇒[ τℓ , P ] C2' →
          App τ1 τ2 V1 C2 ⇒[ τℓ , P ] App τ1 τ2 V1 C2'

  App3 : ∀{C1 C2 C2' τ1 τ2 P} →
          labelDisjoint P (processNames C1) →
          C2 ⇒[ τℓ , P ] C2' →
          App τ1 τ2 C1 C2 ⇒[ τℓ , P ] App τ1 τ2 C1 C2'

  FixAbs : ∀{C τ} →
          Fix τ C
            ⇒[ τℓ , ∅ ]
          sub C⅀ (addSub C⅀ var (Fix τ C)) C

  SendAbs : ∀{ℓ1 ℓ2 tₑ v} →
            𝕃 .Valₑ {!   !} →
            Send ℓ1 (Done tₑ ℓ1 v) tₑ ℓ2
              ⇒[ τℓ , Comm ℓ1 ℓ2 ]
            Done tₑ ℓ2 v

  ITEAbsT : ∀{ℓ C2 C3 τ} →
            ITE ℓ (Done (injTy (𝕃 .Boolₑ)) ℓ {!   !}) C2 C3 τ
              ⇒[ τℓ , ∅ ]
            C2

  ITEAbsF : ∀{ℓ C2 C3 τ} →
              ITE ℓ (Done (injTy (𝕃 .Boolₑ)) ℓ {!   !}) C2 C3 τ
                ⇒[ τℓ , ∅ ]
              C3

  Str : ∀{P C1 C2 C3} →
        C1 ⇝* C2 →
        C2 ⇒[ τℓ , P ] C3 →
        C1 ⇒[ τℓ , P ] C3

⊢⇒* : ∀{Γ Δ C1 C2 t ℓ P} →
      Γ ⨾ Δ c⊢ C1 ∶ t →
      C1 ⇒[ ℓ , P ] C2 →
      Γ ⨾ Δ c⊢ C2 ∶ t
⊢⇒* ⊢C1 C1⇒C2 = {!   !}      