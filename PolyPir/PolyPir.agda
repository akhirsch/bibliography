{-# OPTIONS --safe #-}

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

open import PolyPir.LocalLang

module PolyPir.PolyPir
  -- Location values
  (Loc : Set)
  -- Locations should have decidable equality
  (≡-dec-Loc : DecidableEquality Loc)

  -- Local language
  (𝕃 : LocalLang Loc)
  where

open LocalLang 𝕃
open import ThirdOrderLanguage (𝕃 .⅀ₑ) as LL

Kndₑ     = 𝕃 .⅀ₑ .⅀₂ .Knd
*ₑ'      = 𝕃 .TyKnd
TyShapeₑ = 𝕃 .⅀ₑ .⅀₂ .TyShape
TyPosₑ   = 𝕃 .⅀ₑ .⅀₂ .TyPos
Shapeₑ   = 𝕃 .⅀ₑ .Shape
TmPosₑ   = 𝕃 .⅀ₑ .TmPos
TmTyPosₑ = 𝕃 .⅀ₑ .TmTyPos

----------------------------
-- SECOND-ORDER SIGNATURE --
----------------------------

-- Kinds that can be abstracted over
data ∀Knd : Set where
  -- Embedding of local kinds
  LocKnd' : (κₑ : Kndₑ) → ∀Knd

  -- Kind of choreographic types
  *' : ∀Knd
  
  -- Kind of locations
  *ₗ' : ∀Knd
  -- Kind of sets of locations
  *ₛ' : ∀Knd

-- Choreographic kinds
data CKnd : Set where
  -- Kind for bound types 
  BndKnd : CKnd

  AllKnd : ∀Knd → CKnd

* = AllKnd *'
*ₗ = AllKnd *ₗ'
*ₛ = AllKnd *ₛ'
*ₑ = AllKnd (LocKnd' *ₑ')
LocKnd = AllKnd ∘ LocKnd'

LocKnd-injective : ∀{x y} → LocKnd x ≡ LocKnd y → x ≡ y
LocKnd-injective refl = refl

-- Choreographic types
data CTyShape : Set where
  -- Embedding of local types
  LocalTy : (sₑ : TyShapeₑ) → CTyShape
  -- Type of bound local values
  Bnd : CTyShape
  -- Type of choreographic local values
  At : CTyShape

  -- Function type
  Fun : CTyShape
  -- Universal quantification
  All : (κ : ∀Knd) → CTyShape

  -- Literal locations
  LitLoc : Loc → CTyShape
  -- Empty location set
  Emp : CTyShape
  -- Singleton location set
  Sng : CTyShape
  -- Union of location sets
  Union : CTyShape

-- Choreographic kinding signatures
CTyPos : CTyShape → List (List CKnd × CKnd) × CKnd
-- sₑ Σₑ : κ ⊢ LocalTy{sₑ} Σₑ : κ
CTyPos (LocalTy sₑ) = map (λ{ (Γ , κ) → map LocKnd Γ , LocKnd κ }) (TyPosₑ sₑ .fst) , LocKnd (TyPosₑ sₑ .snd)
-- Bnd *ₗ *ₑ : *b
CTyPos Bnd = ([] , *ₗ) ∷ ([] , *ₑ) ∷ [] , BndKnd
-- At *ₗ *ₑ : *
CTyPos At = ([] , *ₗ) ∷ ([] , *ₑ) ∷ [] , *
-- Fun * * : *
CTyPos Fun = ([] , *) ∷ ([] , *) ∷ [] , *
-- All{κ} [κ]* : *
CTyPos (All κ) = (AllKnd κ ∷ [] , *) ∷ [] , *
-- LitLoc{L} : *ₗ
CTyPos (LitLoc L) = [] , *ₗ
-- Emp : *ₛ
CTyPos Emp = [] , *ₛ
-- Sng *ₗ : *ₛ
CTyPos Sng = ([] , *ₗ) ∷ [] , *ₛ
-- Union *ₛ *ₛ : *ₛ
CTyPos Union = ([] , *ₛ) ∷ ([] , *ₛ) ∷ [] , *ₛ

-- Second-order signature for polymorphic Pirouette
C⅀₂ : SecondOrderSignature
Knd     C⅀₂ = CKnd
TyShape C⅀₂ = CTyShape
TyPos   C⅀₂ = CTyPos

open import SecondOrderContexts C⅀₂ as C

-- Aliases for each type constructor
TyLocalTy : ∀{Γ} (sₑ : TyShapeₑ) →
            (ts : C.TyVec Γ (map (λ{ (Γ , κ) → map LocKnd Γ , LocKnd κ }) (TyPosₑ sₑ .fst))) →
            C.Ty Γ (LocKnd (TyPosₑ sₑ .snd))
TyLocalTy sₑ ts = C.tyConstr (LocalTy sₑ) ts

TyBnd : ∀{Γ} (ℓ : C.Ty Γ *ₗ) (t : C.Ty Γ *ₑ) → C.Ty Γ BndKnd
TyBnd ℓ t = C.tyConstr Bnd (ℓ C.∷ t C.∷ C.[])

TyAt : ∀{Γ} (ℓ : C.Ty Γ *ₗ) (t : C.Ty Γ *ₑ) → C.Ty Γ *
TyAt ℓ t = C.tyConstr At (ℓ C.∷ t C.∷ C.[])

TyFun : ∀{Γ} (s t : C.Ty Γ *) → C.Ty Γ *
TyFun s t = C.tyConstr Fun (s C.∷ t C.∷ C.[])

TyAll : ∀{Γ} (κ : ∀Knd) (t : C.Ty (AllKnd κ ∷ Γ) *) → C.Ty Γ *
TyAll κ t = C.tyConstr (All κ) (t C.∷ C.[])

TyLitLoc : ∀{Γ} (L : Loc) → C.Ty Γ *ₗ
TyLitLoc L = C.tyConstr (LitLoc L) C.[]

TyEmp : ∀{Γ} → C.Ty Γ *ₛ
TyEmp = C.tyConstr Emp C.[]

TySng : ∀{Γ} → C.Ty Γ *ₗ → C.Ty Γ *ₛ
TySng ℓ = C.tyConstr Sng (ℓ C.∷ C.[])

TyUnion : ∀{Γ} (ρ₁ ρ₂ : C.Ty Γ *ₛ) → C.Ty Γ *ₛ
TyUnion ρ₁ ρ₂ = C.tyConstr Union (ρ₁ C.∷ ρ₂ C.∷ C.[])

-----------------------------
-- KIND-CONTEXT PROJECTION --
-----------------------------

{-
Projects a choreographic kinding context to a local kinding
context. Since kinds are not bound to a specific location, we
just extract all local kinds.
-}
∣ₖ : C.KndCtx → LL.KndCtx
∣ₖ [] = []
∣ₖ (BndKnd ∷ Γ) = ∣ₖ Γ
∣ₖ (AllKnd (LocKnd' κₑ) ∷ Γ) = κₑ ∷ ∣ₖ Γ
∣ₖ (AllKnd *' ∷ Γ) = ∣ₖ Γ
∣ₖ (AllKnd *ₗ' ∷ Γ) = ∣ₖ Γ
∣ₖ (AllKnd *ₛ' ∷ Γ) = ∣ₖ Γ

-- Projecting distributes over context concatenation
++∣ₖ : (Γ1 Γ2 : C.KndCtx) → ∣ₖ (Γ1 ++ Γ2) ≡ (∣ₖ Γ1) ++ (∣ₖ Γ2)
++∣ₖ [] Γ2 = refl
++∣ₖ (BndKnd ∷ Γ1) Γ2 = ++∣ₖ Γ1 Γ2
++∣ₖ (AllKnd (LocKnd' κₑ) ∷ Γ1) Γ2 = cong (κₑ ∷_) (++∣ₖ Γ1 Γ2)
++∣ₖ (AllKnd *' ∷ Γ1) Γ2 = ++∣ₖ Γ1 Γ2
++∣ₖ (AllKnd *ₗ' ∷ Γ1) Γ2 = ++∣ₖ Γ1 Γ2
++∣ₖ (AllKnd *ₛ' ∷ Γ1) Γ2 = ++∣ₖ Γ1 Γ2

-- Projecting after injecting a local kind context has no effect
∣ₖ∘LocKnd≡Id : (Γ : LL.KndCtx) → ∣ₖ (map LocKnd Γ) ≡ Γ
∣ₖ∘LocKnd≡Id [] = refl
∣ₖ∘LocKnd≡Id (κₑ ∷ Γ) = cong (κₑ ∷_) (∣ₖ∘LocKnd≡Id Γ)

{-
There is a canonical renaming from a projected and
then injected kind context back to itself.
Essentially, accounting for the non-local kinds
that were lost by the projection.
-}
LocKnd∘∣ₖ-Ren : (Γ : C.KndCtx) → C.TyRen (map LocKnd (∣ₖ Γ)) Γ
LocKnd∘∣ₖ-Ren [] = C.ε
LocKnd∘∣ₖ-Ren (BndKnd ∷ Γ) = C.TyDrop (LocKnd∘∣ₖ-Ren Γ)
LocKnd∘∣ₖ-Ren (AllKnd (LocKnd' κₑ) ∷ Γ) = C.TyKeep (LocKnd∘∣ₖ-Ren Γ)
LocKnd∘∣ₖ-Ren (AllKnd *' ∷ Γ) = C.TyDrop (LocKnd∘∣ₖ-Ren Γ)
LocKnd∘∣ₖ-Ren (AllKnd *ₗ' ∷ Γ) = C.TyDrop (LocKnd∘∣ₖ-Ren Γ)
LocKnd∘∣ₖ-Ren (AllKnd *ₛ' ∷ Γ) = C.TyDrop (LocKnd∘∣ₖ-Ren Γ)

-- Projects a choreographic type variable to a local type variable
projTyVar : ∀{Γ1 Γ2 κ κₑ} → ∣ₖ Γ1 ≡ Γ2 → κ ≡ LocKnd κₑ →
            C.TyVar Γ1 κ → LL.TyVar Γ2 κₑ
projTyVar refl refl C.TV0 = LL.TV0
projTyVar {BndKnd ∷ Γ} refl refl (C.TVS x) = projTyVar refl refl x
projTyVar {AllKnd (LocKnd' κₑ) ∷ Γ} refl refl (LL.TVS x) = LL.TVS (projTyVar refl refl x)
projTyVar {AllKnd *' ∷ Γ} refl refl (C.TVS x) = projTyVar refl refl x
projTyVar {AllKnd *ₗ' ∷ Γ} refl refl (C.TVS x) = projTyVar refl refl x
projTyVar {AllKnd *ₛ' ∷ Γ} refl refl (C.TVS x) = projTyVar refl refl x

-- Projects a choreographic type to a local type
projTy : ∀{Γ1 Γ2 κ κₑ} → ∣ₖ Γ1 ≡ Γ2 → κ ≡ LocKnd κₑ →
         C.Ty Γ1 κ →
         LL.Ty Γ2 κₑ
projTyVec : ∀{Γ1 Γ2 Σ} → ∣ₖ Γ1 ≡ Γ2 → 
            C.TyVec Γ1 (map (λ { (Γₑ , κₑ) → map LocKnd Γₑ , LocKnd κₑ }) Σ) →
            LL.TyVec Γ2 Σ

projTy refl p (C.tyVar x) = LL.tyVar (projTyVar refl p x)
projTy {Γ1} refl p (C.tyConstr (LocalTy sₑ) ts) =
  subst (LL.Ty (∣ₖ Γ1)) (LocKnd-injective p) (LL.tyConstr sₑ (projTyVec refl ts))

projTyVec {Σ = []} refl [] = LL.[]
projTyVec {Γ1} {Σ = (Δₑ , κₑ) ∷ Σ} refl (t ∷ ts) =
  projTy (++∣ₖ (map LocKnd Δₑ) Γ1 ∙ cong (_++ ∣ₖ Γ1) (∣ₖ∘LocKnd≡Id Δₑ)) refl t LL.∷
  projTyVec refl ts

-- Injects a local type to a choreographic type
injTyVar : ∀{Γ κₑ} → LL.TyVar Γ κₑ → C.TyVar (map LocKnd Γ) (LocKnd κₑ)
injTyVar TV0 = C.TV0
injTyVar (TVS x) = C.TVS (injTyVar x)

injTy : ∀{Γ1 Γ2 κₑ} → map LocKnd Γ1 ≡ Γ2 → LL.Ty Γ1 κₑ → C.Ty Γ2 (LocKnd κₑ)
injTyVec : ∀{Γ1 Γ2 Σ} → map LocKnd Γ1 ≡ Γ2 →
          LL.TyVec Γ1 Σ →
          C.TyVec Γ2 (map (λ { (Γ , κ) → map LocKnd Γ , LocKnd κ }) Σ)

injTy refl (tyVar x) = C.tyVar (injTyVar x)
injTy refl (tyConstr sₑ ts) = C.tyConstr (LocalTy sₑ) (injTyVec refl ts)

injTyVec refl [] = C.[]
injTyVec {Γ1} {Σ = (Δ1 , κₑ) ∷ Σ} refl (t ∷ ts) =
  injTy (map-++-commute LocKnd Δ1 Γ1) t C.∷ injTyVec refl ts

injTyp : ∀{Γ1 Γ2} → map LocKnd Γ1 ≡ Γ2 → LL.Typ Γ1 → C.Typ Γ2
injTyp p (κₑ , t) = LocKnd κₑ , injTy p t

-- How substitution acts on types
substTV0 : ∀{Γ1 Γ2 κₑ} (p : κₑ ∷ Γ1 ≡ κₑ ∷ Γ2) →
           LL.TV0 ≡ subst (λ y → LL.TyVar y κₑ) p LL.TV0
substTV0 refl = refl

substTVS : ∀{Γ1 Γ2 κₑ' κₑ} (p : Γ1 ≡ Γ2) (x : LL.TyVar Γ1 κₑ) →
          LL.TVS (subst (flip LL.TyVar κₑ) p x) ≡
          subst (flip LL.TyVar κₑ) (cong (κₑ' ∷_) p) (LL.TVS x)
substTVS refl x = refl

substTyVar : ∀{Γ1 Γ2 κₑ} (p : Γ1 ≡ Γ2) (x : LL.TyVar Γ1 κₑ) →
           LL.tyVar (subst (flip LL.TyVar κₑ) p x) ≡
           subst (flip LL.Ty κₑ) p (LL.tyVar x)
substTyVar refl x = refl

substTyConstr : ∀{Γ1 Γ2 sₑ} (p : Γ1 ≡ Γ2) (ts : LL.TyVec Γ1 (TyPosₑ sₑ .fst)) →
              LL.tyConstr sₑ (subst (flip LL.TyVec (TyPosₑ sₑ .fst)) p ts) ≡
              subst (flip LL.Ty (TyPosₑ sₑ .snd)) p (LL.tyConstr sₑ ts)
substTyConstr refl ts = refl

substTyNil : ∀{Γ1 Γ2} (p : Γ1 ≡ Γ2) →
           LL.[] ≡ subst (flip LL.TyVec []) p LL.[]
substTyNil refl = refl

substTyCons : ∀{Σ Δ Γ1 Γ2 κₑ} (p : Γ1 ≡ Γ2) (t : LL.Ty (Δ ++ Γ1) κₑ) (ts : LL.TyVec Γ1 Σ) →
              subst (flip LL.Ty κₑ) (cong (Δ ++_) p) t LL.∷ subst (flip LL.TyVec Σ) p ts ≡
              subst (flip LL.TyVec ((Δ , κₑ) ∷ Σ)) p (t LL.∷ ts)
substTyCons refl t ts = refl

-- Projecting after injecting a local type has no effect
projInjTyVar : ∀{Γ1 Γ2 κₑ} (p : ∣ₖ (map LocKnd Γ1) ≡ Γ2)
              (q : LocKnd κₑ ≡ LocKnd κₑ) (r : Γ1 ≡ Γ2) (x : LL.TyVar Γ1 κₑ) →
              projTyVar p q (injTyVar x) ≡
              subst (flip LL.TyVar κₑ) r x
projInjTyVar refl refl r TV0 = substTV0 r
projInjTyVar {κₑ' ∷ Γ1} {Γ2} {κₑ} refl refl r (TVS x) =
  LL.TVS (projTyVar refl refl (injTyVar x))
    ≡⟨ cong LL.TVS (projInjTyVar refl refl (sym (∣ₖ∘LocKnd≡Id Γ1)) x) ⟩
  LL.TVS (subst (flip LL.TyVar κₑ) (sym (∣ₖ∘LocKnd≡Id Γ1)) x)
    ≡⟨ cong (λ y → LL.TVS (subst (flip LL.TyVar κₑ) y x)) (UIP _ _) ⟩
  LL.TVS (subst (flip LL.TyVar κₑ) (∷-injective r .snd) x)
    ≡⟨ substTVS (∷-injective r .snd) x ⟩
  subst (flip LL.TyVar κₑ) (cong (κₑ' ∷_) (∷-injective r .snd)) (LL.TVS x)
    ≡⟨ cong (λ y → subst (flip LL.TyVar κₑ) y (LL.TVS x)) (UIP _ _) ⟩
  subst (flip LL.TyVar κₑ) r (LL.TVS x) ∎

projInjTy : ∀{Γ1 Γ2 Γ3 κₑ} (p : map LocKnd Γ1 ≡ Γ2) (q : ∣ₖ Γ2 ≡ Γ3)
            (r : LocKnd κₑ ≡ LocKnd κₑ) (s : Γ1 ≡ Γ3) (t : LL.Ty Γ1 κₑ) →
            projTy q r (injTy p t) ≡
            subst (flip LL.Ty κₑ) s t
projInjTyVec : ∀{Γ1 Γ2 Γ3 Σ} (p : map LocKnd Γ1 ≡ Γ2) (q : ∣ₖ Γ2 ≡ Γ3)
               (r : Γ1 ≡ Γ3) (ts : LL.TyVec Γ1 Σ) →
               projTyVec q (injTyVec p ts) ≡
               subst (flip LL.TyVec Σ) r ts

projInjTy {κₑ = κₑ} refl refl refl s (tyVar x) =
  LL.tyVar (projTyVar refl refl (injTyVar x))
    ≡⟨ cong LL.tyVar (projInjTyVar refl refl s x) ⟩
  LL.tyVar (subst (flip LL.TyVar κₑ) s x)
    ≡⟨ substTyVar s x ⟩
  subst (flip LL.Ty κₑ) s (LL.tyVar x) ∎
projInjTy {κₑ = κₑ} refl refl refl s (tyConstr sₑ ts) =
  LL.tyConstr sₑ (projTyVec refl (injTyVec refl ts))
    ≡⟨ cong (LL.tyConstr sₑ) (projInjTyVec refl refl s ts) ⟩
  LL.tyConstr sₑ (subst (flip LL.TyVec (TyPosₑ sₑ .fst)) s ts)
    ≡⟨ substTyConstr s ts ⟩
  subst (flip LL.Ty κₑ) s (LL.tyConstr sₑ ts) ∎

projInjTyVec refl refl r [] = substTyNil r
projInjTyVec {Γ1} {Σ = (Δ , κₑ) ∷ Σ} refl refl r (t ∷ ts) =
  projTy (++∣ₖ (map LocKnd Δ) (map LocKnd Γ1) ∙ cong (_++ ∣ₖ (map LocKnd Γ1)) (∣ₖ∘LocKnd≡Id Δ))
        refl (injTy (map-++-commute LocKnd Δ Γ1) t)
      LL.∷ projTyVec refl (injTyVec refl ts)
    ≡⟨ cong₂ LL._∷_ (
        projInjTy (map-++-commute LocKnd Δ Γ1)
          (++∣ₖ (map LocKnd Δ) (map LocKnd Γ1) ∙ cong (_++ ∣ₖ (map LocKnd Γ1)) (∣ₖ∘LocKnd≡Id Δ))
          refl (cong (Δ ++_) r) t)
        (projInjTyVec refl refl r ts) ⟩
  subst (flip LL.Ty κₑ) (cong (Δ ++_) r) t LL.∷ subst (flip LL.TyVec Σ) r ts
    ≡⟨ substTyCons r t ts ⟩
  subst (flip LL.TyVec ((Δ , κₑ) ∷ Σ)) r (t LL.∷ ts) ∎

---------------------------
-- THIRD-ORDER SIGNATURE --
---------------------------

-- Choreographic terms
data CShape : Set where
  -- Embedding of local terms
  Local : (sₑ : Shapeₑ) → 
          (isTyp : ∀ Γ ts → TmPosₑ sₑ Γ ts .snd .fst ≡ *ₑ') →
          CShape
  -- Choreographic local terms
  Done : CShape

  -- Lambda abstraction
  Lam : CShape
  -- Fixpoint
  Fix : CShape
  -- Function application
  App : CShape
  -- Type abstraction
  Abs : (κ : ∀Knd) → CShape
  -- Type application
  AppTy : (κ : ∀Knd) → CShape
  -- Send operation
  Send : CShape
  -- Synchronization operation
  Sync : Bool → CShape
  -- If-then-else
  ITE : CShape

  -- Binding local values
  LocalLet : CShape
  -- Binding local types
  LocalLetTy : (κₑ : Kndₑ) → CShape
  -- Binding local locations
  LocalLetLoc : CShape

CTmTyPos : CShape → List (List CKnd × CKnd)
CTmTyPos (Local sₑ isTyp) = ([] , *ₗ) ∷ map (λ{ (Γₑ , κₑ) → map LocKnd Γₑ , LocKnd κₑ }) (TmTyPosₑ sₑ)
CTmTyPos Done = ([] , *ₗ) ∷ ([] , *ₑ) ∷ []
CTmTyPos Lam = ([] , *) ∷ ([] , *) ∷ []
CTmTyPos Fix = ([] , *) ∷ []
CTmTyPos App = ([] , *) ∷ ([] , *) ∷ []
CTmTyPos (Abs κ) = (AllKnd κ ∷ [] , *) ∷ []
CTmTyPos (AppTy κ) = (AllKnd κ ∷ [] , *) ∷ ([] , AllKnd κ) ∷ []
CTmTyPos Send = ([] , *ₗ) ∷ ([] , *ₗ) ∷ ([] , *ₑ) ∷ []
CTmTyPos (Sync d) = ([] , *ₗ) ∷ ([] , *ₗ) ∷ ([] , *) ∷ []
CTmTyPos ITE = ([] , *ₗ) ∷ ([] , *) ∷ []
CTmTyPos LocalLet = ([] , *ₗ) ∷ ([] , *ₑ) ∷ ([] , *) ∷ []
CTmTyPos (LocalLetTy κₑ) = ([] , *ₗ) ∷ ([] , *ₛ) ∷ ([] , *) ∷ []
CTmTyPos LocalLetLoc = ([] , *ₗ) ∷ ([] , *ₛ) ∷ ([] , *) ∷ []

CTmPos : (s : CShape) (Γ : C.KndCtx) →
          C.TyVec Γ (CTmTyPos s) →
          List (Σ[ Γ' ∈ _ ] (C.Ctx (Γ' ++ Γ) × C.Typ (Γ' ++ Γ)))
          × C.Typ Γ
-- sₑ Σₑ : t ⊢ Local{sₑ} ℓ Σₑ : ℓ.t
CTmPos (Local sₑ isTyp) Γ (ℓ ∷ ts) =
  map (λ{ (Γ' , Δ , t) →
    map LocKnd Γ' ,
    map (λ x → C.renTyp (C.TyKeep* (LocKnd∘∣ₖ-Ren Γ) (map LocKnd Γ')) (injTyp (map-++-commute LocKnd Γ' (∣ₖ Γ)) x)) Δ ,
    C.renTyp (C.TyKeep* (LocKnd∘∣ₖ-Ren Γ) (map LocKnd Γ')) (injTyp (map-++-commute LocKnd Γ' (∣ₖ Γ)) t)  }) (TmPosₑ sₑ (∣ₖ Γ) (projTyVec refl ts) .fst) ,
  BndKnd ,
  TyBnd ℓ (C.tyRen (LocKnd∘∣ₖ-Ren Γ) (injTy refl (subst (LL.Ty (∣ₖ Γ)) (isTyp (∣ₖ Γ) (projTyVec refl ts)) (TmPosₑ sₑ (∣ₖ Γ) (projTyVec refl ts) .snd .snd))))
-- Done (ℓ : *ₗ) (t : *ₑ) ℓ.t : t@ℓ
CTmPos Done Γ (ℓ ∷ t ∷ []) = ([] , [] , BndKnd , TyBnd ℓ t) ∷ [] , * , TyAt ℓ t
-- Lam (τ₁ τ₂ : *) [τ₁]τ₂ : τ₁⇒τ₂
CTmPos Lam Γ (τ₁ ∷ τ₂ ∷ []) = ([] , (* , τ₁) ∷ [] , * , τ₂) ∷ [] , * , TyFun τ₁ τ₂
-- Fix (τ : *) [τ]τ : τ
CTmPos Fix Γ (τ ∷ []) = ([] , (* , τ) ∷ [] , * , τ) ∷ [] , * , τ
-- App (τ₁ τ₂ : *) τ₁⇒τ₂ τ₁ : τ₂
CTmPos App Γ (τ₁ ∷ τ₂ ∷ []) = ([] , [] , * , TyFun τ₁ τ₂) ∷ ([] , [] , * , τ₁) ∷ [] , * , τ₂
-- Abs (τ : [κ]*) [κ]τ : ∀κ.τ
CTmPos (Abs κ) Γ (τ ∷ []) = (AllKnd κ ∷ [] , [] , * , τ) ∷ [] , * , TyAll κ τ
-- AppTy (τ : [κ]*) (v : κ) ∀κ.τ : τ⟨v⟩
CTmPos (AppTy κ) Γ (τ ∷ v ∷ []) = ([] , [] , * , TyAll κ τ) ∷ [] , * , C.tySub (C.TyIdSub C.▸ v) τ
-- Send (ℓ₁ ℓ₂ : *ₗ) (t : *ₑ) t@ℓ₁ : t@ℓ₂
CTmPos Send Γ (ℓ₁ ∷ ℓ₂ ∷ t ∷ []) = ([] , [] , * , TyAt ℓ₁ t) ∷ [] , * , TyAt ℓ₂ t
-- Sync{d} (ℓ₁ ℓ₂ : *ₗ) (τ : *) τ : τ
CTmPos (Sync d) Γ (ℓ₁ ∷ ℓ₂ ∷ τ ∷ []) = ([] , [] , * , τ) ∷ [] , * , τ
-- ITE (ℓ : *ₗ) (τ : *) Boolₑ@ℓ τ τ : τ
CTmPos ITE Γ (ℓ ∷ τ ∷ []) = ([] , [] , * , TyAt ℓ (C.tyRen C.ε (injTy refl (𝕃 .Boolₑ)))) ∷ ([] , [] , * , τ) ∷ ([] , [] , * , τ) ∷ [] , * , τ
-- LocalLet (ℓ : *ₗ) (t : *ₑ) (τ : *) t@ℓ [ℓ.t]τ : τ
CTmPos LocalLet Γ (ℓ ∷ t ∷ τ ∷ []) = ([] , [] , * , TyAt ℓ t) ∷ ([] , (BndKnd , TyBnd ℓ t) ∷ [] , * , τ) ∷ [] , * , τ
-- LocalLetTy (ℓ : *ₗ) (ρ : *ₛ) (τ : *) κₑ@ℓ [κₑ]τ : τ
CTmPos (LocalLetTy κₑ) Γ (ℓ ∷ ρ ∷ τ ∷ []) =
  ([] , [] , * , TyAt ℓ (C.tyRen C.ε (injTy refl (𝕃 .TyRepₑ κₑ)))) ∷
  (LocKnd κₑ ∷ [] , [] , * , C.tyRen (C.TyDrop C.TyIdRen) τ) ∷ [] ,
  * , τ
-- LocalLetLoc (ℓ : *ₗ) (ρ : *ₛ) (τ : *) Locₑ@ℓ [*ₗ]τ : τ
CTmPos LocalLetLoc Γ (ℓ ∷ ρ ∷ τ ∷ []) =
  ([] , [] , * , TyAt ℓ (C.tyRen C.ε (injTy refl (𝕃 .Locₑ)))) ∷
  (*ₗ ∷ [] , [] , * , C.tyRen (C.TyDrop C.TyIdRen) τ) ∷ [] ,
  * , τ
