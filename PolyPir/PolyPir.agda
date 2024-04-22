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
open import SecondOrderSolverMacro

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
open import SecondOrderLanguageUntyped (𝕃 .⅀ₑ .⅀₂) as ULL

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

-- Choreographic kinds
data CKnd : Set where
  -- Embedding of local kinds
  LocKnd : (κₑ : Kndₑ) → CKnd

  -- Kind of choreographic types
  * : CKnd

  -- Kind of locations
  *ₗ : CKnd
  -- Kind of sets of locations
  *ₛ : CKnd

*ₑ = LocKnd *ₑ'

LocKnd-injective : ∀{x y} → LocKnd x ≡ LocKnd y → x ≡ y
LocKnd-injective refl = refl

-- Choreographic types
data CTyShape : Set where
  -- Embedding of local types
  LocalTy : (sₑ : TyShapeₑ) → CTyShape
  -- Type of choreographic local values
  At : CTyShape

  -- Function type
  Fun : CTyShape
  -- Universal quantification
  All : (κ : CKnd) → CTyShape

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
-- At *ₗ *ₑ : *
CTyPos At = ([] , *ₗ) ∷ ([] , *ₑ) ∷ [] , *
-- Fun * * : *
CTyPos Fun = ([] , *) ∷ ([] , *) ∷ [] , *
-- All{κ} [κ]* : *
CTyPos (All κ) = (κ ∷ [] , *) ∷ [] , *
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
open import SecondOrderLanguageUntyped C⅀₂ as UC

-- Aliases for each type constructor
TyLocalTy : ∀{Γ} (sₑ : TyShapeₑ) →
            (ts : C.TyVec Γ (map (λ{ (Γ , κ) → map LocKnd Γ , LocKnd κ }) (TyPosₑ sₑ .fst))) →
            C.Ty Γ (LocKnd (TyPosₑ sₑ .snd))
TyLocalTy sₑ ts = C.tyConstr (LocalTy sₑ) ts

TyAt : ∀{Γ} (ℓ : C.Ty Γ *ₗ) (t : C.Ty Γ *ₑ) → C.Ty Γ *
TyAt ℓ t = C.tyConstr At (ℓ C.∷ t C.∷ C.[])

TyFun : ∀{Γ} (s t : C.Ty Γ *) → C.Ty Γ *
TyFun s t = C.tyConstr Fun (s C.∷ t C.∷ C.[])

TyAll : ∀{Γ} (κ : CKnd) (t : C.Ty (κ ∷ Γ) *) → C.Ty Γ *
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
∣ₖ (LocKnd κₑ ∷ Γ) = κₑ ∷ ∣ₖ Γ
∣ₖ (* ∷ Γ) = ∣ₖ Γ
∣ₖ (*ₗ ∷ Γ) = ∣ₖ Γ
∣ₖ (*ₛ ∷ Γ) = ∣ₖ Γ

-- Projecting distributes over context concatenation
++∣ₖ : (Γ1 Γ2 : C.KndCtx) → ∣ₖ (Γ1 ++ Γ2) ≡ (∣ₖ Γ1) ++ (∣ₖ Γ2)
++∣ₖ [] Γ2 = refl
++∣ₖ (LocKnd κₑ ∷ Γ1) Γ2 = cong (κₑ ∷_) (++∣ₖ Γ1 Γ2)
++∣ₖ (* ∷ Γ1) Γ2 = ++∣ₖ Γ1 Γ2
++∣ₖ (*ₗ ∷ Γ1) Γ2 = ++∣ₖ Γ1 Γ2
++∣ₖ (*ₛ ∷ Γ1) Γ2 = ++∣ₖ Γ1 Γ2

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
LocKnd∘∣ₖ-Ren (LocKnd κₑ ∷ Γ) = C.TyKeep (LocKnd∘∣ₖ-Ren Γ)
LocKnd∘∣ₖ-Ren (* ∷ Γ) = C.TyDrop (LocKnd∘∣ₖ-Ren Γ)
LocKnd∘∣ₖ-Ren (*ₗ ∷ Γ) = C.TyDrop (LocKnd∘∣ₖ-Ren Γ)
LocKnd∘∣ₖ-Ren (*ₛ ∷ Γ) = C.TyDrop (LocKnd∘∣ₖ-Ren Γ)

-- Projects a choreographic type to a local type
projTyVar : ∀{Γ1 Γ2 κ κₑ} (p : ∣ₖ Γ1 ≡ Γ2) (q : κ ≡ LocKnd κₑ) → 
            C.TyVar Γ1 κ → LL.TyVar Γ2 κₑ
projTyVar {LocKnd _ ∷ Γ1} {Γ2} {.(LocKnd _)} {κₑ} p q C.TV0 =
  subst (LL.TyVar _) (LocKnd-injective q) (subst (flip LL.TyVar _) p LL.TV0)
projTyVar {LocKnd _ ∷ Γ} {_ ∷ Γ2} p q (C.TVS x) =
  LL.TVS (projTyVar (∷-injective p .snd) q x)
projTyVar {* ∷ Γ} p q (C.TVS x) = projTyVar p q x
projTyVar {*ₗ ∷ Γ} p q (C.TVS x) = projTyVar p q x
projTyVar {*ₛ ∷ Γ} p q (C.TVS x) = projTyVar p q x

eraseProjTyVar : C.KndCtx → ℕ → ℕ
eraseProjTyVar (LocKnd _ ∷ Γ) zero = zero
eraseProjTyVar (LocKnd _ ∷ Γ) (suc x) = suc (eraseProjTyVar Γ x)
eraseProjTyVar (* ∷ Γ) (suc x) = eraseProjTyVar Γ x
eraseProjTyVar (*ₗ ∷ Γ) (suc x) = eraseProjTyVar Γ x
eraseProjTyVar (*ₛ ∷ Γ) (suc x) = eraseProjTyVar Γ x
eraseProjTyVar _ x = x

eraseProjTyVar≡ : ∀{Γ1 Γ2 κ κₑ} (p : ∣ₖ Γ1 ≡ Γ2) (q : κ ≡ LocKnd κₑ) → 
                 (x : C.TyVar Γ1 κ) →
                 ULL.eraseVar (projTyVar p q x) ≡
                 eraseProjTyVar Γ1 (UC.eraseVar x)
eraseProjTyVar≡ {LocKnd _ ∷ Γ1} {.(∣ₖ (LocKnd κₑ ∷ Γ1))} {.(LocKnd κₑ)} {κₑ} refl refl C.TV0 = refl
eraseProjTyVar≡ {LocKnd _ ∷ Γ} {_ ∷ .(∣ₖ Γ)} refl refl (C.TVS x) = cong suc (eraseProjTyVar≡ refl refl x)
eraseProjTyVar≡ {* ∷ Γ} p q (C.TVS x) = eraseProjTyVar≡ p q x
eraseProjTyVar≡ {*ₗ ∷ Γ} p q (C.TVS x) = eraseProjTyVar≡ p q x
eraseProjTyVar≡ {*ₛ ∷ Γ} p q (C.TVS x) = eraseProjTyVar≡ p q x

projTy : ∀{Γ1 Γ2 κ κₑ} (p : ∣ₖ Γ1 ≡ Γ2) (q : κ ≡ LocKnd κₑ) → 
         C.Ty Γ1 κ → LL.Ty Γ2 κₑ
projTyVec : ∀{Γ1 Γ2 Σ1 Σ2} (p : ∣ₖ Γ1 ≡ Γ2)
            (q : map (λ { (Γₑ , κₑ) → map LocKnd Γₑ , LocKnd κₑ }) Σ2 ≡ Σ1) → 
            C.TyVec Γ1 Σ1 → LL.TyVec Γ2 Σ2

projTy p q (C.tyVar x) = LL.tyVar (projTyVar p q x)
projTy {Γ1} {Γ2} p q (C.tyConstr (LocalTy sₑ) ts) =
  subst (LL.Ty Γ2) (LocKnd-injective q) (LL.tyConstr sₑ (projTyVec p refl ts))

projTyVec {Σ1 = .[]} {[]} p q C.[] = LL.[]
projTyVec {Γ1} {Σ1 = (Δ , _) ∷ Σ1} {(Δₑ , κₑ) ∷ Σ2} p q (t C.∷ ts) =
  projTy
      (++∣ₖ Δ Γ1 ∙ cong₂ _++_ (cong ∣ₖ (sym (,-injective (∷-injective q .fst) .fst)) ∙ ∣ₖ∘LocKnd≡Id Δₑ) p)
      (sym (,-injective (∷-injective q .fst) .snd))
      t
    LL.∷
  projTyVec p (∷-injective q .snd) ts

eraseProjTy : C.KndCtx → UC.UTm → ULL.UTm
eraseProjTyVec : C.KndCtx → List (C.KndCtx × CKnd) →
                 UC.UTmVec → ULL.UTmVec

eraseProjTy Γ (UC.var x) = ULL.var (eraseProjTyVar Γ x)
eraseProjTy Γ (UC.constr (LocalTy sₑ) es) =
  ULL.constr sₑ (eraseProjTyVec Γ (map (λ{ (Γₑ , κₑ) → map LocKnd Γₑ , LocKnd κₑ }) (𝕃 .⅀ₑ .⅀₂ .TyPos sₑ .fst)) es)
eraseProjTy Γ e = ULL.var zero

eraseProjTyVec Γ Σ UC.[] = ULL.[]
eraseProjTyVec Γ ((Δ , _) ∷ Σ) ((e , k) UC.∷ es) = (eraseProjTy (Δ ++ Γ) e , k) ULL.∷ eraseProjTyVec Γ Σ es
eraseProjTyVec Γ _ ((e , k) UC.∷ es) = ULL.[]

eraseProjTy≡ : ∀{Γ1 Γ2 κ κₑ} (p : ∣ₖ Γ1 ≡ Γ2) (q : κ ≡ LocKnd κₑ) → 
               (e : C.Ty Γ1 κ) →
                ULL.erase (projTy p q e) ≡
                eraseProjTy Γ1 (UC.erase e)
eraseProjTyVec≡ : ∀{Γ1 Γ2 Σ1 Σ2} (p : ∣ₖ Γ1 ≡ Γ2)
                  (q : map (λ { (Γₑ , κₑ) → map LocKnd Γₑ , LocKnd κₑ }) Σ2 ≡ Σ1) → 
                  (es : C.TyVec Γ1 Σ1) →
                  ULL.eraseVec (projTyVec p q es) ≡
                  eraseProjTyVec Γ1 Σ1 (UC.eraseVec es)

eraseProjTy≡ p q (C.tyVar x) = cong ULL.var (eraseProjTyVar≡ p q x)
eraseProjTy≡ {Γ1} {Γ2} p q (C.tyConstr (LocalTy sₑ) es) =
  ULL.erase (subst (LL.Ty Γ2) (LocKnd-injective q)
    (LL.tyConstr sₑ (projTyVec p refl es)))
    ≡⟨ sym (ULL.substTy-erase (LocKnd-injective q) (LL.tyConstr sₑ (projTyVec p refl es))) ⟩
  ULL.constr sₑ (ULL.eraseVec (projTyVec p refl es))
    ≡⟨ cong (ULL.constr sₑ) (eraseProjTyVec≡ p refl es) ⟩
  ULL.constr sₑ
    (eraseProjTyVec Γ1
    (map (λ { (Γₑ , κₑ) → map LocKnd Γₑ , LocKnd κₑ }) (𝕃 .⅀ₑ .⅀₂ .TyPos sₑ .fst))
    (UC.eraseVec es)) ∎

eraseProjTyVec≡ {Σ1 = []} {[]} p q C.[] = refl
eraseProjTyVec≡ {Γ1} {Σ1 = (Δ , _) ∷ Σ1} {(Δₑ , κₑ) ∷ Σ2} p q (e C.∷ es) =
  cong₂ ULL._∷_ (cong₂ _,_ 
    (eraseProjTy≡
    (++∣ₖ Δ Γ1 ∙ cong₂ _++_ (cong ∣ₖ (sym (,-injective (∷-injective q .fst) .fst)) ∙ ∣ₖ∘LocKnd≡Id Δₑ) p)
    (sym (,-injective (∷-injective q .fst) .snd))
    e)
    (sym (length-map LocKnd Δₑ) ∙ cong length (×-≡,≡↔≡ .Inverse.f⁻¹ (∷-injective q .fst) .fst)))
  (eraseProjTyVec≡  p (∷-injective q .snd) es)

-- Injects a local type to a choreographic type
injTyVar : ∀{Γ1 Γ2 κₑ κ} (p : map LocKnd Γ1 ≡ Γ2) (q : LocKnd κₑ ≡ κ) →
           LL.TyVar Γ1 κₑ → C.TyVar Γ2 κ
injTyVar {Γ1} {κ = κ} p q TV0 = subst (C.TyVar _) q (subst (flip C.TyVar _) p C.TV0)
injTyVar {Γ2 = _ ∷ Γ2} p q (C.TVS x) = C.TVS (injTyVar (∷-injective p .snd) q x)

eraseInjTyVar≡ : ∀{Γ1 Γ2 κₑ κ} (p : map LocKnd Γ1 ≡ Γ2) (q : LocKnd κₑ ≡ κ)
                  (x : LL.TyVar Γ1 κₑ) →
                  UC.eraseVar (injTyVar p q x) ≡ ULL.eraseVar x
eraseInjTyVar≡ {Γ1} {Γ2} {κₑ = κₑ} p q C.TV0 =
  UC.eraseVar (subst (C.TyVar Γ2) q (subst (flip C.TyVar (LocKnd κₑ)) p C.TV0))
    ≡⟨ sym (UC.substTy-eraseVar q (subst (flip C.TyVar (LocKnd κₑ)) p C.TV0)) ⟩
  UC.eraseVar (subst (flip C.TyVar (LocKnd κₑ)) p C.TV0)
    ≡⟨ sym (UC.substCtx-eraseVar p C.TV0) ⟩
  zero ∎
eraseInjTyVar≡ {Γ2 = _ ∷ Γ2} p q (C.TVS x) = cong suc (
  UC.eraseVar (injTyVar (∷-injective p .snd) q x)
    ≡⟨ eraseInjTyVar≡ (∷-injective p .snd) q x ⟩
  ULL.eraseVar x ∎)

injTy : ∀{Γ1 Γ2 κₑ κ} (p : map LocKnd Γ1 ≡ Γ2) (q : LocKnd κₑ ≡ κ) →
        LL.Ty Γ1 κₑ → C.Ty Γ2 κ
injTyVec : ∀{Γ1 Γ2 Σ1 Σ2} →
           (p : map LocKnd Γ1 ≡ Γ2) →
           (q : map (λ { (Γ , κ) → map LocKnd Γ , LocKnd κ }) Σ1 ≡ Σ2) →
           LL.TyVec Γ1 Σ1 → C.TyVec Γ2 Σ2

injTy p q (tyVar x) = C.tyVar (injTyVar p q x)
injTy {Γ1} {Γ2} p q (tyConstr sₑ ts) =
  subst (C.Ty Γ2) q (C.tyConstr (LocalTy sₑ)
    (injTyVec p refl ts))

injTyVec {Γ1} {Σ1 = []} {[]} p q [] = C.[]
injTyVec {Γ1} {Σ1 = (Δ1 , κ1) ∷ Σ1} {(Δ2 , κ2) ∷ Σ2} p q (t ∷ ts) =
  injTy (map-++-commute LocKnd Δ1 Γ1 ∙ cong₂ _++_ (,-injective (∷-injective q .fst) .fst) p) (,-injective (∷-injective q .fst) .snd) t
    C.∷
  injTyVec p (∷-injective q .snd) ts

eraseInjTy : ULL.UTm → UC.UTm
eraseInjTyVec : ULL.UTmVec → UC.UTmVec

eraseInjTy (ULL.var x) = UC.var x
eraseInjTy (ULL.constr sₑ es) = UC.constr (LocalTy sₑ) (eraseInjTyVec es)

eraseInjTyVec ULL.[] = UC.[]
eraseInjTyVec ((e , k) ULL.∷ es) = (eraseInjTy e , k) UC.∷ eraseInjTyVec es

eraseInjTy≡ : ∀{Γ1 Γ2 κₑ κ} (p : map LocKnd Γ1 ≡ Γ2) (q : LocKnd κₑ ≡ κ) →
              (e : LL.Ty Γ1 κₑ) → 
              UC.erase (injTy p q e) ≡
              eraseInjTy (ULL.erase e)
eraseInjTyVec≡ : ∀{Γ1 Γ2 Σ1 Σ2} →
                (p : map LocKnd Γ1 ≡ Γ2) →
                (q : map (λ { (Γ , κ) → map LocKnd Γ , LocKnd κ }) Σ1 ≡ Σ2) →
                (es : LL.TyVec Γ1 Σ1) →
                UC.eraseVec (injTyVec p q es) ≡
                eraseInjTyVec (ULL.eraseVec es)

eraseInjTy≡ p q (LL.tyVar x) = cong UC.var (eraseInjTyVar≡ p q x)
eraseInjTy≡ {Γ1} {Γ2} p q (LL.tyConstr sₑ es) =
  UC.erase (subst (C.Ty Γ2) q (C.tyConstr (LocalTy sₑ) (injTyVec p refl es)))
    ≡⟨ sym (UC.substTy-erase q  (C.tyConstr (LocalTy sₑ) (injTyVec p refl es))) ⟩
  UC.constr (LocalTy sₑ) (UC.eraseVec (injTyVec p refl es))
    ≡⟨ cong (UC.constr (LocalTy sₑ)) (eraseInjTyVec≡ p refl es) ⟩
  UC.constr (LocalTy sₑ) (eraseInjTyVec (ULL.eraseVec es)) ∎

eraseInjTyVec≡ {Γ1} {Σ1 = []} {[]} p q [] = refl
eraseInjTyVec≡ {Γ1} {Σ1 = (Δ1 , κ1) ∷ Σ1} {(Δ2 , κ2) ∷ Σ2} p q (t ∷ ts) =
  cong₂ UC._∷_
    (cong₂ _,_
      (eraseInjTy≡
        (map-++-commute LocKnd Δ1 Γ1 ∙ cong₂ _++_ (,-injective (∷-injective q .fst) .fst) p)
        (,-injective (∷-injective q .fst) .snd)
        t)
      (sym (cong length (×-≡,≡↔≡ .Inverse.f⁻¹ (∷-injective q .fst) .fst))
        ∙ length-map LocKnd Δ1))
    (eraseInjTyVec≡ p (∷-injective q .snd) ts)

injTyp : ∀{Γ1 Γ2} → map LocKnd Γ1 ≡ Γ2 → LL.Typ Γ1 → C.Typ Γ2
injTyp p (κₑ , t) = LocKnd κₑ , injTy p refl t

-- Projecting after injecting a local type just renames the type
eraseInjProjTyVar : ∀{Γ κ κₑ} (q : κ ≡ LocKnd κₑ) (x : C.TyVar Γ κ) →
                    UC.eraseRen (LocKnd∘∣ₖ-Ren Γ) (eraseProjTyVar Γ (UC.eraseVar x)) ≡
                    UC.eraseVar x
eraseInjProjTyVar {[]} refl ()
eraseInjProjTyVar {.(LocKnd _) ∷ Γ} refl C.TV0 = refl
eraseInjProjTyVar {LocKnd κₑ ∷ Γ} refl (C.TVS x) = cong suc (eraseInjProjTyVar refl x)
eraseInjProjTyVar {* ∷ Γ} refl (C.TVS x) = cong suc (eraseInjProjTyVar refl x)
eraseInjProjTyVar {*ₗ ∷ Γ} refl (C.TVS x) = cong suc (eraseInjProjTyVar refl x)
eraseInjProjTyVar {*ₛ ∷ Γ} refl (C.TVS x) = cong suc (eraseInjProjTyVar refl x)

LocKnd∘∣ₖ-Ren-++ : (Δ : LL.KndCtx) (Γ : C.KndCtx) →
                   UC.UKeep* (UC.eraseRen (LocKnd∘∣ₖ-Ren Γ)) (length Δ) ≗
                   UC.eraseRen (LocKnd∘∣ₖ-Ren (map LocKnd Δ ++ Γ))
LocKnd∘∣ₖ-Ren-++ [] Γ x = refl
LocKnd∘∣ₖ-Ren-++ (κ ∷ Δ) Γ zero = refl
LocKnd∘∣ₖ-Ren-++ (κ ∷ Δ) Γ (suc x) = cong suc (LocKnd∘∣ₖ-Ren-++ Δ Γ x)

eraseInjProjTy : ∀{Γ κ κₑ} (q : κ ≡ LocKnd κₑ) (e : C.Ty Γ κ) →
                  UC.renUnty
                    (UC.eraseRen (LocKnd∘∣ₖ-Ren Γ))
                    (eraseInjTy (eraseProjTy Γ (UC.erase e)))
                  ≡ UC.erase e
eraseInjProjTyVec : ∀{Γ} {Σ1 : List (C.KndCtx × CKnd)} {Σ2 : List (LL.KndCtx × Kndₑ)}
                    (q : map (λ { (Γ , κ) → map LocKnd Γ , LocKnd κ }) Σ2 ≡ Σ1) (es : C.TyVec Γ Σ1) →
                    UC.renVecUnty
                      (UC.eraseRen (LocKnd∘∣ₖ-Ren Γ))
                      (eraseInjTyVec (eraseProjTyVec Γ Σ1 (UC.eraseVec es)))
                    ≡ UC.eraseVec es

eraseInjProjTy q (C.tyVar x) = cong UC.var (eraseInjProjTyVar q x)
eraseInjProjTy {Γ} q (C.tyConstr (LocalTy sₑ) es) =
  cong (UC.constr (LocalTy sₑ)) (eraseInjProjTyVec refl es)

eraseInjProjTyVec q C.[] = refl
eraseInjProjTyVec {Γ} {(Δ , κ) ∷ Σ1} {(Δₑ , κₑ) ∷ Σ2} q (e C.∷ es) =
  cong₂ UC._∷_
    (cong₂ _,_ (
      UC.renUnty (UC.UKeep* (UC.eraseRen (LocKnd∘∣ₖ-Ren Γ)) (length Δ))
        (eraseInjTy (eraseProjTy (Δ ++ Γ) (UC.erase e)))
        ≡⟨ cong (λ Δ → UC.renUnty (UC.UKeep* (UC.eraseRen (LocKnd∘∣ₖ-Ren Γ)) (length Δ))
            (eraseInjTy (eraseProjTy (Δ ++ Γ) (UC.erase e))))
            (sym (×-≡,≡↔≡ .Inverse.f⁻¹ (∷-injective q .fst) .fst)) ⟩
      UC.renUnty (UC.UKeep* (UC.eraseRen (LocKnd∘∣ₖ-Ren Γ)) (length (map LocKnd Δₑ)))
        (eraseInjTy (eraseProjTy (map LocKnd Δₑ ++ Γ) (UC.erase e)))
        ≡⟨ cong (λ x → UC.renUnty (UC.UKeep* (UC.eraseRen (LocKnd∘∣ₖ-Ren Γ)) x)
            (eraseInjTy (eraseProjTy (map LocKnd Δₑ ++ Γ) (UC.erase e))))
            (length-map LocKnd Δₑ) ⟩
      UC.renUnty (UC.UKeep* (UC.eraseRen (LocKnd∘∣ₖ-Ren Γ)) (length Δₑ))
        (eraseInjTy (eraseProjTy (map LocKnd Δₑ ++ Γ) (UC.erase e)))
        ≡⟨ UC.renUntyExt (LocKnd∘∣ₖ-Ren-++ Δₑ Γ) 
            (eraseInjTy (eraseProjTy (map LocKnd Δₑ ++ Γ) (UC.erase e))) ⟩
      UC.renUnty (UC.eraseRen (LocKnd∘∣ₖ-Ren (map LocKnd Δₑ ++ Γ)))
        (eraseInjTy (eraseProjTy (map LocKnd Δₑ ++ Γ) (UC.erase e)))
        ≡⟨ cong (λ Δ → UC.renUnty (UC.eraseRen (LocKnd∘∣ₖ-Ren (Δ ++ Γ)))
            (eraseInjTy (eraseProjTy (Δ ++ Γ) (UC.erase e))))
            (×-≡,≡↔≡ .Inverse.f⁻¹ (∷-injective q .fst) .fst) ⟩
      UC.renUnty (UC.eraseRen (LocKnd∘∣ₖ-Ren (Δ ++ Γ)))
        (eraseInjTy (eraseProjTy (Δ ++ Γ) (UC.erase e)))
        ≡⟨ eraseInjProjTy (sym (×-≡,≡↔≡ .Inverse.f⁻¹ (∷-injective q .fst) .snd)) e ⟩
      UC.erase e ∎)
      refl)
    (eraseInjProjTyVec (∷-injective q .snd) es)

injProjTy : ∀{Γ1 Γ2 Γ3 κ κₑ} (p : ∣ₖ Γ1 ≡ Γ2)
            (q : κ ≡ LocKnd κₑ) (q' : LocKnd κₑ ≡ κ)
            (r : map LocKnd Γ2 ≡ Γ3) (s : Γ3 ≡ map LocKnd (∣ₖ Γ1))
            (t : C.Ty Γ1 κ) →
            C.tyRen (LocKnd∘∣ₖ-Ren Γ1) (subst (flip C.Ty κ) s (injTy r q' (projTy p q t)))
            ≡ t
injProjTy {Γ1} p q q' r refl t = UC.erase-inj (
  UC.erase (C.tyRen (LocKnd∘∣ₖ-Ren Γ1) (injTy r q' (projTy p q t)))
    ≡⟨ UC.erase-distr-ren (LocKnd∘∣ₖ-Ren Γ1) (injTy r q' (projTy p q t)) ⟩
  UC.renUnty (UC.eraseRen (LocKnd∘∣ₖ-Ren Γ1)) (UC.erase (injTy r q' (projTy p q t)))
    ≡⟨ cong (UC.renUnty (UC.eraseRen (LocKnd∘∣ₖ-Ren Γ1))) (eraseInjTy≡ r q' (projTy p q t)) ⟩
  UC.renUnty (UC.eraseRen (LocKnd∘∣ₖ-Ren Γ1)) (eraseInjTy (ULL.erase (projTy p q t)))
    ≡⟨ cong (λ x → UC.renUnty (UC.eraseRen (LocKnd∘∣ₖ-Ren Γ1)) (eraseInjTy x)) (eraseProjTy≡ p q t) ⟩
  UC.renUnty (UC.eraseRen (LocKnd∘∣ₖ-Ren Γ1)) (eraseInjTy (eraseProjTy Γ1 (UC.erase t)))
    ≡⟨ eraseInjProjTy q t ⟩
  UC.erase t ∎)

-- Projecting after injecting a local type has no effect
eraseProjInjTyVar : ∀{Γ κₑ} (x : LL.TyVar Γ κₑ) →
                    eraseProjTyVar (map LocKnd Γ) (ULL.eraseVar x)
                    ≡ ULL.eraseVar x
eraseProjInjTyVar LL.TV0 = refl
eraseProjInjTyVar (LL.TVS x) = cong suc (eraseProjInjTyVar x)

eraseProjInjTy : ∀{Γ κₑ} (e : LL.Ty Γ κₑ) →
                 eraseProjTy (map LocKnd Γ) (eraseInjTy (ULL.erase e))
                 ≡ ULL.erase e
eraseProjInjTyVec : ∀{Γ Σ} (es : LL.TyVec Γ Σ) →
                    eraseProjTyVec (map LocKnd Γ) (map (λ{ (Δ , κ) → map LocKnd Δ , LocKnd κ }) Σ)
                      (eraseInjTyVec (ULL.eraseVec es))
                    ≡ ULL.eraseVec es

eraseProjInjTy {Γ} (LL.tyVar x) = cong ULL.var (eraseProjInjTyVar x)
eraseProjInjTy (LL.tyConstr s es) = cong (ULL.constr s) (eraseProjInjTyVec es)

eraseProjInjTyVec LL.[] = refl
eraseProjInjTyVec {Γ} {Σ = (Δ , κ) ∷ Σ} (e LL.∷ es) = cong₂ ULL._∷_
  (cong₂ _,_ (
    eraseProjTy
      (map LocKnd Δ ++ map LocKnd Γ)
      (eraseInjTy (ULL.erase e))
      ≡⟨ cong (λ x → eraseProjTy x (eraseInjTy (ULL.erase e))) (sym (map-++-commute LocKnd Δ Γ)) ⟩
    eraseProjTy (map LocKnd (Δ ++ Γ)) (eraseInjTy (ULL.erase e))
      ≡⟨ eraseProjInjTy e ⟩
    ULL.erase e ∎)
    refl)
  (eraseProjInjTyVec es)

projInjTy : ∀{Γ1 Γ2 Γ3 κₑ κ} (p : map LocKnd Γ1 ≡ Γ2)
            (q : ∣ₖ Γ2 ≡ Γ3) (r : LocKnd κₑ ≡ κ)
            (r' : κ ≡ LocKnd κₑ) (s : Γ1 ≡ Γ3)
            (t : LL.Ty Γ1 κₑ) →
            projTy q r' (injTy p r t) ≡
            subst (flip LL.Ty κₑ) s t
projInjTy {Γ1} {.(map LocKnd Γ1)} refl q r r' refl t = ULL.erase-inj (
  ULL.erase (projTy q r' (injTy refl r t))
    ≡⟨ eraseProjTy≡ q r' (injTy refl r t) ⟩
  eraseProjTy (map LocKnd Γ1) (UC.erase (injTy refl r t))
    ≡⟨ cong (eraseProjTy (map LocKnd Γ1)) (eraseInjTy≡ refl r t) ⟩
  eraseProjTy (map LocKnd Γ1) (eraseInjTy (ULL.erase t))
    ≡⟨ eraseProjInjTy t ⟩
  ULL.erase t ∎)    
