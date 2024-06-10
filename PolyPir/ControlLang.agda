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

open import PolyPir.LocalLang

module PolyPir.ControlLang
  -- Location values
  (Loc : Set)
  -- Locations should have decidable equality
  (≡-dec-Loc : DecidableEquality Loc)

  -- CtrlLocal language
  (𝕃 : LocalLang Loc)

  where

open LocalLang 𝕃
open import ThirdOrderLanguage (𝕃 .⅀ₑ) as LL
open import SecondOrderLanguageUntyped (𝕃 .⅀ₑ .⅀₂) as ULL

⅀ₑ₂      = 𝕃 .⅀ₑ .⅀₂
Kndₑ     = ⅀ₑ₂ .Knd
*ₑ'      = 𝕃 .TyKnd
TyShapeₑ = ⅀ₑ₂ .TyShape
TyPosₑ   = ⅀ₑ₂ .TyPos
Shapeₑ   = 𝕃 .⅀ₑ .Shape
TmPosₑ   = 𝕃 .⅀ₑ .TmPos
TmTyPosₑ = 𝕃 .⅀ₑ .TmTyPos

----------------------------
-- SECOND-ORDER SIGNATURE --
----------------------------

-- Choreographic kinds
data CtrlKnd : Set where
  -- Embedding of local kinds
  CtrlLocKnd : (κₑ : Kndₑ) → CtrlKnd

  -- Kind of control-language types
  *Ctrl : CtrlKnd

  -- Kind of locations
  *Ctrlₗ : CtrlKnd
  -- Kind of sets of locations
  *Ctrlₛ : CtrlKnd

*Ctrlₑ = CtrlLocKnd *ₑ'

CtrlLocKnd-inj : Injective _≡_ _≡_ CtrlLocKnd
CtrlLocKnd-inj refl = refl

CtrlLocKndΣ : List Kndₑ × Kndₑ → List CtrlKnd × CtrlKnd
CtrlLocKndΣ (Δₑ , κₑ) = map CtrlLocKnd Δₑ , CtrlLocKnd κₑ

CtrlLocKndΣ-inj : Injective _≡_ _≡_ CtrlLocKndΣ
CtrlLocKndΣ-inj {Δ1 , κ1} {Δ2 , κ2} p =
  cong₂ _,_
    (map-injective CtrlLocKnd-inj (,-injective p .fst))
    (CtrlLocKnd-inj (,-injective p .snd))

-- Control-language types
data CtrlTyShape : Set where
  -- Embedding of local types
  CtrlLocalTy : (sₑ : TyShapeₑ) → CtrlTyShape
  -- Type of local values
  CtrlAt : CtrlTyShape

  -- Function type
  CtrlFun : CtrlTyShape
  -- Universal quantification
  CtrlAll : (κ : CtrlKnd) → CtrlTyShape
  -- Unit type
  CtrlUnit : CtrlTyShape

  -- Literal locations
  CtrlLitLoc : Loc → CtrlTyShape
  -- CtrlEmpty location set
  CtrlEmp : CtrlTyShape
  -- Singleton location set
  CtrlSng : CtrlTyShape
  -- CtrlUnion of location sets
  CtrlUnion : CtrlTyShape

-- Choreographic kinding signatures
CtrlTyPos : CtrlTyShape → List (List CtrlKnd × CtrlKnd) × CtrlKnd
-- sₑ Σₑ : κ ⊢ CtrlLocalTy{sₑ} Σₑ : κ
CtrlTyPos (CtrlLocalTy sₑ) = map CtrlLocKndΣ (TyPosₑ sₑ .fst) , CtrlLocKnd (TyPosₑ sₑ .snd)
-- CtrlAt *Ctrlₗ *Ctrlₑ : *Ctrl
CtrlTyPos CtrlAt = ([] , *Ctrlₑ) ∷ [] , *Ctrl
-- CtrlFun *Ctrl *Ctrl : *Ctrl
CtrlTyPos CtrlFun = ([] , *Ctrl) ∷ ([] , *Ctrl) ∷ [] , *Ctrl
-- CtrlAll{κ} [κ]*Ctrl : *Ctrl
CtrlTyPos (CtrlAll κ) = (κ ∷ [] , *Ctrl) ∷ [] , *Ctrl
CtrlTyPos CtrlUnit = [] , *Ctrl
-- CtrlLitLoc{L} : *Ctrlₗ
CtrlTyPos (CtrlLitLoc L) = [] , *Ctrlₗ
-- CtrlEmp : *Ctrlₛ
CtrlTyPos CtrlEmp = [] , *Ctrlₛ
-- CtrlSng *Ctrlₗ : *Ctrlₛ
CtrlTyPos CtrlSng = ([] , *Ctrlₗ) ∷ [] , *Ctrlₛ
-- CtrlUnion *Ctrlₛ *Ctrlₛ : *Ctrlₛ
CtrlTyPos CtrlUnion = ([] , *Ctrlₛ) ∷ ([] , *Ctrlₛ) ∷ [] , *Ctrlₛ

-- Second-order signature for polymorphic Pirouette
C⅀₂ : SecondOrderSignature
Knd     C⅀₂ = CtrlKnd
TyShape C⅀₂ = CtrlTyShape
TyPos   C⅀₂ = CtrlTyPos

open import SecondOrderContexts C⅀₂ as C
open import SecondOrderLanguageUntyped C⅀₂ as UC

-- Aliases for each type constructor
TyCtrlLocalTy : ∀{Γ} (sₑ : TyShapeₑ) →
            (ts : C.TyVec Γ (map CtrlLocKndΣ (TyPosₑ sₑ .fst))) →
            C.Ty Γ (CtrlLocKnd (TyPosₑ sₑ .snd))
TyCtrlLocalTy sₑ ts = C.tyConstr (CtrlLocalTy sₑ) ts

TyCtrlAt : ∀{Γ} (t : C.Ty Γ *Ctrlₑ) → C.Ty Γ *Ctrl
TyCtrlAt t = C.tyConstr CtrlAt (t C.∷ C.[])

TyCtrlFun : ∀{Γ} (s t : C.Ty Γ *Ctrl) → C.Ty Γ *Ctrl
TyCtrlFun s t = C.tyConstr CtrlFun (s C.∷ t C.∷ C.[])

TyCtrlUnit : ∀{Γ} → C.Ty Γ *Ctrl
TyCtrlUnit = C.tyConstr CtrlUnit C.[]

TyCtrlAll : ∀{Γ} (κ : CtrlKnd) (t : C.Ty (κ ∷ Γ) *Ctrl) → C.Ty Γ *Ctrl
TyCtrlAll κ t = C.tyConstr (CtrlAll κ) (t C.∷ C.[])

TyCtrlLitLoc : ∀{Γ} (L : Loc) → C.Ty Γ *Ctrlₗ
TyCtrlLitLoc L = C.tyConstr (CtrlLitLoc L) C.[]

TyCtrlEmp : ∀{Γ} → C.Ty Γ *Ctrlₛ
TyCtrlEmp = C.tyConstr CtrlEmp C.[]

TyCtrlSng : ∀{Γ} → C.Ty Γ *Ctrlₗ → C.Ty Γ *Ctrlₛ
TyCtrlSng ℓ = C.tyConstr CtrlSng (ℓ C.∷ C.[])

TyCtrlUnion : ∀{Γ} (ρ₁ ρ₂ : C.Ty Γ *Ctrlₛ) → C.Ty Γ *Ctrlₛ
TyCtrlUnion ρ₁ ρ₂ = C.tyConstr CtrlUnion (ρ₁ C.∷ ρ₂ C.∷ C.[])

--------------------------------
-- KINDING CONTEXT OPERATIONS --
--------------------------------

-- PROJECTION

{-
Projects a choreographic kinding context to a local kinding
context by filtering all non-local kinds.
-}
projCtx : C.KndCtx → LL.KndCtx
projCtx [] = []
projCtx (CtrlLocKnd κₑ ∷ Γ) = κₑ ∷ projCtx Γ
projCtx (*Ctrl ∷ Γ) = projCtx Γ
projCtx (*Ctrlₗ ∷ Γ) = projCtx Γ
projCtx (*Ctrlₛ ∷ Γ) = projCtx Γ

-- Projecting distributes over concatenation
projCtx-++ : (Γ1 Γ2 : C.KndCtx) → projCtx (Γ1 ++ Γ2) ≡ (projCtx Γ1) ++ (projCtx Γ2)
projCtx-++ [] Γ2 = refl
projCtx-++ (CtrlLocKnd κₑ ∷ Γ1) Γ2 = cong (κₑ ∷_) (projCtx-++ Γ1 Γ2)
projCtx-++ (*Ctrl ∷ Γ1) Γ2 = projCtx-++ Γ1 Γ2
projCtx-++ (*Ctrlₗ ∷ Γ1) Γ2 = projCtx-++ Γ1 Γ2
projCtx-++ (*Ctrlₛ ∷ Γ1) Γ2 = projCtx-++ Γ1 Γ2

-- INJECTION

-- Injects a local kinding context to a choreographic kinding context
injCtx : LL.KndCtx → C.KndCtx
injCtx = map CtrlLocKnd

-- Injecting distributes over concatenation
injCtx-++ : (Γ1 Γ2 : LL.KndCtx) → injCtx (Γ1 ++ Γ2) ≡ (injCtx Γ1) ++ (injCtx Γ2)
injCtx-++ Γ1 Γ2 = map-++-commute CtrlLocKnd Γ1 Γ2

-- Projecting after injecting a context has no effect
projCtx∘injCtx≗id : projCtx ∘ injCtx ≗ id
projCtx∘injCtx≗id [] = refl
projCtx∘injCtx≗id (κₑ ∷ Γₑ) = cong (κₑ ∷_) (projCtx∘injCtx≗id Γₑ)

---------------------
-- TYPE OPERATIONS --
---------------------

-- PROJECTION --

-- Projects a choreographic variable to a local variable
projTyVar : ∀{Γ1 Γ2 κ κₑ} (p : projCtx Γ1 ≡ Γ2) (q : κ ≡ CtrlLocKnd κₑ) → 
             C.TyVar Γ1 κ → LL.TyVar Γ2 κₑ
projTyVar {CtrlLocKnd _ ∷ Γ1} {Γ2} {.(CtrlLocKnd _)} {κₑ} p q C.TV0 =
  subst (LL.TyVar _) (CtrlLocKnd-inj q) (subst (flip LL.TyVar _) p LL.TV0)
projTyVar {CtrlLocKnd _ ∷ Γ} {_ ∷ Γ2} p q (C.TVS x) =
  LL.TVS (projTyVar (∷-injective p .snd) q x)
projTyVar {*Ctrl ∷ Γ} p q (C.TVS x) = projTyVar p q x
projTyVar {*Ctrlₗ ∷ Γ} p q (C.TVS x) = projTyVar p q x
projTyVar {*Ctrlₛ ∷ Γ} p q (C.TVS x) = projTyVar p q x

-- Extend this function from variables to all types via a morphism
projTyRel : MorRel C⅀₂ ⅀ₑ₂
α projTyRel Γ Γₑ = projCtx Γ ≡ Γₑ
β projTyRel κ κₑ = κ ≡ CtrlLocKnd κₑ
δ projTyRel Δ Δₑ = projCtx Δ ≡ Δₑ
μ projTyRel Σ Σₑ = Σ ≡ map CtrlLocKndΣ Σₑ
δ-++-α projTyRel {Δ1 = Δ1} {Γ1 = Γ1} refl refl = projCtx-++ Δ1 Γ1
μ-nil projTyRel = refl
μ-head-δ projTyRel {Δ2 = Δ2} refl = projCtx∘injCtx≗id Δ2
μ-head-β projTyRel refl = refl
μ-tail projTyRel refl = refl
μ-cons-nil projTyRel = cons≢nil
μ-nil-cons projTyRel = nil≢cons

projTyMor : LangMor C⅀₂ ⅀ₑ₂
mor-rel projTyMor = projTyRel
mor-var projTyMor p q x = LL.tyVar (projTyVar p q x)
γ projTyMor (CtrlLocalTy sₑ) p = sₑ
γ-ty-≡ projTyMor (CtrlLocalTy sₑ) p = CtrlLocKnd-inj p
γ-resp-arg projTyMor (CtrlLocalTy sₑ) p = refl

-- Projects a choreographic type to a local type
projTyH : ∀{Γ1 Γ2 κ κₑ} → projCtx Γ1 ≡ Γ2 → κ ≡ CtrlLocKnd κₑ →
          C.Ty Γ1 κ → LL.Ty Γ2 κₑ
projTyH = mor projTyMor

projTy : ∀{Γ κₑ} → C.Ty Γ (CtrlLocKnd κₑ) → LL.Ty (projCtx Γ) κₑ
projTy = mor projTyMor refl refl

projTyVec : ∀{Γ Σₑ} → C.TyVec Γ (map CtrlLocKndΣ Σₑ) → LL.TyVec (projCtx Γ) Σₑ
projTyVec {Γ} {Σₑ} es = mor-vec projTyMor refl refl es

-- INJECTION --

-- Injects a local variable to a choreographic variable
injTyVar : ∀{Γ1 Γ2 κₑ κ} (p : injCtx Γ1 ≡ Γ2) (q : CtrlLocKnd κₑ ≡ κ) →
           LL.TyVar Γ1 κₑ → C.TyVar Γ2 κ
injTyVar {Γ1} {κ = κ} p q TV0 = subst (C.TyVar _) q (subst (flip C.TyVar _) p C.TV0)
injTyVar {Γ2 = _ ∷ Γ2} p q (C.TVS x) = C.TVS (injTyVar (∷-injective p .snd) q x)

-- Extend this function from variables to all types via a morphism
injTyRel : MorRel ⅀ₑ₂ C⅀₂
α injTyRel Γₑ Γ = injCtx Γₑ ≡ Γ
β injTyRel κₑ κ = CtrlLocKnd κₑ ≡ κ
δ injTyRel Δₑ Δ = injCtx Δₑ ≡ Δ
μ injTyRel Σₑ Σ = map CtrlLocKndΣ Σₑ ≡ Σ
δ-++-α injTyRel {Δ1 = Δₑ} {Γ1 = Γₑ} refl refl = injCtx-++ Δₑ Γₑ
μ-nil injTyRel = refl
μ-head-δ injTyRel refl = refl
μ-head-β injTyRel refl = refl
μ-tail injTyRel refl = refl
μ-cons-nil injTyRel = cons≢nil
μ-nil-cons injTyRel = nil≢cons

injTyMor : LangMor ⅀ₑ₂ C⅀₂
mor-rel injTyMor = injTyRel
mor-var injTyMor p q x = C.tyVar (injTyVar p q x)
γ injTyMor sₑ p = CtrlLocalTy sₑ
γ-ty-≡ injTyMor Sₑ p = p
γ-resp-arg injTyMor sₑ p = refl

-- Injects a local type to a choreographic type
injTyH : ∀{Γ1 Γ2 κₑ κ} (p : injCtx Γ1 ≡ Γ2) (q : CtrlLocKnd κₑ ≡ κ) →
        LL.Ty Γ1 κₑ → C.Ty Γ2 κ
injTyH = mor injTyMor

injTy : ∀{Γ κₑ} → LL.Ty Γ κₑ → C.Ty (injCtx Γ) (CtrlLocKnd κₑ)
injTy = injTyH refl refl

-- REGAINING --

{-
There is a canonical renaming from a projected and
then injected kind context back to itself.
Essentially, we need to add back the non-local kinds
that were lost by the projection.
-}
regain : (Γ : C.KndCtx) → C.TyRen (injCtx (projCtx Γ)) Γ
regain [] = C.ε
regain (CtrlLocKnd κₑ ∷ Γ) = C.TyKeep (regain Γ)
regain (*Ctrl ∷ Γ) = C.TyDrop (regain Γ)
regain (*Ctrlₗ ∷ Γ) = C.TyDrop (regain Γ)
regain (*Ctrlₛ ∷ Γ) = C.TyDrop (regain Γ)

regain-++ : ∀{Γ} (Δₑ : LL.KndCtx) →
            UC.eraseRen (regain (injCtx Δₑ ++ Γ)) ≡
            UC.eraseRen (C.TyKeep* (regain Γ) (injCtx Δₑ))
regain-++ [] = refl
regain-++ (κₑ ∷ Δₑ) = cong UC.UKeep $ regain-++ Δₑ

---------------------------
-- TYPE OPERATION LEMMAS --
---------------------------

{-
proj ∘ inj ≗ id

Injecting and then projecting a type has no effect
-}

erase-projVar∘injVar≗erase : ∀{Γ1 Γ2 Γ3 κ1 κ2 κ3}
                            (p1 : injCtx Γ1 ≡ Γ2)
                            (p2 : projCtx Γ2 ≡ Γ3)
                            (q1 : CtrlLocKnd κ1 ≡ κ2)
                            (q2 : κ2 ≡ CtrlLocKnd κ3)
                            (x : LL.TyVar Γ1 κ1) →
                            ULL.eraseVar (projTyVar p2 q2 (injTyVar p1 q1 x))
                            ≡ ULL.eraseVar x
erase-projVar∘injVar≗erase refl refl refl refl TV0 = refl
erase-projVar∘injVar≗erase refl refl refl refl (TVS x) =
  cong suc (erase-projVar∘injVar≗erase refl refl refl refl x)

projTyRel∘injTyRel⇒idRel : MorRel⇒ (projTyRel ∘ᵣₖ injTyRel) idRel
α⇒ projTyRel∘injTyRel⇒idRel (Γ2 , p , q) = sym (projCtx∘injCtx≗id _) ∙ cong projCtx q ∙ p
β⇒ projTyRel∘injTyRel⇒idRel (κ2 , p , q) = CtrlLocKnd-inj $ q ∙ p
δ⇒ projTyRel∘injTyRel⇒idRel (Δ2 , p , q) = sym (projCtx∘injCtx≗id _) ∙ cong projCtx q ∙ p
μ⇒ projTyRel∘injTyRel⇒idRel (Σ2 , p , q) = map-injective CtrlLocKndΣ-inj (q ∙ p)
μ-tail-≡ projTyRel∘injTyRel⇒idRel (Σ2 , p , q) = UIP _ _
μ-head-δ-≡ projTyRel∘injTyRel⇒idRel (Σ2 , p , q) = UIP _ _
μ-head-β-≡ projTyRel∘injTyRel⇒idRel (Σ2 , p , q) = UIP _ _

proj∘inj≈id : projTyMor ∘ₘ injTyMor ≈ idMor
mor-rel-⇒ proj∘inj≈id = projTyRel∘injTyRel⇒idRel
γ1≗γ2-Path proj∘inj≈id s βκ = refl
γ-resp-arg-≡-Path proj∘inj≈id s βκ p = UIP _ _
var1≗var2-Path proj∘inj≈id {Γ1 = Γ1} (_ , refl , refl) (_ , refl , refl) x =
  cong LL.tyVar $ ULL.eraseVar-inj $
  ULL.eraseVar (projTyVar refl refl (injTyVar refl refl x))
    ≡⟨ erase-projVar∘injVar≗erase refl refl refl refl x ⟩
  ULL.eraseVar x
    ≡⟨ ULL.subst₂-eraseVar (sym (projCtx∘injCtx≗id Γ1) ∙ refl) refl x ⟩
  ULL.eraseVar (subst₂ LL.TyVar (sym (projCtx∘injCtx≗id Γ1) ∙ refl) refl x) ∎
δ-++-α-Path proj∘inj≈id _ _ = UIP _ _

-- Projecting after injecting a local type has no effect
erase-projTy∘injTy≗erase : ∀{Γ1 Γ2 Γ3 κ1 κ2 κ3}
                          (p1 : injCtx Γ1 ≡ Γ2)
                          (p2 : projCtx Γ2 ≡ Γ3)
                          (q1 : CtrlLocKnd κ1 ≡ κ2)
                          (q2 : κ2 ≡ CtrlLocKnd κ3)
                          (e : LL.Ty Γ1 κ1) →
                          ULL.erase (mor projTyMor p2 q2 (injTyH p1 q1 e))
                          ≡ ULL.erase e
erase-projTy∘injTy≗erase {Γ1} {Γ2} {Γ3} {κ1} {κ2} {κ3} p1 p2 q1 q2 e =
  ULL.erase (mor projTyMor p2 q2 (injTyH p1 q1 e))
    ≡⟨ (cong ULL.erase $ ∘ₘ≗∘ projTyMor injTyMor (Γ2 , p2 , p1) (κ2 , q2 , q1) e) ⟩
  ULL.erase (mor (projTyMor ∘ₘ injTyMor) (Γ2 , p2 , p1) (κ2 , q2 , q1) e)
    ≡⟨ cong ULL.erase (mor-≡ proj∘inj≈id (Γ2 , p2 , p1) (κ2 , q2 , q1) e) ⟩
  ULL.erase (mor idMor _ _ e)
    ≡⟨ erase-idMor≗id _ _ e ⟩
  ULL.erase e ∎

{-
⟨regain⟩ ∘ inj ∘ proj ≗ id

Projecting, then injecting, then regaining lost
variables has no effect on a type
-}

-- Restrict the identity relation to injected contexts and types
local-idRel : MorRel C⅀₂ C⅀₂
α local-idRel = _≡_
β local-idRel κ1 κ2 = κ1 ≡ κ2 × Σ[ κₑ ∈ _ ] (κ1 ≡ CtrlLocKnd κₑ)
δ local-idRel Δ1 Δ2 = Δ1 ≡ Δ2 × Σ[ Δₑ ∈ _ ] (Δ1 ≡ injCtx Δₑ)
μ local-idRel Σ1 Σ2 = Σ1 ≡ Σ2 × Σ[ Σₑ ∈ _ ] (Σ1 ≡ map CtrlLocKndΣ Σₑ)
δ-++-α local-idRel (refl , Δₑ , refl) refl = refl
μ-nil local-idRel = refl , [] , refl
μ-head-δ local-idRel (refl , (Δₑ , κₑ) ∷ Σₑ , refl) = refl , Δₑ , refl
μ-head-β local-idRel (refl , (Δₑ , κₑ) ∷ Σₑ , refl) = refl , κₑ , refl
μ-tail local-idRel (refl , (Δₑ , κₑ) ∷ Σₑ , refl) = refl , Σₑ , refl
μ-cons-nil local-idRel (() , _)
μ-nil-cons local-idRel (() , _)

local-idRel⇒idRel : MorRel⇒ local-idRel idRel
α⇒ local-idRel⇒idRel p = p
β⇒ local-idRel⇒idRel (p , κₑ , q) = p
δ⇒ local-idRel⇒idRel (p , Δₑ , q) = p
μ⇒ local-idRel⇒idRel (p , Σₑ , q) = p
μ-tail-≡ local-idRel⇒idRel (refl , (Δₑ , κₑ) ∷ Σₑ , refl) = refl
μ-head-δ-≡ local-idRel⇒idRel (refl , (Δₑ , κₑ) ∷ Σₑ , refl) = refl
μ-head-β-≡ local-idRel⇒idRel (refl , (Δₑ , κₑ) ∷ Σₑ , refl) = refl

local-idMor-γ-resp-arg : ∀{κ} (s : CtrlTyShape) →
                          (p : local-idRel .β (CtrlTyPos s .snd) κ) →
                          local-idRel .μ (CtrlTyPos s .fst) (CtrlTyPos s .fst)
local-idMor-γ-resp-arg (CtrlLocalTy sₑ) (p , κₑ , q) = refl , TyPosₑ sₑ .fst , refl

local-idMor : LangMor C⅀₂ C⅀₂
local-idMor =
  restr-mor local-idRel idMor local-idRel⇒idRel
    local-idMor-γ-resp-arg

local-id≈id : local-idMor ≈ idMor
local-id≈id =
  restr-mor-path idMor local-idRel⇒idRel
    local-idMor-γ-resp-arg
    (λ{ (CtrlLocalTy sₑ) (p , κₑ , q) refl → refl })
    λ{ (refl , Δₑ , refl) refl → refl }

idRel⇒regainRel∘injRel∘projRel : MorRel⇒ local-idRel (renRel ∘ᵣₖ injTyRel ∘ᵣₖ projTyRel)
α⇒ idRel⇒regainRel∘injRel∘projRel {Γ1} {Γ2} p =
  injCtx (projCtx Γ2) , regain Γ2 , projCtx Γ2 , refl , cong projCtx p
β⇒ idRel⇒regainRel∘injRel∘projRel {κ1} {κ2} (p , κₑ , q) =
  κ2 , refl , κₑ , sym q ∙ p , q
δ⇒ idRel⇒regainRel∘injRel∘projRel {Δ1} {Δ2} (p , Δₑ , q) =
  Δ2 , refl , Δₑ , sym q ∙ p , cong projCtx q ∙ projCtx∘injCtx≗id Δₑ
μ⇒ idRel⇒regainRel∘injRel∘projRel {Σ1} {Σ2} (p , Σₑ , q) =
  Σ2 , refl , Σₑ , sym q ∙ p , q
μ-tail-≡ idRel⇒regainRel∘injRel∘projRel (refl , (Δₑ , κₑ) ∷ Σₑ , refl) = refl
μ-head-δ-≡ idRel⇒regainRel∘injRel∘projRel (refl , (Δₑ , κₑ) ∷ Σₑ , refl) = refl
μ-head-β-≡ idRel⇒regainRel∘injRel∘projRel (refl , (Δₑ , κₑ) ∷ Σₑ , refl) = refl

id≗regainVar∘injVar∘projVar : ∀{Γ1 Γ2 κ1 κ2 κₑ}
                              (Γ1≡Γ2 : Γ1 ≡ Γ2) (κ1≡κ2 : κ1 ≡ κ2)
                              (κ1≡κₑ : κ1 ≡ CtrlLocKnd κₑ)
                              (x : C.TyVar Γ1 κ1) →
                              subst₂ C.TyVar Γ1≡Γ2 κ1≡κ2 x ≡
                              C.tyRenVar (regain Γ2)
                                (injTyVar refl (sym κ1≡κₑ ∙ κ1≡κ2)
                                  (projTyVar (cong projCtx Γ1≡Γ2) κ1≡κₑ x))
id≗regainVar∘injVar∘projVar refl refl refl TV0 = refl
id≗regainVar∘injVar∘projVar {CtrlLocKnd κₑ ∷ Γ} refl refl refl (C.TVS x) =
  cong C.TVS (id≗regainVar∘injVar∘projVar refl refl refl x)
id≗regainVar∘injVar∘projVar {*Ctrl ∷ Γ} refl refl refl (C.TVS x) =
  cong C.TVS (id≗regainVar∘injVar∘projVar refl refl refl x)
id≗regainVar∘injVar∘projVar {*Ctrlₗ ∷ Γ} refl refl refl (C.TVS x) =
  cong C.TVS (id≗regainVar∘injVar∘projVar refl refl refl x)
id≗regainVar∘injVar∘projVar {*Ctrlₛ ∷ Γ} refl refl refl (C.TVS x) =
  cong C.TVS (id≗regainVar∘injVar∘projVar refl refl refl x)

id≈regain∘inj∘proj : local-idMor ≈ renMor ∘ₘ injTyMor ∘ₘ projTyMor
mor-rel-⇒ id≈regain∘inj∘proj = idRel⇒regainRel∘injRel∘projRel
γ1≗γ2-Path id≈regain∘inj∘proj (CtrlLocalTy s) (p , κₑ , q) = refl
γ-resp-arg-≡-Path id≈regain∘inj∘proj (CtrlLocalTy s) (refl , κₑ , refl) refl = refl
var1≗var2-Path id≈regain∘inj∘proj refl (refl , κₑ , refl) x =
  cong C.tyVar (id≗regainVar∘injVar∘projVar refl refl refl x)
δ-++-α-Path id≈regain∘inj∘proj {.(injCtx Δₑ)} {.(injCtx Δₑ)} {Γ1} {Γ2} (refl , Δₑ , refl) r =
  let eq = cong injCtx (projCtx-++ (injCtx Δₑ) Γ2)
            ∙ injCtx-++ (projCtx (injCtx Δₑ)) (projCtx Γ2)
            ∙ (cong (_++ injCtx (projCtx Γ2)) $ cong injCtx $ projCtx∘injCtx≗id Δₑ)
  in Σ-≡-→-≡-Σ eq $
    subst (λ x → C.TyRen x (injCtx Δₑ ++ Γ2) ×
              ((λ Γₑ Γ → injCtx Γₑ ≡ Γ) ∘ᵣ (λ Γ Γₑ → projCtx Γ ≡ Γₑ)) (injCtx Δₑ ++ Γ1) x)
      eq
      (regain (injCtx Δₑ ++ Γ2) ,
        projCtx (injCtx Δₑ ++ Γ2) ,
        refl ,
        cong projCtx (local-idMor .mor-rel .δ-++-α (refl , Δₑ , refl) r))
      ≡⟨ subst-× (λ x → C.TyRen x (injCtx Δₑ ++ Γ2))
          (((λ Γₑ Γ → injCtx Γₑ ≡ Γ) ∘ᵣ (λ Γ Γₑ → projCtx Γ ≡ Γₑ)) (injCtx Δₑ ++ Γ1))
          eq
          (regain (injCtx Δₑ ++ Γ2))
          (projCtx (injCtx Δₑ ++ Γ2) ,
            refl ,
            cong projCtx (local-idMor .mor-rel .δ-++-α (refl , Δₑ , refl) r)) ⟩
    (subst (λ x → C.TyRen x (injCtx Δₑ ++ Γ2)) eq
      (regain (injCtx Δₑ ++ Γ2)) ,
      subst (((λ Γₑ Γ → injCtx Γₑ ≡ Γ) ∘ᵣ (λ Γ Γₑ → projCtx Γ ≡ Γₑ)) (injCtx Δₑ ++ Γ1))
        eq
        (projCtx (injCtx Δₑ ++ Γ2) ,
        refl ,
        cong projCtx (local-idMor .mor-rel .δ-++-α (refl , Δₑ , refl) r)))
      ≡⟨ cong₂ _,_
        (UC.eraseRen-inj $
          sym (UC.subst-fst-eraseRen eq (regain (injCtx Δₑ ++ Γ2)))
          ∙ regain-++ Δₑ)
        (Σ-≡-→-≡-Σ
          (subst-Σ-fst (λ x → _) (λ x Γₑ' → map CtrlLocKnd Γₑ' ≡ x × projCtx (map CtrlLocKnd Δₑ ++ Γ1) ≡ Γₑ')
              eq
              (projCtx (injCtx Δₑ ++ Γ2))
              (refl , cong projCtx (local-idMor .mor-rel .δ-++-α (refl , Δₑ , refl) r))
            ∙ subst-const eq (projCtx (injCtx Δₑ ++ Γ2))
            ∙ projCtx-++ (injCtx Δₑ) Γ2
            ∙ cong (_++ projCtx Γ2) (projCtx∘injCtx≗id Δₑ))
          (×-isProp UIP UIP _ _)) ⟩
    (C.TyKeep* (regain Γ2) (injCtx Δₑ) ,
      Δₑ ++ projCtx Γ2 ,
      injCtx-++ Δₑ (projCtx Γ2) ,
      projTyRel .δ-++-α {injCtx Δₑ} {Δₑ} {Γ1} {projCtx Γ2} (projCtx∘injCtx≗id Δₑ) (cong projCtx r)) ∎

id≗regain∘inj∘proj : ∀{Γ κₑ}
                     (e : C.Ty Γ (CtrlLocKnd κₑ)) →
                     e ≡ C.tyRen (regain Γ) (injTy (projTy e))
id≗regain∘inj∘proj {Γ} e =
  e
    ≡⟨ (sym $ idMor≗id (mor-rel-⇒ local-id≈id .α⇒ refl)
          (mor-rel-⇒ local-id≈id .β⇒ (refl , _ , refl))
          e) ⟩
  mor idMor (mor-rel-⇒ local-id≈id .α⇒ refl)
    (mor-rel-⇒ local-id≈id .β⇒ (refl , _ , refl))
    e
    ≡⟨ (sym $ mor-≡ local-id≈id refl (refl , _ , refl) e) ⟩
  mor local-idMor refl (refl , _ , refl) e
    ≡⟨ mor-≡ id≈regain∘inj∘proj refl (refl , _ , refl) e ⟩
  mor (renMor ∘ₘ injTyMor ∘ₘ projTyMor)
    (_ , regain Γ , _ , refl , refl)
    (_ , refl , _ , refl , refl)
    e
    ≡⟨ (sym $ ∘ₘ≗∘ renMor (injTyMor ∘ₘ projTyMor)
          (_ , regain Γ , _ , refl , refl)
          (_ , refl , _ , refl , refl)
          e) ⟩
  mor renMor (regain Γ) refl
    (mor (injTyMor ∘ₘ projTyMor)
      (projCtx Γ , refl , refl)
      (_ , refl , refl)
      e)
    ≡⟨ (cong (mor renMor (regain Γ) refl) $
          sym $ ∘ₘ≗∘ injTyMor projTyMor
          (projCtx Γ , refl , refl)
          (_ , refl , refl)
          e) ⟩
  mor renMor (regain Γ) refl
    (injTy (projTy e))
    ≡⟨ renMor≗ren (regain Γ) refl (injTy (projTy e)) ⟩
  C.tyRen (regain Γ) (injTy (projTy e)) ∎

------------------------------
-- TYPE RENAMING OPERATIONS --
------------------------------

-- Project a renaming onto the projected contexts
projRen : ∀{Γ1 Γ2} → C.TyRen Γ1 Γ2 → LL.TyRen (projCtx Γ1) (projCtx Γ2)
projRen ε = LL.ε
projRen {CtrlLocKnd κₑ ∷ Γ1} (TyKeep ξ) = LL.TyKeep (projRen ξ)
projRen {*Ctrl ∷ Γ1} (TyKeep ξ) = projRen ξ
projRen {*Ctrlₗ ∷ Γ1} (TyKeep ξ) = projRen ξ
projRen {*Ctrlₛ ∷ Γ1} (TyKeep ξ) = projRen ξ
projRen {Γ2 = CtrlLocKnd κₑ ∷ Γ2} (TyDrop ξ) = LL.TyDrop (projRen ξ)
projRen {Γ2 = *Ctrl ∷ Γ2} (TyDrop ξ) = projRen ξ
projRen {Γ2 = *Ctrlₗ ∷ Γ2} (TyDrop ξ) = projRen ξ
projRen {Γ2 = *Ctrlₛ ∷ Γ2} (TyDrop ξ) = projRen ξ

-- Projecting renamings respects the identity
projRen-Id≡Id : ∀{Γ} → projRen (C.TyIdRen {Γ}) ≡ LL.TyIdRen
projRen-Id≡Id {[]} = refl
projRen-Id≡Id {CtrlLocKnd κₑ ∷ Γ} = cong LL.TyKeep $ projRen-Id≡Id {Γ}
projRen-Id≡Id {*Ctrl ∷ Γ} = projRen-Id≡Id {Γ}
projRen-Id≡Id {*Ctrlₗ ∷ Γ} = projRen-Id≡Id {Γ}
projRen-Id≡Id {*Ctrlₛ ∷ Γ} = projRen-Id≡Id {Γ}

-- Projecting renamings distributes over Keep
erase-projRen-distr-Keep*Ctrl : ∀{Γ1 Γ2} (ξ : C.TyRen Γ1 Γ2) (Δ : List CtrlKnd) →
                            ULL.eraseRen (projRen (C.TyKeep* ξ Δ))
                            ≡ ULL.eraseRen (LL.TyKeep* (projRen ξ) (projCtx Δ))
erase-projRen-distr-Keep*Ctrl ξ [] = refl
erase-projRen-distr-Keep*Ctrl ξ (CtrlLocKnd κₑ ∷ Δ) = cong ULL.UKeep (erase-projRen-distr-Keep*Ctrl ξ Δ)
erase-projRen-distr-Keep*Ctrl ξ (*Ctrl ∷ Δ) = erase-projRen-distr-Keep*Ctrl ξ Δ
erase-projRen-distr-Keep*Ctrl ξ (*Ctrlₗ ∷ Δ) = erase-projRen-distr-Keep*Ctrl ξ Δ
erase-projRen-distr-Keep*Ctrl ξ (*Ctrlₛ ∷ Δ) = erase-projRen-distr-Keep*Ctrl ξ Δ

{-
proj ∘ ⟨ξ⟩ ≗ ⟨proj ξ⟩ ∘ proj

Renaming and then projecting is the same as
projecting and then renaming on the projected renaming
-}
projTyRel∘renRel⇒renRel∘projTyRel : MorRel⇒ (projTyRel ∘ᵣₖ renRel) (renRel ∘ᵣₖ projTyRel)
α⇒ projTyRel∘renRel⇒renRel∘projTyRel {Γ1} {Γₑ} (Γ2 , p , ξ) =
  projCtx Γ1 , subst (LL.TyRen (projCtx Γ1)) p (projRen ξ) , refl
β⇒ projTyRel∘renRel⇒renRel∘projTyRel {κ1} {κₑ} (κ2 , p , q) =
  κₑ , refl , q ∙ p
δ⇒ projTyRel∘renRel⇒renRel∘projTyRel {Δ1} {Δₑ} (Δ2 , p , q) =
  Δₑ , refl , cong projCtx q ∙ p
μ⇒ projTyRel∘renRel⇒renRel∘projTyRel {Σ1} {Σₑ} (Σ2 , p , q) =
  Σₑ , refl , q ∙ p
μ-tail-≡ projTyRel∘renRel⇒renRel∘projTyRel (_ , refl , refl) = refl
μ-head-δ-≡ projTyRel∘renRel⇒renRel∘projTyRel (_ , refl , refl) = refl
μ-head-β-≡ projTyRel∘renRel⇒renRel∘projTyRel (_ , refl , refl) = refl

proj∘⟨ξ⟩≗⟨proj-ξ⟩∘proj-var : ∀{Γ1 Γ2 Γₑ κ1 κ2 κₑ}
                              (p : projCtx Γ2 ≡ Γₑ) (ξ : C.TyRen Γ1 Γ2)
                              (q : κ2 ≡ CtrlLocKnd κₑ) (r : κ1 ≡ κ2)
                              (x : C.TyVar Γ1 κ1) →
                              projTyVar p q (subst (C.TyVar Γ2) r (C.tyRenVar ξ x))
                              ≡ LL.tyRenVar
                                (subst (LL.TyRen (projCtx Γ1)) p (projRen ξ))
                                (projTyVar refl (r ∙ q) x)
proj∘⟨ξ⟩≗⟨proj-ξ⟩∘proj-var refl ε refl refl ()
proj∘⟨ξ⟩≗⟨proj-ξ⟩∘proj-var {Γ2 = CtrlLocKnd κₑ' ∷ Γ2} refl (TyKeep ξ) refl refl TV0 = refl
proj∘⟨ξ⟩≗⟨proj-ξ⟩∘proj-var {Γ2 = CtrlLocKnd κₑ' ∷ Γ2} refl (TyKeep ξ) refl refl (TVS x) =
  cong LL.TVS (proj∘⟨ξ⟩≗⟨proj-ξ⟩∘proj-var refl ξ refl refl x)
proj∘⟨ξ⟩≗⟨proj-ξ⟩∘proj-var {Γ2 = CtrlLocKnd κₑ' ∷ Γ2} refl (TyDrop ξ) refl refl x =
  cong LL.TVS (proj∘⟨ξ⟩≗⟨proj-ξ⟩∘proj-var refl ξ refl refl x)
proj∘⟨ξ⟩≗⟨proj-ξ⟩∘proj-var {Γ2 = *Ctrl ∷ Γ2} refl (TyKeep ξ) refl refl (TVS x) =
  proj∘⟨ξ⟩≗⟨proj-ξ⟩∘proj-var refl ξ refl refl x
proj∘⟨ξ⟩≗⟨proj-ξ⟩∘proj-var {Γ2 = *Ctrl ∷ Γ2} refl (TyDrop ξ) refl refl x =
  proj∘⟨ξ⟩≗⟨proj-ξ⟩∘proj-var refl ξ refl refl x
proj∘⟨ξ⟩≗⟨proj-ξ⟩∘proj-var {Γ2 = *Ctrlₗ ∷ Γ2} refl (TyKeep ξ) refl refl (TVS x) =
  proj∘⟨ξ⟩≗⟨proj-ξ⟩∘proj-var refl ξ refl refl x
proj∘⟨ξ⟩≗⟨proj-ξ⟩∘proj-var {Γ2 = *Ctrlₗ ∷ Γ2} refl (TyDrop ξ) refl refl x =
  proj∘⟨ξ⟩≗⟨proj-ξ⟩∘proj-var refl ξ refl refl x
proj∘⟨ξ⟩≗⟨proj-ξ⟩∘proj-var {Γ2 = *Ctrlₛ ∷ Γ2} refl (TyKeep ξ) refl refl (TVS x) =
  proj∘⟨ξ⟩≗⟨proj-ξ⟩∘proj-var refl ξ refl refl x
proj∘⟨ξ⟩≗⟨proj-ξ⟩∘proj-var {Γ2 = *Ctrlₛ ∷ Γ2} refl (TyDrop ξ) refl refl x =
  proj∘⟨ξ⟩≗⟨proj-ξ⟩∘proj-var refl ξ refl refl x

proj∘⟨ξ⟩≈⟨proj-ξ⟩∘proj : projTyMor ∘ₘ renMor ≈ renMor ∘ₘ projTyMor
mor-rel-⇒ proj∘⟨ξ⟩≈⟨proj-ξ⟩∘proj = projTyRel∘renRel⇒renRel∘projTyRel
γ1≗γ2-Path proj∘⟨ξ⟩≈⟨proj-ξ⟩∘proj s (_ , p , refl) = refl
γ-resp-arg-≡-Path proj∘⟨ξ⟩≈⟨proj-ξ⟩∘proj s (_ , p , refl) refl = refl
var1≗var2-Path proj∘⟨ξ⟩≈⟨proj-ξ⟩∘proj {Γ1} (Γ2 , p , ξ) (κ1 , q , refl) x =
  ULL.erase-inj $ cong (ULL.var ∘ ULL.eraseVar) $ proj∘⟨ξ⟩≗⟨proj-ξ⟩∘proj-var p ξ q refl x
δ-++-α-Path proj∘⟨ξ⟩≈⟨proj-ξ⟩∘proj {.Δ2} {.(projCtx Δ2)} {Γ1} {.(projCtx Γ2)}
  (Δ2 , refl , refl) (Γ2 , refl , ξ) =
  Σ-≡-→-≡-Σ (projCtx-++ Δ2 Γ1) $
  subst (λ x → LL.TyRen x (projCtx Δ2 ++ projCtx Γ2) × projCtx (Δ2 ++ Γ1) ≡ x)
    (projCtx-++ Δ2 Γ1)
    (subst (LL.TyRen (projCtx (Δ2 ++ Γ1))) (projCtx-++ Δ2 Γ2)
      (projRen (C.TyKeep* ξ Δ2))
  , refl)
    ≡⟨ subst-× (λ x → LL.TyRen x (projCtx Δ2 ++ projCtx Γ2)) (λ x → projCtx (Δ2 ++ Γ1) ≡ x)
          (projCtx-++ Δ2 Γ1)
          (subst (LL.TyRen (projCtx (Δ2 ++ Γ1))) (projCtx-++ Δ2 Γ2)
            (projRen (C.TyKeep* ξ Δ2)))
          refl ⟩
  (subst (λ x → LL.TyRen x (projCtx Δ2 ++ projCtx Γ2))
    (projCtx-++ Δ2 Γ1)
    (subst (LL.TyRen (projCtx (Δ2 ++ Γ1))) (projCtx-++ Δ2 Γ2)
      (projRen (C.TyKeep* ξ Δ2)))
  , subst (λ x → projCtx (Δ2 ++ Γ1) ≡ x) (projCtx-++ Δ2 Γ1) refl)
    ≡⟨ cong₂ _,_
        (ULL.eraseRen-inj $
          ULL.eraseRen (subst (λ x → LL.TyRen x (projCtx Δ2 ++ projCtx Γ2))
            (projCtx-++ Δ2 Γ1)
            (subst (LL.TyRen (projCtx (Δ2 ++ Γ1))) (projCtx-++ Δ2 Γ2)
              (projRen (C.TyKeep* ξ Δ2))))
              ≡⟨ (sym $ ULL.subst-fst-eraseRen (projCtx-++ Δ2 Γ1)
                    (subst (LL.TyRen (projCtx (Δ2 ++ Γ1))) (projCtx-++ Δ2 Γ2)
                      (projRen (C.TyKeep* ξ Δ2)))) ⟩
            ULL.eraseRen (subst (LL.TyRen (projCtx (Δ2 ++ Γ1)))
              (projCtx-++ Δ2 Γ2)
              (projRen (C.TyKeep* ξ Δ2)))
              ≡⟨ (sym $ ULL.subst-snd-eraseRen (projCtx-++ Δ2 Γ2)
                    (projRen (C.TyKeep* ξ Δ2))) ⟩
            ULL.eraseRen (projRen (C.TyKeep* ξ Δ2))
              ≡⟨ erase-projRen-distr-Keep*Ctrl ξ Δ2 ⟩
            ULL.eraseRen (LL.TyKeep* (projRen ξ) (projCtx Δ2)) ∎)
        (UIP _ _) ⟩
  (LL.TyKeep* (projRen ξ) (projCtx Δ2) , projCtx-++ Δ2 Γ1) ∎

proj∘⟨ξ⟩≗⟨proj-ξ⟩∘proj : ∀{Γ1 Γ2 κₑ} (ξ : C.TyRen Γ1 Γ2) (e : C.Ty Γ1 (CtrlLocKnd κₑ)) →
                         projTy (C.tyRen ξ e) ≡ LL.tyRen (projRen ξ) (projTy e)
proj∘⟨ξ⟩≗⟨proj-ξ⟩∘proj ξ e =
  mor projTyMor refl refl (C.tyRen ξ e)
    ≡⟨ (cong (mor projTyMor refl refl) $ sym $ renMor≗ren ξ refl e) ⟩
  mor projTyMor refl refl (mor renMor ξ refl e)
    ≡⟨ ∘ₘ≗∘ projTyMor renMor (_ , refl , ξ) (_ , refl , refl) e ⟩
  mor (projTyMor ∘ₘ renMor) (_ , refl , ξ) (_ , refl , refl) e
    ≡⟨ mor-≡ proj∘⟨ξ⟩≈⟨proj-ξ⟩∘proj (_ , refl , ξ) (_ , refl , refl) e ⟩
  mor (renMor ∘ₘ projTyMor) (_ , projRen ξ , refl) (_ , refl , refl) e
    ≡⟨ (sym $ ∘ₘ≗∘ renMor projTyMor (_ , projRen ξ , refl) (_ , refl , refl) e) ⟩
  mor renMor (projRen ξ) refl (mor projTyMor refl refl e)
    ≡⟨ renMor≗ren (projRen ξ) refl (mor projTyMor refl refl e) ⟩
  LL.tyRen (projRen ξ) (mor projTyMor refl refl e) ∎

-- Inject a renaming into the injected contexts
injRen : ∀{Γ1 Γ2} → LL.TyRen Γ1 Γ2 → C.TyRen (injCtx Γ1) (injCtx Γ2)
injRen ε = C.ε
injRen (TyKeep ξ) = C.TyKeep (injRen ξ)
injRen (TyDrop ξ) = C.TyDrop (injRen ξ)

-- Injecting renamings respects the identity
injRen-Id≡Id : ∀{Γ} → injRen (LL.TyIdRen {Γ}) ≡ C.TyIdRen
injRen-Id≡Id {[]} = refl
injRen-Id≡Id {κₑ ∷ Γ} = cong C.TyKeep $ injRen-Id≡Id {Γ}

-- regain • inj (proj ξ) ≡ ξ • regain
regain•inj-proj-ξ≡ξ•regain : ∀{Γ1 Γ2} (ξ : C.TyRen Γ1 Γ2) →
                              regain Γ2 C.• injRen (projRen ξ)
                              ≡ ξ C.• regain Γ1
regain•inj-proj-ξ≡ξ•regain ε = refl
regain•inj-proj-ξ≡ξ•regain {CtrlLocKnd κₑ ∷ Γ1} (TyKeep ξ) =
  cong C.TyKeep $ regain•inj-proj-ξ≡ξ•regain ξ
regain•inj-proj-ξ≡ξ•regain {*Ctrl ∷ Γ1} (TyKeep ξ) =
  cong C.TyDrop $ regain•inj-proj-ξ≡ξ•regain ξ
regain•inj-proj-ξ≡ξ•regain {*Ctrlₗ ∷ Γ1} (TyKeep ξ) =
  cong C.TyDrop $ regain•inj-proj-ξ≡ξ•regain ξ
regain•inj-proj-ξ≡ξ•regain {*Ctrlₛ ∷ Γ1} (TyKeep ξ) =
  cong C.TyDrop $ regain•inj-proj-ξ≡ξ•regain ξ
regain•inj-proj-ξ≡ξ•regain {Γ2 = CtrlLocKnd κₑ ∷ Γ2} (TyDrop ξ) =
  cong C.TyDrop $ regain•inj-proj-ξ≡ξ•regain ξ
regain•inj-proj-ξ≡ξ•regain {Γ2 = *Ctrl ∷ Γ2} (TyDrop ξ) =
  cong C.TyDrop $ regain•inj-proj-ξ≡ξ•regain ξ
regain•inj-proj-ξ≡ξ•regain {Γ2 = *Ctrlₗ ∷ Γ2} (TyDrop ξ) =
  cong C.TyDrop $ regain•inj-proj-ξ≡ξ•regain ξ
regain•inj-proj-ξ≡ξ•regain {Γ2 = *Ctrlₛ ∷ Γ2} (TyDrop ξ) =
  cong C.TyDrop $ regain•inj-proj-ξ≡ξ•regain ξ

-- Injecting projections distributes over Keep
erase-injRen-distr-Keep*Ctrl : ∀{Γ1 Γ2} (ξ : LL.TyRen Γ1 Γ2) (Δ : List Kndₑ) →
                            UC.eraseRen (injRen (LL.TyKeep* ξ Δ))
                            ≡ UC.eraseRen (C.TyKeep* (injRen ξ) (injCtx Δ))
erase-injRen-distr-Keep*Ctrl ξ [] = refl
erase-injRen-distr-Keep*Ctrl ξ (κ ∷ Δ) =
  cong UC.UKeep $ erase-injRen-distr-Keep*Ctrl ξ Δ

{-
inj ∘ ⟨ξ⟩ ≗ ⟨inj ξ⟩ ∘ inj

Injecting and then renaming is the same as
renaming on the projected renaming and then injecting
-}
injTyRel∘renRel⇒renRel∘injTyRel : MorRel⇒ (injTyRel ∘ᵣₖ renRel) (renRel ∘ᵣₖ injTyRel)
α⇒ injTyRel∘renRel⇒renRel∘injTyRel {Γ1ₑ} {Γ2} (Γ2ₑ , p , ξ) =
  injCtx Γ1ₑ , subst (C.TyRen (injCtx Γ1ₑ)) p (injRen ξ) , refl
β⇒ injTyRel∘renRel⇒renRel∘injTyRel {κ1ₑ} {κ2} (κ2ₑ , p , q) =
  κ2 , refl , cong CtrlLocKnd q ∙ p
δ⇒ injTyRel∘renRel⇒renRel∘injTyRel {Δ1ₑ} {Δ2} (Δ2ₑ , p , q) =
  Δ2 , refl , cong injCtx q ∙ p
μ⇒ injTyRel∘renRel⇒renRel∘injTyRel {Σ1ₑ} {Σ2} (Σ2ₑ , p , q) =
  Σ2 , refl , cong (map CtrlLocKndΣ) q ∙ p
μ-tail-≡ injTyRel∘renRel⇒renRel∘injTyRel (_ , refl , refl) = refl
μ-head-δ-≡ injTyRel∘renRel⇒renRel∘injTyRel (_ , refl , refl) = refl
μ-head-β-≡ injTyRel∘renRel⇒renRel∘injTyRel (_ , refl , refl) = refl

inj∘⟨ξ⟩≗⟨inj-ξ⟩∘inj-var : ∀{Γ1ₑ Γ2ₑ Γ2 κ1ₑ κ2ₑ κ2}
                          (p : injCtx Γ2ₑ ≡ Γ2) (ξ : LL.TyRen Γ1ₑ Γ2ₑ)
                          (q : CtrlLocKnd κ2ₑ ≡ κ2) (r : κ1ₑ ≡ κ2ₑ)
                          (x : LL.TyVar Γ1ₑ κ1ₑ) →
                          injTyVar p q (subst (LL.TyVar Γ2ₑ) r (LL.tyRenVar ξ x))
                          ≡ C.tyRenVar
                            (subst (C.TyRen (injCtx Γ1ₑ)) p (injRen ξ))
                            (injTyVar refl (cong CtrlLocKnd r ∙ q) x)
inj∘⟨ξ⟩≗⟨inj-ξ⟩∘inj-var refl (TyKeep ξ) refl refl TV0 = refl
inj∘⟨ξ⟩≗⟨inj-ξ⟩∘inj-var refl (TyKeep ξ) refl refl (TVS x) =
  cong C.TVS $ inj∘⟨ξ⟩≗⟨inj-ξ⟩∘inj-var refl ξ refl refl x
inj∘⟨ξ⟩≗⟨inj-ξ⟩∘inj-var refl (TyDrop ξ) refl refl x =
  cong C.TVS $ inj∘⟨ξ⟩≗⟨inj-ξ⟩∘inj-var refl ξ refl refl x

inj∘⟨ξ⟩≈⟨inj-ξ⟩∘inj : injTyMor ∘ₘ renMor ≈ renMor ∘ₘ injTyMor
mor-rel-⇒ inj∘⟨ξ⟩≈⟨inj-ξ⟩∘inj = injTyRel∘renRel⇒renRel∘injTyRel
γ1≗γ2-Path inj∘⟨ξ⟩≈⟨inj-ξ⟩∘inj s (_ , refl , refl) = refl
γ-resp-arg-≡-Path inj∘⟨ξ⟩≈⟨inj-ξ⟩∘inj s (_ , refl , refl) refl = refl
var1≗var2-Path inj∘⟨ξ⟩≈⟨inj-ξ⟩∘inj (_ , refl , ξ) (_ , q , refl) x =
  cong C.tyVar $ inj∘⟨ξ⟩≗⟨inj-ξ⟩∘inj-var refl ξ q refl x
δ-++-α-Path inj∘⟨ξ⟩≈⟨inj-ξ⟩∘inj {.Δ1ₑ} {.(injCtx Δ1ₑ)} {Γ1ₑ} {.(injCtx Γ2ₑ)}
  (Δ1ₑ , refl , refl) (Γ2ₑ , refl , ξ) =
  Σ-≡-→-≡-Σ (injCtx-++ Δ1ₑ Γ1ₑ) $
  subst (λ x → C.TyRen x (injCtx Δ1ₑ ++ injCtx Γ2ₑ) × injCtx (Δ1ₑ ++ Γ1ₑ) ≡ x)
    (injCtx-++ Δ1ₑ Γ1ₑ)
    (subst (C.TyRen (injCtx (Δ1ₑ ++ Γ1ₑ))) (injCtx-++ Δ1ₑ Γ2ₑ)
      (injRen (LL.TyKeep* ξ Δ1ₑ))
  , refl)
    ≡⟨ subst-× (λ x → C.TyRen x (injCtx Δ1ₑ ++ injCtx Γ2ₑ)) (λ x → injCtx (Δ1ₑ ++ Γ1ₑ) ≡ x)
        (injCtx-++ Δ1ₑ Γ1ₑ)
        (subst (C.TyRen (injCtx (Δ1ₑ ++ Γ1ₑ))) (injCtx-++ Δ1ₑ Γ2ₑ)
          (injRen (LL.TyKeep* ξ Δ1ₑ)))
        refl ⟩
  (subst (λ x → C.TyRen x (injCtx Δ1ₑ ++ injCtx Γ2ₑ))
    (injCtx-++ Δ1ₑ Γ1ₑ)
    (subst (C.TyRen (injCtx (Δ1ₑ ++ Γ1ₑ))) (injCtx-++ Δ1ₑ Γ2ₑ)
      (injRen (LL.TyKeep* ξ Δ1ₑ)))
  , subst (λ x → injCtx (Δ1ₑ ++ Γ1ₑ) ≡ x) (injCtx-++ Δ1ₑ Γ1ₑ) refl)
    ≡⟨ cong₂ _,_ (UC.eraseRen-inj $
      UC.eraseRen (subst (λ x → C.TyRen x (injCtx Δ1ₑ ++ injCtx Γ2ₑ))
        (injCtx-++ Δ1ₑ Γ1ₑ)
        (subst (C.TyRen (injCtx (Δ1ₑ ++ Γ1ₑ))) (injCtx-++ Δ1ₑ Γ2ₑ)
          (injRen (LL.TyKeep* ξ Δ1ₑ))))
        ≡⟨ (sym $ UC.subst-fst-eraseRen (injCtx-++ Δ1ₑ Γ1ₑ)
              (subst (C.TyRen (injCtx (Δ1ₑ ++ Γ1ₑ))) (injCtx-++ Δ1ₑ Γ2ₑ)
                (injRen (LL.TyKeep* ξ Δ1ₑ)))) ⟩
      UC.eraseRen (subst (C.TyRen (injCtx (Δ1ₑ ++ Γ1ₑ)))
        (injCtx-++ Δ1ₑ Γ2ₑ)
        (injRen (LL.TyKeep* ξ Δ1ₑ)))
        ≡⟨ (sym $ UC.subst-snd-eraseRen (injCtx-++ Δ1ₑ Γ2ₑ)
            (injRen (LL.TyKeep* ξ Δ1ₑ))) ⟩
      UC.eraseRen (injRen (LL.TyKeep* ξ Δ1ₑ))
        ≡⟨ erase-injRen-distr-Keep*Ctrl ξ Δ1ₑ ⟩
      UC.eraseRen (C.TyKeep* (injRen ξ) (injCtx Δ1ₑ)) ∎)
      (UIP _ _) ⟩
  (C.TyKeep* (injRen ξ) (injCtx Δ1ₑ) , injCtx-++ Δ1ₑ Γ1ₑ) ∎

inj∘⟨ξ⟩≗⟨inj-ξ⟩∘inj : ∀{Γ1 Γ2 κₑ} (ξ : LL.TyRen Γ1 Γ2) (e : LL.Ty Γ1 κₑ) →
                      injTy (LL.tyRen ξ e) ≡ C.tyRen (injRen ξ) (injTy e)
inj∘⟨ξ⟩≗⟨inj-ξ⟩∘inj ξ e =
  injTy (LL.tyRen ξ e)
    ≡⟨ (cong injTy $ sym $ renMor≗ren ξ refl e) ⟩
  injTy (mor renMor ξ refl e)
    ≡⟨ ∘ₘ≗∘ injTyMor renMor (_ , refl , ξ) (_ , refl , refl) e ⟩
  mor (injTyMor ∘ₘ renMor) (_ , refl , ξ) (_ , refl , refl) e
    ≡⟨ mor-≡ inj∘⟨ξ⟩≈⟨inj-ξ⟩∘inj (_ , refl , ξ) (_ , refl , refl) e ⟩
  mor (renMor ∘ₘ injTyMor) (_ , injRen ξ , refl) (_ , refl , refl) e
    ≡⟨ (sym $ ∘ₘ≗∘ renMor injTyMor (_ , injRen ξ , refl) (_ , refl , refl) e) ⟩
  mor renMor (injRen ξ) refl (mor injTyMor refl refl e)
    ≡⟨ renMor≗ren (injRen ξ) refl (mor injTyMor refl refl e) ⟩
  C.tyRen (injRen ξ) (injTy e) ∎

----------------------------------
-- TYPE SUBSTUTITION OPERATIONS --
----------------------------------

-- Project a substitution onto the projected contexts
projSub : ∀{Γ1 Γ2} → C.TySub Γ1 Γ2 → LL.TySub (projCtx Γ1) (projCtx Γ2)
projSub ε = LL.ε
projSub {CtrlLocKnd κₑ ∷ Γ1} (σ ▸ e) = projSub σ LL.▸ mor projTyMor refl refl e
projSub {*Ctrl ∷ Γ1} (σ ▸ e) = projSub σ
projSub {*Ctrlₗ ∷ Γ1} (σ ▸ e) = projSub σ
projSub {*Ctrlₛ ∷ Γ1} (σ ▸ e) = projSub σ

-- Projecting distributes over combining a renaming and substitution
proj-distr-•◦ : ∀{Γ1 Γ2 Γ3} (ξ : C.TyRen Γ2 Γ3) (σ : C.TySub Γ1 Γ2) →
                projSub (ξ C.•◦ₜ σ) ≡ projRen ξ LL.•◦ₜ projSub σ
proj-distr-•◦ ξ ε = refl
proj-distr-•◦ {Γ1 = CtrlLocKnd κₑ ∷ Γ1} ξ (σ ▸ e) =
  cong₂ LL._▸_
    (proj-distr-•◦ ξ σ)
    (proj∘⟨ξ⟩≗⟨proj-ξ⟩∘proj ξ e)
proj-distr-•◦ {Γ1 = *Ctrl ∷ Γ1} ξ (σ ▸ e) =
  proj-distr-•◦ ξ σ
proj-distr-•◦ {Γ1 = *Ctrlₗ ∷ Γ1} ξ (σ ▸ e) =
  proj-distr-•◦ ξ σ
proj-distr-•◦ {Γ1 = *Ctrlₛ ∷ Γ1} ξ (σ ▸ e) =
  proj-distr-•◦ ξ σ

-- Projecting substitutions distributes over Drop
TyDropSubProj : ∀{Γ1 Γ2} → LL.TySub Γ1 Γ2 → (κ : CtrlKnd) → LL.TySub Γ1 (projCtx (κ ∷ []) ++ Γ2)
TyDropSubProj σ (CtrlLocKnd κₑ) = LL.TyDropSub σ
TyDropSubProj σ *Ctrl = σ
TyDropSubProj σ *Ctrlₗ = σ
TyDropSubProj σ *Ctrlₛ = σ

eraseTyDropSubProj : ULL.USub → CtrlKnd → ULL.USub
eraseTyDropSubProj σ (CtrlLocKnd κₑ) = ULL.UDropSub σ
eraseTyDropSubProj σ *Ctrl = σ
eraseTyDropSubProj σ *Ctrlₗ = σ
eraseTyDropSubProj σ *Ctrlₛ = σ

erase-TyDropSubProj≡ : ∀{Γ1 Γ2} (σ : LL.TySub Γ1 Γ2) (κ : CtrlKnd) →
                       ULL.eraseSub (TyDropSubProj σ κ) ≡
                       eraseTyDropSubProj (ULL.eraseSub σ) κ
erase-TyDropSubProj≡ σ (CtrlLocKnd κₑ) = ULL.eraseSub-distr-DropSub σ
erase-TyDropSubProj≡ σ *Ctrl = refl
erase-TyDropSubProj≡ σ *Ctrlₗ = refl
erase-TyDropSubProj≡ σ *Ctrlₛ = refl

DropSubProj≡Drop∘projSub : ∀{Γ1 Γ2} (σ : C.TySub Γ1 Γ2) (Δ : List CtrlKnd) (κ : CtrlKnd) →
                           ULL.eraseSub (TyDropSubProj (LL.TyDropSub* (projSub σ) (projCtx Δ)) κ)
                           ≡ ULL.eraseSub (LL.TyDropSub* (projSub σ) (projCtx (κ ∷ Δ)))
DropSubProj≡Drop∘projSub σ Δ (CtrlLocKnd κₑ) = refl
DropSubProj≡Drop∘projSub σ Δ *Ctrl = refl
DropSubProj≡Drop∘projSub σ Δ *Ctrlₗ = refl
DropSubProj≡Drop∘projSub σ Δ *Ctrlₛ = refl

erase-projSub-distr-DropSubProj : ∀{Γ1 Γ2} (σ : C.TySub Γ1 Γ2) (κ : CtrlKnd) →
                                 ULL.eraseSub (projSub (C.TyDropSub {t = κ} σ))
                                 ≡ ULL.eraseSub (TyDropSubProj (projSub σ) κ)
erase-projSub-distr-DropSubProj {Γ1} {Γ2} σ (CtrlLocKnd κₑ) =
  ULL.eraseSub (projSub (C.TyDrop C.TyIdRen C.•◦ₜ σ))
    ≡⟨ (cong ULL.eraseSub $ proj-distr-•◦ (C.TyDrop C.TyIdRen) σ) ⟩
  ULL.eraseSub (projRen (C.TyDrop {t = CtrlLocKnd κₑ} (C.TyIdRen {Γ2})) LL.•◦ₜ projSub σ)
    ≡⟨ ULL.erase-distr-•◦
        (projRen (C.TyDrop {t = CtrlLocKnd κₑ} (C.TyIdRen {Γ2})))
        (projSub σ) ⟩
  ULL.UDrop (ULL.eraseRen (projRen (C.TyIdRen {Γ2})))
    ULL.•◦U ULL.eraseSub (projSub σ)
    ≡⟨ (cong (λ x → ULL.UDrop (ULL.eraseRen x)
              ULL.•◦U ULL.eraseSub (projSub σ)) $
          projRen-Id≡Id {Γ2}) ⟩
  ULL.UDrop (ULL.eraseRen LL.TyIdRen)
    ULL.•◦U ULL.eraseSub (projSub σ)
    ≡⟨ (sym $ ULL.erase-distr-•◦
        (LL.TyDrop LL.TyIdRen)
        (projSub σ)) ⟩
  ULL.eraseSub (LL.TyDrop LL.TyIdRen LL.•◦ₜ projSub σ) ∎
erase-projSub-distr-DropSubProj {Γ1} {Γ2} σ *Ctrl =
  ULL.eraseSub (projSub (C.TyDrop C.TyIdRen C.•◦ₜ σ))
    ≡⟨ (cong ULL.eraseSub $ proj-distr-•◦ (C.TyDrop C.TyIdRen) σ) ⟩
  ULL.eraseSub (projRen (C.TyIdRen {Γ2}) LL.•◦ₜ projSub σ)
    ≡⟨ (cong (λ x → ULL.eraseSub (x LL.•◦ₜ projSub σ)) $ projRen-Id≡Id {Γ2}) ⟩
  ULL.eraseSub (LL.TyIdRen LL.•◦ₜ projSub σ)
    ≡⟨ (cong ULL.eraseSub $ LL.Id•◦ (projSub σ)) ⟩
  ULL.eraseSub (projSub σ) ∎
erase-projSub-distr-DropSubProj {Γ1} {Γ2} σ *Ctrlₗ =
  ULL.eraseSub (projSub (C.TyDrop C.TyIdRen C.•◦ₜ σ))
    ≡⟨ (cong ULL.eraseSub $ proj-distr-•◦ (C.TyDrop C.TyIdRen) σ) ⟩
  ULL.eraseSub (projRen (C.TyIdRen {Γ2}) LL.•◦ₜ projSub σ)
    ≡⟨ (cong (λ x → ULL.eraseSub (x LL.•◦ₜ projSub σ)) $ projRen-Id≡Id {Γ2}) ⟩
  ULL.eraseSub (LL.TyIdRen LL.•◦ₜ projSub σ)
    ≡⟨ (cong ULL.eraseSub $ LL.Id•◦ (projSub σ)) ⟩
  ULL.eraseSub (projSub σ) ∎
erase-projSub-distr-DropSubProj {Γ1} {Γ2} σ *Ctrlₛ =
  ULL.eraseSub (projSub (C.TyDrop C.TyIdRen C.•◦ₜ σ))
    ≡⟨ (cong ULL.eraseSub $ proj-distr-•◦ (C.TyDrop C.TyIdRen) σ) ⟩
  ULL.eraseSub (projRen (C.TyIdRen {Γ2}) LL.•◦ₜ projSub σ)
    ≡⟨ (cong (λ x → ULL.eraseSub (x LL.•◦ₜ projSub σ)) $ projRen-Id≡Id {Γ2}) ⟩
  ULL.eraseSub (LL.TyIdRen LL.•◦ₜ projSub σ)
    ≡⟨ (cong ULL.eraseSub $ LL.Id•◦ (projSub σ)) ⟩
  ULL.eraseSub (projSub σ) ∎

erase-projSub-distr-DropSub*Ctrl : ∀{Γ1 Γ2} (σ : C.TySub Γ1 Γ2) (Δ : List CtrlKnd) →
                                ULL.eraseSub (projSub (C.TyDropSub* σ Δ))
                                ≡ ULL.eraseSub (LL.TyDropSub* (projSub σ) (projCtx Δ))
erase-projSub-distr-DropSub*Ctrl σ [] = refl
erase-projSub-distr-DropSub*Ctrl σ (κ ∷ Δ) =
  ULL.eraseSub (projSub (C.TyDropSub (C.TyDropSub* σ Δ)))
    ≡⟨ erase-projSub-distr-DropSubProj (C.TyDropSub* σ Δ) κ ⟩
  ULL.eraseSub (TyDropSubProj (projSub (C.TyDropSub* σ Δ)) κ)
    ≡⟨ erase-TyDropSubProj≡ (projSub (C.TyDropSub* σ Δ)) κ ⟩
  eraseTyDropSubProj (ULL.eraseSub (projSub (C.TyDropSub* σ Δ))) κ
    ≡⟨ (cong (flip eraseTyDropSubProj κ) $ erase-projSub-distr-DropSub*Ctrl σ Δ) ⟩
  eraseTyDropSubProj (ULL.eraseSub (LL.TyDropSub* (projSub σ) (projCtx Δ))) κ
    ≡⟨ (sym $ erase-TyDropSubProj≡ (LL.TyDropSub* (projSub σ) (projCtx Δ)) κ) ⟩
  ULL.eraseSub (TyDropSubProj (LL.TyDropSub* (projSub σ) (projCtx Δ)) κ)
    ≡⟨ DropSubProj≡Drop∘projSub σ Δ κ ⟩
  ULL.eraseSub (LL.TyDropSub* (projSub σ) (projCtx (κ ∷ Δ))) ∎

-- Projecting substitutions distributes over Keep
TyKeepSubProj : ∀{Γ1 Γ2} → LL.TySub Γ1 Γ2 → (κ : CtrlKnd) → LL.TySub (projCtx (κ ∷ []) ++ Γ1) (projCtx (κ ∷ []) ++ Γ2)
TyKeepSubProj σ (CtrlLocKnd κₑ) = LL.TyKeepSub σ
TyKeepSubProj σ *Ctrl = σ
TyKeepSubProj σ *Ctrlₗ = σ
TyKeepSubProj σ *Ctrlₛ = σ

eraseTyKeepSubProj : ULL.USub → CtrlKnd → ULL.USub
eraseTyKeepSubProj σ (CtrlLocKnd κₑ) = ULL.UKeepSub σ
eraseTyKeepSubProj σ *Ctrl = σ
eraseTyKeepSubProj σ *Ctrlₗ = σ
eraseTyKeepSubProj σ *Ctrlₛ = σ

erase-TyKeepSubProj≡ : ∀{Γ1 Γ2} (σ : LL.TySub Γ1 Γ2) (κ : CtrlKnd) →
                       ULL.eraseSub (TyKeepSubProj σ κ) ≡
                       eraseTyKeepSubProj (ULL.eraseSub σ) κ
erase-TyKeepSubProj≡ σ (CtrlLocKnd κₑ) = ULL.eraseSub-distr-KeepSub σ
erase-TyKeepSubProj≡ σ *Ctrl = refl
erase-TyKeepSubProj≡ σ *Ctrlₗ = refl
erase-TyKeepSubProj≡ σ *Ctrlₛ = refl

KeepSubProj≡Keep∘projSub : ∀{Γ1 Γ2} (σ : C.TySub Γ1 Γ2) (Δ : List CtrlKnd) (κ : CtrlKnd) →
                           ULL.eraseSub (TyKeepSubProj (LL.TyKeepSub* (projSub σ) (projCtx Δ)) κ)
                           ≡ ULL.eraseSub (LL.TyKeepSub* (projSub σ) (projCtx (κ ∷ Δ)))
KeepSubProj≡Keep∘projSub σ Δ (CtrlLocKnd κₑ) = refl
KeepSubProj≡Keep∘projSub σ Δ *Ctrl = refl
KeepSubProj≡Keep∘projSub σ Δ *Ctrlₗ = refl
KeepSubProj≡Keep∘projSub σ Δ *Ctrlₛ = refl

erase-projSub-distr-KeepSubProj : ∀{Γ1 Γ2} (σ : C.TySub Γ1 Γ2) (κ : CtrlKnd) →
                                 ULL.eraseSub (projSub (C.TyKeepSub {t = κ} σ))
                                 ≡ ULL.eraseSub (TyKeepSubProj (projSub σ) κ)
erase-projSub-distr-KeepSubProj {Γ1} {Γ2} σ (CtrlLocKnd κₑ) =
  cong₂ ULL._▹_
    (erase-projSub-distr-DropSubProj σ (CtrlLocKnd κₑ))
    refl
erase-projSub-distr-KeepSubProj {Γ1} {Γ2} σ *Ctrl =
  ULL.eraseSub (projSub (C.TyDrop (C.TyIdRen {Γ2}) C.•◦ₜ σ))
    ≡⟨ (cong ULL.eraseSub $ proj-distr-•◦ (C.TyDrop C.TyIdRen) σ) ⟩
  ULL.eraseSub (projRen (C.TyIdRen {Γ2}) LL.•◦ₜ projSub σ)
    ≡⟨ cong (λ x → ULL.eraseSub (x LL.•◦ₜ projSub σ)) (projRen-Id≡Id {Γ2}) ⟩
  ULL.eraseSub (LL.TyIdRen LL.•◦ₜ projSub σ)
    ≡⟨ (cong ULL.eraseSub $ LL.Id•◦ (projSub σ)) ⟩
  ULL.eraseSub (projSub σ) ∎
erase-projSub-distr-KeepSubProj {Γ1} {Γ2} σ *Ctrlₗ =
  ULL.eraseSub (projSub (C.TyDrop (C.TyIdRen {Γ2}) C.•◦ₜ σ))
    ≡⟨ (cong ULL.eraseSub $ proj-distr-•◦ (C.TyDrop C.TyIdRen) σ) ⟩
  ULL.eraseSub (projRen (C.TyIdRen {Γ2}) LL.•◦ₜ projSub σ)
    ≡⟨ cong (λ x → ULL.eraseSub (x LL.•◦ₜ projSub σ)) (projRen-Id≡Id {Γ2}) ⟩
  ULL.eraseSub (LL.TyIdRen LL.•◦ₜ projSub σ)
    ≡⟨ (cong ULL.eraseSub $ LL.Id•◦ (projSub σ)) ⟩
  ULL.eraseSub (projSub σ) ∎
erase-projSub-distr-KeepSubProj {Γ1} {Γ2} σ *Ctrlₛ =
  ULL.eraseSub (projSub (C.TyDrop (C.TyIdRen {Γ2}) C.•◦ₜ σ))
    ≡⟨ (cong ULL.eraseSub $ proj-distr-•◦ (C.TyDrop C.TyIdRen) σ) ⟩
  ULL.eraseSub (projRen (C.TyIdRen {Γ2}) LL.•◦ₜ projSub σ)
    ≡⟨ cong (λ x → ULL.eraseSub (x LL.•◦ₜ projSub σ)) (projRen-Id≡Id {Γ2}) ⟩
  ULL.eraseSub (LL.TyIdRen LL.•◦ₜ projSub σ)
    ≡⟨ (cong ULL.eraseSub $ LL.Id•◦ (projSub σ)) ⟩
  ULL.eraseSub (projSub σ) ∎

erase-projSub-distr-KeepSub*Ctrl : ∀{Γ1 Γ2} (σ : C.TySub Γ1 Γ2) (Δ : List CtrlKnd) →
                                ULL.eraseSub (projSub (C.TyKeepSub* σ Δ))
                                ≡ ULL.eraseSub (LL.TyKeepSub* (projSub σ) (projCtx Δ))
erase-projSub-distr-KeepSub*Ctrl σ [] = refl
erase-projSub-distr-KeepSub*Ctrl σ (κ ∷ Δ) =
  ULL.eraseSub (projSub (C.TyKeepSub {t = κ} (C.TyKeepSub* σ Δ)))
    ≡⟨ erase-projSub-distr-KeepSubProj (C.TyKeepSub* σ Δ) κ ⟩
  ULL.eraseSub (TyKeepSubProj (projSub (C.TyKeepSub* σ Δ)) κ)
    ≡⟨ erase-TyKeepSubProj≡ (projSub (C.TyKeepSub* σ Δ)) κ ⟩
  eraseTyKeepSubProj (ULL.eraseSub (projSub (C.TyKeepSub* σ Δ))) κ
    ≡⟨ (cong (flip eraseTyKeepSubProj κ) $ erase-projSub-distr-KeepSub*Ctrl σ Δ) ⟩
  eraseTyKeepSubProj (ULL.eraseSub (LL.TyKeepSub* (projSub σ) (projCtx Δ))) κ
    ≡⟨ (sym $ erase-TyKeepSubProj≡ (LL.TyKeepSub* (projSub σ) (projCtx Δ)) κ) ⟩
  ULL.eraseSub (TyKeepSubProj (LL.TyKeepSub* (projSub σ) (projCtx Δ)) κ)
    ≡⟨ KeepSubProj≡Keep∘projSub σ Δ κ ⟩
  ULL.eraseSub (LL.TyKeepSub* (projSub σ) (projCtx (κ ∷ Δ))) ∎

{-
proj ∘ ⟨σ⟩ ≗ ⟨proj σ⟩ ∘ proj

Substituting and then projecting is the same as
projecting and then substituting on the projected substitution
-}
projTyRel∘subRel⇒subRel∘projTyRel : MorRel⇒ (projTyRel ∘ᵣₖ subRel) (subRel ∘ᵣₖ projTyRel)
α⇒ projTyRel∘subRel⇒subRel∘projTyRel {Γ1} {Γₑ} (Γ2 , p , σ) =
  projCtx Γ1 , subst (LL.TySub (projCtx Γ1)) p (projSub σ) , refl
β⇒ projTyRel∘subRel⇒subRel∘projTyRel {κ1} {κₑ} (κ2 , p , q) =
  κₑ , refl , q ∙ p
δ⇒ projTyRel∘subRel⇒subRel∘projTyRel {Δ1} {Δₑ} (Δ2 , p , q) =
  Δₑ , refl , cong projCtx q ∙ p
μ⇒ projTyRel∘subRel⇒subRel∘projTyRel {Σ1} {Σₑ} (Σ2 , p , q) =
  Σₑ , refl , q ∙ p
μ-tail-≡ projTyRel∘subRel⇒subRel∘projTyRel (_ , refl , refl) = refl
μ-head-δ-≡ projTyRel∘subRel⇒subRel∘projTyRel (_ , refl , refl) = refl
μ-head-β-≡ projTyRel∘subRel⇒subRel∘projTyRel (_ , refl , refl) = refl

proj∘⟨σ⟩≗⟨proj-σ⟩∘proj-var : ∀{Γ1 Γ2 Γₑ κ1 κ2 κₑ}
                              (p : projCtx Γ2 ≡ Γₑ) (σ : C.TySub Γ1 Γ2)
                              (q : κ2 ≡ CtrlLocKnd κₑ) (r : κ1 ≡ κ2)
                              (x : C.TyVar Γ1 κ1) →
                              projTyH p q (subst (C.Ty Γ2) r (C.tySubVar σ x))
                              ≡ LL.tySubVar
                                (subst (LL.TySub (projCtx Γ1)) p (projSub σ))
                                (projTyVar refl (r ∙ q) x)
proj∘⟨σ⟩≗⟨proj-σ⟩∘proj-var refl ε refl refl ()
proj∘⟨σ⟩≗⟨proj-σ⟩∘proj-var refl (σ ▸ e) refl refl TV0 = refl
proj∘⟨σ⟩≗⟨proj-σ⟩∘proj-var {CtrlLocKnd κₑ ∷ Γ1} refl (σ ▸ e) refl refl (TVS x) =
  proj∘⟨σ⟩≗⟨proj-σ⟩∘proj-var refl σ refl refl x
proj∘⟨σ⟩≗⟨proj-σ⟩∘proj-var {*Ctrl ∷ Γ1} refl (σ ▸ e) refl refl (TVS x) =
  proj∘⟨σ⟩≗⟨proj-σ⟩∘proj-var refl σ refl refl x
proj∘⟨σ⟩≗⟨proj-σ⟩∘proj-var {*Ctrlₗ ∷ Γ1} refl (σ ▸ e) refl refl (TVS x) =
  proj∘⟨σ⟩≗⟨proj-σ⟩∘proj-var refl σ refl refl x
proj∘⟨σ⟩≗⟨proj-σ⟩∘proj-var {*Ctrlₛ ∷ Γ1} refl (σ ▸ e) refl refl (TVS x) =
  proj∘⟨σ⟩≗⟨proj-σ⟩∘proj-var refl σ refl refl x

proj∘⟨σ⟩≈⟨proj-σ⟩∘proj : projTyMor ∘ₘ subMor ≈ subMor ∘ₘ projTyMor
mor-rel-⇒ proj∘⟨σ⟩≈⟨proj-σ⟩∘proj = projTyRel∘subRel⇒subRel∘projTyRel
γ1≗γ2-Path proj∘⟨σ⟩≈⟨proj-σ⟩∘proj s (_ , p , refl) = refl
γ-resp-arg-≡-Path proj∘⟨σ⟩≈⟨proj-σ⟩∘proj s (_ , p , refl) refl = refl
var1≗var2-Path proj∘⟨σ⟩≈⟨proj-σ⟩∘proj (_ , p , σ) (_ , q , r) x =
  proj∘⟨σ⟩≗⟨proj-σ⟩∘proj-var p σ q r x
δ-++-α-Path proj∘⟨σ⟩≈⟨proj-σ⟩∘proj {.Δ} {.(projCtx Δ)} {Γ1} {.(projCtx Γ2)}
  (Δ , refl , refl) (Γ2 , refl , σ) =
    Σ-≡-→-≡-Σ (projCtx-++ Δ Γ1) $
    subst (λ x → LL.TySub x (projCtx Δ ++ projCtx Γ2) × projCtx (Δ ++ Γ1) ≡ x)
      (projCtx-++ Δ Γ1)
      (subst (LL.TySub (projCtx (Δ ++ Γ1))) (projCtx-++ Δ Γ2)
        (projSub (C.TyKeepSub* σ Δ))
    , refl)
      ≡⟨ subst-× (λ x → LL.TySub x (projCtx Δ ++ projCtx Γ2))
          (λ x → projCtx (Δ ++ Γ1) ≡ x)
           (projCtx-++ Δ Γ1)
           (subst (LL.TySub (projCtx (Δ ++ Γ1))) (projCtx-++ Δ Γ2)
              (projSub (C.TyKeepSub* σ Δ)))
            refl ⟩
    (subst (λ x → LL.TySub x (projCtx Δ ++ projCtx Γ2))
      (projCtx-++ Δ Γ1)
      (subst (LL.TySub (projCtx (Δ ++ Γ1))) (projCtx-++ Δ Γ2)
        (projSub (C.TyKeepSub* σ Δ)))
      , subst (λ x → projCtx (Δ ++ Γ1) ≡ x) (projCtx-++ Δ Γ1) refl)
      ≡⟨ cong₂ _,_ (ULL.eraseSub-inj $
          ULL.eraseSub (subst (λ x → LL.TySub x (projCtx Δ ++ projCtx Γ2))
            (projCtx-++ Δ Γ1)
            (subst (LL.TySub (projCtx (Δ ++ Γ1))) (projCtx-++ Δ Γ2)
              (projSub (C.TyKeepSub* σ Δ))))
            ≡⟨ (sym $ ULL.subst-fst-eraseSub (projCtx-++ Δ Γ1)
                (subst (LL.TySub (projCtx (Δ ++ Γ1))) (projCtx-++ Δ Γ2)
                  (projSub (C.TyKeepSub* σ Δ)))) ⟩
          ULL.eraseSub (subst (LL.TySub (projCtx (Δ ++ Γ1))) 
            (projCtx-++ Δ Γ2)
            (projSub (C.TyKeepSub* σ Δ)))
            ≡⟨ (sym $ ULL.subst-snd-eraseSub (projCtx-++ Δ Γ2) (projSub (C.TyKeepSub* σ Δ))) ⟩
          ULL.eraseSub (projSub (C.TyKeepSub* σ Δ))
            ≡⟨ erase-projSub-distr-KeepSub*Ctrl σ Δ ⟩
          ULL.eraseSub (LL.TyKeepSub* (projSub σ) (projCtx Δ)) ∎)
          (UIP _ _) ⟩
    (LL.TyKeepSub* (projSub σ) (projCtx Δ) , projCtx-++ Δ Γ1) ∎

proj∘⟨σ⟩≗⟨proj-σ⟩∘proj-vec : ∀{Γ1 Γ2 Σ} (σ : C.TySub Γ1 Γ2)
                              (es : C.TyVec Γ1 (map CtrlLocKndΣ Σ))  →
                              projTyVec (C.tySubVec σ es)
                              ≡ LL.tySubVec (projSub σ) (projTyVec es)
proj∘⟨σ⟩≗⟨proj-σ⟩∘proj-vec σ es =
  projTyVec (C.tySubVec σ es)
    ≡⟨ (cong projTyVec $ sym $ subMor≗sub-vec σ refl es) ⟩
  mor-vec projTyMor refl refl (mor-vec subMor σ refl es)
    ≡⟨ ∘ₘ≗∘-vec projTyMor subMor (_ , refl , σ) (_ , refl , refl) es ⟩
  mor-vec (projTyMor ∘ₘ subMor) (_ , refl , σ) (_ , refl , refl) es
    ≡⟨ mor-vec-≡ proj∘⟨σ⟩≈⟨proj-σ⟩∘proj (_ , refl , σ) (_ , refl , refl) es ⟩
  mor-vec (subMor ∘ₘ projTyMor) (_ , projSub σ , refl) (_ , refl , refl) es
    ≡⟨ sym $ ∘ₘ≗∘-vec subMor projTyMor  (_ , projSub σ , refl) (_ , refl , refl) es ⟩
  mor-vec subMor (projSub σ) refl (projTyVec es)
    ≡⟨ subMor≗sub-vec (projSub σ) refl (projTyVec es) ⟩
  LL.tySubVec (projSub σ) (projTyVec es) ∎

-- Inject a substitution into the injected contexts
injSub : ∀{Γ1 Γ2} → LL.TySub Γ1 Γ2 → C.TySub (injCtx Γ1) (injCtx Γ2)
injSub ε = C.ε
injSub (σ ▸ e) = injSub σ C.▸ injTy e

erase-injSub-subst₂ : ∀{Γ1 Γ2 Γ1' Γ2'} (p : Γ1 ≡ Γ1') (q : Γ2 ≡ Γ2')
                      (σ : LL.TySub Γ1 Γ2) →
                      UC.eraseSub (injSub (subst₂ LL.TySub p q σ)) ≡
                      UC.eraseSub (injSub σ)
erase-injSub-subst₂ refl refl σ = refl                      

cong-erase-injSub : ∀{Γ1 Γ2 Γ1' Γ2'} {σ1 : LL.TySub Γ1 Γ2} {σ2 : LL.TySub Γ1' Γ2'} →
                    Γ1 ≡ Γ1' → Γ2 ≡ Γ2' →
                    ULL.eraseSub σ1 ≡ ULL.eraseSub σ2 →
                    UC.eraseSub (injSub σ1) ≡ UC.eraseSub (injSub σ2)
cong-erase-injSub {σ1 = σ1} {σ2} p q r =
  UC.eraseSub (injSub σ1)
    ≡⟨ (sym $ erase-injSub-subst₂ p q σ1) ⟩
  UC.eraseSub (injSub (subst₂ LL.TySub p q σ1))
    ≡⟨ (cong (λ x → UC.eraseSub (injSub x)) $ ULL.eraseSub-injH p q r) ⟩
  UC.eraseSub (injSub σ2) ∎

regain•◦inj-proj-σ≡σ◦•regain : ∀{Γ1 Γ2} (σ : C.TySub Γ1 Γ2) →
                                regain Γ2 C.•◦ₜ injSub (projSub σ)
                                ≡ σ C.◦•ₜ regain Γ1
regain•◦inj-proj-σ≡σ◦•regain ε = refl
regain•◦inj-proj-σ≡σ◦•regain {CtrlLocKnd κₑ ∷ Γ1} {Γ2} (σ ▸ e) =
  cong₂ C._▸_
    (regain•◦inj-proj-σ≡σ◦•regain σ)
    (sym $ id≗regain∘inj∘proj e)
regain•◦inj-proj-σ≡σ◦•regain {*Ctrl ∷ Γ1} (σ ▸ e) =
  regain•◦inj-proj-σ≡σ◦•regain σ
regain•◦inj-proj-σ≡σ◦•regain {*Ctrlₗ ∷ Γ1} (σ ▸ e) =
  regain•◦inj-proj-σ≡σ◦•regain σ
regain•◦inj-proj-σ≡σ◦•regain {*Ctrlₛ ∷ Γ1} (σ ▸ e) =
  regain•◦inj-proj-σ≡σ◦•regain σ

erase-regain•◦inj-proj-σ≡σ◦•regain : ∀{Γ1 Γ2} (σ : C.TySub Γ1 Γ2) →
                                      UC.eraseRen (regain Γ2) UC.•◦U UC.eraseSub (injSub (projSub σ))
                                      ≡ UC.eraseSub σ UC.◦•U UC.eraseRen (regain Γ1)
erase-regain•◦inj-proj-σ≡σ◦•regain {Γ1} {Γ2} σ =
  UC.eraseRen (regain Γ2) UC.•◦U UC.eraseSub (injSub (projSub σ))
    ≡⟨ (sym $ UC.erase-distr-•◦ (regain Γ2) (injSub (projSub σ))) ⟩
  UC.eraseSub (regain Γ2 C.•◦ₜ injSub (projSub σ))
    ≡⟨ cong UC.eraseSub $ regain•◦inj-proj-σ≡σ◦•regain σ ⟩
  UC.eraseSub (σ C.◦•ₜ regain Γ1)
    ≡⟨ UC.erase-distr-◦• σ (regain Γ1) ⟩
  UC.eraseSub σ UC.◦•U UC.eraseRen (regain Γ1) ∎

-- Injecting distributes over combining a renaming and substitution
inj-distr-•◦ : ∀{Γ1 Γ2 Γ3} (ξ : LL.TyRen Γ2 Γ3) (σ : LL.TySub Γ1 Γ2) →
                injSub (ξ LL.•◦ₜ σ) ≡ injRen ξ C.•◦ₜ injSub σ
inj-distr-•◦ ξ ε = refl
inj-distr-•◦ ξ (σ ▸ e) =
  cong₂ C._▸_
    (inj-distr-•◦ ξ σ)
    (inj∘⟨ξ⟩≗⟨inj-ξ⟩∘inj ξ e)

injSub-distr-Drop : ∀{Γ1 Γ2 κₑ} (σ : LL.TySub Γ1 Γ2) →
                    injSub (LL.TyDropSub {t = κₑ} σ)
                    ≡ C.TyDropSub {t = CtrlLocKnd κₑ} (injSub σ)
injSub-distr-Drop σ =
  injSub (LL.TyDrop LL.TyIdRen LL.•◦ₜ σ)
    ≡⟨ inj-distr-•◦ (LL.TyDrop LL.TyIdRen) σ ⟩
  C.TyDrop (injRen LL.TyIdRen) C.•◦ₜ injSub σ
    ≡⟨ (cong (λ x → C.TyDrop x C.•◦ₜ injSub σ) $ injRen-Id≡Id) ⟩
  C.TyDrop C.TyIdRen C.•◦ₜ injSub σ ∎

erase-injSub-distr-Keep*Ctrl : ∀{Γ1 Γ2} (σ : LL.TySub Γ1 Γ2) (Δ : List Kndₑ) →
                            UC.eraseSub (injSub (LL.TyKeepSub* σ Δ))
                            ≡ UC.eraseSub (C.TyKeepSub* (injSub σ) (injCtx Δ))
erase-injSub-distr-Keep*Ctrl σ [] = refl
erase-injSub-distr-Keep*Ctrl σ (κₑ ∷ Δ) = cong₂ UC._▹_ (
  UC.eraseSub (injSub (LL.TyDropSub (LL.TyKeepSub* σ Δ)))
    ≡⟨ (cong UC.eraseSub $ injSub-distr-Drop (LL.TyKeepSub* σ Δ)) ⟩
  UC.eraseSub (C.TyDropSub (injSub (LL.TyKeepSub* σ Δ)))
    ≡⟨ UC.eraseSub-distr-DropSub (injSub (LL.TyKeepSub* σ Δ)) ⟩
  UC.UDropSub (UC.eraseSub (injSub (LL.TyKeepSub* σ Δ)))
    ≡⟨ (cong UC.UDropSub $ erase-injSub-distr-Keep*Ctrl σ Δ) ⟩
  UC.UDropSub (UC.eraseSub (C.TyKeepSub* (injSub σ) (injCtx Δ)))
    ≡⟨ sym $ UC.eraseSub-distr-DropSub $ C.TyKeepSub* (injSub σ) (injCtx Δ) ⟩
  UC.eraseSub (C.TyDropSub (C.TyKeepSub* (injSub σ) (injCtx Δ))) ∎)
  refl

{-
inj ∘ ⟨σ⟩ ≗ ⟨inj σ⟩ ∘ inj

Substituting and then injecting is the same as
injecting and then substituting on the injected substitution
-}
injTyRel∘subRel⇒subRel∘injTyRel : MorRel⇒ (injTyRel ∘ᵣₖ subRel) (subRel ∘ᵣₖ injTyRel)
α⇒ injTyRel∘subRel⇒subRel∘injTyRel {Γ1ₑ} {Γ2} (Γ2ₑ , p , σ) =
  injCtx Γ1ₑ , subst (C.TySub (injCtx Γ1ₑ)) p (injSub σ) , refl
β⇒ injTyRel∘subRel⇒subRel∘injTyRel {κ1ₑ} {κ2} (κ2ₑ , p , q) =
  κ2 , refl , cong CtrlLocKnd q ∙ p
δ⇒ injTyRel∘subRel⇒subRel∘injTyRel {Δ1ₑ} {Δ2} (Δ2ₑ , p , q) =
  Δ2 , refl , cong injCtx q ∙ p
μ⇒ injTyRel∘subRel⇒subRel∘injTyRel {Σ1ₑ} {Σ2} (Σ2ₑ , p , q) =
  Σ2 , refl , cong (map CtrlLocKndΣ) q ∙ p
μ-tail-≡ injTyRel∘subRel⇒subRel∘injTyRel (_ , refl , refl) = refl
μ-head-δ-≡ injTyRel∘subRel⇒subRel∘injTyRel (_ , refl , refl) = refl
μ-head-β-≡ injTyRel∘subRel⇒subRel∘injTyRel (_ , refl , refl) = refl

inj∘⟨σ⟩≗⟨inj-σ⟩∘inj-var : ∀{Γ1ₑ Γ2ₑ Γ2 κ1ₑ κ2ₑ κ2}
                          (p : injCtx Γ2ₑ ≡ Γ2) (σ : LL.TySub Γ1ₑ Γ2ₑ)
                          (q : CtrlLocKnd κ2ₑ ≡ κ2) (r : κ1ₑ ≡ κ2ₑ)
                          (x : LL.TyVar Γ1ₑ κ1ₑ) →
                          injTyH p q (subst (LL.Ty Γ2ₑ) r (LL.tySubVar σ x))
                          ≡ C.tySubVar
                            (subst (C.TySub (injCtx Γ1ₑ)) p (injSub σ))
                            (injTyVar refl (cong CtrlLocKnd r ∙ q) x)
inj∘⟨σ⟩≗⟨inj-σ⟩∘inj-var p ε q r ()
inj∘⟨σ⟩≗⟨inj-σ⟩∘inj-var refl (σ ▸ e) refl refl TV0 = refl
inj∘⟨σ⟩≗⟨inj-σ⟩∘inj-var refl (σ ▸ e) refl refl (TVS x) =
  inj∘⟨σ⟩≗⟨inj-σ⟩∘inj-var refl σ refl refl x

inj∘⟨σ⟩≈⟨inj-σ⟩∘inj : injTyMor ∘ₘ subMor ≈ subMor ∘ₘ injTyMor
mor-rel-⇒ inj∘⟨σ⟩≈⟨inj-σ⟩∘inj = injTyRel∘subRel⇒subRel∘injTyRel
γ1≗γ2-Path inj∘⟨σ⟩≈⟨inj-σ⟩∘inj s (_ , refl , refl) = refl
γ-resp-arg-≡-Path inj∘⟨σ⟩≈⟨inj-σ⟩∘inj s (_ , refl , refl) refl = refl
var1≗var2-Path inj∘⟨σ⟩≈⟨inj-σ⟩∘inj (_ , refl , σ) (_ , q , refl) x =
  inj∘⟨σ⟩≗⟨inj-σ⟩∘inj-var refl σ q refl x
δ-++-α-Path inj∘⟨σ⟩≈⟨inj-σ⟩∘inj {.Δ1ₑ} {.(injCtx Δ1ₑ)} {Γ1ₑ} {.(injCtx Γ2ₑ)}
  (Δ1ₑ , refl , refl) (Γ2ₑ , refl , σ) =
  Σ-≡-→-≡-Σ (injCtx-++ Δ1ₑ Γ1ₑ) $
  subst (λ x → C.TySub x (injCtx Δ1ₑ ++ injCtx Γ2ₑ) × injCtx (Δ1ₑ ++ Γ1ₑ) ≡ x)
    (injCtx-++ Δ1ₑ Γ1ₑ)
    (subst (C.TySub (injCtx (Δ1ₑ ++ Γ1ₑ))) (injCtx-++ Δ1ₑ Γ2ₑ)
      (injSub (LL.TyKeepSub* σ Δ1ₑ))
  , refl)
    ≡⟨ subst-× (λ x → C.TySub x (injCtx Δ1ₑ ++ injCtx Γ2ₑ)) (λ x → injCtx (Δ1ₑ ++ Γ1ₑ) ≡ x)
        (injCtx-++ Δ1ₑ Γ1ₑ)
        (subst (C.TySub (injCtx (Δ1ₑ ++ Γ1ₑ))) (injCtx-++ Δ1ₑ Γ2ₑ)
          (injSub (LL.TyKeepSub* σ Δ1ₑ)))
        refl ⟩
  (subst (λ x → C.TySub x (injCtx Δ1ₑ ++ injCtx Γ2ₑ))
    (injCtx-++ Δ1ₑ Γ1ₑ)
    (subst (C.TySub (injCtx (Δ1ₑ ++ Γ1ₑ))) (injCtx-++ Δ1ₑ Γ2ₑ)
      (injSub (LL.TyKeepSub* σ Δ1ₑ)))
  , subst (λ x → injCtx (Δ1ₑ ++ Γ1ₑ) ≡ x) (injCtx-++ Δ1ₑ Γ1ₑ) refl)
    ≡⟨ cong₂ _,_ (UC.eraseSub-inj $
      UC.eraseSub (subst (λ x → C.TySub x (injCtx Δ1ₑ ++ injCtx Γ2ₑ))
        (injCtx-++ Δ1ₑ Γ1ₑ)
        (subst (C.TySub (injCtx (Δ1ₑ ++ Γ1ₑ))) (injCtx-++ Δ1ₑ Γ2ₑ)
          (injSub (LL.TyKeepSub* σ Δ1ₑ))))
        ≡⟨ (sym $ UC.subst-fst-eraseSub (injCtx-++ Δ1ₑ Γ1ₑ)
              (subst (C.TySub (injCtx (Δ1ₑ ++ Γ1ₑ))) (injCtx-++ Δ1ₑ Γ2ₑ)
                (injSub (LL.TyKeepSub* σ Δ1ₑ)))) ⟩
      UC.eraseSub (subst (C.TySub (injCtx (Δ1ₑ ++ Γ1ₑ)))
        (injCtx-++ Δ1ₑ Γ2ₑ)
        (injSub (LL.TyKeepSub* σ Δ1ₑ)))
        ≡⟨ (sym $ UC.subst-snd-eraseSub (injCtx-++ Δ1ₑ Γ2ₑ)
            (injSub (LL.TyKeepSub* σ Δ1ₑ))) ⟩
      UC.eraseSub (injSub (LL.TyKeepSub* σ Δ1ₑ))
        ≡⟨ erase-injSub-distr-Keep*Ctrl σ Δ1ₑ ⟩
      UC.eraseSub (C.TyKeepSub* (injSub σ) (injCtx Δ1ₑ)) ∎)
      (UIP _ _) ⟩
  (C.TyKeepSub* (injSub σ) (injCtx Δ1ₑ) , injCtx-++ Δ1ₑ Γ1ₑ) ∎

inj∘⟨σ⟩≗⟨inj-σ⟩∘inj : ∀{Γ1 Γ2 κₑ} (σ : LL.TySub Γ1 Γ2) (e : LL.Ty Γ1 κₑ) →
                      injTy (LL.tySub σ e) ≡ C.tySub (injSub σ) (injTy e)
inj∘⟨σ⟩≗⟨inj-σ⟩∘inj σ e =
  injTy (LL.tySub σ e)
    ≡⟨ (cong injTy $ sym $ subMor≗sub σ refl e) ⟩
  injTy (mor subMor σ refl e)
    ≡⟨ ∘ₘ≗∘ injTyMor subMor (_ , refl , σ) (_ , refl , refl) e ⟩
  mor (injTyMor ∘ₘ subMor) (_ , refl , σ) (_ , refl , refl) e
    ≡⟨ mor-≡ inj∘⟨σ⟩≈⟨inj-σ⟩∘inj (_ , refl , σ) (_ , refl , refl) e ⟩
  mor (subMor ∘ₘ injTyMor) (_ , injSub σ , refl) (_ , refl , refl) e
    ≡⟨ (sym $ ∘ₘ≗∘ subMor injTyMor (_ , injSub σ , refl) (_ , refl , refl) e) ⟩
  mor subMor (injSub σ) refl (mor injTyMor refl refl e)
    ≡⟨ subMor≗sub (injSub σ) refl (mor injTyMor refl refl e) ⟩
  C.tySub (injSub σ) (injTy e) ∎

---------------------------
-- THIRD-ORDER SIGNATURE --
---------------------------

data Choices : Set where
  Neither : Choices
  Left : Choices
  Right : Choices
  LeftRight : Choices

-- Control-language terms
data CtrlShape : Set where
  -- Embedding of local terms
  CtrlLocal : (sₑ : Shapeₑ) → CtrlShape
  -- Choreographic local terms
  CtrlDone : CtrlShape

  -- CtrlLambda abstraction
  CtrlLam : CtrlShape
  -- CtrlFixpoint
  CtrlFix : CtrlShape
  -- CtrlFunction application
  CtrlApp : CtrlShape
  -- Type abstraction
  CtrlAbs : (κ : CtrlKnd) → CtrlShape
  -- Type application
  CtrlAppTy : (κ : CtrlKnd) → CtrlShape
  -- Send operation
  CtrlSend : CtrlShape
  -- Receive operation
  CtrlRecv : CtrlShape
  -- Send synchronization operation
  CtrlChoose : Bool → CtrlShape
  -- Receive synchronization operation
  CtrlChoice : Choices → CtrlShape
  -- If-then-else
  CtrlITE : CtrlShape
  -- Unit
  CtrlUnit : CtrlShape
  CtrlFail : CtrlShape

  -- Binding local values
  CtrlLocalLet : CtrlShape
  -- Sending types
  CtrlSendTy : (κₑ : Kndₑ) → CtrlShape
  -- Sending locations
  CtrlSendLoc : CtrlShape

CTmTyPos : CtrlShape → List (List CtrlKnd × CtrlKnd)
CTmTyPos (CtrlLocal sₑ) = map CtrlLocKndΣ (TmTyPosₑ sₑ)
CTmTyPos CtrlDone = ([] , *Ctrlₑ) ∷ []
CTmTyPos CtrlLam = ([] , *Ctrl) ∷ ([] , *Ctrl) ∷ []
CTmTyPos CtrlFix = ([] , *Ctrl) ∷ []
CTmTyPos CtrlApp = ([] , *Ctrl) ∷ ([] , *Ctrl) ∷ []
CTmTyPos (CtrlAbs κ) = (κ ∷ [] , *Ctrl) ∷ []
CTmTyPos (CtrlAppTy κ) = (κ ∷ [] , *Ctrl) ∷ ([] , κ) ∷ []
CTmTyPos CtrlSend = ([] , *Ctrlₗ) ∷ ([] , *Ctrlₑ) ∷ []
CTmTyPos CtrlRecv = ([] , *Ctrlₗ) ∷ ([] , *Ctrlₑ) ∷ []
CTmTyPos (CtrlChoose d) = ([] , *Ctrlₗ) ∷ ([] , *Ctrl) ∷ []
CTmTyPos (CtrlChoice d) = ([] , *Ctrlₗ) ∷ ([] , *Ctrl) ∷ []
CTmTyPos CtrlITE = ([] , *Ctrl) ∷ []
CTmTyPos CtrlUnit = []
CTmTyPos CtrlFail = ([] , *Ctrl) ∷ []
CTmTyPos CtrlLocalLet = ([] , *Ctrlₑ) ∷ ([] , *Ctrl) ∷ []
CTmTyPos (CtrlSendTy κₑ) = ([] , *Ctrlₛ) ∷ ([] , *Ctrl) ∷ []
CTmTyPos CtrlSendLoc = ([] , *Ctrlₛ) ∷ ([] , *Ctrl) ∷ []

injTyp : ∀{Γ} → LL.Typ Γ → C.Typ (injCtx Γ)
injTyp (κₑ , t) = CtrlLocKnd κₑ , injTy t

injTypCtrlFun : ∀ Γ1 Γ2 → LL.Typ (Γ1 ++ projCtx Γ2) → C.Typ (injCtx Γ1 ++ Γ2)
injTypCtrlFun Γ1 Γ2 (κₑ , t) =
  CtrlLocKnd κₑ ,
  (C.tyRen (regain (injCtx Γ1 ++ Γ2)) $
    subst (flip C.Ty (CtrlLocKnd κₑ))
      (cong injCtx $
        (cong (_++ projCtx Γ2) $ sym $ projCtx∘injCtx≗id Γ1)
        ∙ (sym $ projCtx-++ (injCtx Γ1) Γ2)) $
      injTy t)

injBinderCtrlFun : (Γ : List CtrlKnd) → LL.Binder (projCtx Γ) →
                Σ[ Γ' ∈ List CtrlKnd ] (C.Ctx (Γ' ++ Γ) × C.Typ (Γ' ++ Γ))
injBinderCtrlFun Γ (Γ' , Δ , t) =
  injCtx Γ' ,
  map (injTypCtrlFun Γ' Γ) Δ ,
  injTypCtrlFun Γ' Γ t

CTmPos : (s : CtrlShape) (Γ : C.KndCtx) →
          C.TyVec Γ (CTmTyPos s) →
          List (Σ[ Γ' ∈ _ ] (C.Ctx (Γ' ++ Γ) × C.Typ (Γ' ++ Γ)))
          × C.Typ Γ
-- sₑ Σₑ : t ⊢ CtrlLocal{sₑ} Σₑ : ℓ.t
CTmPos (CtrlLocal sₑ) Γ ts =
  (map (injBinderCtrlFun Γ) $ TmPosₑ sₑ (projCtx Γ) (projTyVec ts) .fst) ,
  (CtrlLocKnd $ TmPosₑ sₑ (projCtx Γ) (projTyVec ts) .snd .fst) ,
  (C.tyRen (regain Γ) $ injTy (TmPosₑ sₑ (projCtx Γ) (projTyVec ts) .snd .snd))
-- CtrlDone (t : *Ctrlₑ) t : t@
CTmPos CtrlDone Γ (t ∷ []) = ([] , [] , *Ctrlₑ , t) ∷ [] , *Ctrl , TyCtrlAt t
-- CtrlLam (τ₁ τ₂ : *Ctrl) [τ₁]τ₂ : τ₁⇒τ₂
CTmPos CtrlLam Γ (τ₁ ∷ τ₂ ∷ []) = ([] , (*Ctrl , τ₁) ∷ [] , *Ctrl , τ₂) ∷ [] , *Ctrl , TyCtrlFun τ₁ τ₂
-- CtrlFix (τ : *Ctrl) [τ]τ : τ
CTmPos CtrlFix Γ (τ ∷ []) = ([] , (*Ctrl , τ) ∷ [] , *Ctrl , τ) ∷ [] , *Ctrl , τ
-- CtrlApp (τ₁ τ₂ : *Ctrl) τ₁⇒τ₂ τ₁ : τ₂
CTmPos CtrlApp Γ (τ₁ ∷ τ₂ ∷ []) = ([] , [] , *Ctrl , TyCtrlFun τ₁ τ₂) ∷ ([] , [] , *Ctrl , τ₁) ∷ [] , *Ctrl , τ₂
-- CtrlAbs (τ : [κ]*Ctrl) [κ]τ : ∀κ.τ
CTmPos (CtrlAbs κ) Γ (τ ∷ []) = (κ ∷ [] , [] , *Ctrl , τ) ∷ [] , *Ctrl , TyCtrlAll κ τ
-- CtrlAppTy (τ : [κ]*Ctrl) (v : κ) ∀κ.τ : τ⟨v⟩
CTmPos (CtrlAppTy κ) Γ (τ ∷ v ∷ []) = ([] , [] , *Ctrl , TyCtrlAll κ τ) ∷ [] , *Ctrl , C.tySub (C.TyIdSub C.▸ v) τ
-- CtrlSend (ℓ : *Ctrlₗ) (t : *Ctrlₑ) t@ : ⊤
CTmPos CtrlSend Γ (ℓ ∷ t ∷ []) = ([] , [] , *Ctrl , TyCtrlAt t) ∷ [] , *Ctrl , TyCtrlUnit
-- CtrlRecv (ℓ : *Ctrlₗ) (t : *Ctrlₑ) : t@
CTmPos CtrlRecv Γ (ℓ ∷ t ∷ []) = [] , *Ctrl , TyCtrlAt t
-- CtrlChoose{d} (ℓ : *Ctrlₗ) (τ : *Ctrl) τ : τ
CTmPos (CtrlChoose d) Γ (ℓ ∷ τ ∷ []) = ([] , [] , *Ctrl , τ) ∷ [] , *Ctrl , τ
CTmPos (CtrlChoice Neither) Γ (ℓ ∷ τ ∷ []) = [] , *Ctrl , τ
CTmPos (CtrlChoice Left) Γ (ℓ ∷ τ ∷ []) = ([] , [] , *Ctrl , τ) ∷ [] , *Ctrl , τ
CTmPos (CtrlChoice Right) Γ (ℓ ∷ τ ∷ []) = ([] , [] , *Ctrl , τ) ∷ [] , *Ctrl , τ
CTmPos (CtrlChoice LeftRight) Γ (ℓ ∷ τ ∷ []) = ([] , [] , *Ctrl , τ) ∷ ([] , [] , *Ctrl , τ) ∷ [] , *Ctrl , τ
-- CtrlITE (τ : *Ctrl) Boolₑ@ℓ τ τ : τ
CTmPos CtrlITE Γ (τ ∷ []) =
  ([] , [] , *Ctrl , TyCtrlAt (C.tyRen C.ε* (injTy (𝕃 .Boolₑ)))) ∷
  ([] , [] , *Ctrl , τ) ∷
  ([] , [] , *Ctrl , τ) ∷ [] ,
  *Ctrl , τ
CTmPos CtrlUnit Γ [] = [] , *Ctrl , TyCtrlUnit
CTmPos CtrlFail Γ (τ ∷ []) = [] , *Ctrl , τ
-- CtrlLocalLet (t : *Ctrlₑ) (τ : *Ctrl) @ℓ [t]τ : τ
CTmPos CtrlLocalLet Γ (t ∷ τ ∷ []) =
  ([] , [] , *Ctrl , TyCtrlAt t) ∷
  ([] , (*Ctrlₑ , t) ∷ [] , *Ctrl , τ) ∷ [] ,
  *Ctrl , τ
-- CtrlSendTy (ρ : *Ctrlₛ) (τ : *Ctrl) κₑ@ℓ [κₑ]τ : τ
CTmPos (CtrlSendTy κₑ) Γ (ρ ∷ τ ∷ []) =
  ([] , [] , *Ctrl , TyCtrlAt (C.tyRen C.ε* (injTy (𝕃 .TyRepₑ κₑ)))) ∷
  (CtrlLocKnd κₑ ∷ [] , [] , *Ctrl , C.tyWk τ) ∷ [] ,
  *Ctrl , τ
-- CtrlSendLoc (ρ : *Ctrlₛ) (τ : *Ctrl) Locₑ@ℓ [*Ctrlₗ]τ : τ
CTmPos CtrlSendLoc Γ (ρ ∷ τ ∷ []) =
  ([] , [] , *Ctrl , TyCtrlAt (C.tyRen C.ε* (injTy (𝕃 .Locₑ)))) ∷
  (*Ctrlₗ ∷ [] , [] , *Ctrl , C.tyWk τ) ∷ [] ,
  *Ctrl , τ

subVecCTmPos : ∀{Γ1 Γ2} (s : CtrlShape) (σ : C.TySub Γ1 Γ2) (ts : C.TyVec Γ1 (CTmTyPos s)) →
               CTmPos s Γ2 (C.tySubVec σ ts) .snd ≡
               C.subTyp σ (CTmPos s Γ1 ts .snd)
subVecCTmPos {Γ1} {Γ2} (CtrlLocal sₑ) σ ts =
  let eq : CtrlLocKnd (TmPosₑ sₑ (projCtx Γ2) (projTyVec (C.tySubVec σ ts)) .snd .fst)
            ≡ CtrlLocKnd (TmPosₑ sₑ (projCtx Γ1) (projTyVec ts) .snd .fst)
      eq = cong CtrlLocKnd $
        TmPosₑ sₑ (projCtx Γ2) (projTyVec (C.tySubVec σ ts)) .snd .fst
          ≡⟨ (cong (λ x → TmPosₑ sₑ (projCtx Γ2) x .snd .fst) $ proj∘⟨σ⟩≗⟨proj-σ⟩∘proj-vec σ ts) ⟩
        TmPosₑ sₑ (projCtx Γ2) (LL.tySubVec (projSub σ) (projTyVec ts)) .snd .fst
          ≡⟨ (cong fst $ 𝕃 .⅀ₑ .subVecTmPos sₑ (projSub σ) (projTyVec ts)) ⟩
        TmPosₑ sₑ (projCtx Γ1) (projTyVec ts) .snd .fst ∎
  in
  Σ-≡-→-≡-Σ eq $ UC.erase-inj $
  UC.erase (subst (C.Ty Γ2) eq
    (C.tyRen (regain Γ2)
      (injTy (TmPosₑ sₑ (projCtx Γ2) (projTyVec (C.tySubVec σ ts)) .snd .snd))))
    ≡⟨ (sym $ UC.substTy-erase eq 
          (C.tyRen (regain Γ2)
            (injTy
              (TmPosₑ sₑ (projCtx Γ2) (projTyVec (C.tySubVec σ ts)) .snd .snd)))) ⟩
  UC.erase (C.tyRen (regain Γ2)
    (injTy (TmPosₑ sₑ (projCtx Γ2) (projTyVec (C.tySubVec σ ts)) .snd .snd)))
    ≡⟨ (cong (λ x → UC.erase (C.tyRen (regain Γ2)
          (injTy
            (TmPosₑ sₑ (projCtx Γ2) x .snd .snd)))) $
          proj∘⟨σ⟩≗⟨proj-σ⟩∘proj-vec σ ts) ⟩
  UC.erase (C.tyRen (regain Γ2)
    (injTy (TmPosₑ sₑ (projCtx Γ2) (LL.tySubVec (projSub σ) (projTyVec ts)) .snd .snd)))
    ≡⟨ (cong (λ x → UC.erase (C.tyRen (regain Γ2) (injTy (x .snd)))) $
          𝕃 .⅀ₑ .subVecTmPos sₑ (projSub σ) (projTyVec ts)) ⟩
  UC.erase (C.tyRen (regain Γ2)
    (injTy (LL.tySub (projSub σ) (TmPosₑ sₑ (projCtx Γ1) (projTyVec ts) .snd .snd))))
    ≡⟨ (cong (λ x → UC.erase (C.tyRen (regain Γ2) x)) $
        inj∘⟨σ⟩≗⟨inj-σ⟩∘inj (projSub σ) (TmPosₑ sₑ (projCtx Γ1) (projTyVec ts) .snd .snd)) ⟩
  UC.erase (C.tyRen (regain Γ2)
    (C.tySub (injSub (projSub σ))
      (injTy (TmPosₑ sₑ (projCtx Γ1) (projTyVec ts) .snd .snd))))
    ≡⟨ (sym $ cong UC.erase $
          C.sub•◦ (regain Γ2) (injSub (projSub σ)) $
          (injTy (TmPosₑ sₑ (projCtx Γ1) (projTyVec ts) .snd .snd))) ⟩
  UC.erase (C.tySub (regain Γ2 C.•◦ₜ injSub (projSub σ))
    (injTy (TmPosₑ sₑ (projCtx Γ1) (projTyVec ts) .snd .snd)))
    ≡⟨ (cong (λ x → UC.erase (C.tySub x (injTy (TmPosₑ sₑ (projCtx Γ1) (projTyVec ts) .snd .snd)))) $
        regain•◦inj-proj-σ≡σ◦•regain σ) ⟩
  UC.erase (C.tySub (σ C.◦•ₜ regain Γ1)
    (injTy (TmPosₑ sₑ (projCtx Γ1) (projTyVec ts) .snd .snd)))
    ≡⟨ (cong UC.erase $ C.sub◦• σ (regain Γ1) $
          injTy (TmPosₑ sₑ (projCtx Γ1) (projTyVec ts) .snd .snd)) ⟩
  UC.erase (C.tySub σ (C.tyRen (regain Γ1)
    (injTy (TmPosₑ sₑ (projCtx Γ1) (projTyVec ts) .snd .snd)))) ∎
subVecCTmPos CtrlDone σ (t ∷ []) = refl
subVecCTmPos CtrlLam σ (τ₁ ∷ τ₂ ∷ []) = refl
subVecCTmPos CtrlFix σ (τ ∷ []) = refl
subVecCTmPos CtrlApp σ (τ₁ ∷ τ₂ ∷ []) = refl
subVecCTmPos (CtrlAbs κ) σ (τ ∷ []) = refl
subVecCTmPos {Γ1} {Γ2} (CtrlAppTy κ) σ (τ ∷ v ∷ []) = Σ-≡-→-≡-Σ refl eq
  where
  eq1 : (C.TyIdSub C.▸ C.tySub σ v) C.◦ₜ C.TyDropSub σ ≡ σ C.◦ₜ C.TyIdSub
  eq1 =
    (C.TyIdSub C.▸ C.tySub σ v) C.◦ₜ (C.TyDrop C.TyIdRen C.•◦ₜ σ)
      ≡⟨ C.◦•◦ (C.TyIdSub C.▸ C.tySub σ v) (C.TyDrop C.TyIdRen) σ ⟩
    (C.TyIdSub C.◦•ₜ C.TyIdRen) C.◦ₜ σ
      ≡⟨ cong (C._◦ₜ σ) (C.◦•Id C.TyIdSub) ⟩
    C.TyIdSub C.◦ₜ σ
      ≡⟨ C.Id◦ σ ⟩
    σ
      ≡⟨ sym (C.◦Id σ) ⟩
    σ C.◦ₜ C.TyIdSub ∎

  eq : C.tySub (C.TyIdSub C.▸ C.tySub σ v) (C.tySub (C.TyKeepSub σ) τ) ≡
       C.tySub σ (C.tySub (C.TyIdSub C.▸ v) τ)
  eq =
    C.tySub (C.TyIdSub C.▸ C.tySub σ v) (C.tySub (C.TyKeepSub σ) τ)
      ≡⟨ sym (C.tySub◦ (C.TyIdSub C.▸ C.tySub σ v) (C.TyKeepSub σ) τ) ⟩
    C.tySub (((C.TyIdSub C.▸ C.tySub σ v) C.◦ₜ C.TyDropSub σ) C.▸ C.tySub σ v) τ
      ≡⟨ cong (λ x → C.tySub (x C.▸ C.tySub σ v) τ) eq1 ⟩
    C.tySub ((σ C.◦ₜ C.TyIdSub) C.▸ C.tySub σ v) τ
      ≡⟨ C.tySub◦ σ (C.TyIdSub C.▸ v) τ ⟩
    C.tySub σ (C.tySub (C.TyIdSub C.▸ v) τ) ∎
subVecCTmPos CtrlSend σ (ℓ ∷ t ∷ []) = refl
subVecCTmPos CtrlRecv σ (ℓ ∷ t ∷ []) = refl
subVecCTmPos (CtrlChoose d) σ (ℓ ∷ τ ∷ []) = refl
subVecCTmPos (CtrlChoice Neither) σ (ℓ ∷ τ ∷ []) = refl
subVecCTmPos (CtrlChoice Left) σ (ℓ ∷ τ ∷ []) = refl
subVecCTmPos (CtrlChoice Right) σ (ℓ ∷ τ ∷ []) = refl
subVecCTmPos (CtrlChoice LeftRight) σ (ℓ ∷ τ ∷ []) = refl
subVecCTmPos CtrlITE σ (τ ∷ []) = refl
subVecCTmPos CtrlUnit σ [] = refl
subVecCTmPos CtrlFail σ (τ ∷ []) = refl
subVecCTmPos CtrlLocalLet σ (t ∷ τ ∷ []) = refl
subVecCTmPos (CtrlSendTy κₑ) σ (ρ ∷ τ ∷ []) = refl
subVecCTmPos CtrlSendLoc σ (ρ ∷ τ ∷ []) = refl

subVecKndCtxCTmPos :  ∀{Γ1 Γ2} (s : CtrlShape) (σ : C.TySub Γ1 Γ2)
                      (ts : C.TyVec Γ1 (CTmTyPos s)) →
                      CTmPos s Γ2 (C.tySubVec σ ts) .fst ≡
                      C.subBinders σ (CTmPos s Γ1 ts .fst)
subVecKndCtxCTmPos {Γ1} {Γ2} (CtrlLocal sₑ) σ ts =
  map (injBinderCtrlFun Γ2) (TmPosₑ sₑ (projCtx Γ2) (projTyVec (C.tySubVec σ ts)) .fst)
    ≡⟨ (cong (λ x → map (injBinderCtrlFun Γ2) (TmPosₑ sₑ (projCtx Γ2) x .fst)) $
        proj∘⟨σ⟩≗⟨proj-σ⟩∘proj-vec σ ts) ⟩
  map (injBinderCtrlFun Γ2) (TmPosₑ sₑ (projCtx Γ2) (LL.tySubVec (projSub σ) (projTyVec ts)) .fst)
    ≡⟨ (cong (map (injBinderCtrlFun Γ2)) $ 𝕃 .⅀ₑ .subVecKndCtxTmPos sₑ (projSub σ) (projTyVec ts)) ⟩
  map (injBinderCtrlFun Γ2) (map (LL.subBinder (projSub σ)) (TmPosₑ sₑ (projCtx Γ1) (projTyVec ts) .fst))
    ≡⟨ (sym $ map-compose {g = injBinderCtrlFun Γ2} {LL.subBinder (projSub σ)} $
          TmPosₑ sₑ (projCtx Γ1) (projTyVec ts) .fst) ⟩
  map (injBinderCtrlFun Γ2 ∘ LL.subBinder (projSub σ)) (TmPosₑ sₑ (projCtx Γ1) (projTyVec ts) .fst)
    ≡⟨ (map-cong
        (λ{ (Γ' , Δ , κₑ , t) → Σ-≡-→-≡-Σ refl $ cong₂ _,_
            (map (injTypCtrlFun Γ' Γ2) (map (LL.subTyp (LL.TyKeepSub* (projSub σ) Γ')) Δ)
              ≡⟨ (sym $ map-compose {g = injTypCtrlFun Γ' Γ2} {LL.subTyp (LL.TyKeepSub* (projSub σ) Γ')} Δ) ⟩
            map (injTypCtrlFun Γ' Γ2 ∘ LL.subTyp (LL.TyKeepSub* (projSub σ) Γ')) Δ
              ≡⟨ map-cong (λ{ (κₑ , t) →
                Σ-≡-→-≡-Σ refl
                (UC.erase-inj $
                UC.erase (C.tyRen (regain (map CtrlLocKnd Γ' ++ Γ2))
                  (subst (λ x → C.Ty x (CtrlLocKnd κₑ))
                    (cong (map CtrlLocKnd)
                    (trans (cong (_++ projCtx Γ2) (sym (projCtx∘injCtx≗id Γ')))
                      (sym (projCtx-++ (map CtrlLocKnd Γ') Γ2))))
                    (mor injTyMor refl refl
                    (LL.tySub (LL.TyKeepSub* (projSub σ) Γ') t))))
                  ≡⟨ UC.erase-distr-ren (regain (map CtrlLocKnd Γ' ++ Γ2))
                        (subst (λ x → C.Ty x (CtrlLocKnd κₑ))
                          (cong (map CtrlLocKnd)
                          (trans (cong (_++ projCtx Γ2) (sym (projCtx∘injCtx≗id Γ')))
                            (sym (projCtx-++ (map CtrlLocKnd Γ') Γ2))))
                          (mor injTyMor refl refl
                          (LL.tySub (LL.TyKeepSub* (projSub σ) Γ') t))) ⟩
                UC.renUnty (UC.eraseRen (regain (map CtrlLocKnd Γ' ++ Γ2)))
                  (UC.erase (subst (λ x → C.Ty x (CtrlLocKnd κₑ))
                    (cong (map CtrlLocKnd)
                    (trans (cong (_++ projCtx Γ2) (sym (projCtx∘injCtx≗id Γ')))
                      (sym (projCtx-++ (map CtrlLocKnd Γ') Γ2))))
                    (injTy (LL.tySub (LL.TyKeepSub* (projSub σ) Γ') t))))
                  ≡⟨ (cong (UC.renUnty (UC.eraseRen (regain (map CtrlLocKnd Γ' ++ Γ2)))) $
                        sym $ UC.substCtx-erase 
                        (cong (map CtrlLocKnd)
                          (trans (cong (_++ projCtx Γ2) (sym (projCtx∘injCtx≗id Γ')))
                            (sym (projCtx-++ (map CtrlLocKnd Γ') Γ2))))
                        (injTy (LL.tySub (LL.TyKeepSub* (projSub σ) Γ') t))) ⟩
                UC.renUnty (UC.eraseRen (regain (map CtrlLocKnd Γ' ++ Γ2)))
                  (UC.erase (injTy (LL.tySub (LL.TyKeepSub* (projSub σ) Γ') t)))
                  ≡⟨ (cong (λ x → UC.renUnty (UC.eraseRen (regain (map CtrlLocKnd Γ' ++ Γ2))) (UC.erase x)) $
                        inj∘⟨σ⟩≗⟨inj-σ⟩∘inj (LL.TyKeepSub* (projSub σ) Γ') t) ⟩
                UC.renUnty (UC.eraseRen (regain (map CtrlLocKnd Γ' ++ Γ2)))
                  (UC.erase (C.tySub (injSub (LL.TyKeepSub* (projSub σ) Γ')) (injTy t)))
                  ≡⟨ (cong (UC.renUnty (UC.eraseRen (regain (map CtrlLocKnd Γ' ++ Γ2)))) $ 
                        UC.erase-distr-sub (injSub (LL.TyKeepSub* (projSub σ) Γ')) (injTy t)) ⟩
                UC.renUnty (UC.eraseRen (regain (map CtrlLocKnd Γ' ++ Γ2)))
                  (UC.subUnty (UC.eraseSub (injSub (LL.TyKeepSub* (projSub σ) Γ'))) (UC.erase (injTy t)))
                  ≡⟨ UC.sub•◦UH (regain (map CtrlLocKnd Γ' ++ Γ2))
                        (injSub (LL.TyKeepSub* (projSub σ) Γ'))
                        (injTy t)
                        (cong injCtx $
                          cong (_++ projCtx Γ2) (sym (projCtx∘injCtx≗id Γ'))
                          ∙ sym (projCtx-++ (injCtx Γ') Γ2))
                        refl ⟩
                UC.subUnty (UC.eraseRen (regain (map CtrlLocKnd Γ' ++ Γ2))
                    UC.•◦U UC.eraseSub (injSub (LL.TyKeepSub* (projSub σ) Γ')))
                  (UC.erase (injTy t))
                  ≡⟨ (cong (λ x → UC.subUnty (UC.eraseRen (regain (map CtrlLocKnd Γ' ++ Γ2))
                    UC.•◦U UC.eraseSub (injSub (LL.TyKeepSub* (projSub σ) x)))
                  (UC.erase (injTy t))) $
                  sym (projCtx∘injCtx≗id Γ')) ⟩
                UC.subUnty (UC.eraseRen (regain (map CtrlLocKnd Γ' ++ Γ2))
                    UC.•◦U UC.eraseSub (injSub (LL.TyKeepSub* (projSub σ) (projCtx (injCtx Γ')))))
                  (UC.erase (injTy t))
                  ≡⟨ (cong (λ x → UC.subUnty (UC.eraseRen (regain (map CtrlLocKnd Γ' ++ Γ2)) UC.•◦U x) (UC.erase (injTy t))) $
                      cong-erase-injSub
                        (sym (projCtx-++ (injCtx Γ') Γ1))
                        (sym (projCtx-++ (injCtx Γ') Γ2))
                        (sym $ erase-projSub-distr-KeepSub*Ctrl σ (injCtx Γ'))) ⟩
                UC.subUnty (UC.eraseRen (regain (map CtrlLocKnd Γ' ++ Γ2))
                    UC.•◦U UC.eraseSub (injSub (projSub (C.TyKeepSub* σ (injCtx Γ')))))
                  (UC.erase (injTy t))
                  ≡⟨ (cong (λ x → UC.subUnty x (UC.erase (injTy t))) $
                        erase-regain•◦inj-proj-σ≡σ◦•regain (C.TyKeepSub* σ (injCtx Γ'))) ⟩
                UC.subUnty (UC.eraseSub (C.TyKeepSub* σ (injCtx Γ'))
                    UC.◦•U UC.eraseRen (regain (injCtx Γ' ++ Γ1)))
                  (UC.erase (injTy t))
                  ≡⟨ (sym $ UC.sub◦•UH (C.TyKeepSub* σ (injCtx Γ')) (regain (injCtx Γ' ++ Γ1)) (injTy t)
                      (cong injCtx (projCtx-++ (injCtx Γ') Γ1 ∙ cong (_++ projCtx Γ1) (projCtx∘injCtx≗id Γ')))
                      refl) ⟩
                UC.subUnty (UC.eraseSub (C.TyKeepSub* σ (injCtx Γ')))
                  (UC.renUnty (UC.eraseRen (regain (injCtx Γ' ++ Γ1)))
                    (UC.erase (injTy t)))
                  ≡⟨ (cong (λ x → UC.subUnty (UC.eraseSub (C.TyKeepSub* σ (injCtx Γ')))
                          (UC.renUnty (UC.eraseRen (regain (injCtx Γ' ++ Γ1))) x)) $
                      UC.substCtx-erase
                        (cong injCtx
                          (trans (cong (_++ projCtx Γ1) (sym (projCtx∘injCtx≗id Γ')))
                          (sym (projCtx-++ (injCtx Γ') Γ1))))
                          (injTy t)) ⟩
                UC.subUnty (UC.eraseSub (C.TyKeepSub* σ (injCtx Γ')))
                  (UC.renUnty (UC.eraseRen (regain (injCtx Γ' ++ Γ1)))
                  (UC.erase (subst (λ x → C.Ty x (CtrlLocKnd κₑ))
                    (cong injCtx
                      (trans (cong (_++ projCtx Γ1) (sym (projCtx∘injCtx≗id Γ')))
                      (sym (projCtx-++ (injCtx Γ') Γ1))))
                    (injTy t))))
                  ≡⟨ (sym $ cong (UC.subUnty (UC.eraseSub (C.TyKeepSub* σ (injCtx Γ')))) $
                        UC.erase-distr-ren (regain (injCtx Γ' ++ Γ1))
                        (subst (λ x → C.Ty x (CtrlLocKnd κₑ))
                          (cong injCtx
                            (trans (cong (_++ projCtx Γ1) (sym (projCtx∘injCtx≗id Γ')))
                            (sym (projCtx-++ (injCtx Γ') Γ1))))
                          (injTy t))) ⟩
                UC.subUnty (UC.eraseSub (C.TyKeepSub* σ (injCtx Γ')))
                  (UC.erase (C.tyRen (regain (injCtx Γ' ++ Γ1))
                    (subst (λ x → C.Ty x (CtrlLocKnd κₑ))
                    (cong injCtx
                      (trans (cong (_++ projCtx Γ1) (sym (projCtx∘injCtx≗id Γ')))
                      (sym (projCtx-++ (injCtx Γ') Γ1))))
                    (injTy t))))
                  ≡⟨ (sym $ UC.erase-distr-sub (C.TyKeepSub* σ (injCtx Γ'))
                        (C.tyRen (regain (injCtx Γ' ++ Γ1))
                          (subst (λ x → C.Ty x (CtrlLocKnd κₑ))
                          (cong injCtx
                            (trans (cong (_++ projCtx Γ1) (sym (projCtx∘injCtx≗id Γ')))
                            (sym (projCtx-++ (injCtx Γ') Γ1))))
                          (injTy t)))) ⟩
                UC.erase (C.tySub (C.TyKeepSub* σ (injCtx Γ'))
                  (C.tyRen (regain (injCtx Γ' ++ Γ1))
                    (subst (λ x → C.Ty x (CtrlLocKnd κₑ))
                    (cong injCtx
                      (trans (cong (_++ projCtx Γ1) (sym (projCtx∘injCtx≗id Γ')))
                      (sym (projCtx-++ (injCtx Γ') Γ1))))
                    (injTy t)))) ∎)
                }) Δ ⟩
            map (C.subTyp (C.TyKeepSub* σ (injCtx Γ')) ∘ injTypCtrlFun Γ' Γ1) Δ
              ≡⟨ map-compose {g = C.subTyp (C.TyKeepSub* σ (injCtx Γ'))} {injTypCtrlFun Γ' Γ1} Δ ⟩
            map (C.subTyp (C.TyKeepSub* σ (injCtx Γ'))) (map (injTypCtrlFun Γ' Γ1) Δ) ∎)
            $ Σ-≡-→-≡-Σ refl $
            UC.erase-inj $
            UC.erase (C.tyRen (regain (injCtx Γ' ++ Γ2))
              (subst (λ x → C.Ty x (CtrlLocKnd κₑ))
                (cong injCtx
                  (cong (_++ projCtx Γ2) (sym (projCtx∘injCtx≗id Γ'))
                  ∙ sym (projCtx-++ (injCtx Γ') Γ2)))
                (mor injTyMor refl refl
                  (LL.tySub (LL.TyKeepSub* (projSub σ) Γ') t))))
              ≡⟨ UC.erase-distr-ren (regain (injCtx Γ' ++ Γ2))
                  (subst (λ x → C.Ty x (CtrlLocKnd κₑ))
                    (cong injCtx
                      (cong (_++ projCtx Γ2) (sym (projCtx∘injCtx≗id Γ'))
                      ∙ sym (projCtx-++ (injCtx Γ') Γ2)))
                    (mor injTyMor refl refl
                      (LL.tySub (LL.TyKeepSub* (projSub σ) Γ') t))) ⟩
            UC.renUnty (UC.eraseRen (regain (injCtx Γ' ++ Γ2)))
              (UC.erase (subst (λ x → C.Ty x (CtrlLocKnd κₑ))
                (cong injCtx
                  (cong (_++ projCtx Γ2) (sym (projCtx∘injCtx≗id Γ')) ∙
                    sym (projCtx-++ (injCtx Γ') Γ2)))
                (injTy (LL.tySub (LL.TyKeepSub* (projSub σ) Γ') t))))
              ≡⟨ (sym $ cong (UC.renUnty (UC.eraseRen (regain (injCtx Γ' ++ Γ2)))) $
                  UC.substCtx-erase 
                    (cong injCtx
                      (cong (_++ projCtx Γ2) (sym (projCtx∘injCtx≗id Γ')) ∙
                        sym (projCtx-++ (injCtx Γ') Γ2)))
                    (injTy (LL.tySub (LL.TyKeepSub* (projSub σ) Γ') t))) ⟩
            UC.renUnty (UC.eraseRen (regain (injCtx Γ' ++ Γ2)))
              (UC.erase (injTy (LL.tySub (LL.TyKeepSub* (projSub σ) Γ') t)))
              ≡⟨ (cong (λ x → UC.renUnty (UC.eraseRen (regain (injCtx Γ' ++ Γ2))) (UC.erase x)) $
                  inj∘⟨σ⟩≗⟨inj-σ⟩∘inj (LL.TyKeepSub* (projSub σ) Γ') t) ⟩
            UC.renUnty (UC.eraseRen (regain (injCtx Γ' ++ Γ2)))
              (UC.erase (C.tySub (injSub (LL.TyKeepSub* (projSub σ) Γ')) (injTy t)))
              ≡⟨ (cong (UC.renUnty (UC.eraseRen (regain (injCtx Γ' ++ Γ2)))) $
                    UC.erase-distr-sub (injSub (LL.TyKeepSub* (projSub σ) Γ')) (injTy t)) ⟩
            UC.renUnty (UC.eraseRen (regain (injCtx Γ' ++ Γ2)))
              (UC.subUnty (UC.eraseSub (injSub (LL.TyKeepSub* (projSub σ) Γ')))
                (UC.erase (injTy t)))
              ≡⟨ (cong (λ x → UC.renUnty (UC.eraseRen (regain (injCtx Γ' ++ Γ2)))
                  (UC.subUnty x (UC.erase (injTy t)))) $
                  erase-injSub-distr-Keep*Ctrl (projSub σ) Γ') ⟩
            UC.renUnty (UC.eraseRen (regain (injCtx Γ' ++ Γ2)))
              (UC.subUnty (UC.eraseSub (C.TyKeepSub* (injSub (projSub σ)) (injCtx Γ')))
                (UC.erase (injTy t)))
              ≡⟨ UC.sub•◦UH (regain (injCtx Γ' ++ Γ2))
                    (C.TyKeepSub* (injSub (projSub σ)) (injCtx Γ'))
                    (injTy t)
                    (sym (injCtx-++ Γ' (projCtx Γ2))
                      ∙ cong injCtx (cong (_++ projCtx Γ2) (sym (projCtx∘injCtx≗id Γ'))
                      ∙ (sym $ projCtx-++ (injCtx Γ') Γ2)))
                    (injCtx-++ Γ' (projCtx Γ1)) ⟩
            UC.subUnty (UC.eraseRen (regain (injCtx Γ' ++ Γ2))
                UC.•◦U UC.eraseSub (C.TyKeepSub* (injSub (projSub σ)) (injCtx Γ')))
              (UC.erase (injTy t))
              ≡⟨ (cong (λ x → UC.subUnty (UC.eraseRen (regain (injCtx Γ' ++ Γ2)) UC.•◦U x) (UC.erase (injTy t))) $
                    sym $ erase-injSub-distr-Keep*Ctrl (projSub σ) Γ') ⟩
            UC.subUnty (UC.eraseRen (regain (injCtx Γ' ++ Γ2))
                UC.•◦U UC.eraseSub (injSub (LL.TyKeepSub* (projSub σ) Γ')))
              (UC.erase (injTy t))
              ≡⟨ (sym $ cong (λ x → UC.subUnty (UC.eraseRen (regain (injCtx Γ' ++ Γ2))
                    UC.•◦U UC.eraseSub (injSub (LL.TyKeepSub* (projSub σ) x)))
                  (UC.erase (injTy t))) $
                  projCtx∘injCtx≗id Γ') ⟩
            UC.subUnty (UC.eraseRen (regain (injCtx Γ' ++ Γ2))
                UC.•◦U UC.eraseSub (injSub (LL.TyKeepSub* (projSub σ) (projCtx (injCtx Γ')))))
              (UC.erase (injTy t))
              ≡⟨ (cong (λ x → UC.subUnty (UC.eraseRen (regain (injCtx Γ' ++ Γ2)) UC.•◦U x) (UC.erase (injTy t))) $
                    cong-erase-injSub
                      (sym $ projCtx-++ (injCtx Γ') Γ1)
                      (sym $ projCtx-++ (injCtx Γ') Γ2) $
                    sym $ erase-projSub-distr-KeepSub*Ctrl σ (injCtx Γ')) ⟩
            UC.subUnty (UC.eraseRen (regain (injCtx Γ' ++ Γ2))
                UC.•◦U UC.eraseSub (injSub (projSub (C.TyKeepSub* σ (injCtx Γ')))))
              (UC.erase (injTy t))
              ≡⟨ (cong (λ x → UC.subUnty x (UC.erase (injTy t))) $
                    erase-regain•◦inj-proj-σ≡σ◦•regain (C.TyKeepSub* σ (injCtx Γ'))) ⟩
            UC.subUnty (UC.eraseSub (C.TyKeepSub* σ (injCtx Γ'))
                UC.◦•U UC.eraseRen (regain (injCtx Γ' ++ Γ1)))
              (UC.erase (injTy t))
              ≡⟨ (sym $ UC.sub◦•UH (C.TyKeepSub* σ (injCtx Γ')) (regain (injCtx Γ' ++ Γ1))
                    (injTy t)
                    (cong injCtx (projCtx-++ (injCtx Γ') Γ1 ∙ cong (_++ projCtx Γ1) (projCtx∘injCtx≗id Γ')))
                    refl) ⟩

            UC.subUnty (UC.eraseSub (C.TyKeepSub* σ (map CtrlLocKnd Γ')))
              (UC.renUnty (UC.eraseRen (regain (map CtrlLocKnd Γ' ++ Γ1)))
                (UC.erase (injTy t)))
              ≡⟨ (cong (λ x → UC.subUnty (UC.eraseSub (C.TyKeepSub* σ (map CtrlLocKnd Γ')))
                    (UC.renUnty (UC.eraseRen (regain (map CtrlLocKnd Γ' ++ Γ1))) x)) $
                  UC.substCtx-erase 
                    (cong (map CtrlLocKnd)
                      (trans (cong (_++ projCtx Γ1) (sym (projCtx∘injCtx≗id Γ')))
                        (sym (projCtx-++ (map CtrlLocKnd Γ') Γ1))))
                    (mor injTyMor refl refl t)) ⟩
            UC.subUnty (UC.eraseSub (C.TyKeepSub* σ (map CtrlLocKnd Γ')))
              (UC.renUnty (UC.eraseRen (regain (map CtrlLocKnd Γ' ++ Γ1)))
              (UC.erase (subst (λ x → C.Ty x (CtrlLocKnd κₑ))
                (cong (map CtrlLocKnd)
                  (trans (cong (_++ projCtx Γ1) (sym (projCtx∘injCtx≗id Γ')))
                  (sym (projCtx-++ (map CtrlLocKnd Γ') Γ1))))
                (mor injTyMor refl refl t))))
              ≡⟨ (sym $ cong (UC.subUnty (UC.eraseSub (C.TyKeepSub* σ (map CtrlLocKnd Γ')))) $
                  UC.erase-distr-ren (regain (map CtrlLocKnd Γ' ++ Γ1))
                    (subst (λ x → C.Ty x (CtrlLocKnd κₑ))
                      (cong (map CtrlLocKnd)
                        (trans (cong (_++ projCtx Γ1) (sym (projCtx∘injCtx≗id Γ')))
                        (sym (projCtx-++ (map CtrlLocKnd Γ') Γ1))))
                      (mor injTyMor refl refl t))) ⟩
            UC.subUnty (UC.eraseSub (C.TyKeepSub* σ (map CtrlLocKnd Γ')))
              (UC.erase (C.tyRen (regain (map CtrlLocKnd Γ' ++ Γ1))
                (subst (λ x → C.Ty x (CtrlLocKnd κₑ))
                  (cong (map CtrlLocKnd)
                    (trans (cong (_++ projCtx Γ1) (sym (projCtx∘injCtx≗id Γ')))
                    (sym (projCtx-++ (map CtrlLocKnd Γ') Γ1))))
                  (mor injTyMor refl refl t))))
              ≡⟨ (sym $ UC.erase-distr-sub (C.TyKeepSub* σ (map CtrlLocKnd Γ'))
                  (C.tyRen (regain (map CtrlLocKnd Γ' ++ Γ1))
                    (subst (λ x → C.Ty x (CtrlLocKnd κₑ))
                      (cong (map CtrlLocKnd)
                        (trans (cong (_++ projCtx Γ1) (sym (projCtx∘injCtx≗id Γ')))
                          (sym (projCtx-++ (map CtrlLocKnd Γ') Γ1))))
                      (mor injTyMor refl refl t)))) ⟩
            UC.erase (C.tySub (C.TyKeepSub* σ (map CtrlLocKnd Γ'))
              (C.tyRen (regain (map CtrlLocKnd Γ' ++ Γ1))
                (subst (λ x → C.Ty x (CtrlLocKnd κₑ))
                  (cong (map CtrlLocKnd)
                    (trans (cong (_++ projCtx Γ1) (sym (projCtx∘injCtx≗id Γ')))
                      (sym (projCtx-++ (map CtrlLocKnd Γ') Γ1))))
                  (mor injTyMor refl refl t)))) ∎ })
        $ TmPosₑ sₑ (projCtx Γ1) (projTyVec ts) .fst) ⟩
  map (C.subBinder σ ∘ injBinderCtrlFun Γ1) (TmPosₑ sₑ (projCtx Γ1) (projTyVec ts) .fst)
    ≡⟨ map-compose {g = C.subBinder σ} {injBinderCtrlFun Γ1} (TmPosₑ sₑ (projCtx Γ1) (projTyVec ts) .fst) ⟩
  map (C.subBinder σ) (map (injBinderCtrlFun Γ1) (TmPosₑ sₑ (projCtx Γ1) (projTyVec ts) .fst)) ∎
subVecKndCtxCTmPos CtrlDone σ (t ∷ []) = refl
subVecKndCtxCTmPos CtrlLam σ (τ1 ∷ τ2 ∷ []) = refl
subVecKndCtxCTmPos CtrlFix σ (τ ∷ []) = refl
subVecKndCtxCTmPos CtrlApp σ (τ1 ∷ τ2 ∷ []) = refl
subVecKndCtxCTmPos (CtrlAbs κ) σ (τ ∷ []) = refl
subVecKndCtxCTmPos (CtrlAppTy κ) σ (τ1 ∷ τ2 ∷ []) = refl
subVecKndCtxCTmPos CtrlSend σ (ℓ ∷ t ∷ []) = refl
subVecKndCtxCTmPos CtrlRecv σ (ℓ ∷ t ∷ []) = refl
subVecKndCtxCTmPos (CtrlChoose d) σ (ℓ ∷ t ∷ []) = refl
subVecKndCtxCTmPos (CtrlChoice Neither) σ (ℓ ∷ t ∷ []) = refl
subVecKndCtxCTmPos (CtrlChoice Left) σ (ℓ ∷ t ∷ []) = refl
subVecKndCtxCTmPos (CtrlChoice Right) σ (ℓ ∷ t ∷ []) = refl
subVecKndCtxCTmPos (CtrlChoice LeftRight) σ (ℓ ∷ t ∷ []) = refl
subVecKndCtxCTmPos CtrlITE σ (τ ∷ []) =
  cong₂ _∷_
    (cong (λ x → [] , [] , *Ctrl , C.tyConstr CtrlAt (x C.∷ C.[])) $
      C.tyRen C.ε* (injTy (𝕃 .Boolₑ))
        ≡⟨ (sym $ C.subι C.ε* (injTy (𝕃 .Boolₑ))) ⟩
      C.tySub (C.ιₜ C.ε*) (injTy (𝕃 .Boolₑ))
        ≡⟨ (cong (λ x → C.tySub x (injTy (𝕃 .Boolₑ))) $ C.ιε*) ⟩
      C.tySub C.ε (injTy (𝕃 .Boolₑ))
        ≡⟨ (sym $ cong (λ x → C.tySub x (injTy (𝕃 .Boolₑ))) $ C.◦•ε σ) ⟩
      C.tySub (σ C.◦•ₜ C.ε*) (injTy (𝕃 .Boolₑ))
        ≡⟨ C.sub◦• σ C.ε* (injTy (𝕃 .Boolₑ)) ⟩
      C.tySub σ (C.tyRen C.ε* (injTy (𝕃 .Boolₑ))) ∎) 
    refl
subVecKndCtxCTmPos CtrlUnit σ [] = refl
subVecKndCtxCTmPos CtrlFail σ (τ ∷ []) = refl
subVecKndCtxCTmPos CtrlLocalLet σ (t ∷ τ ∷ []) = refl
subVecKndCtxCTmPos (CtrlSendTy κₑ) σ (ρ ∷ τ ∷ []) = cong₂ (λ x y →
    ([] , [] , *Ctrl , C.tyConstr CtrlAt (x C.∷ C.[]))
      ∷ (CtrlLocKnd κₑ ∷ [] , [] , *Ctrl , y)
      ∷ [])
      (C.tyRen C.ε* (injTy (𝕃 .TyRepₑ κₑ))
        ≡⟨ (sym $ C.subι C.ε* (injTy (𝕃 .TyRepₑ κₑ))) ⟩
      C.tySub (C.ιₜ C.ε*) (injTy (𝕃 .TyRepₑ κₑ))
        ≡⟨ (cong (λ x → C.tySub x (injTy (𝕃 .TyRepₑ κₑ))) $ C.ιε*) ⟩
      C.tySub C.ε (injTy (𝕃 .TyRepₑ κₑ))
        ≡⟨ (sym $ cong (λ x → C.tySub x (injTy (𝕃 .TyRepₑ κₑ))) $ C.◦•ε σ) ⟩
      C.tySub (σ C.◦•ₜ C.ε*) (injTy (𝕃 .TyRepₑ κₑ))
        ≡⟨ C.sub◦• σ C.ε* (injTy (𝕃 .TyRepₑ κₑ)) ⟩
      C.tySub σ (C.tyRen C.ε* (injTy (𝕃 .TyRepₑ κₑ))) ∎)
      (C.tyWk (C.tySub σ τ)
        ≡⟨ (sym $ C.sub•◦ (C.TyDrop C.TyIdRen) σ τ) ⟩
      C.tySub (C.TyDrop C.TyIdRen C.•◦ₜ σ) τ
        ≡⟨ (cong (λ x → C.tySub x τ) $ sym $ C.◦•Id (C.TyDrop C.TyIdRen C.•◦ₜ σ)) ⟩
      C.tySub ((C.TyDrop C.TyIdRen C.•◦ₜ σ) C.◦•ₜ C.TyIdRen) τ
        ≡⟨ C.sub◦• (C.TyKeepSub σ) (C.TyDrop C.TyIdRen) τ ⟩
      C.tySub (C.TyKeepSub σ) (C.tyWk τ) ∎)
subVecKndCtxCTmPos CtrlSendLoc σ (ρ ∷ τ ∷ []) = cong₂ (λ x y →
  ([] , [] , *Ctrl , C.tyConstr CtrlAt (x C.∷ C.[]))
  ∷ (*Ctrlₗ ∷ [] , [] , *Ctrl , y)
  ∷ [])
  (C.tyRen C.ε* (injTy (𝕃 .Locₑ))
    ≡⟨ (sym $ C.subι C.ε* (injTy (𝕃 .Locₑ))) ⟩
  C.tySub (C.ιₜ C.ε*) (injTy (𝕃 .Locₑ))
    ≡⟨ (cong (λ x → C.tySub x (injTy (𝕃 .Locₑ))) $ C.ιε*) ⟩
  C.tySub C.ε (injTy (𝕃 .Locₑ))
    ≡⟨ (sym $ cong (λ x → C.tySub x (injTy (𝕃 .Locₑ))) $ C.◦•ε σ) ⟩
  C.tySub (σ C.◦•ₜ C.ε*) (injTy (𝕃 .Locₑ))
    ≡⟨ C.sub◦• σ C.ε* (injTy (𝕃 .Locₑ)) ⟩
  C.tySub σ (C.tyRen C.ε* (injTy (𝕃 .Locₑ))) ∎)
  (C.tyWk (C.tySub σ τ)
    ≡⟨ (sym $ C.sub•◦ (C.TyDrop C.TyIdRen) σ τ) ⟩
  C.tySub (C.TyDropSub σ) τ
    ≡⟨ (cong (λ x → C.tySub x τ) $ sym $ C.◦•Id $ C.TyDropSub σ) ⟩
  C.tySub (C.TyDropSub σ C.◦•ₜ C.TyIdRen) τ
    ≡⟨ C.sub◦• (C.TyKeepSub σ) (C.TyDrop C.TyIdRen) τ ⟩
  C.tySub (C.TyKeepSub σ) (C.tyWk τ) ∎)

C⅀ : ThirdOrderSignature
⅀₂                C⅀ = C⅀₂
Shape             C⅀ = CtrlShape
TmTyPos           C⅀ = CTmTyPos
TmPos             C⅀ = CTmPos
subVecTmPos       C⅀ = subVecCTmPos
subVecKndCtxTmPos C⅀ = subVecKndCtxCTmPos

open import ThirdOrderLanguage C⅀ as CL

TmCtrlLam : ∀{Γ Δ} {s t : C.Ty Γ *Ctrl} →
        CL.Tm Γ ((*Ctrl , s) ∷ Δ) (*Ctrl , t) →
        CL.Tm Γ Δ (*Ctrl , TyCtrlFun s t)
TmCtrlLam {Γ} {Δ} {s} {t} C =
  let eq : Δ ≡ CL.renCtx (CL.TyDrop* CL.TyIdRen []) Δ
      eq = sym $ CL.renCtxId Δ
  in CL.constr CtrlLam 
      (s CL.∷ t CL.∷ CL.[])
      (subst (λ x → CL.Tm Γ ((*Ctrl , s) ∷ x) (*Ctrl , t)) eq C CL.∷ CL.[])

TmCtrlApp : ∀{Γ Δ} {s t : C.Ty Γ *Ctrl} →
        CL.Tm Γ Δ (*Ctrl , TyCtrlFun s t) →
        CL.Tm Γ Δ (*Ctrl , s) →
        CL.Tm Γ Δ (*Ctrl , t)
TmCtrlApp {Γ} {Δ} {s} {t} C1 C2 =
  let eq : Δ ≡ CL.renCtx (CL.TyDrop* CL.TyIdRen []) Δ
      eq = sym $ CL.renCtxId Δ
  in CL.constr CtrlApp 
      (s CL.∷ t CL.∷ CL.[])
      (subst (λ x → CL.Tm Γ x (*Ctrl , TyCtrlFun s t)) eq C1 CL.∷
      subst (λ x → CL.Tm Γ x (*Ctrl , s)) eq C2 CL.∷ CL.[])

TmCtrlDone : ∀{Γ Δ} {t : C.Ty Γ *Ctrlₑ} →
        CL.Tm Γ Δ (*Ctrlₑ , t) →
        CL.Tm Γ Δ (*Ctrl , TyCtrlAt t)
TmCtrlDone {Γ} {Δ} {t} e =
  let eq : Δ ≡ CL.renCtx (CL.TyDrop* CL.TyIdRen []) Δ
      eq = sym $ CL.renCtxId Δ
  in CL.constr CtrlDone
    (t CL.∷ CL.[])
    (subst (λ x → CL.Tm Γ x (*Ctrlₑ , t)) eq e CL.∷ CL.[])