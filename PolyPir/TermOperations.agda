{-# OPTIONS --safe #-}

open import Level renaming (zero to ℓ-zero; suc to ℓ-suc)
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map)
open import Data.Product.Properties
open import Data.Bool
open import Data.Nat
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

module PolyPir.TermOperations
  -- Location values
  (Loc : Set)
  -- Locations should have decidable equality
  (≡-dec-Loc : DecidableEquality Loc)

  -- Local language
  (𝕃 : LocalLang Loc)
  where

open import PolyPir.ChorTypes Loc ≡-dec-Loc 𝕃
open import PolyPir.ChorTerms Loc ≡-dec-Loc 𝕃

≡-dec-ChorKnd : DecidableEquality ChorKnd
≡-dec-ChorKnd (LocKnd κ1ₑ) (LocKnd κ2ₑ)
  with 𝕃 .≡-dec-Kndₑ κ1ₑ κ2ₑ
... | yes p = yes $ cong LocKnd p
... | no ¬p = no λ{ refl → ¬p refl }
≡-dec-ChorKnd (LocKnd κₑ) (Bnd κₑ₁) = no (λ ())
≡-dec-ChorKnd (LocKnd κₑ) * = no (λ ())
≡-dec-ChorKnd (LocKnd κₑ) *ₗ = no (λ ())
≡-dec-ChorKnd (LocKnd κₑ) *ₛ = no (λ ())
≡-dec-ChorKnd (Bnd κₑ) (LocKnd κₑ₁) = no (λ ())
≡-dec-ChorKnd (Bnd κ1ₑ) (Bnd κ2ₑ)
  with 𝕃 .≡-dec-Kndₑ κ1ₑ κ2ₑ
... | yes p = yes $ cong Bnd p
... | no ¬p = no λ{ refl → ¬p refl }
≡-dec-ChorKnd (Bnd κₑ) * = no (λ ())
≡-dec-ChorKnd (Bnd κₑ) *ₗ = no (λ ())
≡-dec-ChorKnd (Bnd κₑ) *ₛ = no (λ ())
≡-dec-ChorKnd * (LocKnd κₑ) = no (λ ())
≡-dec-ChorKnd * (Bnd κₑ) = no (λ ())
≡-dec-ChorKnd * * = yes refl
≡-dec-ChorKnd * *ₗ = no (λ ())
≡-dec-ChorKnd * *ₛ = no (λ ())
≡-dec-ChorKnd *ₗ (LocKnd κₑ) = no (λ ())
≡-dec-ChorKnd *ₗ (Bnd κₑ) = no (λ ())
≡-dec-ChorKnd *ₗ * = no (λ ())
≡-dec-ChorKnd *ₗ *ₗ = yes refl
≡-dec-ChorKnd *ₗ *ₛ = no (λ ())
≡-dec-ChorKnd *ₛ (LocKnd κₑ) = no (λ ())
≡-dec-ChorKnd *ₛ (Bnd κₑ) = no (λ ())
≡-dec-ChorKnd *ₛ * = no (λ ())
≡-dec-ChorKnd *ₛ *ₗ = no (λ ())
≡-dec-ChorKnd *ₛ *ₛ = yes refl

≡-dec-ChorTySymb : DecidableEquality ChorTySymb
≡-dec-ChorTySymb (EmbLocalTyS s1ₑ) (EmbLocalTyS s2ₑ)
  with 𝕃 .≡-dec-TySymbₑ s1ₑ s2ₑ
... | yes p = yes $ cong EmbLocalTyS p
... | no ¬p = no λ{ refl → ¬p refl }
≡-dec-ChorTySymb (EmbLocalTyS sₑ) (LocalS κₑ) = no (λ ())
≡-dec-ChorTySymb (EmbLocalTyS sₑ) AtS = no (λ ())
≡-dec-ChorTySymb (EmbLocalTyS sₑ) FunS = no (λ ())
≡-dec-ChorTySymb (EmbLocalTyS sₑ) (AllS κ ∀κ) = no (λ ())
≡-dec-ChorTySymb (EmbLocalTyS sₑ) (LitLocS L) = no (λ ())
≡-dec-ChorTySymb (EmbLocalTyS sₑ) EmpS = no (λ ())
≡-dec-ChorTySymb (EmbLocalTyS sₑ) SngS = no (λ ())
≡-dec-ChorTySymb (EmbLocalTyS sₑ) UnionS = no (λ ())
≡-dec-ChorTySymb (LocalS κₑ) (EmbLocalTyS sₑ) = no (λ ())
≡-dec-ChorTySymb (LocalS κ1ₑ) (LocalS κ2ₑ)
  with 𝕃 .≡-dec-Kndₑ κ1ₑ κ2ₑ
... | yes p = yes $ cong LocalS p
... | no ¬p = no λ{ refl → ¬p refl }
≡-dec-ChorTySymb (LocalS κₑ) AtS = no (λ ())
≡-dec-ChorTySymb (LocalS κₑ) FunS = no (λ ())
≡-dec-ChorTySymb (LocalS κₑ) (AllS κ ∀κ) = no (λ ())
≡-dec-ChorTySymb (LocalS κₑ) (LitLocS L) = no (λ ())
≡-dec-ChorTySymb (LocalS κₑ) EmpS = no (λ ())
≡-dec-ChorTySymb (LocalS κₑ) SngS = no (λ ())
≡-dec-ChorTySymb (LocalS κₑ) UnionS = no (λ ())
≡-dec-ChorTySymb AtS (EmbLocalTyS sₑ) = no (λ ())
≡-dec-ChorTySymb AtS (LocalS κₑ) = no (λ ())
≡-dec-ChorTySymb AtS AtS = yes refl
≡-dec-ChorTySymb AtS FunS = no (λ ())
≡-dec-ChorTySymb AtS (AllS κ ∀κ) = no (λ ())
≡-dec-ChorTySymb AtS (LitLocS L) = no (λ ())
≡-dec-ChorTySymb AtS EmpS = no (λ ())
≡-dec-ChorTySymb AtS SngS = no (λ ())
≡-dec-ChorTySymb AtS UnionS = no (λ ())
≡-dec-ChorTySymb FunS (EmbLocalTyS sₑ) = no (λ ())
≡-dec-ChorTySymb FunS (LocalS κₑ) = no (λ ())
≡-dec-ChorTySymb FunS AtS = no (λ ())
≡-dec-ChorTySymb FunS FunS = yes refl
≡-dec-ChorTySymb FunS (AllS κ ∀κ) = no (λ ())
≡-dec-ChorTySymb FunS (LitLocS L) = no (λ ())
≡-dec-ChorTySymb FunS EmpS = no (λ ())
≡-dec-ChorTySymb FunS SngS = no (λ ())
≡-dec-ChorTySymb FunS UnionS = no (λ ())
≡-dec-ChorTySymb (AllS κ ∀κ) (EmbLocalTyS sₑ) = no (λ ())
≡-dec-ChorTySymb (AllS κ ∀κ) (LocalS κₑ) = no (λ ())
≡-dec-ChorTySymb (AllS κ ∀κ) AtS = no (λ ())
≡-dec-ChorTySymb (AllS κ ∀κ) FunS = no (λ ())
≡-dec-ChorTySymb (AllS κ1 ∀κ1) (AllS κ2 ∀κ2) with ≡-dec-ChorKnd κ1 κ2
... | yes refl = yes $ cong (AllS κ1) $ canAbstract-isProp κ1 ∀κ1 ∀κ2
... | no  ¬p   = no λ{ refl → ¬p refl }
≡-dec-ChorTySymb (AllS κ ∀κ) (LitLocS L) = no (λ ())
≡-dec-ChorTySymb (AllS κ ∀κ) EmpS = no (λ ())
≡-dec-ChorTySymb (AllS κ ∀κ) SngS = no (λ ())
≡-dec-ChorTySymb (AllS κ ∀κ) UnionS = no (λ ())
≡-dec-ChorTySymb (LitLocS L) (EmbLocalTyS sₑ) = no (λ ())
≡-dec-ChorTySymb (LitLocS L) (LocalS κₑ) = no (λ ())
≡-dec-ChorTySymb (LitLocS L) AtS = no (λ ())
≡-dec-ChorTySymb (LitLocS L) FunS = no (λ ())
≡-dec-ChorTySymb (LitLocS L) (AllS κ ∀κ) = no (λ ())
≡-dec-ChorTySymb (LitLocS L1) (LitLocS L2) with ≡-dec-Loc L1 L2
... | yes p = yes $ cong LitLocS p
... | no ¬p = no λ{ refl → ¬p refl }
≡-dec-ChorTySymb (LitLocS L) EmpS = no (λ ())
≡-dec-ChorTySymb (LitLocS L) SngS = no (λ ())
≡-dec-ChorTySymb (LitLocS L) UnionS = no (λ ())
≡-dec-ChorTySymb EmpS (EmbLocalTyS sₑ) = no (λ ())
≡-dec-ChorTySymb EmpS (LocalS κₑ) = no (λ ())
≡-dec-ChorTySymb EmpS AtS = no (λ ())
≡-dec-ChorTySymb EmpS FunS = no (λ ())
≡-dec-ChorTySymb EmpS (AllS κ ∀κ) = no (λ ())
≡-dec-ChorTySymb EmpS (LitLocS L) = no (λ ())
≡-dec-ChorTySymb EmpS EmpS = yes refl
≡-dec-ChorTySymb EmpS SngS = no (λ ())
≡-dec-ChorTySymb EmpS UnionS = no (λ ())
≡-dec-ChorTySymb SngS (EmbLocalTyS sₑ) = no (λ ())
≡-dec-ChorTySymb SngS (LocalS κₑ) = no (λ ())
≡-dec-ChorTySymb SngS AtS = no (λ ())
≡-dec-ChorTySymb SngS FunS = no (λ ())
≡-dec-ChorTySymb SngS (AllS κ ∀κ) = no (λ ())
≡-dec-ChorTySymb SngS (LitLocS L) = no (λ ())
≡-dec-ChorTySymb SngS EmpS = no (λ ())
≡-dec-ChorTySymb SngS SngS = yes refl
≡-dec-ChorTySymb SngS UnionS = no (λ ())
≡-dec-ChorTySymb UnionS (EmbLocalTyS sₑ) = no (λ ())
≡-dec-ChorTySymb UnionS (LocalS κₑ) = no (λ ())
≡-dec-ChorTySymb UnionS AtS = no (λ ())
≡-dec-ChorTySymb UnionS FunS = no (λ ())
≡-dec-ChorTySymb UnionS (AllS κ ∀κ) = no (λ ())
≡-dec-ChorTySymb UnionS (LitLocS L) = no (λ ())
≡-dec-ChorTySymb UnionS EmpS = no (λ ())
≡-dec-ChorTySymb UnionS SngS = no (λ ())
≡-dec-ChorTySymb UnionS UnionS = yes refl

≡-dec-CTy : DecidableEquality CTy
≡-dec-CTy = ≡-dec-Ty C⅀ₖ ≡-dec-ChorTySymb

-- Predicate for whether a type is of the form tₑ @ ℓ
isAtTy : CTy → CTyp → Set
isAtTy ℓ (κ , t) = Σ[ tₑ ∈ _ ] (κ ≡ * × t ≡ At tₑ ℓ)

dec-isAtTy : (ℓ : CTy) (t : CTyp) → Dec (isAtTy ℓ t)
dec-isAtTy ℓ (LocKnd κₑ , t) = no λ ()
dec-isAtTy ℓ (Bnd κₑ , t) = no λ ()
dec-isAtTy ℓ (* , tyVar x) = no λ ()
dec-isAtTy ℓ (* , tyConstr (EmbLocalTyS sₑ) ts) = no λ ()
dec-isAtTy ℓ (* , tyConstr (LocalS κₑ) ts) = no λ ()
dec-isAtTy ℓ (* , tyConstr AtS []) = no λ ()
dec-isAtTy ℓ (* , tyConstr AtS ((tₑ , zero) ∷ [])) = no λ ()
dec-isAtTy ℓ (* , tyConstr AtS ((tₑ , zero) ∷ (ℓ' , zero) ∷ [])) with ≡-dec-CTy ℓ ℓ'
... | yes refl = yes (tₑ , refl , refl)
... | no ¬p = no λ{ (_ , refl , refl) → ¬p refl }
dec-isAtTy ℓ (* , tyConstr AtS ((tₑ , zero) ∷ (ℓ' , zero) ∷ tk ∷ ts)) = no λ ()
dec-isAtTy ℓ (* , tyConstr AtS ((tₑ , zero) ∷ (ℓ' , suc k) ∷ ts)) = no λ ()
dec-isAtTy ℓ (* , tyConstr AtS ((tₑ , suc k) ∷ ts)) = no λ ()
dec-isAtTy ℓ (* , tyConstr FunS ts) = no λ ()
dec-isAtTy ℓ (* , tyConstr (AllS κ ∀κ) ts) = no λ ()
dec-isAtTy ℓ (* , tyConstr (LitLocS L) ts) = no λ ()
dec-isAtTy ℓ (* , tyConstr EmpS ts) = no λ ()
dec-isAtTy ℓ (* , tyConstr SngS ts) = no λ ()
dec-isAtTy ℓ (* , tyConstr UnionS ts) = no λ ()
dec-isAtTy ℓ (*ₗ , t) = no λ ()
dec-isAtTy ℓ (*ₛ , t) = no λ ()

-- Predicate for whether a type is of the form ℓ.tₑ
isLocalTy : CTy → CTyp → Set
isLocalTy ℓ (κ , t) = Σ[ κₑ ∈ _ ] Σ[ tₑ ∈ _ ] (κ ≡ Bnd κₑ × t ≡ Local κₑ tₑ ℓ)

dec-isLocalTy : (ℓ : CTy) (t : CTyp) → Dec (isLocalTy ℓ t)
dec-isLocalTy ℓ (LocKnd κₑ , t) = no λ ()
dec-isLocalTy ℓ (* , t) = no λ ()
dec-isLocalTy ℓ (Bnd κ1ₑ , tyVar x) = no λ ()
dec-isLocalTy ℓ (Bnd κ1ₑ , tyConstr (EmbLocalTyS sₑ) ts) = no λ ()
dec-isLocalTy ℓ (Bnd κ1ₑ , tyConstr AtS ts) = no λ ()
dec-isLocalTy ℓ (Bnd κ1ₑ , tyConstr (LocalS κ2ₑ) []) = no λ ()
dec-isLocalTy ℓ (Bnd κ1ₑ , tyConstr (LocalS κ2ₑ) ((tₑ , zero) ∷ [])) = no λ ()
dec-isLocalTy ℓ (Bnd κ1ₑ , tyConstr (LocalS κ2ₑ) ((tₑ , zero) ∷ (ℓ' , zero) ∷ []))
  with ≡-dec-CTy ℓ ℓ' | 𝕃 .≡-dec-Kndₑ κ1ₑ κ2ₑ
... | yes refl | yes refl = yes (κ1ₑ , tₑ , refl , refl)
... | yes p    | no  ¬q   = no λ{ (_ , _ , refl , refl) → ¬q refl }
... | no ¬p    | _        = no λ{ (_ , _ , refl , refl) → ¬p refl }
dec-isLocalTy ℓ (Bnd κ1ₑ , tyConstr (LocalS κ2ₑ) ((tₑ , zero) ∷ (ℓ' , zero) ∷ tk ∷ ts)) = no λ ()
dec-isLocalTy ℓ (Bnd κ1ₑ , tyConstr (LocalS κ2ₑ) ((tₑ , zero) ∷ (ℓ' , suc k) ∷ ts)) = no λ ()
dec-isLocalTy ℓ (Bnd κ1ₑ , tyConstr (LocalS κ2ₑ) ((tₑ , suc k) ∷ ts)) = no λ ()
dec-isLocalTy ℓ (Bnd κ1ₑ , tyConstr FunS ts) = no λ ()
dec-isLocalTy ℓ (Bnd κ1ₑ , tyConstr (AllS κ ∀κ) ts) = no λ ()
dec-isLocalTy ℓ (Bnd κ1ₑ , tyConstr (LitLocS L) ts) = no λ ()
dec-isLocalTy ℓ (Bnd κ1ₑ , tyConstr EmpS ts) = no λ ()
dec-isLocalTy ℓ (Bnd κ1ₑ , tyConstr SngS ts) = no λ ()
dec-isLocalTy ℓ (Bnd κ1ₑ , tyConstr UnionS ts) = no λ ()
dec-isLocalTy ℓ (*ₗ , t) = no λ ()
dec-isLocalTy ℓ (*ₛ , t) = no λ ()

?isLocalTy : CTy → CTyp → Bool
?isLocalTy ℓ t = dec-isLocalTy ℓ t .does

{-
Context projection

Projects a choreographic context to a local context at ℓ
by keeping all types of the form ℓ.tₑ

proj ℓ [] = []
proj ℓ (ℓ.tₑ ∷ Δ) = tₑ ∷ proj ℓ Δ
proj ℓ (t ∷ Δ) = proj ℓ Δ
-}
projCtx : List Bool → CTy → ChorCtx → Ctxₑ
projCtx Γ ℓ [] = []
projCtx Γ ℓ (t ∷ Δ) with dec-isLocalTy ℓ t
... | yes (κₑ , tₑ , _ , _) = (κₑ , projTy Γ tₑ) ∷ projCtx Γ ℓ Δ
... | no ¬p = projCtx Γ ℓ Δ

{-
Projecting preserves context well-formedness

Γ ⊢ Δ
--------
Γ∣ ⊢ₑ Δ∣ℓ
-}
⊢projCtx : ∀{Γ Δ} →
           (ℓ : CTy) →
           Γ c⊢ctx Δ →
           projKndCtx Γ e⊢ctx projCtx (map isLocKnd Γ) ℓ Δ
⊢projCtx {Δ = []} ℓ tt = tt
⊢projCtx {Δ = t ∷ Δ} ℓ (⊢t , ⊢Δ) with dec-isLocalTy ℓ t
... | yes (κₑ , tₑ , refl , refl) =
  (⊢projTy $ ⊢Local⁻ ⊢t .fst) , ⊢projCtx ℓ ⊢Δ
... | no ¬p = ⊢projCtx ℓ ⊢Δ

-- Projecting distributes over concatenation
projCtx-++ : (Γ : List Bool) (ℓ : CTy) (Δ1 Δ2 : ChorCtx) →
             projCtx Γ ℓ (Δ1 ++ Δ2) ≡
             projCtx Γ ℓ Δ1 ++ projCtx Γ ℓ Δ2
projCtx-++ Γ ℓ [] Δ2 = refl
projCtx-++ Γ ℓ (t ∷ Δ1) Δ2 with dec-isLocalTy ℓ t
... | yes (κₑ , tₑ , refl , refl) =
  cong ((κₑ , projTy Γ tₑ) ∷_) $
  projCtx-++ Γ ℓ Δ1 Δ2
... | no ¬p = projCtx-++ Γ ℓ Δ1 Δ2

{-
projCtx ∘ ⟨ξ⟩ ≗ ⟨proj ξ⟩ ∘ projCtx

Renaming and then projecting a context is
identical to projecting and then renaming the
context on the projected renaming.
-}
proj∘ren≗projRen∘projCtx
  : ∀{Γ1 Γ2 ξ Δ} →
    Injective _≡_ _≡_ ξ →
    TYREN C⅀ₖ ξ Γ1 Γ2 →
    Γ1 c⊢ctx Δ →
    (ℓ : CTy) →
    projCtx (map isLocKnd Γ2) (renTy C⅀ₖ ξ ℓ) (renCtx C⅀ₖ ξ Δ) ≡
    renCtx ⅀ₑₖ (projTyRen Γ1 Γ2 ξ) (projCtx (map isLocKnd Γ1) ℓ Δ)
proj∘ren≗projRen∘projCtx {Δ = []} ξ-inj ⊢ξ tt ℓ = refl
proj∘ren≗projRen∘projCtx {Γ1} {Γ2} {ξ} {Δ = t ∷ Δ} ξ-inj ⊢ξ (⊢t , ⊢Δ) ℓ
  with dec-isLocalTy ℓ t | dec-isLocalTy (renTy C⅀ₖ ξ ℓ) (renTyp C⅀ₖ ξ t)
... | yes (κₑ , tₑ , refl , refl) | yes (.κₑ , .(renTy C⅀ₖ (Keep* ξ 0) tₑ) , refl , refl) =
  cong₂ (λ x y → (κₑ , x) ∷ y)
    (proj∘ren≗projRen∘projTy ⊢ξ (⊢Local⁻ ⊢t .fst))
    (proj∘ren≗projRen∘projCtx ξ-inj ⊢ξ ⊢Δ ℓ)
... | yes (κₑ , tₑ , refl , refl) | no ¬q =
  ⊥-elim $ ¬q (κₑ , renTy C⅀ₖ ξ tₑ , refl , refl)
proj∘ren≗projRen∘projCtx {Γ1} {Γ2} {ξ} {(.(Bnd κₑ) , tyConstr (LocalS κₑ') ((tₑ' , 0) ∷ (ℓ' , 0) ∷ [])) ∷ Δ}
  ξ-inj ⊢ξ (⊢t , ⊢Δ) ℓ | no ¬p | yes (κₑ , tₑ , refl , r) =
   ⊥-elim $ ¬p (κₑ , tₑ' , refl ,
   cong₂ (λ x y → tyConstr (LocalS x)
        ((tₑ' , 0) ∷ (y , 0) ∷ []))
        (LocalS-inj $ tyConstr-inj C⅀ₖ r .fst)
        (renTy-inj C⅀ₖ ξ-inj $ fst $ tyCons-inj C⅀ₖ $ snd $ snd $ tyCons-inj C⅀ₖ (tyConstr-inj C⅀ₖ r .snd)))
... | no ¬p | no ¬q = proj∘ren≗projRen∘projCtx ξ-inj ⊢ξ ⊢Δ ℓ

-- Inject a local type at a specified location ℓ
LocalTyp : (ℓ : CTy) (tₑ : Typₑ) → CTyp
LocalTyp ℓ (κₑ , tₑ) = Bnd κₑ , Local κₑ (injTy tₑ) ℓ

-- A local type is local
Local-isLocalTy : (κₑ : Kndₑ) (ℓ : CTy) (tₑ : CTy) → isLocalTy ℓ (Bnd κₑ , Local κₑ tₑ ℓ)
Local-isLocalTy κₑ ℓ tₑ = κₑ , tₑ , refl , refl

Local-?isLocalTy : (κₑ : Kndₑ) (ℓ : CTy) (tₑ : CTy) → ?isLocalTy ℓ (Bnd κₑ , Local κₑ tₑ ℓ) ≡ true
Local-?isLocalTy κₑ ℓ tₑ = dec-true (dec-isLocalTy ℓ (Bnd κₑ , Local κₑ tₑ ℓ)) (Local-isLocalTy κₑ ℓ tₑ)

-- An injected type is local
LocalTyp-isLocalTy : (ℓ : CTy) (tₑ : Typₑ) → isLocalTy ℓ (LocalTyp ℓ tₑ)
LocalTyp-isLocalTy ℓ (κₑ , tₑ) = κₑ , injTy tₑ , refl , refl

LocalTyp-?isLocalTy : (ℓ : CTy) (tₑ : Typₑ) → ?isLocalTy ℓ (LocalTyp ℓ tₑ) ≡ true
LocalTyp-?isLocalTy ℓ tₑ =
  dec-true (dec-isLocalTy ℓ (LocalTyp ℓ tₑ)) (LocalTyp-isLocalTy ℓ tₑ)


{-
Context injection

Injects a local context to a choreographic context by converting
every local type tₑ to the type ℓ.tₑ

inj ℓ [] = []
inj ℓ (tₑ ∷ Δₑ) = ℓ.tₑ ∷ inj Δₑ
-}
injCtx : CTy → Ctxₑ → ChorCtx
injCtx ℓ Δₑ = map (LocalTyp ℓ) Δₑ

{-
Injecting preserves context well-formedness

Γₑ ⊢ₑ Δₑ
?.Γₑ ⊢ ℓ : *ₗ
-------------
?.Γₑ ⊢ ℓ.Δₑ
-}
⊢injCtx : ∀{Γₑ Δₑ ℓ} →
           injKndCtx Γₑ c⊢ₜ ℓ ∶ *ₗ →
           Γₑ e⊢ctx Δₑ →
           injKndCtx Γₑ c⊢ctx injCtx ℓ Δₑ
⊢injCtx {Δₑ = []} ⊢ℓ tt = tt 
⊢injCtx {Δₑ = (κₑ , tₑ) ∷ Δₑ} ⊢ℓ (⊢tₑ , ⊢Δₑ) =
  ⊢Local (⊢injTy ⊢tₑ) ⊢ℓ , ⊢injCtx ⊢ℓ ⊢Δₑ

-- Injecting distributes over concatenation
injCtx-++ : (ℓ : CTy) (Δ1ₑ Δ2ₑ : Ctxₑ) →
             injCtx ℓ (Δ1ₑ ++ Δ2ₑ) ≡ injCtx ℓ Δ1ₑ ++ injCtx ℓ Δ2ₑ
injCtx-++ ℓ Δ1 Δ2 = map-++-commute (LocalTyp ℓ) Δ1 Δ2

-- Projecting after injecting a context has no effect
proj∘injCtx≗id : (n : ℕ) (ℓ : CTy) → projCtx (replicate n true) ℓ ∘ injCtx ℓ ≗ id
proj∘injCtx≗id n ℓ [] = refl
proj∘injCtx≗id n ℓ ((κₑ , tₑ) ∷ Δₑ) with dec-isLocalTy ℓ (LocalTyp ℓ (κₑ , tₑ))
... | yes (_ , _ , refl , refl) =
  cong₂ (λ x y → (κₑ , x) ∷ y)
    (proj∘injTy≗id n tₑ)
    (proj∘injCtx≗id n ℓ Δₑ)
... | no ¬p = ⊥-elim $ ¬p $ LocalTyp-isLocalTy ℓ (κₑ , tₑ)

-- An injected context only contains local types
isLocalTy∘injCtx≡true : (ℓ : CTy) (Δₑ : Ctxₑ) →
                        map (?isLocalTy ℓ) (injCtx ℓ Δₑ) ≡
                        replicate (length Δₑ) true
isLocalTy∘injCtx≡true ℓ Δₑ =
  map (?isLocalTy ℓ) (map (LocalTyp ℓ) Δₑ)
    ≡⟨ (sym $ map-compose {g = ?isLocalTy ℓ} {LocalTyp ℓ} Δₑ) ⟩
  map (?isLocalTy ℓ ∘ LocalTyp ℓ) Δₑ
    ≡⟨ map-cong (LocalTyp-?isLocalTy ℓ) Δₑ ⟩
  map (λ _ → true) Δₑ
    ≡⟨ map-const true Δₑ ⟩
  replicate (length Δₑ) true ∎

---------------------
-- TERM PROJECTION --
---------------------

{-
Term projection

If a choreographic term C has type ℓ.tₑ
Γ ⨾ Δ ⊢ C : ℓ.tₑ
then there is a corresponding local term
Γ∣ ⨾ Δ∣ℓ ⊢ proj ℓ C : tₑ
in the projected context
-}
projVar : (Δ : List Bool) → Ren
projVar [] = id
projVar (true ∷ Δ) = Keep (projVar Δ)
projVar (false ∷ Δ) zero = zero
projVar (false ∷ Δ) (suc x) = projVar Δ x

⊢projVar : ∀{Γ Δ x κₑ tₑ} →
            (ℓ : CTy) →
            Γ ⨾ Δ c⊢var x ∶ (Bnd κₑ , Local κₑ tₑ ℓ) →
            projKndCtx Γ ⨾ projCtx (map isLocKnd Γ) ℓ Δ
            e⊢var projVar (map (?isLocalTy ℓ) Δ) x
            ∶ ((κₑ , projTy (map isLocKnd Γ) tₑ))
⊢projVar {Γ} {.(Bnd κₑ , Local κₑ tₑ ℓ) ∷ Δ} {zero} {κₑ} {tₑ} ℓ (⊢0 ⊢Δ ⊢t)
  with dec-isLocalTy ℓ (Bnd κₑ , Local κₑ tₑ ℓ)
... | yes (_ , _ , refl , refl) = ⊢0 (⊢projCtx ℓ ⊢Δ) (⊢projTy (fst $ ⊢Local⁻ ⊢t))
... | no ¬p = ⊥-elim $ ¬p $ Local-isLocalTy κₑ ℓ tₑ
⊢projVar {Γ} {Δ = t ∷ Δ} {suc x} ℓ (⊢S ⊢x ⊢t) with dec-isLocalTy ℓ t
... | yes (κₑ , tₑ , refl , refl) = ⊢S (⊢projVar ℓ ⊢x) (⊢projTy (fst $ ⊢Local⁻ ⊢t))
... | no _ = ⊢projVar ℓ ⊢x

proj : (Γ Δ : List Bool) → CTm → Tmₑ
projVec : (Γ Δ : List Bool) → CTmVec → TmVecₑ

proj Γ Δ (var x) = var (projVar Δ x)
proj Γ Δ (constr (LocalTmS sₑ) ((ℓ , 0) ∷ ts) es) =
  constr sₑ (projTyVec Γ ts) (projVec Γ Δ es)
proj Γ Δ _ = var zero

projVec Γ Δ [] = []
projVec Γ Δ ((e , m , n) ∷ es) =
  (proj (replicate m true ++ Γ) (replicate n true ++ Δ) e , m , n)
  ∷ projVec Γ Δ es
