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
open import PolyPir.TypeOperations Loc ≡-dec-Loc 𝕃
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

?isLocalTy∘TypFun≡true :
  ∀ Γ ℓ Γₑ' tₑ →
  ?isLocalTy
    (renTy C⅀ₖ (Drop* id (length (injKndCtx Γₑ'))) ℓ)
    (TypFun Γ ℓ Γₑ' tₑ)
    ≡ true
?isLocalTy∘TypFun≡true Γ ℓ Γₑ' (κₑ , tₑ) with
  dec-isLocalTy (renTy C⅀ₖ (Drop* id (length (injKndCtx Γₑ'))) ℓ) (TypFun Γ ℓ Γₑ' (κₑ , tₑ))
... | yes p = refl
... | no ¬p = ⊥-elim $ ¬p
      (κₑ ,
      renTy C⅀ₖ
        (regainTyVar (replicate (length Γₑ') true ++ map isLocKnd Γ))
        (injTy tₑ) ,
      refl ,
      refl)

isLocalTy-ren
  : ∀ ℓ tₑ ξ →
    isLocalTy ℓ tₑ →
    isLocalTy (renTy C⅀ₖ ξ ℓ) (renTyp C⅀ₖ ξ tₑ)
isLocalTy-ren ℓ (.(Bnd κₑ) , .(Local κₑ tₑ ℓ)) ξ (κₑ , tₑ , refl , refl) =
  κₑ , renTy C⅀ₖ ξ tₑ , refl , refl

isLocalTy-ren⁻
  : ∀ ℓ tₑ ξ →
    Injective _≡_ _≡_ ξ →
    isLocalTy (renTy C⅀ₖ ξ ℓ) (renTyp C⅀ₖ ξ tₑ) →
    isLocalTy ℓ tₑ
isLocalTy-ren⁻ ℓ (.(Bnd κₑ) , tyConstr (LocalS κₑ') ((tₑ' , 0) ∷ (ℓ' , 0) ∷ [])) ξ ξ-inj (κₑ , tₑ , refl , q) =
  κₑ , tₑ' , refl ,
  cong₃ Local
    (LocalS-inj $ tyConstr-inj C⅀ₖ q .fst)
    refl
    (renTy-inj C⅀ₖ ξ-inj $
       fst $ tyCons-inj C⅀ₖ $ snd $ snd $ tyCons-inj C⅀ₖ $ snd $ tyConstr-inj C⅀ₖ q)

?isLocalTy-ren-≡
  : ∀ ℓ tₑ ξ →
    Injective _≡_ _≡_ ξ →
    ?isLocalTy ℓ tₑ ≡ ?isLocalTy (renTy C⅀ₖ ξ ℓ) (renTyp C⅀ₖ ξ tₑ)
?isLocalTy-ren-≡ ℓ tₑ ξ ξ-inj
  with dec-isLocalTy ℓ tₑ | dec-isLocalTy (renTy C⅀ₖ ξ ℓ) (renTyp C⅀ₖ ξ tₑ)
... | yes p | yes q = refl
... | yes p | no ¬q = ⊥-elim $ ¬q $ isLocalTy-ren ℓ tₑ ξ p
... | no ¬p | yes q = ⊥-elim $ ¬p $ isLocalTy-ren⁻ ℓ tₑ ξ ξ-inj q
... | no ¬p | no ¬q = refl

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

-- A local type is local
Local-isLocalTy : (κₑ : Kndₑ) (ℓ : CTy) (tₑ : CTy) → isLocalTy ℓ (Bnd κₑ , Local κₑ tₑ ℓ)
Local-isLocalTy κₑ ℓ tₑ = κₑ , tₑ , refl , refl

Local-?isLocalTy : (κₑ : Kndₑ) (ℓ : CTy) (tₑ : CTy) → ?isLocalTy ℓ (Bnd κₑ , Local κₑ tₑ ℓ) ≡ true
Local-?isLocalTy κₑ ℓ tₑ = dec-true (dec-isLocalTy ℓ (Bnd κₑ , Local κₑ tₑ ℓ)) (Local-isLocalTy κₑ ℓ tₑ)

LocalTyp : (ξ : Ren) (ℓ : CTy) (tₑ : Typₑ) → CTyp
LocalTyp ξ ℓ (κₑ , tₑ) = Bnd κₑ , Local κₑ (renTy C⅀ₖ ξ (injTy tₑ)) ℓ

-- An injected type is local
LocalTyp-isLocalTy : (ξ : Ren) (ℓ : CTy) (tₑ : Typₑ) → isLocalTy ℓ (LocalTyp ξ ℓ tₑ)
LocalTyp-isLocalTy ξ ℓ (κₑ , tₑ) = κₑ , renTy C⅀ₖ ξ (injTy tₑ) , refl , refl

LocalTyp-?isLocalTy : (ξ : Ren) (ℓ : CTy) (tₑ : Typₑ) → ?isLocalTy ℓ (LocalTyp ξ ℓ tₑ) ≡ true
LocalTyp-?isLocalTy ξ ℓ tₑ =
  dec-true (dec-isLocalTy ℓ (LocalTyp ξ ℓ tₑ)) (LocalTyp-isLocalTy ξ ℓ tₑ)

{-
Context injection

Injects a local context to a choreographic context by converting
every local type tₑ to the type ℓ.tₑ

inj ξ ℓ [] = []
inj ξ ℓ (tₑ ∷ Δₑ) = ℓ.⟨ξ⟩tₑ ∷ inj Δₑ
-}
injCtx : Ren → CTy → Ctxₑ → ChorCtx
injCtx ξ ℓ Δₑ = map (LocalTyp ξ ℓ) Δₑ

{-
Injecting preserves context well-formedness

Γₑ ⊢ₑ Δₑ
ξ : inj Γₑ ⇒ Γ
Γ ⊢ ℓ : *ₗ
-------------
Γ ⊢ ℓ.⟨ξ⟩Δₑ
-}
⊢injCtx : ∀{ξ Γₑ Γ Δₑ ℓ} →
          TYREN C⅀ₖ ξ (injKndCtx Γₑ) Γ →
          Γ c⊢ₜ ℓ ∶ *ₗ →
          Γₑ e⊢ctx Δₑ →
          Γ c⊢ctx injCtx ξ ℓ Δₑ
⊢injCtx {Δₑ = []} ⊢ξ ⊢ℓ tt = tt 
⊢injCtx {Δₑ = (κₑ , tₑ) ∷ Δₑ} ⊢ξ ⊢ℓ (⊢tₑ , ⊢Δₑ) =
  ⊢Local (⊢renTy C⅀ₖ ⊢ξ (⊢injTy ⊢tₑ)) ⊢ℓ , ⊢injCtx ⊢ξ ⊢ℓ ⊢Δₑ

-- Injecting contexts distributes over concatenation
injCtx-++ : (ξ : Ren) (ℓ : CTy) (Δ1ₑ Δ2ₑ : Ctxₑ) →
             injCtx ξ ℓ (Δ1ₑ ++ Δ2ₑ) ≡ injCtx  ξ ℓ Δ1ₑ ++ injCtx ξ ℓ Δ2ₑ
injCtx-++ ξ ℓ Δ1 Δ2 = map-++-commute (LocalTyp ξ ℓ) Δ1 Δ2

regainTyVarId : ∀{Γₑ x κₑ} →
                injKndCtx Γₑ c⊢ₜvar x ∶ LocKnd κₑ →
                regainTyVar (map isLocKnd (injKndCtx Γₑ)) x ≡ x
regainTyVarId {κₑ ∷ Γₑ} ⊢ₜ0 = refl
regainTyVarId {κₑ ∷ Γₑ} (⊢ₜS ⊢x) = cong suc $ regainTyVarId ⊢x

regainTyId : ∀{Γₑ t κₑ} →
              injKndCtx Γₑ c⊢ₜ t ∶ LocKnd κₑ →
              regainTy (map isLocKnd (injKndCtx Γₑ)) t ≡ t
regainTyVecId : ∀{Γₑ ts Σₑ} →
                injKndCtx Γₑ c⊢ₜvec ts ∶ map LocKndΣ Σₑ →
                regainTyVec (map isLocKnd (injKndCtx Γₑ)) ts ≡ ts

regainTyId {t = tyVar x} (⊢ₜvar ⊢x) =
  cong tyVar $ regainTyVarId ⊢x
regainTyId {t = tyConstr (EmbLocalTyS sₑ) ts}
  (⊢ₜtyConstr .(EmbLocalTyS sₑ) ⊢ts) =
    cong (tyConstr (EmbLocalTyS sₑ)) $ regainTyVecId ⊢ts

regainTyVecId {ts = []} {[]} ⊢ₜ[] = refl
regainTyVecId {Γₑ} {(t , .(length (injKndCtx Γₑ'))) ∷ ts}
  {(Γₑ' , κₑ) ∷ Σₑ} (⊢t ⊢ₜ∷ ⊢ts) =
    cong₂ (λ x y → (x , length (injKndCtx Γₑ')) ∷ y)
      (renTy C⅀ₖ
          (Keep* (regainTyVar (map isLocKnd (injKndCtx Γₑ)))
            (length (injKndCtx Γₑ')))
        t
        ≡⟨ renTy-ext C⅀ₖ
              (Keep*-regainTyVar (map isLocKnd (injKndCtx Γₑ))
                (length (injKndCtx Γₑ')))
              t ⟩
      renTy C⅀ₖ
        (regainTyVar
          (replicate (length (injKndCtx Γₑ')) true ++
            map isLocKnd (injKndCtx Γₑ)))
        t
        ≡⟨ (cong (λ x → renTy C⅀ₖ
                (regainTyVar
                  (replicate x true ++ map isLocKnd (injKndCtx Γₑ)))
                  t) $
              length-map LocKnd Γₑ') ⟩
      renTy C⅀ₖ
        (regainTyVar
          (replicate (length Γₑ') true ++
            map isLocKnd (injKndCtx Γₑ)))
        t
        ≡⟨ (cong (λ x → renTy C⅀ₖ
                (regainTyVar (x ++ map isLocKnd (injKndCtx Γₑ))) t) $
              sym $ isLocKnd∘injKndCtx≡true Γₑ') ⟩
      renTy C⅀ₖ
        (regainTyVar
          (map isLocKnd (injKndCtx Γₑ') ++
            map isLocKnd (injKndCtx Γₑ)))
        t
        ≡⟨ (cong (λ x → renTy C⅀ₖ (regainTyVar x) t) $
            sym $ map-++-commute isLocKnd (injKndCtx Γₑ') (injKndCtx Γₑ)) ⟩
      renTy C⅀ₖ (regainTyVar (map isLocKnd (injKndCtx Γₑ' ++ injKndCtx Γₑ))) t
        ≡⟨ (cong (λ x → renTy C⅀ₖ (regainTyVar (map isLocKnd x)) t) $
            sym $ injKndCtx-++ Γₑ' Γₑ) ⟩
      renTy C⅀ₖ (regainTyVar (map isLocKnd (injKndCtx (Γₑ' ++ Γₑ)))) t
        ≡⟨ (regainTyId $
            subst (_c⊢ₜ t ∶ LocKnd κₑ)
              (sym $ injKndCtx-++ Γₑ' Γₑ)
              ⊢t) ⟩
      t ∎)
      (regainTyVecId ⊢ts)

projTyRen-regain≗id : ∀{Γ x κₑ} →
                      projKndCtx Γ e⊢ₜvar x ∶ κₑ →
                      projTyRen (injKndCtx (projKndCtx Γ)) Γ (regainTyVar (map isLocKnd Γ)) x ≡ x
projTyRen-regain≗id {Γ} {x} {κₑ} ⊢x =
  projTyVar (map isLocKnd Γ)
    (regainTyVar (map isLocKnd Γ)
     (regainTyVar (map isLocKnd (injKndCtx (projKndCtx Γ))) x))
    ≡⟨ (cong (λ y → projTyVar (map isLocKnd Γ) (regainTyVar (map isLocKnd Γ) y)) $
        regainTyVarId (⊢injTyVar ⊢x)) ⟩
  projTyVar (map isLocKnd Γ) (regainTyVar (map isLocKnd Γ) x)
    ≡⟨ proj∘regain∘injTyVar≗id (map isLocKnd Γ) x ⟩
  x ∎

-- Projecting after injecting a context has no effect
proj∘regain∘injCtx≗id
  : ∀{Γ Δₑ} →
    (ℓ : CTy) →
    projKndCtx Γ e⊢ctx Δₑ →
    projCtx (map isLocKnd Γ) ℓ (injCtx (regainTyVar (map isLocKnd Γ)) ℓ Δₑ) ≡ Δₑ
proj∘regain∘injCtx≗id {Δₑ = []} ℓ tt = refl
proj∘regain∘injCtx≗id {Γ} {(κₑ , tₑ) ∷ Δₑ} ℓ (⊢tₑ , ⊢Δₑ) with dec-isLocalTy ℓ (LocalTyp (regainTyVar (map isLocKnd Γ)) ℓ (κₑ , tₑ))
... | yes (.κₑ , .(renTy C⅀ₖ (regainTyVar (map isLocKnd Γ)) (injTy tₑ)) , refl , refl) =
  cong₂ (λ x y → (κₑ , x) ∷ y)
    (proj∘regain∘injTy≗id ⊢tₑ)
    (proj∘regain∘injCtx≗id ℓ ⊢Δₑ)
... | no ¬p = ⊥-elim $ ¬p $ LocalTyp-isLocalTy (regainTyVar (map isLocKnd Γ)) ℓ (κₑ , tₑ)

-- An injected context only contains local types
isLocalTy∘injCtx≡true : (ξ : Ren) (ℓ : CTy) (Δₑ : Ctxₑ) →
                        map (?isLocalTy ℓ) (injCtx ξ ℓ Δₑ) ≡
                        replicate (length Δₑ) true
isLocalTy∘injCtx≡true ξ ℓ Δₑ =
  map (?isLocalTy ℓ) (map (LocalTyp ξ ℓ) Δₑ)
    ≡⟨ (sym $ map-compose {g = ?isLocalTy ℓ} {LocalTyp ξ ℓ} Δₑ) ⟩
  map (?isLocalTy ℓ ∘ LocalTyp ξ ℓ) Δₑ
    ≡⟨ map-cong (LocalTyp-?isLocalTy ξ ℓ) Δₑ ⟩
  map (λ _ → true) Δₑ
    ≡⟨ map-const true Δₑ ⟩
  replicate (length Δₑ) true ∎

---------------------
-- TERM PROJECTION --
---------------------

{-
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
            ∶ (κₑ , projTy (map isLocKnd Γ) tₑ)
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

projCtx∘TypFun≗id
  : ∀{Γ ℓ} (Δₑ : Ctx ⅀ₑₖ) (Γₑ' : KndCtxₑ) →
    projKndCtx (map LocKnd Γₑ' ++ Γ) e⊢ctx Δₑ →
    projCtx (map isLocKnd (injKndCtx Γₑ' ++ Γ))
      (renTy C⅀ₖ (Drop* id (length (injKndCtx Γₑ'))) ℓ)
      (map (TypFun Γ ℓ Γₑ') Δₑ)
    ≡ Δₑ
projCtx∘TypFun≗id [] Γₑ' tt = refl
projCtx∘TypFun≗id {Γ} {ℓ} ((κₑ , tₑ) ∷ Δₑ) Γₑ' (⊢tₑ , ⊢Δₑ)
  with dec-isLocalTy (renTy C⅀ₖ (Drop* id (length (injKndCtx Γₑ'))) ℓ) (TypFun Γ ℓ Γₑ' (κₑ , tₑ))
... | yes (_ , _ , refl , refl) =
  let eq : replicate (length Γₑ') true ++ map isLocKnd Γ
           ≡ map isLocKnd (map LocKnd Γₑ' ++ Γ)
      eq =
        replicate (length Γₑ') true ++ map isLocKnd Γ
          ≡⟨ (cong (_++ map isLocKnd Γ) $ sym $ isLocKnd∘injKndCtx≡true Γₑ') ⟩
        map isLocKnd (map LocKnd Γₑ') ++ map isLocKnd Γ
          ≡⟨ (sym $ map-++-commute isLocKnd (map LocKnd Γₑ') Γ) ⟩
        map isLocKnd (map LocKnd Γₑ' ++ Γ) ∎
  in cong₂ (λ x y → (κₑ , x) ∷ y)
    (projTy (map isLocKnd (map LocKnd Γₑ' ++ Γ))
      (regainTy (replicate (length Γₑ') true ++ map isLocKnd Γ)
        (injTy tₑ))
      ≡⟨ cong (λ x → projTy (map isLocKnd (map LocKnd Γₑ' ++ Γ))
            (regainTy x (injTy tₑ)))
          eq ⟩
    projTy (map isLocKnd (map LocKnd Γₑ' ++ Γ))
      (regainTy (map isLocKnd (map LocKnd Γₑ' ++ Γ))
        (injTy tₑ))
      ≡⟨ proj∘regain∘injTy≗id ⊢tₑ ⟩
    tₑ ∎)
    (projCtx∘TypFun≗id Δₑ Γₑ' ⊢Δₑ)
... | no ¬p = ⊥-elim $ ¬p (κₑ , _ , refl , refl)

⊢proj : ∀{Γ Δ e κₑ tₑ} →
          (ℓ : CTy) →
          Γ ⨾ Δ c⊢ e ∶ (Bnd κₑ , Local κₑ tₑ ℓ) →
          projKndCtx Γ ⨾ projCtx (map isLocKnd Γ) ℓ Δ
          e⊢ proj (map isLocKnd Γ) (map (?isLocalTy ℓ) Δ) e
          ∶ (κₑ , projTy (map isLocKnd Γ) tₑ)
⊢projVec : ∀{Γ Δ es Σₑ} →
            (ℓ : CTy) →
            Γ ⨾ Δ c⊢vec es ∶ map (BinderFun Γ ℓ) Σₑ →
            projKndCtx Γ ⨾ projCtx (map isLocKnd Γ) ℓ Δ
            e⊢vec projVec (map isLocKnd Γ) (map (?isLocalTy ℓ) Δ) es
            ∶ Σₑ

⊢proj {e = var x} ℓ (⊢var ⊢x) = ⊢var $ ⊢projVar ℓ ⊢x
⊢proj {Γ} {Δ} {e = constr (LocalTmS sₑ) ((ℓ , 0) ∷ ts) es}
  {.(TmSigₑ sₑ (projKndCtx Γ) (projTyVec (map isLocKnd Γ) ts) .snd .fst)}
  {.(regainTy (map isLocKnd Γ) (injTy (TmSigₑ sₑ (projKndCtx Γ) (projTyVec (map isLocKnd Γ) ts) .snd .snd)))}
  .ℓ (⊢constr .(LocalTmS sₑ) (⊢ℓ ⊢ₜ∷ ⊢ts) ⊢es) =
    let eq : projTy (map isLocKnd Γ) (regainTy (map isLocKnd Γ)
              (injTy (TmSigₑ sₑ (projKndCtx Γ) (projTyVec (map isLocKnd Γ) ts) .snd .snd)))
             ≡ TmSigₑ sₑ (projKndCtx Γ) (projTyVec (map isLocKnd Γ) ts) .snd .snd
        eq = proj∘regain∘injTy≗id $ 𝕃 .⅀ₑ .⊢TmSig-snd sₑ $ ⊢projTyVec ⊢ts
    in subst (λ x →
          projKndCtx Γ ⨾ projCtx (map isLocKnd Γ) ℓ Δ
          e⊢ constr sₑ
            (projTyVec (map isLocKnd Γ) ts)
            (projVec (map isLocKnd Γ) (map (λ t → dec-isLocalTy ℓ t .does) Δ) es)
          ∶ (TmSigₑ sₑ (projKndCtx Γ) (projTyVec (map isLocKnd Γ) ts) .snd .fst , x))
        (sym eq)
        (⊢constr sₑ (⊢projTyVec ⊢ts) (⊢projVec ℓ ⊢es))
⊢proj {e = constr DoneS ((tₑ , 0) ∷ (ℓ' , 0) ∷ []) ((e , 0 , 0) ∷ [])} ℓ ()
⊢proj {e = constr LamS ((τ1 , 0) ∷ (τ2 , 0) ∷ []) ((C , 0 , 1) ∷ [])} ℓ ()
⊢proj {e = constr FixS ((τ , 0) ∷ []) ((C , 0 , 1) ∷ [])} ℓ ()
⊢proj {e = constr AppS ((τ1 , 0) ∷ (τ2 , 0) ∷ []) ((C1 , 0 , 0) ∷ (C2 , 0 , 0) ∷ [])} ℓ ()
⊢proj {e = constr (AbsS κ ∀κ) ((τ , 1) ∷ []) ((C , 1 , 0) ∷ [])} ℓ ()
⊢proj {e = constr (AppTyS κ ∀κ) ((τ , 1) ∷ (T , 0) ∷ []) ((C , 0 , 0) ∷ [])} ℓ ()
⊢proj {e = constr SendS ((ℓ1 , 0) ∷ (ℓ2 , 0) ∷ (tₑ , 0) ∷ []) ((C , 0 , 0) ∷ [])} ℓ ()
⊢proj {e = constr (SyncS d) ((ℓ1 , 0) ∷ (ℓ2 , 0) ∷ (τ , 0) ∷ []) ((C , 0 , 0) ∷ [])} ℓ ()
⊢proj {e = constr ITES ((ℓ' , 0) ∷ (τ1 , 0) ∷ []) ((C1 , 0 , 0) ∷ (C2 , 0 , 0) ∷ (C3 , 0 , 0) ∷ [])} ℓ ()
⊢proj {e = constr LocalLetS ((ℓ' , 0) ∷ (tₑ , 0) ∷ (τ , 0) ∷ []) ((C1 , 0 , 0) ∷ (C2 , 0 , 1) ∷ [])} ℓ ()
⊢proj {e = constr TellTyS ((ℓ' , 0) ∷ (ρ , 0) ∷ (τ , 0) ∷ []) ((C1 , 0 , 0) ∷ (C2 , 1 , 0) ∷ [])} ℓ ()
⊢proj {e = constr TellLocS ((ℓ' , 0) ∷ (ρ , 0) ∷ (τ , 0) ∷ []) ((C1 , 0 , 0) ∷ (C2 , 1 , 0) ∷ [])} ℓ ()

⊢projVec {es = []} {[]} ℓ (⊢[] ⊢Δ) = ⊢[] (⊢projCtx ℓ ⊢Δ)
⊢projVec {Γ} {Δ} {es = (e , .(length (injKndCtx Γₑ')) , .(length (map (TypFun _ ℓ Γₑ') Δₑ'))) ∷ es}
  {(Γₑ' , Δₑ' , κₑ , tₑ) ∷ Σₑ} ℓ (⊢e ⊢∷ ⊢es) =
    let ⊢Δ : Γ c⊢ctx Δ
        ⊢Δ = ⊢renCtx⁻ C⅀ₖ (⊢TyDrop⁻* C⅀ₖ (⊢TyIdRen⁻ C⅀ₖ) (injKndCtx Γₑ')) $
                ⊢ctx-++⁻ C⅀ₖ (map (TypFun Γ ℓ Γₑ') Δₑ')
                (renCtx (C⅀ .⅀ₖ) (Drop* id (length (injKndCtx Γₑ'))) Δ)
                (⊢⇒⊢ctx C⅀ ⊢e) .snd
        ⊢TypFun-Δₑ' : (injKndCtx Γₑ' ++ Γ) c⊢ctx map (TypFun Γ ℓ Γₑ') Δₑ'
        ⊢TypFun-Δₑ' = ⊢ctx-++⁻ C⅀ₖ (map (TypFun Γ ℓ Γₑ') Δₑ')
                        (renCtx (C⅀ .⅀ₖ) (Drop* id (length (injKndCtx Γₑ'))) Δ)
                        (⊢⇒⊢ctx C⅀ ⊢e) .fst
        eq : Γₑ' ++ projKndCtx Γ ≡ projKndCtx (injKndCtx Γₑ' ++ Γ)
        eq =
          Γₑ' ++ projKndCtx Γ
            ≡⟨ (cong (_++ projKndCtx Γ) $ sym $ proj∘injKndCtx≗id Γₑ') ⟩
          projKndCtx (injKndCtx Γₑ') ++ projKndCtx Γ
            ≡⟨ (sym $ projKndCtx-++ (injKndCtx Γₑ')  Γ) ⟩
          projKndCtx (injKndCtx Γₑ' ++ Γ) ∎
        ⊢Δₑ' : projKndCtx (injKndCtx Γₑ' ++ Γ) e⊢ctx Δₑ'
        ⊢Δₑ' = map-AllElems⁻
                  (wfTyp ⅀ₑₖ (projKndCtx (injKndCtx Γₑ' ++ Γ)))
                  (wfTyp C⅀ₖ (injKndCtx Γₑ' ++ Γ))
                  (TypFun Γ ℓ Γₑ')
                  (λ tₑ ⊢Local-tₑ →
                    subst (λ x → wfTyp ⅀ₑₖ x tₑ) eq $
                    ⊢TypFun⁻ {Γ} {ℓ} {Γₑ'} {tₑ} ⊢Local-tₑ .snd)
                  ⊢TypFun-Δₑ'
        eq2 : replicate (length Γₑ') true ++ map isLocKnd Γ
              ≡ map isLocKnd (injKndCtx Γₑ' ++ Γ)
        eq2 =
          replicate (length Γₑ') true ++ map isLocKnd Γ
            ≡⟨ (cong (_++ map isLocKnd Γ) $ sym $ isLocKnd∘injKndCtx≡true Γₑ') ⟩
          map isLocKnd (injKndCtx Γₑ') ++ map isLocKnd Γ
            ≡⟨ (sym $ map-++-commute isLocKnd (injKndCtx Γₑ') Γ) ⟩
          map isLocKnd (injKndCtx Γₑ' ++ Γ) ∎
        eq3 : projTy (map isLocKnd (injKndCtx Γₑ' ++ Γ))
                (regainTy (replicate (length Γₑ') true ++ map isLocKnd Γ)
                  (injTy tₑ))
              ≡ tₑ
        eq3 =
          projTy (map isLocKnd (injKndCtx Γₑ' ++ Γ))
            (regainTy (replicate (length Γₑ') true ++ map isLocKnd Γ)
              (injTy tₑ))
            ≡⟨ (cong (λ x → projTy (map isLocKnd (injKndCtx Γₑ' ++ Γ))
                  (regainTy x (injTy tₑ))) eq2) ⟩
          projTy (map isLocKnd (injKndCtx Γₑ' ++ Γ))
            (regainTy (map isLocKnd (injKndCtx Γₑ' ++ Γ))
              (injTy tₑ))
            ≡⟨ proj∘regain∘injTy≗id {injKndCtx Γₑ' ++ Γ}
                {κₑ} {tₑ} $
                (subst (_e⊢ₜ tₑ ∶ κₑ) eq $
                  ⊢TypFun⁻ {Γ} {ℓ} {Γₑ'} {κₑ , tₑ} (⊢⇒⊢typ C⅀ ⊢e) .snd) ⟩
          tₑ ∎
        eq4 : map (?isLocalTy (renTy C⅀ₖ (Drop* id (length (injKndCtx Γₑ'))) ℓ))
                (map (TypFun Γ ℓ Γₑ') Δₑ'
                  ++ renCtx C⅀ₖ (Drop* id (length (injKndCtx Γₑ'))) Δ)
              ≡ replicate (length (map (TypFun Γ ℓ Γₑ') Δₑ')) true
                  ++ map (?isLocalTy ℓ) Δ
        eq4 =
          let ξ = Drop* id (length (injKndCtx Γₑ'))
              ℓ' = renTy C⅀ₖ ξ ℓ
              Δ' = renCtx C⅀ₖ ξ Δ in
          map (?isLocalTy ℓ') (map (TypFun Γ ℓ Γₑ') Δₑ' ++ Δ')
            ≡⟨ map-++-commute (?isLocalTy ℓ') (map (TypFun Γ ℓ Γₑ') Δₑ') Δ' ⟩
          map (?isLocalTy ℓ') (map (TypFun Γ ℓ Γₑ') Δₑ')
          ++ map (?isLocalTy ℓ') Δ'
            ≡⟨ (sym $ cong (_++ map (?isLocalTy ℓ') Δ') $
                  map-compose {g = ?isLocalTy ℓ'} {TypFun Γ ℓ Γₑ'} Δₑ') ⟩
          map (?isLocalTy ℓ' ∘ TypFun Γ ℓ Γₑ') Δₑ'
          ++ map (?isLocalTy ℓ') Δ'
            ≡⟨ (cong (_++ map (?isLocalTy ℓ') Δ') $
                  map-cong (?isLocalTy∘TypFun≡true Γ ℓ Γₑ') Δₑ') ⟩
          map (λ _ → true) Δₑ'
          ++ map (?isLocalTy ℓ') Δ'
            ≡⟨ (cong (_++ map (?isLocalTy ℓ') Δ') $
                  map-const true Δₑ') ⟩
          replicate (length Δₑ') true
          ++ map (?isLocalTy ℓ') Δ'
            ≡⟨ (cong (λ x → replicate x true ++ map (?isLocalTy ℓ') Δ') $
                  sym $ length-map (TypFun Γ ℓ Γₑ') Δₑ') ⟩
          replicate (length (map (TypFun Γ ℓ Γₑ') Δₑ')) true
          ++ map (?isLocalTy ℓ') (map (renTyp C⅀ₖ ξ) Δ)
            ≡⟨ (sym $ cong (replicate (length (map (TypFun Γ ℓ Γₑ') Δₑ')) true ++_) $
                map-compose {g = ?isLocalTy ℓ'}
                {renTyp C⅀ₖ ξ}
                Δ) ⟩
          replicate (length (map (TypFun Γ ℓ Γₑ') Δₑ')) true
          ++ map (?isLocalTy ℓ' ∘ renTyp C⅀ₖ ξ) Δ
            ≡⟨ (cong (replicate (length (map (TypFun Γ ℓ Γₑ') Δₑ')) true ++_) $
                map-cong
                  (λ tₑ → sym $
                    ?isLocalTy-ren-≡ ℓ tₑ ξ
                      (Drop*-inj id (length (injKndCtx Γₑ'))))
                  Δ) ⟩
          replicate (length (map (TypFun Γ ℓ Γₑ') Δₑ')) true
          ++ map (?isLocalTy ℓ) Δ ∎
    in ⊢∷'
      (𝕃 .⅀ₑ)
      (⊢proj (renTy C⅀ₖ (Drop* id (length (injKndCtx Γₑ'))) ℓ) ⊢e)
      (⊢projVec ℓ ⊢es)
      (projKndCtx (injKndCtx Γₑ' ++ Γ)
        ≡⟨ projKndCtx-++ (injKndCtx Γₑ') Γ ⟩
      projKndCtx (injKndCtx Γₑ') ++ projKndCtx Γ
        ≡⟨ (cong (_++ projKndCtx Γ) $ proj∘injKndCtx≗id Γₑ') ⟩
      Γₑ' ++ projKndCtx Γ ∎)
      (projCtx (map isLocKnd (injKndCtx Γₑ' ++ Γ))
          (renTy C⅀ₖ (Drop* id (length (injKndCtx Γₑ'))) ℓ)
          (map (TypFun Γ ℓ Γₑ') Δₑ'
            ++ renCtx (C⅀ .⅀ₖ) (Drop* id (length (injKndCtx Γₑ'))) Δ)
        ≡⟨ projCtx-++ (map isLocKnd (injKndCtx Γₑ' ++ Γ))
            (renTy C⅀ₖ (Drop* id (length (injKndCtx Γₑ'))) ℓ)
            (map (TypFun Γ ℓ Γₑ') Δₑ')
            (renCtx (C⅀ .⅀ₖ) (Drop* id (length (injKndCtx Γₑ'))) Δ) ⟩
      projCtx (map isLocKnd (injKndCtx Γₑ' ++ Γ))
        (renTy C⅀ₖ (Drop* id (length (injKndCtx Γₑ'))) ℓ)
        (map (TypFun Γ ℓ Γₑ') Δₑ')
      ++ projCtx (map isLocKnd (injKndCtx Γₑ' ++ Γ))
          (renTy C⅀ₖ (Drop* id (length (injKndCtx Γₑ'))) ℓ)
          (renCtx C⅀ₖ (Drop* id (length (injKndCtx Γₑ'))) Δ)
        ≡⟨ (cong (projCtx (map isLocKnd (injKndCtx Γₑ' ++ Γ))
              (renTy C⅀ₖ (Drop* id (length (injKndCtx Γₑ'))) ℓ)
              (map (TypFun Γ ℓ Γₑ') Δₑ') ++_) $
            proj∘ren≗projRen∘projCtx
                (Drop*-inj (λ p → p) (length (injKndCtx Γₑ')))
                (⊢TyDrop* C⅀ₖ (⊢TyIdRen C⅀ₖ) (injKndCtx Γₑ'))
                ⊢Δ ℓ) ⟩
      projCtx (map isLocKnd (injKndCtx Γₑ' ++ Γ))
        (renTy C⅀ₖ (Drop* id (length (injKndCtx Γₑ'))) ℓ)
        (map (TypFun Γ ℓ Γₑ') Δₑ')
      ++ renCtx ⅀ₑₖ
        (projTyRen Γ (injKndCtx Γₑ' ++ Γ) (Drop* id (length (map LocKnd Γₑ'))))
        (projCtx (map isLocKnd Γ) ℓ Δ)
        ≡⟨ (cong (projCtx (map isLocKnd (injKndCtx Γₑ' ++ Γ))
              (renTy C⅀ₖ (Drop* id (length (injKndCtx Γₑ'))) ℓ)
              (map (TypFun Γ ℓ Γₑ') Δₑ') ++_) $
                ⊢renCtx-≗TyRen ⅀ₑₖ
                  (Drop*-projTyRen (⊢TyIdRen C⅀ₖ {Γ}) Γₑ')
                  (⊢projCtx ℓ ⊢Δ)) ⟩
      projCtx (map isLocKnd (injKndCtx Γₑ' ++ Γ))
        (renTy C⅀ₖ (Drop* id (length (injKndCtx Γₑ'))) ℓ)
        (map (TypFun Γ ℓ Γₑ') Δₑ')
      ++ renCtx ⅀ₑₖ (Drop* (projTyRen Γ Γ id) (length (map LocKnd Γₑ'))) (projCtx (map isLocKnd Γ) ℓ Δ)
        ≡⟨ (cong (projCtx (map isLocKnd (injKndCtx Γₑ' ++ Γ))
              (renTy C⅀ₖ (Drop* id (length (injKndCtx Γₑ'))) ℓ)
              (map (TypFun Γ ℓ Γₑ') Δₑ') ++_) $
              renCtx-ext ⅀ₑₖ
                (subst (λ x →
                    Drop* (projTyRen Γ Γ id) (length (map LocKnd Γₑ')) ≗
                    Drop* id x)
                  (length-map LocKnd Γₑ')
                  (Drop*-ext (projTyRenId Γ) (length (map LocKnd Γₑ'))))
                (projCtx (map isLocKnd Γ) ℓ Δ)) ⟩
      projCtx (map isLocKnd (injKndCtx Γₑ' ++ Γ))
        (renTy C⅀ₖ (Drop* id (length (injKndCtx Γₑ'))) ℓ)
        (map (TypFun Γ ℓ Γₑ') Δₑ')
      ++ renCtx ⅀ₑₖ (Drop* id (length Γₑ')) (projCtx (map isLocKnd Γ) ℓ Δ)
        ≡⟨ (cong (_++ renCtx ⅀ₑₖ (Drop* id (length Γₑ')) (projCtx (map isLocKnd Γ) ℓ Δ)) $
            projCtx∘TypFun≗id Δₑ' Γₑ' ⊢Δₑ') ⟩
      Δₑ' ++ renCtx ⅀ₑₖ (Drop* id (length Γₑ')) (projCtx (map isLocKnd Γ) ℓ Δ) ∎)
      (length-map LocKnd Γₑ')
      (length-map (TypFun Γ ℓ Γₑ') Δₑ')
      refl
      (cong (κₑ ,_) $ eq3)
      (cong₂ (λ x y → proj x y e)
        (sym eq2 ∙ (cong (λ x → replicate x true ++ map isLocKnd Γ) $ sym $ length-map LocKnd Γₑ'))
        eq4)

ren-Local : (ξ : Ren) (κₑ : Kndₑ) (tₑ : CTy) (ℓ : CTy) →
            renTy C⅀ₖ ξ (Local κₑ tₑ ℓ) ≡
            Local κₑ (renTy C⅀ₖ ξ tₑ) (renTy C⅀ₖ ξ ℓ)
ren-Local ξ κₑ tₑ ℓ = refl

ren-LocalTyp : (ξ1 ξ2 : Ren) (ℓ : CTy) (tₑ : Typₑ) →
               renTyp C⅀ₖ ξ1 (LocalTyp ξ2 ℓ tₑ) ≡
               LocalTyp (ξ1 • ξ2) (renTy C⅀ₖ ξ1 ℓ) tₑ
ren-LocalTyp ξ1 ξ2 ℓ (κₑ , tₑ) =
  cong (λ x → Bnd κₑ , tyConstr (LocalS κₑ) ((x , 0) ∷ (renTy C⅀ₖ ξ1 ℓ , 0) ∷ [])) $
  renTy• C⅀ₖ ξ1 ξ2 (injTy tₑ)

--------------------
-- TERM INJECTION --
--------------------

{-
If a local term e has type tₑ 
Γₑ ⨾ Δₑ ⊢ₑ e : tₑ
ℓ is a valid location in contex Γ,
and ξ renames inj Γₑ to Γ,
then there is a corresponding choreographic term
Γ ⨾ ℓ.Δₑ ⊢ inj ℓ C : tₑ
-}
⊢injVar
  : ∀{Γₑ Γ ξ Δₑ x tₑ ℓ} →
    TYREN C⅀ₖ ξ (injKndCtx Γₑ) Γ →
    Γ c⊢ₜ ℓ ∶ *ₗ →
    Γₑ ⨾ Δₑ e⊢var x ∶ tₑ →
    Γ ⨾ injCtx ξ ℓ Δₑ c⊢var x ∶ LocalTyp ξ ℓ tₑ
⊢injVar ⊢ξ ⊢ℓ (⊢0 ⊢Δₑ ⊢tₑ) = ⊢0 (⊢injCtx ⊢ξ ⊢ℓ ⊢Δₑ) (⊢Local (⊢renTy C⅀ₖ ⊢ξ (⊢injTy ⊢tₑ)) ⊢ℓ)
⊢injVar ⊢ξ ⊢ℓ (⊢S ⊢x ⊢t2) = ⊢S (⊢injVar ⊢ξ ⊢ℓ ⊢x) (⊢Local (⊢renTy C⅀ₖ ⊢ξ (⊢injTy ⊢t2)) ⊢ℓ)

inj : Ren → CTy → Tmₑ → CTm
injVec : Ren → CTy → TmVecₑ → CTmVec

inj ξ ℓ (var x) = var x
inj ξ ℓ (constr sₑ ts es) =
  constr (LocalTmS sₑ) ((ℓ , 0) ∷ renTyVec C⅀ₖ ξ (injTyVec ts)) (injVec ξ ℓ es)

injVec ξ ℓ [] = []
injVec ξ ℓ ((e , m , n) ∷ es) =
  (inj (Keep* ξ m) (renTy C⅀ₖ (Drop* id m) ℓ) e , m , n) ∷ injVec ξ ℓ es


⊢inj
  : ∀{Γₑ Γ ξ Δₑ e tₑ ℓ} →
    TYREN C⅀ₖ ξ (injKndCtx Γₑ) Γ →
    Γ c⊢ₜ ℓ ∶ *ₗ →
    Γₑ ⨾ Δₑ e⊢ e ∶ tₑ →
    Γ ⨾ injCtx ξ ℓ Δₑ c⊢ inj ξ ℓ e ∶ LocalTyp ξ ℓ tₑ
⊢injVec
  : ∀{Γₑ Γ ξ Δₑ es Σₑ ℓ} →
    TYREN C⅀ₖ ξ (injKndCtx Γₑ) Γ →
    Γ c⊢ₜ ℓ ∶ *ₗ →
    Γₑ ⨾ Δₑ e⊢vec es ∶ Σₑ →
    Γ ⨾ injCtx ξ ℓ Δₑ c⊢vec injVec ξ ℓ es ∶ map (BinderFun Γ ℓ) (renBinders ⅀ₑₖ (projTyRen (injKndCtx Γₑ) Γ ξ) Σₑ)

⊢inj ⊢ξ ⊢ℓ (⊢var ⊢x) = ⊢var (⊢injVar ⊢ξ ⊢ℓ ⊢x)
⊢inj {Γₑ} {Γ} {ξ} {Δₑ} {ℓ = ℓ} ⊢ξ ⊢ℓ (⊢constr {ts = ts} {es = es} sₑ ⊢ts ⊢es) =
  let eq1 : TmSigₑ sₑ (projKndCtx Γ) (projTyVec (map isLocKnd Γ) (renTyVec C⅀ₖ ξ (injTyVec ts))) .snd .fst
            ≡ 𝕃 .⅀ₑ .TmSig sₑ Γₑ ts .snd .fst
      eq1 =
        (fst $ snd $ TmSigₑ sₑ (projKndCtx Γ) (projTyVec (map isLocKnd Γ) (renTyVec C⅀ₖ ξ (injTyVec ts))))
          ≡⟨ (cong (fst ∘ snd ∘ TmSigₑ sₑ (projKndCtx Γ)) $
                proj∘ren≗projRen∘projTyVec ⊢ξ (⊢injTyVec ⊢ts)) ⟩
        (fst $ snd $ TmSigₑ sₑ (projKndCtx Γ)
          (renTyVec ⅀ₑₖ (projTyRen (injKndCtx Γₑ) Γ ξ)
            (projTyVec (map isLocKnd (injKndCtx Γₑ)) (injTyVec ts))))
          ≡⟨ (cong (λ x → fst $ snd $ TmSigₑ sₑ (projKndCtx Γ)
                (renTyVec ⅀ₑₖ (projTyRen (injKndCtx Γₑ) Γ ξ)
                  (projTyVec x (injTyVec ts)))) $
              isLocKnd∘injKndCtx≡true Γₑ) ⟩
        (fst $ snd $ TmSigₑ sₑ (projKndCtx Γ)
          (renTyVec ⅀ₑₖ (projTyRen (injKndCtx Γₑ) Γ ξ)
            (projTyVec (replicate (length Γₑ) true) (injTyVec ts))))
          ≡⟨ (cong (λ x → fst $ snd $ TmSigₑ sₑ (projKndCtx Γ)
                (renTyVec ⅀ₑₖ (projTyRen (injKndCtx Γₑ) Γ ξ) x)) $
              proj∘injTyVec≗id (length Γₑ) ts) ⟩
        (fst $ snd $ TmSigₑ sₑ (projKndCtx Γ)
          (renTyVec ⅀ₑₖ (projTyRen (injKndCtx Γₑ) Γ ξ) ts))
          ≡⟨ cong fst $ ren-comm-TmSig-snd (𝕃 .⅀ₑ) sₑ
              (subst
                (λ x → TYREN ⅀ₑₖ (projTyRen (injKndCtx Γₑ) Γ ξ) x (projKndCtx Γ))
                (proj∘injKndCtx≗id Γₑ)
                (⊢projTyRen ⊢ξ))
              ⊢ts ⟩
        (fst $ snd $ TmSigₑ sₑ Γₑ ts) ∎
      eq2 : regainTy (map isLocKnd Γ)
              (injTy (snd $ snd $ TmSigₑ sₑ (projKndCtx Γ)
                (projTyVec (map isLocKnd Γ) (renTyVec C⅀ₖ ξ (injTyVec ts)))))
            ≡ renTy C⅀ₖ ξ (injTy (snd $ snd $ TmSigₑ sₑ Γₑ ts))
      eq2 =
        regainTy (map isLocKnd Γ) (injTy
          (snd $ snd $ TmSigₑ sₑ (projKndCtx Γ)
            (projTyVec (map isLocKnd Γ) (renTyVec C⅀ₖ ξ (injTyVec ts)))))
          ≡⟨ (cong (λ x → regainTy (map isLocKnd Γ) (injTy
                  (snd $ snd $ TmSigₑ sₑ (projKndCtx Γ) x))) $
              proj∘ren≗projRen∘projTyVec ⊢ξ (⊢injTyVec ⊢ts)) ⟩
        regainTy (map isLocKnd Γ) (injTy
          (snd $ snd $ TmSigₑ sₑ (projKndCtx Γ)
            (renTyVec ⅀ₑₖ (projTyRen (injKndCtx Γₑ) Γ ξ)
              (projTyVec (map isLocKnd (injKndCtx Γₑ)) (injTyVec ts)))))
          ≡⟨ (cong (λ x → regainTy (map isLocKnd Γ) (injTy
                (snd $ snd $ TmSigₑ sₑ (projKndCtx Γ)
                  (renTyVec ⅀ₑₖ (projTyRen (injKndCtx Γₑ) Γ ξ)
                    (projTyVec x (injTyVec ts)))))) $
              isLocKnd∘injKndCtx≡true Γₑ) ⟩
        regainTy (map isLocKnd Γ) (injTy
          (snd $ snd $ TmSigₑ sₑ (projKndCtx Γ)
            (renTyVec ⅀ₑₖ (projTyRen (injKndCtx Γₑ) Γ ξ)
              (projTyVec (replicate (length Γₑ) true) (injTyVec ts)))))
          ≡⟨ (cong (λ x → regainTy (map isLocKnd Γ) (injTy
                (snd $ snd $ TmSigₑ sₑ (projKndCtx Γ)
                  (renTyVec ⅀ₑₖ (projTyRen (injKndCtx Γₑ) Γ ξ) x)))) $
              proj∘injTyVec≗id (length Γₑ) ts) ⟩
        regainTy (map isLocKnd Γ) (injTy
          (snd $ snd $ TmSigₑ sₑ (projKndCtx Γ)
            (renTyVec ⅀ₑₖ (projTyRen (injKndCtx Γₑ) Γ ξ) ts)))
          ≡⟨ (cong (λ x → regainTy (map isLocKnd Γ) (injTy (snd x))) $
              ren-comm-TmSig-snd (𝕃 .⅀ₑ) sₑ
                  (subst
                    (λ x → TYREN ⅀ₑₖ (projTyRen (injKndCtx Γₑ) Γ ξ) x (projKndCtx Γ))
                    (proj∘injKndCtx≗id Γₑ)
                    (⊢projTyRen ⊢ξ))
                  ⊢ts) ⟩
        regainTy (map isLocKnd Γ) (injTy
          (renTy ⅀ₑₖ (projTyRen (injKndCtx Γₑ) Γ ξ)
            (snd $ snd $ TmSigₑ sₑ Γₑ ts)))
          ≡⟨ regain∘inj∘projRen≗ren∘regain∘inj {injKndCtx Γₑ} {Γ} {ξ}
                {snd $ snd $ TmSigₑ sₑ Γₑ ts}
                ⊢ξ
                (subst (λ x → wfTyp ⅀ₑₖ x (snd $ TmSigₑ sₑ Γₑ ts))
                    (sym $ proj∘injKndCtx≗id Γₑ)
                    (𝕃 .⅀ₑ .⊢TmSig-snd sₑ ⊢ts)) ⟩
        renTy C⅀ₖ ξ
          (regainTy (map isLocKnd (injKndCtx Γₑ))
            (injTy $ snd $ snd $ TmSigₑ sₑ Γₑ ts))
          ≡⟨ (cong (renTy C⅀ₖ ξ) $
                regainTyId $ ⊢injTy $ 𝕃 .⅀ₑ .⊢TmSig-snd sₑ ⊢ts) ⟩
        renTy C⅀ₖ ξ (injTy $ snd $ snd $ TmSigₑ sₑ Γₑ ts) ∎
      eq3 : map (BinderFun Γ ℓ)
              (renBinders ⅀ₑₖ (projTyRen (injKndCtx Γₑ) Γ ξ)
                (TmSigₑ sₑ Γₑ ts .fst)) ≡
            map (BinderFun Γ ℓ)
              (TmSigₑ sₑ (projKndCtx Γ)
                (projTyVec (map isLocKnd Γ) (renTyVec C⅀ₖ ξ (injTyVec ts))) .fst)
      eq3 =
        map (BinderFun Γ ℓ)
          (renBinders ⅀ₑₖ (projTyRen (injKndCtx Γₑ) Γ ξ)
            (TmSigₑ sₑ Γₑ ts .fst))
          ≡⟨ (cong (map (BinderFun Γ ℓ)) $
              sym $ ren-comm-TmSig-fst (𝕃 .⅀ₑ) sₑ
              (subst
                (λ x → TYREN ⅀ₑₖ (projTyRen (injKndCtx Γₑ) Γ ξ) x (projKndCtx Γ))
                (proj∘injKndCtx≗id Γₑ)
                (⊢projTyRen ⊢ξ))
              ⊢ts) ⟩
        map (BinderFun Γ ℓ)
          (fst $ TmSigₑ sₑ (projKndCtx Γ)
            (renTyVec ⅀ₑₖ (projTyRen (injKndCtx Γₑ) Γ ξ) ts))
          ≡⟨ (sym $ cong (λ x → map (BinderFun Γ ℓ)
                (fst $ TmSigₑ sₑ (projKndCtx Γ)
                  (renTyVec ⅀ₑₖ (projTyRen (injKndCtx Γₑ) Γ ξ) x))) $
              proj∘injTyVec≗id (length Γₑ) ts) ⟩
        map (BinderFun Γ ℓ)
          (fst $ TmSigₑ sₑ (projKndCtx Γ)
            (renTyVec ⅀ₑₖ (projTyRen (injKndCtx Γₑ) Γ ξ)
              (projTyVec (replicate (length Γₑ) true) (injTyVec ts))))
          ≡⟨ (sym $ cong (λ x → map (BinderFun Γ ℓ)
              (fst $ TmSigₑ sₑ (projKndCtx Γ)
                (renTyVec ⅀ₑₖ (projTyRen (injKndCtx Γₑ) Γ ξ)
                  (projTyVec x (injTyVec ts))))) $
              isLocKnd∘injKndCtx≡true Γₑ) ⟩
        map (BinderFun Γ ℓ)
          (fst $ TmSigₑ sₑ (projKndCtx Γ)
            (renTyVec ⅀ₑₖ (projTyRen (injKndCtx Γₑ) Γ ξ)
              (projTyVec (map isLocKnd (injKndCtx Γₑ)) (injTyVec ts))))
          ≡⟨ (sym $ cong (λ x → map (BinderFun Γ ℓ) (fst $ TmSigₑ sₑ (projKndCtx Γ) x)) $
             proj∘ren≗projRen∘projTyVec ⊢ξ (⊢injTyVec ⊢ts)) ⟩
        map (BinderFun Γ ℓ)
          (fst $ TmSigₑ sₑ (projKndCtx Γ)
            (projTyVec (map isLocKnd Γ) (renTyVec C⅀ₖ ξ (injTyVec ts)))) ∎
  in 
  subst
      (λ x → Γ ⨾ injCtx ξ ℓ Δₑ c⊢ constr (LocalTmS sₑ) ((ℓ , 0) ∷ renTyVec C⅀ₖ ξ (injTyVec ts)) (injVec ξ ℓ es) ∶ x)
      (cong₂ _,_ (cong Bnd eq1) (cong₂ (λ x y → Local x y ℓ) eq1 eq2))
      (⊢constr (LocalTmS sₑ)
        (⊢ℓ ⊢ₜ∷ ⊢renTyVec C⅀ₖ ⊢ξ (⊢injTyVec ⊢ts))
        (subst (Γ ⨾ injCtx ξ ℓ Δₑ c⊢vec injVec ξ ℓ es ∶_) eq3
          (⊢injVec ⊢ξ ⊢ℓ ⊢es)))

⊢injVec ⊢ξ ⊢ℓ (⊢[] ⊢Δ) = ⊢[] (⊢injCtx ⊢ξ ⊢ℓ ⊢Δ)  
⊢injVec {Γₑ} {Γ} {ξ} {Δₑ} {ℓ = ℓ} ⊢ξ ⊢ℓ (_⊢∷_ {e} {es} {Γₑ'} {Δₑ'} {κₑ , tₑ} ⊢e ⊢es) =
  let eq3 : length Δₑ' ≡
            length (map (TypFun Γ ℓ Γₑ')
              (map (renTyp ⅀ₑₖ
                    (Keep* (projTyRen (injKndCtx Γₑ) Γ ξ)
                      (length Γₑ')))
                  Δₑ'))
      eq3 =
        length Δₑ'
          ≡⟨ (sym $ length-map
                (renTyp ⅀ₑₖ
                (Keep* (projTyRen (injKndCtx Γₑ) Γ ξ)
                  (length Γₑ')))
                  Δₑ') ⟩
        length (map (renTyp ⅀ₑₖ
                (Keep* (projTyRen (injKndCtx Γₑ) Γ ξ)
                  (length Γₑ')))
              Δₑ')
          ≡⟨ (sym $ length-map (TypFun Γ ℓ Γₑ')
                (map (renTyp ⅀ₑₖ
                (Keep* (projTyRen (injKndCtx Γₑ) Γ ξ)
                  (length Γₑ')))
              Δₑ')) ⟩
        length (map (TypFun Γ ℓ Γₑ')
          (map (renTyp ⅀ₑₖ
                (Keep* (projTyRen (injKndCtx Γₑ) Γ ξ)
                  (length Γₑ')))
              Δₑ')) ∎
      ⊢tₑ' : ∀{tₑ κₑ} →
             (Γₑ' ++ Γₑ) e⊢ₜ tₑ ∶ κₑ →
             (Γₑ' ++ projKndCtx (injKndCtx Γₑ)) e⊢ₜ tₑ ∶ κₑ              
      ⊢tₑ' {tₑ} {κₑ} ⊢tₑ =
        subst (_e⊢ₜ tₑ ∶ κₑ)
          (cong (Γₑ' ++_) $ sym $ proj∘injKndCtx≗id Γₑ)
          ⊢tₑ
      ⊢tₑ'' : ∀{tₑ κₑ} →
              (Γₑ' ++ Γₑ) e⊢ₜ tₑ ∶ κₑ →
              projKndCtx (injKndCtx Γₑ' ++ injKndCtx Γₑ) e⊢ₜ tₑ ∶ κₑ
      ⊢tₑ'' {tₑ} {κₑ} ⊢tₑ =
        subst (_e⊢ₜ tₑ ∶ κₑ)
          (cong₂ _++_
            (sym $ proj∘injKndCtx≗id Γₑ')
            (sym $ proj∘injKndCtx≗id Γₑ)
            ∙ sym (projKndCtx-++ (injKndCtx Γₑ') (injKndCtx Γₑ))) 
          ⊢tₑ
      eq4 : ∀{tₑ κₑ} →
            (Γₑ' ++ Γₑ) e⊢ₜ tₑ ∶ κₑ →
            renTy C⅀ₖ (Keep* ξ (length Γₑ')) (injTy tₑ) ≡
            regainTy (replicate (length Γₑ') true ++ map isLocKnd Γ)
              (injTy (renTy ⅀ₑₖ
                (Keep* (projTyRen (injKndCtx Γₑ) Γ ξ) (length Γₑ'))
                tₑ))
      eq4 {tₑ} {κₑ} ⊢tₑ =
        renTy C⅀ₖ (Keep* ξ (length Γₑ')) (injTy tₑ)
          ≡⟨ (cong (λ x → renTy C⅀ₖ (Keep* ξ x) (injTy tₑ)) $
                sym $ length-map LocKnd Γₑ') ⟩
       renTy C⅀ₖ (Keep* ξ (length (injKndCtx Γₑ'))) (injTy tₑ)
          ≡⟨ (sym $ ⊢renTy-≗TyRen C⅀ₖ
                (Keep*-≗TyRen C⅀ₖ
                  (regain∘inj∘projTyRenVar≗id ⊢ξ)
                  (injKndCtx Γₑ'))
                (subst (_c⊢ₜ injTy tₑ ∶ LocKnd κₑ)
                  (injKndCtx-++ Γₑ' Γₑ) $
                  ⊢injTy ⊢tₑ)) ⟩
        renTy C⅀ₖ
          (Keep*
            (regainTyVar (map isLocKnd Γ)
              • injTyRen Γₑ (projKndCtx Γ)
                  (projTyRen (injKndCtx Γₑ) Γ ξ))
            (length (injKndCtx Γₑ')))
          (injTy tₑ)
          ≡⟨ (cong (λ x → 
                renTy C⅀ₖ
                  (Keep*
                    (regainTyVar (map isLocKnd Γ)
                      • injTyRen Γₑ (projKndCtx Γ)
                          (projTyRen (injKndCtx Γₑ) Γ ξ))
                    x)
                  (injTy tₑ)) $
            length-map LocKnd Γₑ') ⟩
        renTy C⅀ₖ
          (Keep*
            (regainTyVar (map isLocKnd Γ)
              • injTyRen Γₑ (projKndCtx Γ)
                  (projTyRen (injKndCtx Γₑ) Γ ξ))
            (length Γₑ'))
          (injTy tₑ)
          ≡⟨ (cong (λ x → 
                  renTy C⅀ₖ
                    (Keep*
                      (regainTyVar (map isLocKnd Γ)
                        • injTyRen x (projKndCtx Γ)
                            (projTyRen (injKndCtx Γₑ) Γ ξ))
                      (length Γₑ'))
                    (injTy tₑ)) $
                sym $ proj∘injKndCtx≗id Γₑ) ⟩
        renTy C⅀ₖ
          (Keep*
            (regainTyVar (map isLocKnd Γ)
              • injTyRen (projKndCtx (injKndCtx Γₑ)) (projKndCtx Γ)
                  (projTyRen (injKndCtx Γₑ) Γ ξ))
            (length Γₑ'))
          (injTy tₑ)
          ≡⟨ (sym $ renTy-ext C⅀ₖ
                (Keep*•Keep*
                  (regainTyVar (map isLocKnd Γ))
                  (injTyRen (projKndCtx (injKndCtx Γₑ)) (projKndCtx Γ)
                    (projTyRen (injKndCtx Γₑ) Γ ξ))
                    (length Γₑ'))
                (injTy tₑ)) ⟩
        renTy C⅀ₖ
          (Keep* (regainTyVar (map isLocKnd Γ)) (length Γₑ')
            • Keep*
                (injTyRen (projKndCtx (injKndCtx Γₑ)) (projKndCtx Γ)
                  (projTyRen (injKndCtx Γₑ) Γ ξ))
                (length Γₑ'))
          (injTy tₑ)                
          ≡⟨ (sym $ renTy• C⅀ₖ
                (Keep* (regainTyVar (map isLocKnd Γ)) (length Γₑ'))
                (Keep*
                  (injTyRen (projKndCtx (injKndCtx Γₑ)) (projKndCtx Γ)
                    (projTyRen (injKndCtx Γₑ) Γ ξ))
                  (length Γₑ'))
                (injTy tₑ)) ⟩
        renTy C⅀ₖ (Keep* (regainTyVar (map isLocKnd Γ)) (length Γₑ'))
          (renTy C⅀ₖ
            (Keep*
                (injTyRen (projKndCtx (injKndCtx Γₑ)) (projKndCtx Γ)
                  (projTyRen (injKndCtx Γₑ) Γ ξ))
                (length Γₑ'))
            (injTy tₑ))
          ≡⟨ renTy-ext C⅀ₖ
                (Keep*-regainTyVar (map isLocKnd Γ) (length Γₑ'))
                (renTy C⅀ₖ
                  (Keep*
                      (injTyRen (projKndCtx (injKndCtx Γₑ)) (projKndCtx Γ)
                        (projTyRen (injKndCtx Γₑ) Γ ξ))
                      (length Γₑ'))
                  (injTy tₑ)) ⟩
        renTy C⅀ₖ (regainTyVar (replicate (length Γₑ') true ++ map isLocKnd Γ))
          (renTy C⅀ₖ
            (Keep*
                (injTyRen (projKndCtx (injKndCtx Γₑ)) (projKndCtx Γ)
                  (projTyRen (injKndCtx Γₑ) Γ ξ))
                (length Γₑ'))
            (injTy tₑ))
          ≡⟨ (cong (regainTy (replicate (length Γₑ') true ++ map isLocKnd Γ)) $
              sym $ renTy-ext C⅀ₖ
                (Keep*-injTyRen
                  (projKndCtx (injKndCtx Γₑ))
                  (projKndCtx Γ)
                  (projTyRen (injKndCtx Γₑ) Γ ξ)
                  Γₑ')
                (injTy tₑ)) ⟩
        regainTy (replicate (length Γₑ') true ++ map isLocKnd Γ)
          (renTy C⅀ₖ
            (injTyRen (Γₑ' ++ projKndCtx (injKndCtx Γₑ))
              (Γₑ' ++ projKndCtx Γ)
              (Keep* (projTyRen (injKndCtx Γₑ) Γ ξ)
                (length Γₑ')))
            (injTy tₑ))
          ≡⟨ cong₂ (λ x y →
                  regainTy (replicate (length Γₑ') true ++ map isLocKnd Γ)
                    (renTy C⅀ₖ
                      (injTyRen (Γₑ' ++ projKndCtx (injKndCtx Γₑ))
                        x
                        (Keep* (projTyRen (injKndCtx Γₑ) Γ ξ)
                          y))
                      (injTy tₑ)))
                  (cong (_++ projKndCtx Γ) (sym $ proj∘injKndCtx≗id Γₑ')
                    ∙ sym (projKndCtx-++ (injKndCtx Γₑ') Γ))
                  (sym $ length-map LocKnd Γₑ') ⟩
        regainTy (replicate (length Γₑ') true ++ map isLocKnd Γ)
          (renTy C⅀ₖ
            (injTyRen (Γₑ' ++ projKndCtx (injKndCtx Γₑ))
              (projKndCtx (injKndCtx Γₑ' ++ Γ))
              (Keep* (projTyRen (injKndCtx Γₑ) Γ ξ)
                (length (injKndCtx Γₑ'))))
            (injTy tₑ))
          ≡⟨ (cong (regainTy (replicate (length Γₑ') true ++ map isLocKnd Γ)) $
                ⊢renTy-≗TyRen C⅀ₖ
                  (⊢injTyRen-ext
                    {Γ2 = projKndCtx (injKndCtx Γₑ' ++ Γ)}
                    (≗TyRen-sym ⅀ₑₖ (Keep*-projTyRen ⊢ξ Γₑ')))
                  (⊢injTy (⊢tₑ' ⊢tₑ))) ⟩
        regainTy (replicate (length Γₑ') true ++ map isLocKnd Γ)
          (renTy C⅀ₖ
            (injTyRen (Γₑ' ++ projKndCtx (injKndCtx Γₑ))
              (projKndCtx (injKndCtx Γₑ' ++ Γ))
              (projTyRen (injKndCtx Γₑ' ++ injKndCtx Γₑ) (injKndCtx Γₑ' ++ Γ)
                (Keep* ξ (length (injKndCtx Γₑ')))))
            (injTy tₑ))
          ≡⟨ (cong (λ x → 
                regainTy (replicate (length Γₑ') true ++ map isLocKnd Γ)
                  (renTy C⅀ₖ
                    (injTyRen x
                      (projKndCtx (injKndCtx Γₑ' ++ Γ))
                      (projTyRen (injKndCtx Γₑ' ++ injKndCtx Γₑ) (injKndCtx Γₑ' ++ Γ)
                        (Keep* ξ (length (injKndCtx Γₑ')))))
                    (injTy tₑ))) $
              cong (_++ projKndCtx (injKndCtx Γₑ)) (sym $ proj∘injKndCtx≗id Γₑ') 
                ∙ sym (projKndCtx-++ (injKndCtx Γₑ') (injKndCtx Γₑ))) ⟩
        regainTy (replicate (length Γₑ') true ++ map isLocKnd Γ)
          (renTy C⅀ₖ
            (injTyRen (projKndCtx (injKndCtx Γₑ' ++ injKndCtx Γₑ))
              (projKndCtx (injKndCtx Γₑ' ++ Γ))
              (projTyRen (injKndCtx Γₑ' ++ injKndCtx Γₑ) (injKndCtx Γₑ' ++ Γ)
                (Keep* ξ (length (injKndCtx Γₑ')))))
            (injTy tₑ))
          ≡⟨ (cong (regainTy (replicate (length Γₑ') true ++ map isLocKnd Γ)) $
                sym $ inj∘ren≗injRen∘injTy
                (⊢projTyRen (⊢TyKeep* C⅀ₖ ⊢ξ (injKndCtx Γₑ')))
                (⊢tₑ'' ⊢tₑ)) ⟩
        regainTy (replicate (length Γₑ') true ++ map isLocKnd Γ)
          (injTy (renTy ⅀ₑₖ
            (projTyRen
              (injKndCtx Γₑ' ++ injKndCtx Γₑ)
              (injKndCtx Γₑ' ++ Γ)
              (Keep* ξ (length (injKndCtx Γₑ'))))
            tₑ))
          ≡⟨ (cong (regainTy (replicate (length Γₑ') true ++ map isLocKnd Γ) ∘ injTy ) $
                 ⊢renTy-≗TyRen ⅀ₑₖ
                  (Keep*-projTyRen ⊢ξ Γₑ')
                  (⊢tₑ' ⊢tₑ)) ⟩
        regainTy (replicate (length Γₑ') true ++ map isLocKnd Γ)
          (injTy (renTy ⅀ₑₖ
            (Keep* (projTyRen (injKndCtx Γₑ) Γ ξ) (length (injKndCtx Γₑ')))
            tₑ))
          ≡⟨ (cong (λ x → regainTy (replicate (length Γₑ') true ++ map isLocKnd Γ)
                (injTy (renTy ⅀ₑₖ
                  (Keep* (projTyRen (injKndCtx Γₑ) Γ ξ) x)
                  tₑ))) $
                length-map LocKnd Γₑ') ⟩
        regainTy (replicate (length Γₑ') true ++ map isLocKnd Γ)
          (injTy (renTy ⅀ₑₖ
            (Keep* (projTyRen (injKndCtx Γₑ) Γ ξ) (length Γₑ'))
            tₑ)) ∎
      ⊢Δₑ' : (Γₑ' ++ Γₑ) e⊢ctx Δₑ'
      ⊢Δₑ' = ⊢ctx-++⁻ ⅀ₑₖ Δₑ'
              (renCtx (𝕃 .⅀ₑ .⅀ₖ) (Drop* id (length Γₑ')) Δₑ)
              (⊢⇒⊢ctx (𝕃 .⅀ₑ) ⊢e) .fst
      ⊢Δₑ : Γₑ e⊢ctx Δₑ
      ⊢Δₑ = ⊢renCtx⁻ ⅀ₑₖ (⊢TyDrop⁻* ⅀ₑₖ (⊢TyIdRen⁻ ⅀ₑₖ) Γₑ') $
              ⊢ctx-++⁻ ⅀ₑₖ Δₑ'
                (renCtx (𝕃 .⅀ₑ .⅀ₖ) (Drop* id (length Γₑ')) Δₑ)
                (⊢⇒⊢ctx (𝕃 .⅀ₑ) ⊢e) .snd              
      eq1 : map (LocalTyp (Keep* ξ (length Γₑ'))
                  (renTy C⅀ₖ (Drop* id (length Γₑ')) ℓ))
              (Δₑ' ++ renCtx ⅀ₑₖ (Drop* id (length Γₑ')) Δₑ)
            ≡ map (TypFun Γ ℓ Γₑ')
                (renCtx ⅀ₑₖ
                  (Keep* (projTyRen (injKndCtx Γₑ) Γ ξ) (length Γₑ'))
                  Δₑ')
              ++ renCtx C⅀ₖ
                  (Drop* id (length (injKndCtx Γₑ')))
                  (map (LocalTyp ξ ℓ) Δₑ)
      eq1 =
          map-++-commute
            ((LocalTyp (Keep* ξ (length Γₑ'))
              (renTy C⅀ₖ (Drop* id (length Γₑ')) ℓ)))
            Δₑ'
            (renCtx ⅀ₑₖ (Drop* id (length Γₑ')) Δₑ) ∙
            cong₂ _++_
              (map (LocalTyp (Keep* ξ (length Γₑ'))
                  (renTy C⅀ₖ (Drop* id (length Γₑ')) ℓ))
                Δₑ'
                ≡⟨ map-cong-AllElems (wfTyp ⅀ₑₖ (Γₑ' ++ Γₑ))
                    (λ{ (κₑ , tₑ) ⊢tₑ →
                      cong₂ (λ x y → Bnd κₑ ,
                            tyConstr (LocalS κₑ) ((x , 0) ∷ (y , 0) ∷ []))
                        (eq4 ⊢tₑ)
                        (cong (λ x → renTy C⅀ₖ (Drop* id x) ℓ) $
                            sym $ length-map LocKnd Γₑ') })
                    ⊢Δₑ' ⟩
              map
                (TypFun Γ ℓ Γₑ'
                  ∘ renTyp ⅀ₑₖ
                      (Keep* (projTyRen (injKndCtx Γₑ) Γ ξ) (length Γₑ')))
                Δₑ'
                ≡⟨ map-compose
                    {g = TypFun Γ ℓ Γₑ'}
                    {renTyp ⅀ₑₖ
                        (Keep* (projTyRen (injKndCtx Γₑ) Γ ξ) (length Γₑ'))}
                    Δₑ' ⟩
              map (TypFun Γ ℓ Γₑ')
                (renCtx ⅀ₑₖ
                  (Keep* (projTyRen (injKndCtx Γₑ) Γ ξ) (length Γₑ'))
                  Δₑ') ∎)
              (map (LocalTyp (Keep* ξ (length Γₑ'))
                  (renTy C⅀ₖ (Drop* id (length Γₑ')) ℓ))
                    (map (renTyp ⅀ₑₖ (Drop* id (length Γₑ'))) Δₑ)
                ≡⟨ (sym $ map-compose
                      {g = LocalTyp (Keep* ξ (length Γₑ'))
                        (renTy C⅀ₖ (Drop* id (length Γₑ')) ℓ)}
                      {renTyp ⅀ₑₖ (Drop* id (length Γₑ'))}
                      Δₑ) ⟩
              map (LocalTyp (Keep* ξ (length Γₑ'))
                    (renTy C⅀ₖ (Drop* id (length Γₑ')) ℓ)
                  ∘ renTyp ⅀ₑₖ (Drop* id (length Γₑ')))
                Δₑ
                ≡⟨ map-cong-AllElems (wfTyp ⅀ₑₖ Γₑ)
                    (λ{ (κₑ , tₑ) ⊢tₑ →
                      cong₂ (λ x y →
                            (Bnd κₑ ,
                              tyConstr (LocalS κₑ) ((x , 0) ∷ (y , 0) ∷ [])))
                          (renTy C⅀ₖ (Keep* ξ (length Γₑ'))
                            (injTy (renTy ⅀ₑₖ (Drop* id (length Γₑ')) tₑ))
                            ≡⟨ (cong (renTy C⅀ₖ (Keep* ξ (length Γₑ'))) $
                                  inj∘ren≗injRen∘injTy
                                  (⊢TyDrop* ⅀ₑₖ (⊢TyIdRen ⅀ₑₖ {Γₑ}) Γₑ')
                                  ⊢tₑ) ⟩
                          renTy C⅀ₖ (Keep* ξ (length Γₑ'))
                            (renTy C⅀ₖ (injTyRen Γₑ (Γₑ' ++ Γₑ) (Drop* id (length Γₑ'))) (injTy tₑ))
                            ≡⟨ (cong (renTy C⅀ₖ (Keep* ξ (length Γₑ'))) $
                                renTy-ext C⅀ₖ (Drop*-injTyRen Γₑ Γₑ id Γₑ') (injTy tₑ)) ⟩
                          renTy C⅀ₖ (Keep* ξ (length Γₑ'))
                            (renTy C⅀ₖ (Drop* (injTyRen Γₑ Γₑ id) (length Γₑ')) (injTy tₑ))
                            ≡⟨ (cong (renTy C⅀ₖ (Keep* ξ (length Γₑ'))) $
                                renTy-ext C⅀ₖ (Drop*-ext (injTyRenId Γₑ) (length Γₑ'))
                                  (injTy tₑ)) ⟩
                          renTy C⅀ₖ (Keep* ξ (length Γₑ'))
                            (renTy C⅀ₖ (Drop* id (length Γₑ')) (injTy tₑ))
                            ≡⟨ renTy• C⅀ₖ
                                  (Keep* ξ (length Γₑ'))
                                  (Drop* id (length Γₑ'))
                                  (injTy tₑ) ⟩
                          renTy C⅀ₖ
                            (Keep* ξ (length Γₑ')
                              • Drop* id (length Γₑ'))
                            (injTy tₑ)
                            ≡⟨ renTy-ext C⅀ₖ
                                  (Keep*•Drop* ξ id (length Γₑ'))
                                  (injTy tₑ) ⟩
                          renTy C⅀ₖ (Drop* ξ (length Γₑ')) (injTy tₑ)
                            ≡⟨ (sym $ renTy-ext C⅀ₖ
                                  (Drop*• id ξ (length Γₑ'))
                                  (injTy tₑ)) ⟩
                          renTy C⅀ₖ
                            (Drop* id (length Γₑ') • ξ)
                            (injTy tₑ)
                            ≡⟨ (sym $ cong (λ x → renTy C⅀ₖ (Drop* id x • ξ) (injTy tₑ)) $
                                  length-map LocKnd Γₑ') ⟩
                          renTy C⅀ₖ
                            (Drop* id (length (injKndCtx Γₑ')) • ξ)
                            (injTy tₑ)
                            ≡⟨ (sym $ renTy• C⅀ₖ
                                  (Drop* id (length (injKndCtx Γₑ')))
                                  ξ
                                  (injTy tₑ)) ⟩
                          renTy C⅀ₖ (Drop* id (length (injKndCtx Γₑ')))
                            (renTy C⅀ₖ ξ (injTy tₑ)) ∎)
                          (cong (λ x → renTy C⅀ₖ (Drop* id x) ℓ) $
                              sym $ length-map LocKnd Γₑ') })
                    ⊢Δₑ ⟩
              map (renTyp C⅀ₖ (Drop* id (length (injKndCtx Γₑ')))
                  ∘ LocalTyp ξ ℓ)
                Δₑ
                ≡⟨ map-compose
                    {g = renTyp C⅀ₖ (Drop* id (length (injKndCtx Γₑ')))}
                    {LocalTyp ξ ℓ}
                    Δₑ ⟩
              map
                (renTyp C⅀ₖ (Drop* id (length (injKndCtx Γₑ'))))
                (map (LocalTyp ξ ℓ) Δₑ) ∎)
  in ⊢∷' C⅀
  (⊢inj {Γₑ' ++ Γₑ} {injKndCtx Γₑ' ++ Γ}
      {Keep* ξ (length Γₑ')}
      {Δₑ' ++ renCtx ⅀ₑₖ (Drop* id (length Γₑ')) Δₑ}
      {e} {κₑ , tₑ} {renTy C⅀ₖ (Drop* id (length Γₑ')) ℓ}
      (subst₃ (TYREN C⅀ₖ)
        (cong (Keep* ξ) $ length-map LocKnd Γₑ')
        (sym $ injKndCtx-++ Γₑ' Γₑ)
        refl
        (⊢TyKeep* C⅀ₖ ⊢ξ (injKndCtx Γₑ')))
      (⊢renTy C⅀ₖ
        (subst (λ x → TYREN C⅀ₖ x Γ (injKndCtx Γₑ' ++ Γ))
          (cong (Drop* id) $ length-map LocKnd Γₑ') $
          ⊢TyDrop* C⅀ₖ (⊢TyIdRen C⅀ₖ) (injKndCtx Γₑ'))
        ⊢ℓ)
      ⊢e)
  (⊢injVec ⊢ξ ⊢ℓ ⊢es)
  refl
  eq1
  (sym $ length-map LocKnd Γₑ')
  eq3
  refl
  (cong₂ (λ x y → Bnd κₑ , Local κₑ x (renTy C⅀ₖ (Drop* id y) ℓ))
    (eq4 $ ⊢⇒⊢typ (𝕃 .⅀ₑ) ⊢e)
    (sym $ length-map LocKnd Γₑ'))
  refl
