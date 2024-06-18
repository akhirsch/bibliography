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

module PolyPir.Dev
  -- Location values
  (Loc : Set)
  -- Locations should have decidable equality
  (≡-dec-Loc : DecidableEquality Loc)

  -- Local language
  (𝕃 : LocalLang Loc)
  where

open import PolyPir.ChorTypes Loc ≡-dec-Loc 𝕃
open import PolyPir.ChorTerms Loc ≡-dec-Loc 𝕃
open import PolyPir.TermOperations Loc ≡-dec-Loc 𝕃


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
    ⊢∷'
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
                {! ⊢ctx-++⁻ C⅀ₖ (map (TypFun Γ ℓ Γₑ') Δₑ')
                    (renCtx (C⅀ .⅀ₖ) (Drop* id (length (injKndCtx Γₑ'))) Δ)
                    (⊢⇒⊢ctx C⅀ ⊢e) .snd
                     !} -- ⊢⇒⊢ctx C⅀ ⊢e -- ⊢ctx-++⁻ C⅀ₖ
                ℓ) ⟩
{-
map (TypFun Γ ℓ Γₑ') Δₑ' ++
 renCtx (C⅀ .⅀ₖ) (Drop* id (length (injKndCtx Γₑ'))) Δ
-}
      projCtx (map isLocKnd (injKndCtx Γₑ' ++ Γ))
        (renTy C⅀ₖ (Drop* id (length (injKndCtx Γₑ'))) ℓ)
        (map (TypFun Γ ℓ Γₑ') Δₑ')
      ++ renCtx ⅀ₑₖ
        (projTyRen Γ (injKndCtx Γₑ' ++ Γ)
          (Drop* id (length (map LocKnd Γₑ'))))
        (projCtx (map isLocKnd Γ) ℓ Δ)
        ≡⟨ {!   !} ⟩
{-
cong (projCtx (map isLocKnd (injKndCtx Γₑ' ++ Γ))
                  (renTy C⅀ₖ (Drop* id (length (injKndCtx Γₑ'))) ℓ)
                  (map (TypFun Γ ℓ Γₑ') Δₑ')
                ++_)
              ((proj∘ren≗projRen∘projCtx
                (Drop*-inj (λ p → p) (length (injKndCtx Γₑ')))
                (⊢TyDrop* C⅀ₖ (⊢TyIdRen C⅀ₖ) (injKndCtx Γₑ'))
                {!   !}))

_Γ1_446 = Γ
_ℓ_450 = ℓ
_Δ_449 = Δ

proj∘ren≗projRen∘projCtx
                ?
                (⊢TyDrop* C⅀ₖ (⊢TyIdRen C⅀ₖ) (injKndCtx Γₑ'))
                ?
              

proj∘ren≗projRen∘projCtx
                ?
                (⊢TyDrop* C⅀ₖ ? (injKndCtx Γₑ'))
                ?
-}
      Δₑ' ++ renCtx (𝕃 .⅀ₑ .⅀ₖ) (Drop* id (length Γₑ')) (projCtx (map isLocKnd Γ) ℓ Δ) ∎)
      (length-map LocKnd Γₑ')
      (length-map (TypFun Γ ℓ Γₑ') Δₑ')
      refl
      {!   !}
      {!   !}
    -- subst₂ (λ x y →
    --   projKndCtx Γ ⨾ projCtx Γ ℓ Δ
    --   e⊢vec projVec (map isLocKnd Γ) (map (?isLocalTy ℓ) Δ)
    --         ((e , x , y) ∷ es)
    --     ∶ ((Γₑ' , Δₑ' , κₑ , tₑ) ∷ Σₑ))
    --   (sym $ length-map LocKnd Γₑ')
    --   (sym $ length-map (TypFun Γ ℓ Γₑ') Δₑ')
    --   ({!  !} ⊢∷ ⊢projVec ℓ ⊢es)

{-
? : Γₑ' ++ projKndCtx Γ ⨾ Δₑ' ++ renCtx (𝕃 .⅀ₑ .⅀ₖ) (Drop* id (length Γₑ')) (projCtx Γ ℓ Δ)
    ⊢ₑ proj (replicate (length Γₑ') true ++ map isLocKnd Γ)
        (replicate (length Δₑ') true ++ map (?isLocalTy ℓ) Δ) e
    ∶ (κₑ , tₑ)

⊢proj (renTy C⅀ₖ (Drop* id (length (injKndCtx Γₑ'))) ℓ) ⊢e 
  : projKndCtx (injKndCtx Γₑ' ++ Γ)
    ⨾ projCtx (injKndCtx Γₑ' ++ Γ)
        (renTy C⅀ₖ (Drop* id (length (injKndCtx Γₑ'))) ℓ)
        (map (TypFun Γ ℓ Γₑ') Δₑ' ++ renCtx (C⅀ .⅀ₖ) (Drop* id (length (injKndCtx Γₑ'))) Δ)
    e⊢ proj (map isLocKnd (injKndCtx Γₑ' ++ Γ))
        (map (?isLocalTy (renTy C⅀ₖ (Drop* id (length (injKndCtx Γₑ'))) ℓ))
          (map (TypFun Γ ℓ Γₑ') Δₑ'
            ++ renCtx (C⅀ .⅀ₖ) (Drop* id (length (injKndCtx Γₑ'))) Δ))
        e
    ∶ (κₑ ,
        projTy (map isLocKnd (injKndCtx Γₑ' ++ Γ))
          (regainTy (replicate (length Γₑ') true ++ map isLocKnd Γ)
            (injTy tₑ)))
-} 