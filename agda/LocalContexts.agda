{-# OPTIONS --safe #-}

open import Data.Empty
open import Data.Unit
open import Data.Nat renaming (_≟_ to ≡-dec-Nat) 
open import Data.Nat.Properties
open import Data.List
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function

open import Common
open import LocalLang
open import TypedLocalLang
open import Locations

module LocalContexts
  (L : Location)
  (E : Language L)
  (LE : LawfulLanguage L E)
  (TE : TypedLocalLanguage L E LE)
  where

open import Types L E LE TE
open import Choreographies L E LE TE
open import LocalRenamings L E LE TE
open import LocationRenamings L E LE TE
open import Renamings L E LE TE
open import LocationSubstitutions L E LE TE
open import LocationContexts L E LE TE
open Location L
open Language E
open LawfulLanguage LE
open TypedLocalLanguage TE


{-
  Local contexts are a finite list of variable bindings at a
  specified location and local type
-}
LocalCtx : Set
LocalCtx = List (Loc × Typₑ)

-- Infinite local contexts which map every local variable to a type
LocalCtxFun : Set
LocalCtxFun = Loc → ℕ → Typₑ

{-
  We can project to an infinite context for each location,
  arbitrarily mapping the type of any remaining variables.
-}
proj : LocalCtx → LocalCtxFun
proj [] ℓ n = Boolₑ
proj ((ℓ' , t) ∷ Δ) ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = λ{ zero → t
              ; (suc n) → proj Δ ℓ n }
... | no  _ = proj Δ ℓ

{-
  Local renaming used to make the variables in a local
  expression match with the projection of the given location.
-}
projₑ : LocalCtx → Loc → ℕ → ℕ
projₑ [] ℓ = idRen
projₑ ((ℓ' , t) ∷ Δ) ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = ↑ (projₑ Δ ℓ)
... | no  _ = projₑ Δ ℓ

-- Add a type to specified local context
_,,[_]_ : LocalCtx → Loc → Typₑ → LocalCtx
(Δ ,,[ ℓ ] t) = (ℓ , t) ∷ Δ

-- Add a type to specified infinite local context
_,,F[_]_ : LocalCtxFun → Loc → Typₑ → LocalCtxFun
(Δ ,,F[ ℓ' ] t) ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = λ{ zero → t
              ; (suc n) → Δ ℓ n }
... | no  _ = Δ ℓ

-- Adding a type respects extensional equality
,,[ℓ]Ext : ∀{Δ1 Δ2} → Δ1 ≈₂ Δ2 → ∀ ℓ t → Δ1 ,,F[ ℓ ] t ≈₂ Δ2 ,,F[ ℓ ] t
,,[ℓ]Ext Δ1≈Δ2 ℓ' t ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = λ{ zero → refl
              ; (suc n) → Δ1≈Δ2 ℓ n }
... | no  _ = Δ1≈Δ2 ℓ

-- Adding a type respects projection
,,[ℓ]Proj : ∀ Δ ℓ t → proj (Δ ,,[ ℓ ] t) ≈₂ proj Δ ,,F[ ℓ ] t
,,[ℓ]Proj Δ ℓ' t ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = λ{ zero → refl
              ; (suc n) → refl }
... | no  _ = λ n → refl

-- Renaming of locations in local contexts
renₗ-LocalCtx : LocalCtx → (ℕ → ℕ) → LocalCtx
renₗ-LocalCtx [] ξ = []
renₗ-LocalCtx ((ℓ , t) ∷ Δ) ξ = (renₗ-Loc ℓ ξ , t) ∷ (renₗ-LocalCtx Δ ξ)

-- Renaming respects extensional equality
renExtₗ-LocalCtx : ∀{ξ1 ξ2} → ξ1 ≈ ξ2 → ∀ Δ → renₗ-LocalCtx Δ ξ1 ≡ renₗ-LocalCtx Δ ξ2
renExtₗ-LocalCtx ξ1≈ξ2 [] = refl
renExtₗ-LocalCtx ξ1≈ξ2 ((ℓ , t) ∷ Δ) = cong₂ _∷_ (cong₂ _,_ (renExtₗ-Loc ξ1≈ξ2 ℓ) refl) (renExtₗ-LocalCtx ξ1≈ξ2 Δ)

-- Renaming respects the identity
renIdₗ-LocalCtx : ∀ Δ → renₗ-LocalCtx Δ idRen ≡ Δ
renIdₗ-LocalCtx [] = refl
renIdₗ-LocalCtx ((ℓ , t) ∷ Δ) = cong₂ _∷_ (cong₂ _,_ (renIdₗ-Loc ℓ) refl) (renIdₗ-LocalCtx Δ)

-- Renaming enjoys fusion
renFuseₗ-LocalCtx : ∀ ξ1 ξ2 Δ → renₗ-LocalCtx Δ (ξ1 ∘ ξ2) ≡ renₗ-LocalCtx (renₗ-LocalCtx Δ ξ2) ξ1
renFuseₗ-LocalCtx ξ1 ξ2 [] = refl
renFuseₗ-LocalCtx ξ1 ξ2 ((ℓ , t) ∷ Δ) = cong₂ _∷_ (cong₂ _,_ (renFuseₗ-Loc ξ2 ξ1 ℓ) refl) (renFuseₗ-LocalCtx ξ1 ξ2 Δ)

-- ↑ for location variables on local contexts
↑LocalCtx : LocalCtx → LocalCtx
↑LocalCtx Δ = renₗ-LocalCtx Δ suc

-- ↑ for infinite local contexts
↑LocalCtxFun : LocalCtxFun → LocalCtxFun
↑LocalCtxFun Δ (Var zero) = λ _ → Boolₑ
↑LocalCtxFun Δ (Var (suc x)) = Δ (Var x)
↑LocalCtxFun Δ (Lit L) = Δ (Lit L)

-- ↑LocalCtx respects projection
↑LocalCtxProj : ∀ Δ → proj (↑LocalCtx Δ) ≈₂ ↑LocalCtxFun (proj Δ)
↑LocalCtxProj [] (Var zero) n = refl
↑LocalCtxProj [] (Var (suc x)) n = refl
↑LocalCtxProj [] (Lit L) n = refl
↑LocalCtxProj ((Var x1 , t) ∷ Δ) (Var zero) n = ↑LocalCtxProj Δ (Var zero) n
↑LocalCtxProj ((Var x1 , t) ∷ Δ) (Var (suc x2)) with ≡-dec-Loc (Var (suc x2)) (Var (suc x1)) | ≡-dec-Loc (Var x2) (Var x1)
... | yes p | yes q = λ{ zero → refl
                       ; (suc n) → ↑LocalCtxProj Δ (Var (suc x2)) n }
... | yes p | no ¬q = ⊥-elim (¬q (cong Var (suc-injective (Varₗ-inj p))))
... | no ¬p | yes q = ⊥-elim (¬p (cong Var (cong suc (Varₗ-inj q))))
... | no ¬p | no ¬q = λ n → ↑LocalCtxProj Δ (Var (suc x2)) n
↑LocalCtxProj ((Var x , t) ∷ Δ) (Lit L) y = ↑LocalCtxProj Δ (Lit L) y
↑LocalCtxProj ((Lit L1 , t) ∷ Δ) (Var zero) y = ↑LocalCtxProj Δ (Var zero) y
↑LocalCtxProj ((Lit L1 , t) ∷ Δ) (Var (suc x2)) y = ↑LocalCtxProj Δ (Var (suc x2)) y
↑LocalCtxProj ((Lit L1 , t) ∷ Δ) (Lit L2) with ≡-dec-Loc (Lit L2) (Lit L1)
... | yes p = λ{ zero → refl
               ; (suc n) → ↑LocalCtxProj Δ (Lit L2) n }
... | no ¬p = λ{ zero → ↑LocalCtxProj Δ (Lit L2) zero
               ; (suc n) → ↑LocalCtxProj Δ (Lit L2) (suc n) }

-- ↑ distributes over renaming
↑renₗ-LocalCtx : ∀ Δ ξ → ↑LocalCtx (renₗ-LocalCtx Δ ξ) ≡ renₗ-LocalCtx (↑LocalCtx Δ) (↑ ξ)
↑renₗ-LocalCtx [] ξ = refl
↑renₗ-LocalCtx ((Var x , t) ∷ Δ) ξ = cong₂ _∷_ refl (↑renₗ-LocalCtx Δ ξ)
↑renₗ-LocalCtx ((Lit L , t) ∷ Δ) ξ = cong₂ _∷_ refl (↑renₗ-LocalCtx Δ ξ)

-- Projection respects injective renaming 
projRen : ∀{ξ} → Injective _≡_ _≡_ ξ → ∀ Δ ℓ → proj Δ ℓ ≈ proj (renₗ-LocalCtx Δ ξ) (renₗ-Loc ℓ ξ)
projRen ξ-inj [] ℓ n = refl
projRen {ξ} ξ-inj ((ℓ' , t) ∷ Δ) ℓ zero with ≡-dec-Loc ℓ ℓ' | ≡-dec-Loc (renₗ-Loc ℓ ξ) (renₗ-Loc ℓ' ξ)
... | yes refl | yes _ = refl
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | no ¬p    | yes q = ⊥-elim (¬p (renInjₗ-Loc ξ-inj q))
... | no _     | no _  = projRen ξ-inj Δ ℓ zero
projRen {ξ} ξ-inj ((ℓ' , t) ∷ Δ) ℓ (suc n) with ≡-dec-Loc ℓ ℓ' | ≡-dec-Loc (renₗ-Loc ℓ ξ) (renₗ-Loc ℓ' ξ)
... | yes refl | yes _ = projRen ξ-inj Δ ℓ n
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | no ¬p    | yes q = ⊥-elim (¬p (renInjₗ-Loc ξ-inj q))
... | no _     | no _  = projRen ξ-inj Δ ℓ (suc n)

-- Substitution of locations in local contexts
subₗ-LocalCtx : LocalCtx → (ℕ → Loc) → LocalCtx
subₗ-LocalCtx [] σ = []
subₗ-LocalCtx ((ℓ , t) ∷ Δ) σ = (subₗ-Loc ℓ σ , t) ∷ (subₗ-LocalCtx Δ σ)

-- Substitution respects extensional equality
subExtₗ-LocalCtx : ∀{σ1 σ2} → σ1 ≈ σ2 → ∀ Δ → subₗ-LocalCtx Δ σ1 ≡ subₗ-LocalCtx Δ σ2
subExtₗ-LocalCtx σ1≈σ2 [] = refl 
subExtₗ-LocalCtx σ1≈σ2 ((ℓ , t) ∷ Δ) = cong₂ _∷_ (cong₂ _,_ (subExtₗ-Loc σ1≈σ2 ℓ) refl) (subExtₗ-LocalCtx σ1≈σ2 Δ)

-- Substitution respects the identity
subIdₗ-LocalCtx : ∀ Δ → subₗ-LocalCtx Δ idSubₗ ≡ Δ
subIdₗ-LocalCtx [] = refl
subIdₗ-LocalCtx ((ℓ , t) ∷ Δ) = cong₂ _∷_ (cong₂ _,_ (subIdₗ-Loc ℓ) refl) (subIdₗ-LocalCtx Δ)

-- Substitution respects the inclusion
subιₗ-LocalCtx : ∀ ξ Δ → subₗ-LocalCtx Δ (ιₗ ξ) ≡ renₗ-LocalCtx Δ ξ
subιₗ-LocalCtx ξ [] = refl
subιₗ-LocalCtx ξ ((ℓ , t) ∷ Δ) = cong₂ _∷_ (cong₂ _,_ (subιₗ-Loc ξ ℓ) refl) (subιₗ-LocalCtx ξ Δ)


{-
  ξ changes Δ1 to Δ2 if for all locations ℓ,
  Δ1 ℓ ≈ Δ2 ℓ ∘ ξ ℓ
-}
_∶_⇒ₗₑ_ : LocalRen → LocalCtxFun → LocalCtxFun → Set
ξ ∶ Δ1 ⇒ₗₑ Δ2 = ∀ ℓ → Δ1 ℓ ≈ Δ2 ℓ ∘ ξ ℓ

{-
  For any local context Δ, location substitution σ, and location ℓ,
  there is a renaming ξ that changes the projection of Δ at ℓ
  into the projection of Δ⟨σ⟩ at ℓ⟨σ⟩
-}
locSubProj : ∀ Δ σ ℓ →
            Σ (ℕ → ℕ) λ ξ → 
            proj Δ ℓ ≈ proj (subₗ-LocalCtx Δ σ) (subₗ-Loc ℓ σ) ∘ ξ
locSubProj [] σ ℓ = idRen , λ n → refl
locSubProj ((ℓ' , t) ∷ Δ) σ ℓ with ≡-dec-Loc ℓ ℓ' | ≡-dec-Loc (subₗ-Loc ℓ σ) (subₗ-Loc ℓ' σ)
... | yes _ | yes _ = (λ{ zero → zero
                       ; (suc n) → suc (locSubProj Δ σ ℓ .fst n) }) ,
                      λ{ zero → refl
                      ; (suc n) → locSubProj Δ σ ℓ .snd n }
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | no ¬p | yes q = (λ n → suc (locSubProj Δ σ ℓ .fst n)) ,
                      λ n → locSubProj Δ σ ℓ .snd n
... | no _ | no _ = locSubProj Δ σ ℓ

-- Change of context respects extensional equality
Ext⇒ₗₑ : ∀{ξ Δ1 Δ1' Δ2 Δ2'} →
         Δ1 ≈₂ Δ1' → Δ2 ≈₂ Δ2' →
         ξ ∶ Δ1 ⇒ₗₑ Δ2 →
         ξ ∶ Δ1' ⇒ₗₑ Δ2'
Ext⇒ₗₑ {ξ} Δ1≈Δ1' Δ2≈Δ2' ξ⇒ ℓ n =
  sym (Δ1≈Δ1' ℓ n)
  ∙ ξ⇒ ℓ n
  ∙ Δ2≈Δ2' ℓ (ξ ℓ n)

-- Renaming that shifts all local variables in a context
suc⟦_⟧ : LocalCtx → LocalRen
suc⟦ [] ⟧ = idRenₗₑ
suc⟦ (ℓ' , t) ∷ Σ ⟧ ℓ n with ≡-dec-Loc ℓ ℓ'
... | yes _ = suc (suc⟦ Σ ⟧ ℓ n)
... | no  _ = suc⟦ Σ ⟧ ℓ n

-- suc⟦_⟧ correctly renames local contexts
proj-suc : ∀{Δ} Σ → suc⟦ Σ ⟧ ∶ proj Δ ⇒ₗₑ proj (Σ ++ Δ)
proj-suc [] ℓ n = refl
proj-suc {Δ} ((ℓ' , t) ∷ Σ) ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = proj-suc Σ ℓ
... | no _  = proj-suc Σ ℓ

-- ↑[ℓ] preserves context renamings
↑[ℓ]⇒ : ∀{ξ Δ1 Δ2} →
        ξ ∶ proj Δ1 ⇒ₗₑ proj Δ2 →
        ∀ ℓ t →
        (↑[ ℓ ] ξ) ∶ proj (Δ1 ,,[ ℓ ] t) ⇒ₗₑ proj (Δ2 ,,[ ℓ ] t)
↑[ℓ]⇒ ξ⇒ ℓ t ℓ' with ≡-dec-Loc ℓ' ℓ | ≡-dec-Loc ℓ ℓ'
... | yes _ | yes _ = λ{ zero → refl
                       ; (suc n) → ξ⇒ ℓ' n }
... | yes p | no ¬p = ⊥-elim (¬p (sym p))
... | no ¬p | yes p = ⊥-elim (¬p (sym p))
... | no  _ | no  _ = λ n → ξ⇒ ℓ' n

-- ↑ₗₑ preserves functional context renamings
↑ₗₑFun⇒ : ∀{ξ Δ1 Δ2} →
        ξ ∶ Δ1 ⇒ₗₑ Δ2 →
        (↑ₗₑ ξ) ∶ (↑LocalCtxFun Δ1) ⇒ₗₑ (↑LocalCtxFun Δ2)
↑ₗₑFun⇒ ξ⇒ (Var zero) n = refl
↑ₗₑFun⇒ ξ⇒ (Var (suc x)) n = ξ⇒ (Var x) n
↑ₗₑFun⇒ ξ⇒ (Lit L) n = ξ⇒ (Lit L) n

-- ↑ₗₑ preserves context renamings
↑ₗₑ⇒ : ∀ Δ1 Δ2 ξ →
        ξ ∶ proj Δ1 ⇒ₗₑ proj Δ2 →
        (↑ₗₑ ξ) ∶ proj (↑LocalCtx Δ1) ⇒ₗₑ proj (↑LocalCtx Δ2)
↑ₗₑ⇒ Δ1 Δ2 ξ ξ⇒ = ↑ξ∶⟦↑Δ1⟧⇒⟦↑Δ2⟧
  where
  ↑ξ∶↑⟦Δ1⟧⇒↑⟦Δ2⟧ : (↑ₗₑ ξ) ∶ (↑LocalCtxFun (proj Δ1)) ⇒ₗₑ (↑LocalCtxFun (proj Δ2))
  ↑ξ∶↑⟦Δ1⟧⇒↑⟦Δ2⟧ = ↑ₗₑFun⇒ ξ⇒

  ↑ξ∶⟦↑Δ1⟧⇒⟦↑Δ2⟧ : (↑ₗₑ ξ) ∶ proj (↑LocalCtx Δ1) ⇒ₗₑ proj (↑LocalCtx Δ2)
  ↑ξ∶⟦↑Δ1⟧⇒⟦↑Δ2⟧ = Ext⇒ₗₑ (≈₂-sym (↑LocalCtxProj Δ1)) (≈₂-sym (↑LocalCtxProj Δ2)) ↑ξ∶↑⟦Δ1⟧⇒↑⟦Δ2⟧

-- suc[ℓ] changes Δ to Δ,ℓ.t
suc[ℓ]⇒ : ∀ Δ ℓ t → ⟨ ℓ ∣ suc ∣ idRenₗₑ ⟩ ∶ proj Δ ⇒ₗₑ proj (Δ ,,[ ℓ ] t)
suc[ℓ]⇒ Δ ℓ' t ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = λ n → refl
... | no  _ = λ n → refl

-- the projection is unchanged by an injective location renaming
projRenInj : ∀ ξ Δ ℓ →
             Injective _≡_ _≡_ ξ →
             proj Δ ℓ ≈ proj (renₗ-LocalCtx Δ ξ) (renₗ-Loc ℓ ξ)
projRenInj ξ [] ℓ ξ-inj n = refl
projRenInj ξ ((ℓ' , t) ∷ Δ) ℓ ξ-inj with ≡-dec-Loc ℓ ℓ' | ≡-dec-Loc (renₗ-Loc ℓ ξ) (renₗ-Loc ℓ' ξ)
... | yes _ | yes _ =  λ{ zero → refl ; (suc n) → projRenInj ξ Δ ℓ ξ-inj n }
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | no ¬p | yes q = ⊥-elim (¬p (renInjₗ-Loc ξ-inj q))
... | no _ | no _ = projRenInj ξ Δ ℓ ξ-inj

-- The projecting local renaming is unchanged by an injective location renaming
projRenInjₑ : ∀ ξ Δ ℓ →
             Injective _≡_ _≡_ ξ →
             projₑ Δ ℓ ≈ projₑ (renₗ-LocalCtx Δ ξ) (renₗ-Loc ℓ ξ)
projRenInjₑ ξ [] ℓ ξ-inj n = refl
projRenInjₑ ξ ((ℓ' , t) ∷ Δ) ℓ ξ-inj with ≡-dec-Loc ℓ ℓ' | ≡-dec-Loc (renₗ-Loc ℓ ξ) (renₗ-Loc ℓ' ξ)
... | yes _ | yes _ =  λ{ zero → refl ; (suc n) → cong suc (projRenInjₑ ξ Δ ℓ ξ-inj n) }
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | no ¬p | yes q = ⊥-elim (¬p (renInjₗ-Loc ξ-inj q))
... | no _ | no _ = projRenInjₑ ξ Δ ℓ ξ-inj

-- Typing of local expressions is stable under injective renamings
tyProjₑ : ∀{t} ξ Δ ℓ e →
          Injective _≡_ _≡_ ξ →
          proj Δ ℓ ⊢ₑ renₑ e (projₑ Δ ℓ) ∶ t →
          proj (renₗ-LocalCtx Δ ξ) (renₗ-Loc ℓ ξ)
            ⊢ₑ renₑ e (projₑ (renₗ-LocalCtx Δ ξ) (renₗ-Loc ℓ ξ)) ∶ t
tyProjₑ {t} ξ Δ ℓ e ξ-inj e∶t = Δ⟨ξ⟩∣ℓ⟨ξ⟩⊢e⟨Δ⟨ξ⟩∣ℓ⟨ξ⟩⟩
  where
  Δ⟨ξ⟩∣ℓ⟨ξ⟩⊢e⟨Δ∣ℓ⟩ : proj (renₗ-LocalCtx Δ ξ) (renₗ-Loc ℓ ξ) ⊢ₑ renₑ e (projₑ Δ ℓ) ∶ t
  Δ⟨ξ⟩∣ℓ⟨ξ⟩⊢e⟨Δ∣ℓ⟩ = tyExtₑ (projRenInj ξ Δ ℓ ξ-inj) e∶t

  e⟨Δ∣ℓ⟩≡e⟨Δ⟨ξ⟩∣ℓ⟨ξ⟩⟩ : renₑ e (projₑ Δ ℓ) ≡ renₑ e (projₑ (renₗ-LocalCtx Δ ξ) (renₗ-Loc ℓ ξ))
  e⟨Δ∣ℓ⟩≡e⟨Δ⟨ξ⟩∣ℓ⟨ξ⟩⟩ = renExtₑ (projRenInjₑ ξ Δ ℓ ξ-inj) e
  
  Δ⟨ξ⟩∣ℓ⟨ξ⟩⊢e⟨Δ⟨ξ⟩∣ℓ⟨ξ⟩⟩ : proj (renₗ-LocalCtx Δ ξ) (renₗ-Loc ℓ ξ)
                       ⊢ₑ renₑ e (projₑ (renₗ-LocalCtx Δ ξ) (renₗ-Loc ℓ ξ)) ∶ t
  Δ⟨ξ⟩∣ℓ⟨ξ⟩⊢e⟨Δ⟨ξ⟩∣ℓ⟨ξ⟩⟩ =
    subst (λ x → proj (renₗ-LocalCtx Δ ξ) (renₗ-Loc ℓ ξ) ⊢ₑ x ∶ t)
      e⟨Δ∣ℓ⟩≡e⟨Δ⟨ξ⟩∣ℓ⟨ξ⟩⟩ Δ⟨ξ⟩∣ℓ⟨ξ⟩⊢e⟨Δ∣ℓ⟩

-- Order preserving embeddings between local contexts
data OPE : (Δ1 Δ2 : LocalCtx) → Set where
  ε : OPE [] []
  Keep : ∀{Δ1 Δ2} (ξ : OPE Δ1 Δ2) (ℓ : Loc) (t : Typₑ) → OPE ((ℓ , t) ∷ Δ1) ((ℓ , t) ∷ Δ2)
  Drop : ∀{Δ1 Δ2} (ξ : OPE Δ1 Δ2) (ℓ : Loc) (t : Typₑ) → OPE Δ1 ((ℓ , t) ∷ Δ2)

-- Interpret an OPE as a local variable renaming
renOPE : ∀{Δ1 Δ2} → OPE Δ1 Δ2 → LocalRen
renOPE ε = idRenₗₑ
renOPE (Keep ξ ℓ' t) ℓ = ↑[ ℓ' ] (renOPE ξ) ℓ
renOPE (Drop ξ ℓ' t) ℓ = suc[ ℓ' ] ℓ ∘ renOPE ξ ℓ

-- An OPE from Δ1 to Δ2 changes Δ1 to Δ2
renOPE⇒ : ∀{Δ1 Δ2} (ξ : OPE Δ1 Δ2) → renOPE ξ ∶ proj Δ1 ⇒ₗₑ proj Δ2
renOPE⇒ ε ℓ n = refl
renOPE⇒ (Keep ξ ℓ' t) ℓ with ≡-dec-Loc ℓ ℓ' | ≡-dec-Loc ℓ' ℓ
... | yes _ | yes _ = λ{ zero → refl ; (suc n) → renOPE⇒ ξ ℓ n }
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | no ¬p | yes refl = ⊥-elim (¬p refl)
... | no _ | no _ = renOPE⇒ ξ ℓ
renOPE⇒ (Drop ξ ℓ' t) ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = renOPE⇒ ξ ℓ
... | no _ = renOPE⇒ ξ ℓ

-- Identity embedding
idOPE : (Δ : LocalCtx) → OPE Δ Δ
idOPE [] = ε
idOPE ((ℓ , t) ∷ Δ) = Keep (idOPE Δ) ℓ t

-- The interpretation respects the identity
renIdOPE : (Δ : LocalCtx) → renOPE (idOPE Δ) ≈₂ idRenₗₑ
renIdOPE [] ℓ n = refl
renIdOPE ((ℓ' , t) ∷ Δ) ℓ with ≡-dec-Loc ℓ' ℓ
... | yes _ = λ{ zero → refl
               ; (suc n) → cong suc (renIdOPE Δ ℓ n) }
... | no  _ = λ n → renIdOPE Δ ℓ n

open import Relation.Binary.Reasoning.Setoid (≈-Setoid′ ℕ ℕ)

-- Local context projection and OPEs commute
renOPE∘proj : ∀{Δ1 Δ2} →
              (ξ : OPE Δ1 Δ2) →
              ∀ ℓ →
              renOPE ξ ℓ ∘ projₑ Δ1 ℓ ≈
              projₑ Δ2 ℓ ∘ renOPE ξ ℓ
renOPE∘proj ε ℓ n = refl
renOPE∘proj (Keep {Δ1} {Δ2} ξ ℓ' t) ℓ with ≡-dec-Loc ℓ ℓ' | ≡-dec-Loc ℓ' ℓ
... | yes _ | yes _ = begin
  ↑ (renOPE ξ ℓ) ∘ ↑ (projₑ Δ1 ℓ) ≈⟨ ≈-sym (↑Fuse (projₑ Δ1 ℓ) (renOPE ξ ℓ)) ⟩
  ↑ (renOPE ξ ℓ ∘ projₑ Δ1 ℓ)     ≈⟨ ↑Ext (renOPE∘proj ξ ℓ) ⟩
  ↑ (projₑ Δ2 ℓ ∘ renOPE ξ ℓ)     ≈⟨ ↑Fuse (renOPE ξ ℓ) (projₑ Δ2 ℓ) ⟩
  ↑ (projₑ Δ2 ℓ) ∘ ↑ (renOPE ξ ℓ) ∎
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | no ¬p | yes refl = ⊥-elim (¬p refl)
... | no _ | no _ = renOPE∘proj ξ ℓ
renOPE∘proj (Drop ξ ℓ' t) ℓ with ≡-dec-Loc ℓ ℓ' | ≡-dec-Loc ℓ' ℓ
... | yes _ | yes _ = ∘Ext suc suc _ _ ≈-refl (renOPE∘proj ξ ℓ)
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | no ¬p | yes refl = ⊥-elim (¬p refl)
... | no _ | no _ = renOPE∘proj ξ ℓ

-- Bind a location in an OPE
↑OPE : ∀{Δ1 Δ2} → OPE Δ1 Δ2 → OPE (↑LocalCtx Δ1) (↑LocalCtx Δ2)
↑OPE ε = ε
↑OPE (Keep ξ ℓ t) = Keep (↑OPE ξ) (renₗ-Loc ℓ suc) t 
↑OPE (Drop ξ ℓ t) = Drop (↑OPE ξ) (renₗ-Loc ℓ suc) t

renₗ-Loc-suc≡Var : ∀ ℓ x → renₗ-Loc ℓ suc ≡ Var (suc x) → ℓ ≡ Var x
renₗ-Loc-suc≡Var (Var y) x p = cong Var (suc-injective (Varₗ-inj p))

renₗ-Loc-suc≡Var0 : ∀ ℓ → renₗ-Loc ℓ suc ≡ Var 0 → ⊥
renₗ-Loc-suc≡Var0 (Var x) ()
renₗ-Loc-suc≡Var0 (Lit L) ()

renₗ-Loc≡Lit : ∀{ξ} ℓ L → renₗ-Loc ℓ ξ ≡ Lit L → ℓ ≡ Lit L
renₗ-Loc≡Lit (Lit L) .L refl = refl

-- Binding a location respects the interpretation of an OPE
renOPE↑ : ∀{Δ1 Δ2} (ξ : OPE Δ1 Δ2) →
          renOPE (↑OPE ξ) ≈₂ ↑ₗₑ (renOPE ξ)
renOPE↑ ε (Var zero) n = refl
renOPE↑ ε (Var (suc x)) n = refl
renOPE↑ ε (Lit L) n = refl
renOPE↑ (Keep ξ ℓ t) (Var zero) with ≡-dec-Loc (renₗ-Loc ℓ suc) (Var 0)
... | yes _ = λ{ zero → refl ; (suc n) → cong suc (renOPE↑ ξ (Var 0) n) }
... | no  _ = renOPE↑ ξ (Var 0)
renOPE↑ (Keep ξ ℓ t) (Var (suc x)) with ≡-dec-Loc ℓ (Var x) | ≡-dec-Loc (renₗ-Loc ℓ suc) (Var (suc x))
... | yes _    | yes _ = λ{ zero → refl ; (suc n) → cong suc (renOPE↑ ξ (Var (suc x)) n) }
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | no  ¬p   | yes q = ⊥-elim (¬p (renₗ-Loc-suc≡Var ℓ x q))
... | no  _    | no  _ = renOPE↑ ξ (Var (suc x))
renOPE↑ (Keep ξ ℓ t) (Lit L) with ≡-dec-Loc ℓ (Lit L) | ≡-dec-Loc (renₗ-Loc ℓ suc) (Lit L)
... | yes _    | yes _ = λ{ zero → refl ; (suc n) → cong suc (renOPE↑ ξ (Lit L) n) }
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | no  ¬p   | yes q = ⊥-elim (¬p (renₗ-Loc≡Lit ℓ L q))
... | no  _    | no  _ = renOPE↑ ξ (Lit L)
renOPE↑ (Drop ξ ℓ t) (Var zero) with ≡-dec-Loc (Var 0) (renₗ-Loc ℓ suc)
... | yes p = ⊥-elim (renₗ-Loc-suc≡Var0 ℓ (sym p))
... | no  _ = renOPE↑ ξ (Var 0)
renOPE↑ (Drop ξ ℓ t) (Var (suc x)) with ≡-dec-Loc (Var x) ℓ | ≡-dec-Loc (Var (suc x)) (renₗ-Loc ℓ suc)
... | yes _    | yes _ = λ n → cong suc (renOPE↑ ξ (Var (suc x)) n)
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | no ¬p    | yes q = ⊥-elim (¬p (sym (renₗ-Loc-suc≡Var ℓ x (sym q))))
... | no _     | no _ = renOPE↑ ξ (Var (suc x))
renOPE↑ (Drop ξ ℓ t) (Lit L) with ≡-dec-Loc (Lit L) ℓ | ≡-dec-Loc (Lit L) (renₗ-Loc ℓ suc)
... | yes _    | yes _ = λ n → cong suc (renOPE↑ ξ (Lit L) n)
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | no ¬p    | yes q = ⊥-elim (¬p (sym (renₗ-Loc≡Lit ℓ L (sym q))))
... | no _     | no _  = renOPE↑ ξ (Lit L)
