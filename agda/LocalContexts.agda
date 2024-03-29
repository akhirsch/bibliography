{-# OPTIONS --safe #-}

open import Level using (Lift; lift)
open import Data.Empty
open import Data.Unit
open import Data.Maybe
open import Data.Maybe.Properties
open import Data.Nat renaming (_≟_ to ≡-dec-Nat) 
open import Data.Nat.Properties
open import Data.List hiding (map)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map)
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
  Local contexts are a finite list of variable bindings of a
  specified location and local type
-}
LocalCtx : Set
LocalCtx = List (Loc × Typₑ)

-- Infinite local contexts which map every local variable to a type
LocalCtxFun : Set
LocalCtxFun = Loc → ℕ → Typₑ

-- Renaming of locations in local contexts
renₗ-LocalCtx : LocalCtx → (ℕ → ℕ) → LocalCtx
renₗ-LocalCtx [] ξ = []
renₗ-LocalCtx ((ℓ , t) ∷ Δ) ξ = (renₗ-Loc ℓ ξ , t) ∷ (renₗ-LocalCtx Δ ξ)

{-
  The projection Δ ∣ ℓ of a local context Δ at a given location ℓ,
  arbitrarily mapping the type of any remaining variables.

  E.g.
  [x0:ℓ0.Bool, x1:L.ℕ, x2:ℓ0:ℕ] ∣ ℓ0 = [x0:Bool, x1:ℕ]
  [x0:ℓ0.Bool, x1:L.ℕ, x2:ℓ0:ℕ] ∣ L  = [x0:ℕ]
-}
proj : LocalCtx → LocalCtxFun
proj [] ℓ n = Boolₑ
proj ((ℓ' , t) ∷ Δ) ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = λ{ zero → t
              ; (suc n) → proj Δ ℓ n }
... | no  _ = proj Δ ℓ

_∣_ = proj

{-
  Renaming Δ ⦊ ℓ used to change the variables in a local expression
  that uses variables from Δ to match with the projected context Δ ∣ ℓ.
  That is, if Δ ∣ ℓ ⊢ₑ e⟨Δ ⦊ ℓ⟩ ∶ t then Δ ⊢ ℓ.e ∶ t @ ℓ.
  This function is undefined when a local variable is not in the projection.

  E.g.
  [x0:ℓ0.Bool, x1:L.ℕ, x2:ℓ0:ℕ] ⦊ ℓ0 = ⟨x0 ↦ x0, x1 ↦ ⊥, x2 ↦ x1⟩
  (ITE x0 x2 (x2 + 1))⟨x0 ↦ x0, x1 ↦ ⊥, x2 ↦ x1⟩ = ITE x0 x1 (x1 + 1)
  [x0:ℓ0.Bool, x1:L.ℕ, x2:ℓ0:ℕ] ∣ ℓ0 = [x0:Bool, x1:ℕ]
  [x0:Bool, x1:ℕ] ⊢ ITE x0 x1 (x1 + 1) : ℕ
  [x0:ℓ0.Bool, x1:L.ℕ, x2:ℓ0:ℕ] ⊢ ℓ0.(ITE x0 x2 (x2 + 1)) : ℕ @ ℓ0

  [x0:ℓ0.Bool, x1:L.ℕ, x2:ℓ0:ℕ] ⦊ L = ⟨x0 ↦ ⊥, x1 ↦ x0, x2 ↦ ⊥⟩
  (x1 + x1)⟨x0 ↦ ⊥, x1 ↦ x0, x2 ↦ ⊥⟩ = x0 + x0
  [x0:ℓ0.Bool, x1:L.ℕ, x2:ℓ0:ℕ] ∣ L = [x0:ℕ]
  [x0:ℕ] ⊢ x0 + x0 : ℕ
  [x0:ℓ0.Bool, x1:L.ℕ, x2:ℓ0:ℕ] ⊢ L.(x1 + x1) : ℕ @ L

  [x0:ℓ0.Bool, x1:L.ℕ, x2:ℓ0:ℕ] ⦊ ℓ0 = ⟨x0 ↦ x0, x1 ↦ ⊥, x2 ↦ x1⟩
  (ITE x0 x1 x2)⟨x0 ↦ x0, x1 ↦ ⊥, x2 ↦ x1⟩ = ⊥
  [x0:ℓ0.Bool, x1:L.ℕ, x2:ℓ0:ℕ] ⊬ L.(ITE x0 x1 x2) : ℕ @ L
-}
projVars : LocalCtx → Loc → ℕ → Maybe ℕ
projVars [] ℓ n = just n
projVars ((ℓ' , t) ∷ Δ) ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = λ{ zero → just zero ; (suc n) → map suc (projVars Δ ℓ n) }
... | no  _ = λ{ zero → nothing ; (suc n) → projVars Δ ℓ n }

_⦊_ = projVars

-- Determines whether the projection renaming is defined at a given variable
projVarsDef : LocalCtx → Loc → ℕ → Set
projVarsDef [] ℓ n = ⊤
projVarsDef ((ℓ' , t) ∷ Δ) ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = λ{ zero → ⊤ ; (suc n) → projVarsDef Δ ℓ n }
... | no  _ = λ{ zero → ⊥ ; (suc n) → projVarsDef Δ ℓ n }

_⦊↓_ = projVarsDef

-- Projection renaming is a total function on the defined domain
projVarsJust : (Δ : LocalCtx) (ℓ : Loc) (n : ℕ) →
               (Δ ⦊↓ ℓ) n → ↓ ((Δ ⦊ ℓ) n)
projVarsJust [] ℓ' n tt = n , refl
projVarsJust ((ℓ' , t) ∷ Δ) ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = λ{ zero tt → zero , refl ; (suc n) ⦊↓n → suc (projVarsJust Δ ℓ n ⦊↓n .fst) , cong (map suc) (projVarsJust Δ ℓ n ⦊↓n .snd) }
... | no  _ = λ{ zero () ; (suc n) ⦊↓n → projVarsJust Δ ℓ n ⦊↓n }

-- ⦊↓ exactly computes the defined domain of ⦊
justProjVars : (Δ : LocalCtx) (ℓ : Loc) (n : ℕ) →
                ↓ ((Δ ⦊ ℓ) n) → (Δ ⦊↓ ℓ) n
justProjVars [] ℓ n (m , p) = tt
justProjVars ((ℓ' , t) ∷ Δ) ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = λ{ zero (m , eq) → tt
              ; (suc n) (zero , eq) → ⊥-elim (1+n≢0 (Maybe-map-just suc (projVars Δ ℓ n) zero eq .snd .fst))
              ; (suc n) (suc m , eq) → justProjVars Δ ℓ n (m ,
                     Maybe-map-just suc (projVars Δ ℓ n) (suc m) eq .snd .snd
                     ∙ cong just (suc-injective (Maybe-map-just suc (projVars Δ ℓ n) (suc m) eq .snd .fst))) }
... | no  _ = λ{ zero (m , ()) ; (suc n) (m , eq) → justProjVars Δ ℓ n (m , eq) }

-- Add a type to specified infinite local context
_,,[_]_ : LocalCtxFun → Loc → Typₑ → LocalCtxFun
(Δ ,,[ ℓ' ] t) ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = λ{ zero → t
              ; (suc n) → Δ ℓ n }
... | no  _ = Δ ℓ

-- Adding a local type to the context respects extensional equality
,,[ℓ]Ext : ∀{Δ1 Δ2} → Δ1 ≈₂ Δ2 → ∀ ℓ t → Δ1 ,,[ ℓ ] t ≈₂ Δ2 ,,[ ℓ ] t
,,[ℓ]Ext Δ1≈Δ2 ℓ' t ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = λ{ zero → refl
              ; (suc n) → Δ1≈Δ2 ℓ n }
... | no  _ = Δ1≈Δ2 ℓ

-- Adding a local type to the context respects projection
,,[ℓ]Proj : ∀ Δ ℓ t → proj ((ℓ , t) ∷ Δ) ≈₂ proj Δ ,,[ ℓ ] t
,,[ℓ]Proj Δ ℓ' t ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = λ{ zero → refl
              ; (suc n) → refl }
... | no  _ = λ n → refl

-- The projection of a context is unchanged by injective location renaming
projInj : ∀ ξ Δ ℓ →
             Injective _≡_ _≡_ ξ →
             Δ ∣ ℓ ≈ renₗ-LocalCtx Δ ξ ∣ renₗ-Loc ℓ ξ
projInj ξ [] ℓ ξ-inj n = refl
projInj ξ ((ℓ' , t) ∷ Δ) ℓ ξ-inj with ≡-dec-Loc ℓ ℓ' | ≡-dec-Loc (renₗ-Loc ℓ ξ) (renₗ-Loc ℓ' ξ)
... | yes _ | yes _ =  λ{ zero → refl
                       ; (suc n) → projInj ξ Δ ℓ ξ-inj n }
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | no ¬p | yes q = ⊥-elim (¬p (renInjₗ-Loc ξ-inj q))
... | no _ | no _ = projInj ξ Δ ℓ ξ-inj

-- The projecting renaming is unchanged by an injective location renaming
projVarsInj : ∀ ξ Δ ℓ →
             Injective _≡_ _≡_ ξ →
             Δ ⦊ ℓ ≈ renₗ-LocalCtx Δ ξ ⦊ renₗ-Loc ℓ ξ
projVarsInj ξ [] ℓ ξ-inj n = refl
projVarsInj ξ ((ℓ' , t) ∷ Δ) ℓ ξ-inj with ≡-dec-Loc ℓ ℓ' | ≡-dec-Loc (renₗ-Loc ℓ ξ) (renₗ-Loc ℓ' ξ)
... | yes _ | yes _ = λ{ zero → refl
                       ; (suc n) → cong (map suc) (projVarsInj ξ Δ ℓ ξ-inj n) }
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | no ¬p | yes q = ⊥-elim (¬p (renInjₗ-Loc ξ-inj q))
... | no _ | no _ = λ{ zero → refl
                    ; (suc n) → projVarsInj ξ Δ ℓ ξ-inj n }

-- Definedness of local projection is preserved under injective location renamings
projVarsDefInj : ∀{ξ} (Δ : LocalCtx) (ℓ : Loc) →
          Injective _≡_ _≡_ ξ →
          (n : ℕ) →
          (Δ ⦊↓ ℓ) n →
          (renₗ-LocalCtx Δ ξ ⦊↓ renₗ-Loc ℓ ξ) n
projVarsDefInj [] ℓ ξ-inj n tt = tt
projVarsDefInj {ξ} ((ℓ' , t) ∷ Δ) ℓ ξ-inj with ≡-dec-Loc ℓ ℓ' | ≡-dec-Loc (renₗ-Loc ℓ ξ) (renₗ-Loc ℓ' ξ)
... | yes _    | yes _ = λ{ zero tt → tt ; (suc n) ⦊↓n → projVarsDefInj Δ ℓ ξ-inj n ⦊↓n }
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | no ¬p    | yes q = ⊥-elim (¬p (renInjₗ-Loc ξ-inj q))
... | no  _    | no  _ = λ{ zero () ; (suc n) ⦊↓n → projVarsDefInj Δ ℓ ξ-inj n ⦊↓n }

-- Definedness of local projection is reflected under injective location renamings
projVarsDefInj⁻ : ∀{ξ} (Δ : LocalCtx) (ℓ : Loc) →
          Injective _≡_ _≡_ ξ →
          (n : ℕ) →
          (renₗ-LocalCtx Δ ξ ⦊↓ renₗ-Loc ℓ ξ) n →
          (Δ ⦊↓ ℓ) n
projVarsDefInj⁻ [] ℓ ξ-inj n tt = tt
projVarsDefInj⁻ {ξ} ((ℓ' , t) ∷ Δ) ℓ ξ-inj with ≡-dec-Loc ℓ ℓ' | ≡-dec-Loc (renₗ-Loc ℓ ξ) (renₗ-Loc ℓ' ξ)
... | yes _    | yes _ = λ{ zero tt → tt ; (suc n) ⦊↓n → projVarsDefInj⁻ Δ ℓ ξ-inj n ⦊↓n }
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | no ¬p    | yes q = ⊥-elim (¬p (renInjₗ-Loc ξ-inj q))
... | no  _    | no  _ = λ{ zero () ; (suc n) ⦊↓n → projVarsDefInj⁻ Δ ℓ ξ-inj n ⦊↓n }

-- Typing of local expressions is preserved under injective location renamings
tyProjRen : ∀{t} ξ Δ ℓ e →
            Injective _≡_ _≡_ ξ →
            (Δ ∣ ℓ) ⊢ₑ renMaybeₑ e (Δ ⦊ ℓ) ?∶ t →
            (renₗ-LocalCtx Δ ξ ∣ renₗ-Loc ℓ ξ)
              ⊢ₑ renMaybeₑ e (renₗ-LocalCtx Δ ξ ⦊ renₗ-Loc ℓ ξ) ?∶ t
tyProjRen {t} ξ Δ ℓ e ξ-inj (e' , e⟨Δ⦊ℓ⟩≡e' , e'∶t) = e' , sym e⟨Δ⦊ℓ⟩≡e⟨Δ⟨ξ⟩⦊ℓ⟨ξ⟩⟩ ∙ e⟨Δ⦊ℓ⟩≡e' , Δ⟨ξ⟩∣ℓ⟨ξ⟩⊢e'∶t
  where
  Δ⟨ξ⟩∣ℓ⟨ξ⟩⊢e'∶t : (renₗ-LocalCtx Δ ξ ∣ renₗ-Loc ℓ ξ) ⊢ₑ e' ∶ t
  Δ⟨ξ⟩∣ℓ⟨ξ⟩⊢e'∶t = tyExtₑ (projInj ξ Δ ℓ ξ-inj) e'∶t
  
  e⟨Δ⦊ℓ⟩≡e⟨Δ⟨ξ⟩⦊ℓ⟨ξ⟩⟩ : renMaybeₑ e (Δ ⦊ ℓ) ≡ renMaybeₑ e (renₗ-LocalCtx Δ ξ ⦊ renₗ-Loc ℓ ξ)
  e⟨Δ⦊ℓ⟩≡e⟨Δ⟨ξ⟩⦊ℓ⟨ξ⟩⟩ = renMaybeExtₑ (projVarsInj ξ Δ ℓ ξ-inj) e

-- Renaming locations respects extensional equality
renExtₗ-LocalCtx : ∀{ξ1 ξ2} → ξ1 ≈ ξ2 → ∀ Δ → renₗ-LocalCtx Δ ξ1 ≡ renₗ-LocalCtx Δ ξ2
renExtₗ-LocalCtx ξ1≈ξ2 [] = refl
renExtₗ-LocalCtx ξ1≈ξ2 ((ℓ , t) ∷ Δ) = cong₂ _∷_ (cong₂ _,_ (renExtₗ-Loc ξ1≈ξ2 ℓ) refl) (renExtₗ-LocalCtx ξ1≈ξ2 Δ)

-- Renaming locations respects the identity
renIdₗ-LocalCtx : ∀ Δ → renₗ-LocalCtx Δ idRen ≡ Δ
renIdₗ-LocalCtx [] = refl
renIdₗ-LocalCtx ((ℓ , t) ∷ Δ) = cong₂ _∷_ (cong₂ _,_ (renIdₗ-Loc ℓ) refl) (renIdₗ-LocalCtx Δ)

-- Renaming locations enjoys fusion
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

-- ↑ distributes over location renaming
↑renₗ-LocalCtx : ∀ Δ ξ → ↑LocalCtx (renₗ-LocalCtx Δ ξ) ≡ renₗ-LocalCtx (↑LocalCtx Δ) (↑ ξ)
↑renₗ-LocalCtx [] ξ = refl
↑renₗ-LocalCtx ((Var x , t) ∷ Δ) ξ = cong₂ _∷_ refl (↑renₗ-LocalCtx Δ ξ)
↑renₗ-LocalCtx ((Lit L , t) ∷ Δ) ξ = cong₂ _∷_ refl (↑renₗ-LocalCtx Δ ξ)

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
  For any local context Δ, location substitution σ, and location ℓ,
  there is a substitution renaming ξ that changes Δ ∣ ℓ into Δ⟨σ⟩ ∣ ℓ⟨σ⟩.
  Essentially, we need to determine which NEW local variables are added
  into a given location's context by the substitution.

  E.g.
  Δ = [x0:ℓ.t1, x1:L1.t2, x2:L2.t3, x3:ℓ.t4]
  σ = ⟨ℓ ↦ L2⟩
  ℓ = ℓ

  Δ∣ℓ = [x0:t1, x1:t4]
  Δ⟨σ⟩ = [x0:L2.t1, x1:L1.t2, x2:L2.t3, x3:L2.t4]
  ℓ⟨σ⟩ = L2
  Δ⟨σ⟩∣ℓ⟨σ⟩ = [x0:t1, x1:t3, x2:t4]

  The renaming for this substitution is ξ = ⟨x0 ↦ x0, x1 ↦ x2⟩
-}
locSubProj : (Δ : LocalCtx) (σ : ℕ → Loc) (ℓ : Loc) → ℕ → ℕ
locSubProj [] σ ℓ = idRen
locSubProj ((ℓ' , t) ∷ Δ) σ ℓ with ≡-dec-Loc ℓ ℓ' | ≡-dec-Loc (subₗ-Loc ℓ σ) (subₗ-Loc ℓ' σ)
... | yes _    | yes _ = ↑ (locSubProj Δ σ ℓ)
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | no ¬p    | yes q = suc ∘ locSubProj Δ σ ℓ
... | no  _    | no  _ = locSubProj Δ σ ℓ

-- The substitution renaming changes Δ ∣ ℓ into Δ⟨σ⟩ ∣ ℓ⟨σ⟩
locSubProj⇒ : ∀ Δ σ ℓ →
              Δ ∣ ℓ ≈ (subₗ-LocalCtx Δ σ ∣ subₗ-Loc ℓ σ) ∘ locSubProj Δ σ ℓ
locSubProj⇒ [] σ ℓ n = refl
locSubProj⇒ ((ℓ' , t) ∷ Δ) σ ℓ with ≡-dec-Loc ℓ ℓ' | ≡-dec-Loc (subₗ-Loc ℓ σ) (subₗ-Loc ℓ' σ)
... | yes _    | yes _ = λ{ zero → refl
                         ; (suc n) → locSubProj⇒ Δ σ ℓ n }
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | no ¬p    | yes q = locSubProj⇒ Δ σ ℓ
... | no  _    | no  _ = locSubProj⇒ Δ σ ℓ

-- The substitution renaming is injective
locSubProjInj' : ∀ Δ σ ℓ x y → locSubProj Δ σ ℓ x ≡ locSubProj Δ σ ℓ y → x ≡ y
locSubProjInj' [] σ ℓ x y x≡y = x≡y
locSubProjInj' ((ℓ' , t) ∷ Δ) σ ℓ with ≡-dec-Loc ℓ ℓ' | ≡-dec-Loc (subₗ-Loc ℓ σ) (subₗ-Loc ℓ' σ)
... | yes _    | yes _ = λ{ zero    zero    z≡z → z≡z
                          ; zero    (suc y) z≡s → ⊥-elim (1+n≢0 (sym z≡s))
                          ; (suc x) zero    s≡z → ⊥-elim (1+n≢0 s≡z)
                          ; (suc x) (suc y) s≡s → cong suc (locSubProjInj' Δ σ ℓ x y (suc-injective s≡s)) }
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | no ¬p    | yes q = λ x y s≡s → locSubProjInj' Δ σ ℓ x y (suc-injective s≡s)
... | no  _    | no  _ = locSubProjInj' Δ σ ℓ

locSubProjInj : ∀ Δ σ ℓ → Injective _≡_ _≡_ (locSubProj Δ σ ℓ)
locSubProjInj Δ σ ℓ {x} {y} eq = locSubProjInj' Δ σ ℓ x y eq

open ≡-Reasoning

{-
  The substitution renaming correctly acts on the projection renaming
  when it is defined.

  E.g.
  Δ = [x0:ℓ.t1, x1:L1.t2, x2:L2.t3, x3:ℓ.t4]
  σ = ⟨ℓ ↦ L2⟩
  ℓ = ℓ

  ξ = ⟨x0 ↦ x0, x1 ↦ x2⟩
  Δ ⦊ ℓ = ⟨x0 ↦ x0, x1 ↦ ⊥, x2 ↦ ⊥, x3 ↦ x1⟩
  ξ ∘ (Δ ⦊ ℓ) = ⟨x0 ↦ x0, x1 ↦ ⊥, x2 ↦ ⊥, x3 ↦ x2⟩

  Δ⟨σ⟩ = [x0:L2.t1, x1:L1.t2, x2:L2.t3, x3:L2.t4]
  ℓ⟨σ⟩ = L2
  Δ⟨σ⟩ ⦊ ℓ⟨σ⟩ = ⟨x0 ↦ x0, x1 ↦ ⊥, x2 ↦ x1, x3 ↦ x2⟩
  
-}
locSubProjVars : ∀ Δ σ ℓ n →
                 (Δ ⦊↓ ℓ) n →
                 (subₗ-LocalCtx Δ σ ⦊ subₗ-Loc ℓ σ) n ≡ map (locSubProj Δ σ ℓ) ((Δ ⦊ ℓ) n)
locSubProjVars [] σ ℓ n tt = refl
locSubProjVars ((ℓ' , t) ∷ Δ) σ ℓ with ≡-dec-Loc ℓ ℓ' | ≡-dec-Loc (subₗ-Loc ℓ σ) (subₗ-Loc ℓ' σ)
... | yes _    | yes _ = λ{ zero tt → refl
                         ; (suc n) Δ⦊↓ℓn → 
    map suc ((subₗ-LocalCtx Δ σ ⦊ subₗ-Loc ℓ σ) n)
      ≡⟨ cong (map suc) (locSubProjVars Δ σ ℓ n Δ⦊↓ℓn) ⟩
    map suc (map (locSubProj Δ σ ℓ) ((Δ ⦊ ℓ) n))
      ≡⟨ sym (Maybe-map-fuse suc (locSubProj Δ σ ℓ) (projVars Δ ℓ n)) ⟩
    map (suc ∘ locSubProj Δ σ ℓ) (projVars Δ ℓ n)
      ≡⟨ sym (Maybe-map-ext (↑∘suc (locSubProj Δ σ ℓ)) (projVars Δ ℓ n)) ⟩
    map (↑ (locSubProj Δ σ ℓ) ∘ suc) (projVars Δ ℓ n)
      ≡⟨ Maybe-map-fuse (↑ (locSubProj Δ σ ℓ)) suc (projVars Δ ℓ n) ⟩
    map (↑ (locSubProj Δ σ ℓ)) (map suc (projVars Δ ℓ n)) ∎ }
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | no ¬p    | yes q = λ{ zero ()
                         ; (suc n) Δ⦊↓ℓn → 
    map suc ((subₗ-LocalCtx Δ σ ⦊ subₗ-Loc ℓ σ) n)
      ≡⟨ cong (map suc) (locSubProjVars Δ σ ℓ n Δ⦊↓ℓn) ⟩
    map suc (map (locSubProj Δ σ ℓ) ((Δ ⦊ ℓ) n))
      ≡⟨ sym (Maybe-map-fuse suc (locSubProj Δ σ ℓ) (projVars Δ ℓ n)) ⟩
    map (suc ∘ locSubProj Δ σ ℓ) (projVars Δ ℓ n) ∎ }
... | no  _    | no  _ = λ{ zero ()
                         ; (suc n) Δ⦊↓ℓn → locSubProjVars Δ σ ℓ n Δ⦊↓ℓn }

{-
  The substitution renaming after the projection renaming is
  less-defined-than or equal to the substituted projection renaming.
-}
locSubProjVars≲ : ∀ Δ σ ℓ n → (subₗ-LocalCtx Δ σ ⦊ subₗ-Loc ℓ σ) n ≲ map (locSubProj Δ σ ℓ) ((Δ ⦊ ℓ) n)
locSubProjVars≲ Δ σ ℓ =
  map↓≡⇒≲ (locSubProj Δ σ ℓ) (Δ ⦊ ℓ) (subₗ-LocalCtx Δ σ ⦊ subₗ-Loc ℓ σ)
    λ{ n ↓Δ⦊ℓ → sym (locSubProjVars Δ σ ℓ n (justProjVars Δ ℓ n ↓Δ⦊ℓ)) }

-- Order preserving embeddings between local contexts
data OPE : (Δ1 Δ2 : LocalCtx) → Set where
  ε : OPE [] []
  Keep : ∀{Δ1 Δ2} (ξ : OPE Δ1 Δ2) (ℓ : Loc) (t : Typₑ) → OPE ((ℓ , t) ∷ Δ1) ((ℓ , t) ∷ Δ2)
  Drop : ∀{Δ1 Δ2} (ξ : OPE Δ1 Δ2) (ℓ : Loc) (t : Typₑ) → OPE Δ1 ((ℓ , t) ∷ Δ2)

-- Interpret an OPE as a local variable renaming
⟦_⟧ : ∀{Δ1 Δ2} → OPE Δ1 Δ2 → ℕ → ℕ
⟦ ε ⟧ = idRen
⟦ Keep ξ ℓ t ⟧ = ↑ ⟦ ξ ⟧
⟦ Drop ξ ℓ t ⟧ = suc ∘ ⟦ ξ ⟧

-- Interpret an OPE as a renaming under the projection to a location
⟦_⟧⦊ : ∀{Δ1 Δ2} → OPE Δ1 Δ2 → Loc → ℕ → ℕ
⟦ ε ⟧⦊ ℓ = idRen
⟦ Keep ξ ℓ' t ⟧⦊ ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = ↑ (⟦ ξ ⟧⦊ ℓ)
... | no  _ = ⟦ ξ ⟧⦊ ℓ
⟦ Drop ξ ℓ' t ⟧⦊ ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = suc ∘ ⟦ ξ ⟧⦊ ℓ
... | no  _ = ⟦ ξ ⟧⦊ ℓ

open ≡-Reasoning

-- Projecting a renaming to a location acts naturally
projNatural : ∀{Δ1 Δ2} (ξ : OPE Δ1 Δ2) (ℓ : Loc) →
              map (⟦ ξ ⟧⦊ ℓ) ∘ (Δ1 ⦊ ℓ) ≈ (Δ2 ⦊ ℓ) ∘ ⟦ ξ ⟧
projNatural ε ℓ n = refl
projNatural (Keep ξ ℓ' t) ℓ zero with ≡-dec-Loc ℓ ℓ'
... | yes _ = refl
... | no _ = refl
projNatural (Keep {Δ1} {Δ2} ξ ℓ' t) ℓ (suc n) with ≡-dec-Loc ℓ ℓ'
... | yes _ =
    map (↑ (⟦ ξ ⟧⦊ ℓ)) (map suc (projVars Δ1 ℓ n))
      ≡⟨ sym (Maybe-map-fuse (↑ (⟦ ξ ⟧⦊ ℓ)) suc ((Δ1 ⦊ ℓ) n)) ⟩
    map (↑ (⟦ ξ ⟧⦊ ℓ) ∘ suc) ((Δ1 ⦊ ℓ) n)
      ≡⟨ Maybe-map-ext (↑∘suc (⟦ ξ ⟧⦊ ℓ)) ((Δ1 ⦊ ℓ) n) ⟩
    map (suc ∘ ⟦ ξ ⟧⦊ ℓ) ((Δ1 ⦊ ℓ) n)
      ≡⟨ Maybe-map-fuse suc (⟦ ξ ⟧⦊ ℓ) ((Δ1 ⦊ ℓ) n) ⟩
    map suc (map (⟦ ξ ⟧⦊ ℓ) ((Δ1 ⦊ ℓ) n))
      ≡⟨ cong (map suc) (projNatural ξ ℓ n) ⟩
    map suc ((Δ2 ⦊ ℓ) (⟦ ξ ⟧ n)) ∎
... | no _ = projNatural ξ ℓ n
projNatural (Drop {Δ1} {Δ2} ξ ℓ' t) ℓ n with ≡-dec-Loc ℓ ℓ'
... | yes _ =
  map (suc ∘ ⟦ ξ ⟧⦊ ℓ) ((Δ1 ⦊ ℓ) n)
    ≡⟨ Maybe-map-fuse suc (⟦ ξ ⟧⦊ ℓ) ((Δ1 ⦊ ℓ) n) ⟩
  map suc (map (⟦ ξ ⟧⦊ ℓ) ((Δ1 ⦊ ℓ) n))
    ≡⟨ cong (map suc) (projNatural ξ ℓ n) ⟩
  map suc ((Δ2 ⦊ ℓ) (⟦ ξ ⟧ n)) ∎
... | no _ = projNatural ξ ℓ n

-- Identity embedding
idOPE : (Δ : LocalCtx) → OPE Δ Δ
idOPE [] = ε
idOPE ((ℓ , t) ∷ Δ) = Keep (idOPE Δ) ℓ t

-- The interpretation respects the identity
renIdOPE : (Δ : LocalCtx) → ⟦ idOPE Δ ⟧ ≈ idRen
renIdOPE [] n = refl
renIdOPE ((ℓ , t) ∷ Δ) zero = refl
renIdOPE ((ℓ , t) ∷ Δ) (suc n) = cong suc (renIdOPE Δ n)

-- The projected interpretation respects the identity
renIdOPE⦊ : (Δ : LocalCtx) (ℓ : Loc) → ⟦ idOPE Δ ⟧⦊ ℓ ≈ idRen
renIdOPE⦊ [] ℓ n = refl
renIdOPE⦊ ((ℓ' , t) ∷ Δ) ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = λ{ zero → refl
               ; (suc n) → cong suc (renIdOPE⦊ Δ ℓ n) }
... | no  _ = renIdOPE⦊ Δ ℓ

-- Bind a location in an OPE
↑OPE : ∀{Δ1 Δ2} → OPE Δ1 Δ2 → OPE (↑LocalCtx Δ1) (↑LocalCtx Δ2)
↑OPE ε = ε
↑OPE (Keep ξ ℓ t) = Keep (↑OPE ξ) (renₗ-Loc ℓ suc) t 
↑OPE (Drop ξ ℓ t) = Drop (↑OPE ξ) (renₗ-Loc ℓ suc) t

-- The interpretation respects binding a location variable
↑renOPE : ∀{Δ1 Δ2} (ξ : OPE Δ1 Δ2) → ⟦ ↑OPE ξ ⟧ ≈ ⟦ ξ ⟧
↑renOPE ε = ≈-refl
↑renOPE (Keep ξ ℓ t) = ↑Ext (↑renOPE ξ)
↑renOPE (Drop ξ ℓ t) = ∘Ext suc _ _ _ ≈-refl (↑renOPE ξ)

-- The projected interpretation respects binding a location variable
↑renOPE⦊ : ∀{Δ1 Δ2} (ξ : OPE Δ1 Δ2) (ℓ : Loc) →
          ⟦ ↑OPE ξ ⟧⦊ (renₗ-Loc ℓ suc) ≈ ⟦ ξ ⟧⦊ ℓ
↑renOPE⦊ ε ℓ n = refl
↑renOPE⦊ (Keep ξ ℓ' t) ℓ with ≡-dec-Loc ℓ ℓ' | ≡-dec-Loc (renₗ-Loc ℓ suc) (renₗ-Loc ℓ' suc)
... | yes refl | yes _ = λ{ zero → refl ; (suc n) → cong suc (↑renOPE⦊ ξ ℓ n) }
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | no ¬p    | yes q = ⊥-elim (¬p (renInjₗ-Loc suc-injective q))
... | no _     | no  _ = ↑renOPE⦊ ξ ℓ
↑renOPE⦊ (Drop ξ ℓ' t) ℓ with ≡-dec-Loc ℓ ℓ' | ≡-dec-Loc (renₗ-Loc ℓ suc) (renₗ-Loc ℓ' suc)
... | yes refl | yes _ = λ n → cong suc (↑renOPE⦊ ξ ℓ n)
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | no ¬p    | yes q = ⊥-elim (¬p (renInjₗ-Loc suc-injective q))
... | no _     | no  _ = ↑renOPE⦊ ξ ℓ

-- The projected interpretation of an OPE from Δ1 to Δ2 changes Δ1 ∣ ℓ to Δ2 ∣ ℓ
renOPE⦊⇒ : ∀{Δ1 Δ2} (ξ : OPE Δ1 Δ2) (ℓ : Loc) →
            (Δ1 ∣ ℓ) ≈ (Δ2 ∣ ℓ) ∘ (⟦ ξ ⟧⦊ ℓ)
renOPE⦊⇒ ε ℓ n = refl
renOPE⦊⇒ (Keep ξ ℓ' t) ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = λ{ zero → refl ; (suc n) → renOPE⦊⇒ ξ ℓ n }
... | no  _ = renOPE⦊⇒ ξ ℓ
renOPE⦊⇒ (Drop ξ ℓ' t) ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = renOPE⦊⇒ ξ ℓ
... | no  _ = renOPE⦊⇒ ξ ℓ
