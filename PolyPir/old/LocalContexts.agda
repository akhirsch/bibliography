{-# OPTIONS --safe #-}

open import Level using (Lift; lift)
open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Maybe
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
  (E : TypedLocalLanguage L)
  where

open import Types L E
open import Choreographies L E
open import LocationRenamings L E
open import Renamings L E
open import LocationContexts L E
open Location L
open TypedLocalLanguage E


{-
  Local contexts are a finite list of variable bindings of a
  specified location and local type
-}
LocalCtx : Set
LocalCtx = List (Loc × Typₑ)

-- Infinite partial local contexts which map local variables to types
LocalCtxFun : Set
LocalCtxFun = Loc → ℕ → Maybe Typₑ

-- Renaming of locations in local contexts
renₗ-LocalCtx : (ℕ → ℕ) → LocalCtx → LocalCtx
renₗ-LocalCtx ξ = Data.List.map (λ{ (ℓ , t) → (renₗ-Loc ξ ℓ , t) })

-- Renaming locations respects extensional equality
renExtₗ-LocalCtx : ∀{ξ1 ξ2} → ξ1 ≈ ξ2 → ∀ Δ → renₗ-LocalCtx ξ1 Δ ≡ renₗ-LocalCtx ξ2 Δ
renExtₗ-LocalCtx ξ1≈ξ2 [] = refl
renExtₗ-LocalCtx ξ1≈ξ2 ((ℓ , t) ∷ Δ) = cong₂ _∷_ (cong₂ _,_ (renExtₗ-Loc ξ1≈ξ2 ℓ) refl) (renExtₗ-LocalCtx ξ1≈ξ2 Δ)

-- Renaming locations respects the identity
renIdₗ-LocalCtx : ∀ Δ → renₗ-LocalCtx idRen Δ ≡ Δ
renIdₗ-LocalCtx [] = refl
renIdₗ-LocalCtx ((ℓ , t) ∷ Δ) = cong₂ _∷_ (cong₂ _,_ (renIdₗ-Loc ℓ) refl) (renIdₗ-LocalCtx Δ)

-- Renaming locations enjoys fusion
renFuseₗ-LocalCtx : ∀ ξ1 ξ2 → renₗ-LocalCtx (ξ1 ∘ ξ2) ≈ renₗ-LocalCtx ξ1 ∘ renₗ-LocalCtx ξ2
renFuseₗ-LocalCtx ξ1 ξ2 [] = refl
renFuseₗ-LocalCtx ξ1 ξ2 ((ℓ , t) ∷ Δ) = cong₂ _∷_ (cong₂ _,_ (renFuseₗ-Loc ξ1 ξ2 ℓ) refl) (renFuseₗ-LocalCtx ξ1 ξ2 Δ)


-- ↑ for location variables on local contexts
↑LocalCtx : LocalCtx → LocalCtx
↑LocalCtx = renₗ-LocalCtx suc

-- ↑ for infinite local contexts
↑LocalCtxFun : LocalCtxFun → LocalCtxFun
↑LocalCtxFun Δ (Var zero) n = nothing
↑LocalCtxFun Δ (Var (suc x)) = Δ (Var x)
↑LocalCtxFun Δ (Lit L) = Δ (Lit L)


-- ↑ distributes over location renaming
↑renₗ-LocalCtx : ∀ ξ Δ → ↑LocalCtx (renₗ-LocalCtx ξ Δ) ≡ renₗ-LocalCtx (↑ ξ) (↑LocalCtx Δ)
↑renₗ-LocalCtx ξ [] = refl
↑renₗ-LocalCtx ξ ((Var x , t) ∷ Δ) = cong₂ _∷_ refl (↑renₗ-LocalCtx ξ Δ)
↑renₗ-LocalCtx ξ ((Lit L , t) ∷ Δ) = cong₂ _∷_ refl (↑renₗ-LocalCtx ξ Δ)

{-
  The projection Δ ∣ ℓ of a local context Δ at a given location ℓ

  E.g.
  [x0:ℓ0.Bool, x1:L.ℕ, x2:ℓ0:ℕ] ∣ ℓ0 = [x0:Bool, x1:ℕ]
  [x0:ℓ0.Bool, x1:L.ℕ, x2:ℓ0:ℕ] ∣ L  = [x0:ℕ]
-}
proj : LocalCtx → LocalCtxFun
proj [] ℓ n = nothing
proj ((ℓ' , t) ∷ Δ) ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = ifZeroElse (just t) (proj Δ ℓ)
... | no  _ = proj Δ ℓ

_∣_ = proj

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

-- Add a type to an infinite local context
_,,[_]_ : LocalCtxFun → Loc → Typₑ → LocalCtxFun
(Δ ,,[ ℓ' ] t) ℓ with ≡-dec-Loc ℓ ℓ'
... | yes _ = λ{ zero → just t
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
projInj : ∀{ξ} Δ ℓ →
          Injective _≡_ _≡_ ξ →
          Δ ∣ ℓ ≈ renₗ-LocalCtx ξ Δ ∣ renₗ-Loc ξ ℓ
projInj [] ℓ ξ-inj n = refl
projInj {ξ} ((ℓ' , t) ∷ Δ) ℓ ξ-inj with ≡-dec-Loc ℓ ℓ' | ≡-dec-Loc (renₗ-Loc ξ ℓ) (renₗ-Loc ξ ℓ')
... | yes _ | yes _ =  λ{ zero → refl
                       ; (suc n) → projInj Δ ℓ ξ-inj n }
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | no ¬p | yes q = ⊥-elim (¬p (renInjₗ-Loc ξ-inj q))
... | no _ | no _ = projInj Δ ℓ ξ-inj

-- Typing of local expressions is preserved under injective location renamings
tyProjRen : ∀{t ξ Δ ℓ e} →
            Injective _≡_ _≡_ ξ →
            (Δ ∣ ℓ) ⊢ₑ e ∶ t →
            (renₗ-LocalCtx ξ Δ ∣ renₗ-Loc ξ ℓ) ⊢ₑ e ∶ t
tyProjRen {Δ = Δ} {ℓ} ξ-inj Δ∣ℓ⊢e∶t = tyExtₑ (projInj Δ ℓ ξ-inj) Δ∣ℓ⊢e∶t

-- Substitution of locations in local contexts
subₗ-LocalCtx : (ℕ → Loc) → LocalCtx → LocalCtx
subₗ-LocalCtx σ = Data.List.map (λ{ (ℓ , t) → subₗ-Loc σ ℓ , t })

-- Substitution respects extensional equality
subExtₗ-LocalCtx : ∀{σ1 σ2} → σ1 ≈ σ2 → subₗ-LocalCtx σ1 ≈ subₗ-LocalCtx σ2
subExtₗ-LocalCtx σ1≈σ2 [] = refl 
subExtₗ-LocalCtx σ1≈σ2 ((ℓ , t) ∷ Δ) = cong₂ _∷_ (cong₂ _,_ (subExtₗ-Loc σ1≈σ2 ℓ) refl) (subExtₗ-LocalCtx σ1≈σ2 Δ)

-- Substitution respects the identity
subIdₗ-LocalCtx : ∀ Δ → subₗ-LocalCtx idSubₗ Δ ≡ Δ
subIdₗ-LocalCtx [] = refl
subIdₗ-LocalCtx ((ℓ , t) ∷ Δ) = cong₂ _∷_ (cong₂ _,_ (subIdₗ-Loc ℓ) refl) (subIdₗ-LocalCtx Δ)

-- Substitution respects the inclusion
subιₗ-LocalCtx : ∀ ξ Δ → subₗ-LocalCtx (ιₗ ξ) Δ ≡ renₗ-LocalCtx ξ Δ
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
locSubProj ((ℓ' , t) ∷ Δ) σ ℓ with ≡-dec-Loc ℓ ℓ' | ≡-dec-Loc (subₗ-Loc σ ℓ) (subₗ-Loc σ ℓ')
... | yes _    | yes _ = ↑ (locSubProj Δ σ ℓ)
... | yes refl | no ¬p = ⊥-elim (¬p refl)
... | no  _    | yes _ = suc ∘ locSubProj Δ σ ℓ
... | no  _    | no  _ = locSubProj Δ σ ℓ

locSubProjExt : ∀{σ1 σ2} (Δ : LocalCtx) → σ1 ≈ σ2 → (ℓ : Loc) → 
                locSubProj Δ σ1 ℓ ≈ locSubProj Δ σ2 ℓ
locSubProjExt [] σ1≈σ2 ℓ n = refl
locSubProjExt {σ1} {σ2} ((ℓ' , t) ∷ Δ) σ1≈σ2 ℓ
  with ≡-dec-Loc ℓ ℓ'
  | ≡-dec-Loc (subₗ-Loc σ1 ℓ) (subₗ-Loc σ1 ℓ')
  | ≡-dec-Loc (subₗ-Loc σ2 ℓ) (subₗ-Loc σ2 ℓ')
... | yes _    | yes _ | yes _ = λ{ zero → refl
                                  ; (suc n) → cong suc (locSubProjExt Δ σ1≈σ2 ℓ n) }
... | yes refl | _     | no ¬p = ⊥-elim (¬p refl)
... | yes refl | no ¬p | _     = ⊥-elim (¬p refl)
... | no  _    | yes _ | yes _ = λ n → cong suc (locSubProjExt Δ σ1≈σ2 ℓ n)
... | no  _    | yes p | no ¬p = ⊥-elim (¬p (sym (subExtₗ-Loc σ1≈σ2 ℓ) ∙ p ∙ subExtₗ-Loc σ1≈σ2 ℓ'))
... | no  _    | no ¬p | yes p = ⊥-elim (¬p (subExtₗ-Loc σ1≈σ2 ℓ ∙ p ∙ sym (subExtₗ-Loc σ1≈σ2 ℓ')))
... | no  _    | no  _ | no  _ = locSubProjExt Δ σ1≈σ2 ℓ

locSubProjId : (Δ : LocalCtx) (ℓ : Loc) → 
               ∀ n → locSubProj Δ idSubₗ ℓ n ≡ n
locSubProjId [] ℓ n = refl
locSubProjId ((ℓ' , t) ∷ Δ) ℓ with ≡-dec-Loc ℓ ℓ' | ≡-dec-Loc (subₗ-Loc idSubₗ ℓ) (subₗ-Loc idSubₗ ℓ')
... | yes _    | yes _ = λ{ zero → refl
                          ; (suc n) → cong suc (locSubProjId Δ ℓ n) }
... | yes refl | no ¬p = ⊥-elim (¬p refl)
... | no  ¬p   | yes p = ⊥-elim (¬p (sym (subIdₗ-Loc ℓ) ∙ p ∙ subIdₗ-Loc ℓ'))
... | no  _    | no  _ = locSubProjId Δ ℓ

locSubProjι : (Δ : LocalCtx) (ξ : ℕ → ℕ) (ℓ : Loc) →
              Injective _≡_ _≡_ ξ →
              ∀ n → locSubProj Δ (ιₗ ξ) ℓ n ≡ n
locSubProjι [] ξ ℓ ξ-inj n = refl
locSubProjι ((ℓ' , t) ∷ Δ) ξ ℓ ξ-inj with ≡-dec-Loc ℓ ℓ' | ≡-dec-Loc (subₗ-Loc (ιₗ ξ) ℓ) (subₗ-Loc (ιₗ ξ) ℓ')
... | yes _    | yes _ = λ{ zero → refl
                          ; (suc n) → cong suc (locSubProjι Δ ξ ℓ ξ-inj n) }
... | yes refl | no ¬p = ⊥-elim (¬p refl)
... | no  ¬p   | yes p = ⊥-elim (¬p (subInjₗ-Loc ξ-inj p))
... | no  _    | no  _ = locSubProjι Δ ξ ℓ ξ-inj

-- The substitution renaming changes Δ ∣ ℓ into Δ⟨σ⟩ ∣ ℓ⟨σ⟩
locSubProj⇒ : ∀ Δ σ ℓ →
              Δ ∣ ℓ ≈ (subₗ-LocalCtx σ Δ ∣ subₗ-Loc σ ℓ) ∘ locSubProj Δ σ ℓ
locSubProj⇒ [] σ ℓ n = refl
locSubProj⇒ ((ℓ' , t) ∷ Δ) σ ℓ with ≡-dec-Loc ℓ ℓ' | ≡-dec-Loc (subₗ-Loc σ ℓ) (subₗ-Loc σ ℓ')
... | yes _    | yes _ = λ{ zero → refl
                         ; (suc n) → locSubProj⇒ Δ σ ℓ n }
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | no ¬p    | yes q = locSubProj⇒ Δ σ ℓ
... | no  _    | no  _ = locSubProj⇒ Δ σ ℓ

-- The substitution renaming is injective
locSubProjInj' : ∀ Δ σ ℓ x y → locSubProj Δ σ ℓ x ≡ locSubProj Δ σ ℓ y → x ≡ y
locSubProjInj' [] σ ℓ x y x≡y = x≡y
locSubProjInj' ((ℓ' , t) ∷ Δ) σ ℓ with ≡-dec-Loc ℓ ℓ' | ≡-dec-Loc (subₗ-Loc σ ℓ) (subₗ-Loc σ ℓ')
... | yes _    | yes _ = λ{ zero    zero    z≡z → z≡z
                          ; zero    (suc y) z≡s → ⊥-elim (1+n≢0 (sym z≡s))
                          ; (suc x) zero    s≡z → ⊥-elim (1+n≢0 s≡z)
                          ; (suc x) (suc y) s≡s → cong suc (locSubProjInj' Δ σ ℓ x y (suc-injective s≡s)) }
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | no ¬p    | yes q = λ x y s≡s → locSubProjInj' Δ σ ℓ x y (suc-injective s≡s)
... | no  _    | no  _ = locSubProjInj' Δ σ ℓ

locSubProjInj : ∀ Δ σ ℓ → Injective _≡_ _≡_ (locSubProj Δ σ ℓ)
locSubProjInj Δ σ ℓ {x} {y} eq = locSubProjInj' Δ σ ℓ x y eq
