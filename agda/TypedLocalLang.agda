{-# OPTIONS --safe #-}

open import Data.Empty
open import Data.Nat
open import Data.Maybe
open import Data.Maybe.Properties
open import Data.Sum
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Function

open import Common
open import LocalLang
open import Locations

-- Module for (non-dependent) type systems of local languages
module TypedLocalLang where

-- Type theory for a local language
record TypedLocalLanguage
       (L : Location)
       (E : Language L)
       (LE : LawfulLanguage L E)
       : Set₁ where
  open Location L
  open Language E
  open LawfulLanguage LE

  field
    -- Local types
    Typₑ : Set

    -- Types have decidable equality
    ≡-dec-Typₑ : (t₁ t₂ : Typₑ) → Dec (t₁ ≡ t₂)

    {-
      Typing judgment of the form Γ ⊢ e : t.
      Contexts are partial infinite maps from variables to possible types.
      Should fail if any free variable in an expression has an undefined type.
    -}
    _?⊢ₑ_∶_ : (ℕ → Maybe Typₑ) → Expr → Typₑ → Set

    -- Typing respects extensional equality of contexts
    tyMaybeExtₑ : ∀{Γ Δ e t} →
                  Γ ≈ Δ →
                  Γ ?⊢ₑ e ∶ t →
                  Δ ?⊢ₑ e ∶ t

    -- Typing is monotone with respect to definedness of contexts
    tyMaybeMonoₑ : ∀{Γ Δ e t} →
                   (∀ x → Γ x ≲ Δ x) →
                   Γ ?⊢ₑ e ∶ t →
                   Δ ?⊢ₑ e ∶ t

    -- Variables have the type they are assigned by the context
    tyMaybeVarₑ : ∀ Γ n t → Γ n ≡ just t → Γ ?⊢ₑ varₑ n ∶ t

    -- Expressions have a unique type
    tyMaybeUniqₑ : ∀{Γ e t1 t2} →
                   Γ ?⊢ₑ e ∶ t1 →
                   Γ ?⊢ₑ e ∶ t2 →
                   t1 ≡ t2

    {-
      The typing judgment should only take into account the free
      variables in an expression. Thus, if an expression is closed
      above n, the values of the context above n should not matter.
    -}
    tyMaybeClosedAboveₑ : ∀{Γ Δ e t n} →
                          ClosedAboveₑ n e →
                          (∀{m} → m < n → Γ m ≡ Δ m) →
                          Γ ?⊢ₑ e ∶ t →
                          Δ ?⊢ₑ e ∶ t

    -- Weakening is allowed
    tyMaybeWkₑ : ∀{Γ1 Γ2 e t} →
                (ξ : ℕ → ℕ) →
                Γ1 ≈ Γ2 ∘ ξ →
                Γ1 ?⊢ₑ e ∶ t →
                Γ2 ?⊢ₑ renₑ ξ e ∶ t

    -- We have a type for booleans, and the appropriate judgments
    Boolₑ : Typₑ
    tyTrueₑ : ∀{Γ} → Γ ?⊢ₑ ttₑ ∶ Boolₑ
    tyFalseₑ : ∀{Γ} → Γ ?⊢ₑ ffₑ ∶ Boolₑ

    -- Each boolean value is either true or false
    boolValₑ : ∀{Γ v} →
               Γ ?⊢ₑ v ∶ Boolₑ →
               Valₑ v →
               (v ≡ ttₑ) ⊎ (v ≡ ffₑ)
  
    -- We have a type for locations, and the appropriate judgments
    Locₑ : Typₑ
    ty-locₑ : ∀{Γ ℓ} → Γ ?⊢ₑ locₑ ℓ ∶ Locₑ

    -- Each location value corresponds to an actual location
    locValₑ : ∀{Γ v} →
              Γ ?⊢ₑ v ∶ Locₑ →
              Valₑ v →
              Σ[ ℓ ∈ LocVal ] (v ≡ locₑ ℓ)
 
    -- Progress and preservation hold
    preservationₑ : ∀{Γ e1 e2 t} →
                    e1 ⇒ₑ e2 →
                    Γ ?⊢ₑ e1 ∶ t →
                    Γ ?⊢ₑ e2 ∶ t

    progressₑ : ∀{Γ e₁ t} →
                Γ ?⊢ₑ e₁ ∶ t →
                Closedₑ e₁ →
                (Valₑ e₁) ⊎ Σ[ e₂ ∈ _ ] e₁ ⇒ₑ e₂

  -- Typing judgment on total contexts
  _⊢ₑ_∶_ : (ℕ → Typₑ) → Expr → Typₑ → Set
  Γ ⊢ₑ e ∶ t = (just ∘ Γ) ?⊢ₑ e ∶ t

  tyExtₑ : ∀{Γ Δ e t} →
            Γ ≈ Δ →
            Γ ⊢ₑ e ∶ t →
            Δ ⊢ₑ e ∶ t
  tyExtₑ Γ≈Δ Γ⊢e∶t = tyMaybeExtₑ (λ x → cong just (Γ≈Δ x)) Γ⊢e∶t

  tyVarₑ : ∀ Γ n → Γ ⊢ₑ varₑ n ∶ Γ n
  tyVarₑ Γ n = tyMaybeVarₑ (just ∘ Γ) n (Γ n) refl

  -- Expressions have a unique type
  tyUniqₑ : ∀{Γ e t1 t2} →
            Γ ⊢ₑ e ∶ t1 →
            Γ ⊢ₑ e ∶ t2 →
            t1 ≡ t2
  tyUniqₑ = tyMaybeUniqₑ

  tyClosedAboveₑ : ∀{Γ Δ e t n} →
                   ClosedAboveₑ n e →
                   (∀{m} → m < n → Γ m ≡ Δ m) →
                   Γ ⊢ₑ e ∶ t →
                   Δ ⊢ₑ e ∶ t
  tyClosedAboveₑ closed Γ≈Δ = tyMaybeClosedAboveₑ closed (λ m<n → cong just (Γ≈Δ m<n))

  tyWkₑ : ∀{Γ1 Γ2 e t} →
          (ξ : ℕ → ℕ) →
          Γ1 ≈ Γ2 ∘ ξ →
          Γ1 ⊢ₑ e ∶ t →
          Γ2 ⊢ₑ renₑ ξ e ∶ t
  tyWkₑ ξ Γ1≈Γ2∘ξ = tyMaybeWkₑ ξ λ x → cong just (Γ1≈Γ2∘ξ x)

  -- Convenience relation for typing of a possibly undefined expression
  _?⊢ₑ_?∶_ : (Γ : ℕ → Maybe Typₑ) → Maybe Expr → Typₑ → Set
  Γ ?⊢ₑ m ?∶ t = Σ[ e ∈ Expr ] (m ≡ just e × Γ ?⊢ₑ e ∶ t)

  _⊢ₑ_?∶_ : (Γ : ℕ → Typₑ) → Maybe Expr → Typₑ → Set
  Γ ⊢ₑ m ?∶ t = (just ∘ Γ) ?⊢ₑ m ?∶ t

  {-
    A substitution σ changes context Γ to context Δ
    if for every variable n that is well-typed under Γ,
    σ assigns n to an expression which, under Δ, has the
    same type that Γ assigns to n.
  -}
  _∶_?⇒ₑ_ : (σ : ℕ → Maybe Expr) (Γ Δ : ℕ → Maybe Typₑ) → Set
  σ ∶ Γ ?⇒ₑ Δ = ∀ n t → Γ n ≡ just t → Δ ?⊢ₑ σ n ?∶ t

  _∶_⇒ₑ_ : (σ : ℕ → Expr) (Γ Δ : ℕ → Typₑ) → Set
  σ ∶ Γ ⇒ₑ Δ = ∀ n → Δ ⊢ₑ σ n ∶ Γ n

  field
    -- The typing judgment respects substitutions which change contexts
    tyMaybeSubₑ : ∀{σ Γ Δ e t} →
                  σ ∶ Γ ?⇒ₑ Δ →
                  Γ ?⊢ₑ e ∶ t →
                  Δ ?⊢ₑ subMaybeₑ σ e ?∶ t

  -- Deduced lemmas for convenience.
  changes⇒?changes : ∀{σ Γ Δ} →
                     σ ∶ Γ ⇒ₑ Δ →
                     (just ∘ σ) ∶ (just ∘ Γ) ?⇒ₑ (just ∘ Δ)
  changes⇒?changes {σ} {Γ} {Δ} σ⇒ n t Γn≡t =
    σ n , refl , subst (λ x → (just ∘ Δ) ?⊢ₑ σ n ∶ x) (just-injective Γn≡t) (σ⇒ n)

  tySubₑ : ∀{σ Γ Δ e t} →
           σ ∶ Γ ⇒ₑ Δ →
           Γ ⊢ₑ e ∶ t →
           Δ ⊢ₑ subₑ σ e ∶ t
  tySubₑ {σ} {Γ} {Δ} {e} {t} σ⇒ Γ⊢e∶t with tyMaybeSubₑ (changes⇒?changes σ⇒) Γ⊢e∶t
  ... | (e' , e⟨σ⟩≡e' , Δ⊢e'∶t) =
    subst (λ x → Δ ⊢ₑ x ∶ t)
      (just-injective (sym e⟨σ⟩≡e' ∙ subMaybeJustₑ σ e .snd)) Δ⊢e'∶t

  -- The context is irrelevant when typing closed expressions
  tyMaybeClosedₑ : ∀{Γ Δ e t} → Closedₑ e → Γ ?⊢ₑ e ∶ t → Δ ?⊢ₑ e ∶ t
  tyMaybeClosedₑ closed Γ⊢e:t = tyMaybeClosedAboveₑ closed (λ ()) Γ⊢e:t

  tyClosedₑ : ∀{Γ Δ e t} → Closedₑ e → Γ ⊢ₑ e ∶ t → Δ ⊢ₑ e ∶ t
  tyClosedₑ closed Γ⊢e:t = tyClosedAboveₑ closed (λ ()) Γ⊢e:t

  -- The context is irrelevant when typing values.
  tyMaybeValₑ : ∀{Γ Δ v t} → Valₑ v → Γ ?⊢ₑ v ∶ t → Δ ?⊢ₑ v ∶ t
  tyMaybeValₑ val Γ⊢v:t = tyMaybeClosedₑ (valClosedₑ val) Γ⊢v:t

  tyValₑ : ∀{Γ Δ v t} → Valₑ v → Γ ⊢ₑ v ∶ t → Δ ⊢ₑ v ∶ t
  tyValₑ val Γ⊢v:t = tyMaybeClosedₑ (valClosedₑ val) Γ⊢v:t

  -- The identity substitution changes any context to itself
  idSubMaybeChangesₑ : (Γ : ℕ → Maybe Typₑ) → (just ∘ idSubₑ) ∶ Γ ?⇒ₑ Γ
  idSubMaybeChangesₑ Γ n t Γn≡t = varₑ n , refl , tyMaybeVarₑ Γ n t Γn≡t

  idSubChangesₑ : (Γ : ℕ → Typₑ) → idSubₑ ∶ Γ ⇒ₑ Γ
  idSubChangesₑ = tyVarₑ

  -- The identity substitution respects typing
  tyMaybeSubIdₑ : ∀{Γ e t} → Γ ?⊢ₑ e ∶ t → Γ ?⊢ₑ subₑ idSubₑ e ∶ t
  tyMaybeSubIdₑ {Γ} {e} {t} Γ⊢e:t with tyMaybeSubₑ (idSubMaybeChangesₑ Γ) Γ⊢e:t
  ... | (e' , e⟨id⟩≡e' , Γ⊢e'∶t) =
    subst (λ x → Γ ?⊢ₑ x ∶ t)
      (just-injective (sym e⟨id⟩≡e' ∙ subMaybeJustₑ varₑ e .snd)) Γ⊢e'∶t
  
  tySubIdₑ : ∀{Γ e t} → Γ ⊢ₑ e ∶ t → Γ ⊢ₑ subₑ idSubₑ e ∶ t
  tySubIdₑ Γ⊢e:t = tySubₑ (idSubChangesₑ _) Γ⊢e:t

  -- Uniqueness of typing for possibly undefined expressions
  tyUniq??ₑ : ∀{Γ m t1 t2} →
             Γ ?⊢ₑ m ?∶ t1 →
             Γ ?⊢ₑ m ?∶ t2 →
             t1 ≡ t2
  tyUniq??ₑ {Γ} {just e} {t1} {t2} (e , refl , Γ⊢e∶t1) (e' , eq' , Γ⊢e'∶t2) =
    tyMaybeUniqₑ Γ⊢e∶t1 Γ⊢e∶t2
    where
    Γ⊢e∶t2 : Γ ?⊢ₑ e ∶ t2
    Γ⊢e∶t2 = subst (λ x → Γ ?⊢ₑ x ∶ t2) (sym (just-injective eq')) Γ⊢e'∶t2


  tyUniq?ₑ : ∀{Γ m t1 t2} →
             Γ ⊢ₑ m ?∶ t1 →
             Γ ⊢ₑ m ?∶ t2 →
             t1 ≡ t2
  tyUniq?ₑ {Γ} {just e} {t1} {t2} (e , refl , Γ⊢e∶t1) (e' , eq' , Γ⊢e'∶t2) =
    tyUniqₑ Γ⊢e∶t1 Γ⊢e∶t2
    where
    Γ⊢e∶t2 : Γ ⊢ₑ e ∶ t2
    Γ⊢e∶t2 = subst (λ x → Γ ⊢ₑ x ∶ t2) (sym (just-injective eq')) Γ⊢e'∶t2

  -- Extensionality of typing for possibly undefined expressions
  tyExt??ₑ : ∀{Γ1 Γ2 m t} →
             Γ1 ≈ Γ2 →
             Γ1 ?⊢ₑ m ?∶ t →
             Γ2 ?⊢ₑ m ?∶ t
  tyExt??ₑ Γ1≈Γ2 (e , m≡e , Γ1⊢e∶t) = e , m≡e , tyMaybeExtₑ Γ1≈Γ2 Γ1⊢e∶t

  tyExt?ₑ : ∀{Γ1 Γ2 m t} →
            Γ1 ≈ Γ2 →
            Γ1 ⊢ₑ m ?∶ t →
            Γ2 ⊢ₑ m ?∶ t
  tyExt?ₑ Γ1≈Γ2 (e , m≡e , Γ1⊢e∶t) = e , m≡e , tyExtₑ Γ1≈Γ2 Γ1⊢e∶t

  -- Weakening is allowed for possibly undefined expressions
  tyWk?ₑ : ∀{Γ1 Γ2 m t} →
           (ξ : ℕ → ℕ) →
           Γ1 ≈ Γ2 ∘ ξ →
           Γ1 ⊢ₑ m ?∶ t →
           Γ2 ⊢ₑ maybe′ (λ e → renMaybeₑ (just ∘ ξ) e) nothing m ?∶ t
  tyWk?ₑ ξ Γ1≈Γ2∘ξ (e , refl , Γ1⊢e∶t) = renₑ ξ e , renMaybeJustₑ ξ e .snd , tyWkₑ ξ Γ1≈Γ2∘ξ Γ1⊢e∶t
