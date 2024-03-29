{-# OPTIONS --safe #-}

open import Data.Empty
open import Data.Nat
open import Data.Maybe
open import Data.Maybe.Properties
open import Data.Sum
open import Data.Product
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
      Contexts are infinite maps from variables to types.
    -}
    _⊢ₑ_∶_ : (ℕ → Typₑ) → Expr → Typₑ → Set

    -- Typing respects extensional equality of contexts.
    tyExtₑ : ∀{Γ Δ e t} →
            Γ ≈ Δ →
            Γ ⊢ₑ e ∶ t →
            Δ ⊢ₑ e ∶ t

    -- Variables have the type they are assigned by the context.
    tyExprₑ : ∀ Γ n → Γ ⊢ₑ varₑ n ∶ Γ n

    -- Expressions have a unique type.
    tyUniqₑ : ∀{Γ e t₁ t₂} →
             Γ ⊢ₑ e ∶ t₁ →
             Γ ⊢ₑ e ∶ t₂ →
             t₁ ≡ t₂

    {-
      The typing judgment should only take into account the free
      variables in an expression. Thus, if an expression is closed
      above n, the values of the context above n should not matter.
    -}
    tyClosedAboveₑ : ∀{Γ Δ e t n} →
                    ClosedAboveₑ n e →
                    (∀{m} → m < n → Γ m ≡ Δ m) →
                    Γ ⊢ₑ e ∶ t →
                    Δ ⊢ₑ e ∶ t

    -- Weakening should be allowed.
    tyWkₑ : ∀{Γ1 Γ2 e t} →
            (ξ : ℕ → ℕ) →
            Γ1 ≈ Γ2 ∘ ξ →
            Γ1 ⊢ₑ e ∶ t →
            Γ2 ⊢ₑ renₑ e ξ ∶ t

    -- We have a type for booleans, and the appropriate judgments.
    Boolₑ : Typₑ
    ty-ttₑ : ∀{Γ} → Γ ⊢ₑ ttₑ ∶ Boolₑ
    ty-ffₑ : ∀{Γ} → Γ ⊢ₑ ffₑ ∶ Boolₑ

    -- Each boolean value is either true or false.
    boolValₑ : ∀{Γ v} →
               Γ ⊢ₑ v ∶ Boolₑ →
               Valₑ v →
               (v ≡ ttₑ) ⊎ (v ≡ ffₑ)
    
    -- We have a type for locations, and the appropriate judgments.
    Locₑ : Typₑ
    ty-locₑ : ∀{Γ ℓ} → Γ ⊢ₑ locₑ ℓ ∶ Locₑ

    -- Each location value corresponds to an actual location.
    locValₑ : ∀{Γ v} →
              Γ ⊢ₑ v ∶ Locₑ →
              Valₑ v →
              Σ[ ℓ ∈ LocVal ] (v ≡ locₑ ℓ)
 
    -- Progress and preservation must hold.
    preservationₑ : ∀{Γ e₁ e₂ t} →
                   Γ ⊢ₑ e₁ ∶ t →
                   e₁ ⇒ₑ e₂ →
                   Γ ⊢ₑ e₂ ∶ t

    progressₑ : ∀{Γ e₁ t} →
               Γ ⊢ₑ e₁ ∶ t →
               Closedₑ e₁ →
               (Valₑ e₁) ⊎ Σ[ e₂ ∈ _ ] e₁ ⇒ₑ e₂

  {-
    A substitution σ changes context Γ to context Δ
    if for every variable n, σ assigns n to an expression
    which, under Δ, has the same type that Γ assigns to n.
  -}
  _∶_⇒ₑ_ : (σ : ℕ → Expr) (Γ Δ : ℕ → Typₑ) → Set
  σ ∶ Γ ⇒ₑ Δ = ∀ n → Δ ⊢ₑ σ n ∶ Γ n

  field
    {-
      The typing judgment should respect substitutions
      which change contexts.
    -}
    tySubₑ : ∀{σ Γ Δ e t} →
             σ ∶ Γ ⇒ₑ Δ →
             Γ ⊢ₑ e ∶ t →
             Δ ⊢ₑ subₑ e σ ∶ t

  -- Deduced lemmas for convenience.

  -- The context is irrelevant when typing closed expressions.
  tyClosedₑ : ∀{Γ Δ e t} → Closedₑ e → Γ ⊢ₑ e ∶ t → Δ ⊢ₑ e ∶ t
  tyClosedₑ closed Γ⊢e:t = tyClosedAboveₑ closed (λ ()) Γ⊢e:t

  -- The context is irrelevant when typing values.
  tyValₑ : ∀{Γ Δ v t} → Valₑ v → Γ ⊢ₑ v ∶ t → Δ ⊢ₑ v ∶ t
  tyValₑ val Γ⊢v:t = tyClosedₑ (valClosedₑ val) Γ⊢v:t

  -- The identity substitution changes any context to itself
  idSubChangesₑ : (Γ : ℕ → Typₑ) → idSubₑ ∶ Γ ⇒ₑ Γ
  idSubChangesₑ Γ n = tyExprₑ Γ n

  -- The identity substitution respects typing
  tySubIdₑ : ∀{Γ e t} → Γ ⊢ₑ e ∶ t → Γ ⊢ₑ subₑ e idSubₑ ∶ t
  tySubIdₑ Γ⊢e:t = tySubₑ (idSubChangesₑ _) Γ⊢e:t

  -- Convenience function for typing of a possibly undefined expression 
  _⊢ₑ_?∶_ : (Γ : ℕ → Typₑ) → Maybe Expr → Typₑ → Set
  Γ ⊢ₑ m ?∶ t = Σ[ e ∈ Expr ] (m ≡ just e × Γ ⊢ₑ e ∶ t)

  -- Uniqueness of typing for possibly undefined expressions
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
           Γ2 ⊢ₑ maybe′ (λ e → renMaybeₑ e (just ∘ ξ)) nothing m ?∶ t
  tyWk?ₑ ξ Γ1≈Γ2∘ξ (e , refl , Γ1⊢e∶t) = renₑ e ξ , renMaybeJustₑ ξ e , tyWkₑ ξ Γ1≈Γ2∘ξ Γ1⊢e∶t
