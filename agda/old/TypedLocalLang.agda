{-# OPTIONS --safe #-}

open import Data.Empty
open import Data.Nat
open import Data.Sum
open import Data.Maybe
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
record TypedLocalLanguage (L : Location) : Set₁ where
  open Location L

  field
    {{LL}} : LawfulLanguage L

  open LawfulLanguage LL public

  field
    -- Local types
    TypVal : Set

    -- Types have decidable equality
    ≡-dec-TypVal : (t₁ t₂ : TypVal) → Dec (t₁ ≡ t₂)

    {-
      Typing judgment of the form Γ ⊢ e : t.
      Contexts are infinite maps from variables to types.
    -}
    _⊢ₑ_∶_ : (ℕ → Maybe TypVal) → Expr → TypVal → Set

    -- Typing respects extensional equality of contexts.
    tyExtₑ : ∀{Γ Δ e t} →
              Γ ≈ Δ →
              Γ ⊢ₑ e ∶ t →
              Δ ⊢ₑ e ∶ t

    -- Variables have the type they are assigned by the context.
    tyVarₑ : ∀ Γ n t → Γ n ≡ just t → Γ ⊢ₑ varₑ n ∶ t

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

    -- Weakening should be allowed
    tyWkₑ : ∀{Γ Γ' e t} →
            (ξ : ℕ → ℕ) →
            Γ ≈ Γ' ∘ ξ →
            Γ ⊢ₑ e ∶ t →
            Γ' ⊢ₑ renₑ ξ e ∶ t

    -- We have a type for booleans, and the appropriate judgments.
    Boolₑ : TypVal
    ty-ttₑ : ∀{Γ} → Γ ⊢ₑ ttₑ ∶ Boolₑ
    ty-ffₑ : ∀{Γ} → Γ ⊢ₑ ffₑ ∶ Boolₑ

    -- Each boolean value is either true or false.
    boolInvertₑ : ∀{v} →
                  (λ _ → nothing) ⊢ₑ v ∶ Boolₑ →
                  Valₑ v →
                  (v ≡ ttₑ) ⊎ (v ≡ ffₑ)
    
    -- We have a type for locations, and the appropriate judgments.
    Locₑ : TypVal
    ty-locₑ : ∀{Γ ℓ} → Γ ⊢ₑ locₑ ℓ ∶ Locₑ

    -- Each location value corresponds to an actual location.
    locInvertₑ : ∀{v} →
                 (λ _ → nothing) ⊢ₑ v ∶ Locₑ →
                 Valₑ v →
                 Σ[ L ∈ LocVal ] (v ≡ locₑ L)
 
    -- Progress and preservation must hold.
    preservationₑ : ∀{e1 e2 t} →
                    (λ _ → nothing) ⊢ₑ e1 ∶ t →
                    e1 ⇒ₑ e2 →
                    (λ _ → nothing) ⊢ₑ e2 ∶ t

    progressₑ : ∀{e1 t} →
                (λ _ → nothing) ⊢ₑ e1 ∶ t →
                (Valₑ e1) ⊎ Σ[ e2 ∈ _ ] e1 ⇒ₑ e2

  {-
    A substitution σ changes context Γ to context Δ
    if for every variable n, σ assigns n to an expression
    which, under Δ, has the same type that Γ assigns to n.
  -}
  _∶_⇒ₑ_ : (σ : ℕ → Expr) (Γ Δ : ℕ → Maybe TypVal) → Set
  σ ∶ Γ ⇒ₑ Δ = ∀ n t → Γ n ≡ just t → Δ ⊢ₑ σ n ∶ t

  field
    {-
      The typing judgment should respect substitutions
      which change contexts.
    -}
    tySubₑ : ∀{σ Γ Δ e t} →
             σ ∶ Γ ⇒ₑ Δ →
             Γ ⊢ₑ e ∶ t →
             Δ ⊢ₑ subₑ σ e ∶ t

  -- Deduced lemmas for convenience.

  -- The context is irrelevant when typing closed expressions.
  tyClosedₑ : ∀{Γ Δ e t} → Closedₑ e → Γ ⊢ₑ e ∶ t → Δ ⊢ₑ e ∶ t
  tyClosedₑ closed Γ⊢e:t = tyClosedAboveₑ closed (λ ()) Γ⊢e:t

  -- The context is irrelevant when typing values.
  tyValₑ : ∀{Γ Δ v t} → Valₑ v → Γ ⊢ₑ v ∶ t → Δ ⊢ₑ v ∶ t
  tyValₑ val Γ⊢v:t = tyClosedₑ (valClosedₑ val) Γ⊢v:t

  -- The identity substitution changes any context to itself
  idSubChangesₑ : (Γ : ℕ → Maybe TypVal) → idSubₑ ∶ Γ ⇒ₑ Γ
  idSubChangesₑ Γ n = tyVarₑ Γ n

  -- The identity substitution respects typing
  tySubIdₑ : ∀{Γ e t} → Γ ⊢ₑ e ∶ t → Γ ⊢ₑ subₑ idSubₑ e ∶ t
  tySubIdₑ Γ⊢e:t = tySubₑ (idSubChangesₑ _) Γ⊢e:t