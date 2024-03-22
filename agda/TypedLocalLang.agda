{-# OPTIONS --safe --without-K #-}

open import Data.Empty
open import Data.Nat
open import Data.Sum
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Function

open import LocalLang

-- Module for (non-dependent) type systems of local languages
module TypedLocalLang where

-- Type theory for a local language
record TypedLocalLanguage
       (L : Language)
       (LL : LawfulLanguage L) : Set₁ where
  open Language L
  open LawfulLanguage LL

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
            (∀ n → Γ n ≡ Δ n) →
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
    tyWkₑ : ∀{Γ Δ e t} →
           (ξ : ℕ → ℕ) →
           (∀ n → Γ n ≡ Δ (ξ n)) →
           Γ ⊢ₑ e ∶ t →
           Δ ⊢ₑ renₑ e ξ ∶ t

    -- We have a type for booleans, and the appropriate judgments.
    Boolₑ : Typₑ
    ty-ttₑ : ∀{Γ} → Γ ⊢ₑ ttₑ ∶ Boolₑ
    ty-ffₑ : ∀{Γ} → Γ ⊢ₑ ffₑ ∶ Boolₑ

    -- Each boolean value is either true or false
    boolValₑ : ∀{Γ v} →
                    Γ ⊢ₑ v ∶ Boolₑ →
                    Valₑ v →
                    (v ≡ ttₑ) ⊎ (v ≡ ffₑ)
  

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
  Changesₑ : (ℕ → Expr) → (ℕ → Typₑ) → (ℕ → Typₑ) → Set
  Changesₑ σ Γ Δ = ∀ n → Δ ⊢ₑ σ n ∶ Γ n

  field
    {-
      The typing judgment should respect substitutions
      which change contexts.
    -}
    tyChangesₑ : ∀{σ Γ Δ e t} →
                Changesₑ σ Γ Δ →
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
  idSubChangesₑ : (Γ : ℕ → Typₑ) → Changesₑ idSubₑ Γ Γ
  idSubChangesₑ Γ n = tyExprₑ Γ n

  -- The identity substitution respects typing
  tySubIdₑ : ∀{Γ e t} → Γ ⊢ₑ e ∶ t → Γ ⊢ₑ subₑ e idSubₑ ∶ t
  tySubIdₑ Γ⊢e:t = tyChangesₑ (idSubChangesₑ _) Γ⊢e:t
