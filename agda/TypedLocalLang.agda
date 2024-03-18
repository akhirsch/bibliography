{-# OPTIONS --safe --without-K #-}

open import Data.Empty
open import Data.Nat
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Function

open import LocalLang

{-
Module for (non-dependent) type systems of local languages
-}
module TypedLocalLang
  (L : Language)
  (LL : LawfulLanguage L)
  where

open Language L
open LawfulLanguage LL

-- Type theory for a local language
record TypedLocalLanguage : Set₁ where
  field
    -- Set of types
    Typ : Set

    -- Types should have decidable equality
    decEq : (t₁ t₂ : Typ) → Dec (t₁ ≡ t₂)

    {-
      Typing judgment of the form Γ ⊢ e : t.
      Contexts are infinite maps from variables to types.
    -}
    Typing : (ℕ → Typ) → Expr → Typ → Set

    -- Typing respects extensional equality of contexts.
    tyExt : ∀{Γ Δ e t} →
            (∀ n → Γ n ≡ Δ n) →
            Typing Γ e t →
            Typing Δ e t

    -- Variables have the type they are assigned by the context.
    tyVar : ∀ Γ n → Typing Γ (var n) (Γ n)

    -- Expressions have a unique type.
    tyUniq : ∀{Γ e t₁ t₂} →
             Typing Γ e t₁ →
             Typing Γ e t₂ →
             t₁ ≡ t₂

    {-
      The typing judgment should only take into account the free
      variables in an expression. Thus, if an expression is closed
      above n, the values of the context above n should not matter.
    -}
    tyClosedAbove : ∀{Γ Δ e t n} →
                    ClosedAbove n e →
                    (∀{m} → m < n → Γ m ≡ Δ m) →
                    Typing Γ e t →
                    Typing Δ e t

    -- Weaking should be allowed.
    tyWk : ∀{Γ Δ e t} →
           (ξ : ℕ → ℕ) →
           (∀ n → Γ n ≡ Δ (ξ n)) →
           Typing Γ e t →
           Typing Δ (ren e ξ) t

    -- We have a type for booleans, and the appropriate judgments.
    boolTy : Typ
    ty-tt : ∀{Γ} → Typing Γ tt boolTy
    ty-ff : ∀{Γ} → Typing Γ ff boolTy

  {-
    A substitution σ changes context Γ to context Δ
    if for every variable n, σ assigns n to an expression
    which, under Δ, has the same type that Γ assigns to n.
  -}
  Changes : (ℕ → Expr) → (ℕ → Typ) → (ℕ → Typ) → Set
  Changes σ Γ Δ = ∀ n → Typing Δ (σ n) (Γ n)

  field
    {-
      The typing judgment should respect substitutions
      which change contexts.
    -}
    tyChanges : ∀{σ Γ Δ e t} →
                Changes σ Γ Δ →
                Typing Γ e t →
                Typing Δ (sub e σ) t

  -- Deduced lemmas for convenience.

  -- The context is irrelevant when typing closed expressions.
  tyClosed : ∀{Γ Δ e t} → Closed e → Typing Γ e t → Typing Δ e t
  tyClosed closed Γ⊢e:t = tyClosedAbove closed (λ ()) Γ⊢e:t

  -- The context is irrelevant when typing values.
  tyVal : ∀{Γ Δ v t} → Val v → Typing Γ v t → Typing Δ v t
  tyVal val Γ⊢v:t = tyClosed (valClosed val) Γ⊢v:t

  -- The identity substitution changes any context to itself
  idSubChanges : (Γ : ℕ → Typ) → Changes idSub Γ Γ
  idSubChanges Γ n = tyVar Γ n

  -- The identity substitution respects typing
  ty-idSub : ∀{Γ e t} → Typing Γ e t → Typing Γ (sub e idSub) t
  ty-idSub Γ⊢e:t = tyChanges (idSubChanges _) Γ⊢e:t
