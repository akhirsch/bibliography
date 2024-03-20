{-# OPTIONS --safe --without-K #-}

open import Data.Empty
open import Data.Nat
open import Data.Sum
open import Data.Product
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
    TypExpr : Set

    -- Types should have decidable equality
    ≡-dec-TypExpr : (t₁ t₂ : TypExpr) → Dec (t₁ ≡ t₂)

    {-
      Typing judgment of the form Γ ⊢ e : t.
      Contexts are infinite maps from variables to types.
    -}
    _⊢ₑ_∶_ : (ℕ → TypExpr) → Expr → TypExpr → Set

    -- Typing respects extensional equality of contexts.
    tyExprExt : ∀{Γ Δ e t} →
            (∀ n → Γ n ≡ Δ n) →
            Γ ⊢ₑ e ∶ t →
            Δ ⊢ₑ e ∶ t

    -- Variables have the type they are assigned by the context.
    tyExprVar : ∀ Γ n → Γ ⊢ₑ varExpr n ∶ Γ n

    -- Expressions have a unique type.
    tyExprUniq : ∀{Γ e t₁ t₂} →
             Γ ⊢ₑ e ∶ t₁ →
             Γ ⊢ₑ e ∶ t₂ →
             t₁ ≡ t₂

    {-
      The typing judgment should only take into account the free
      variables in an expression. Thus, if an expression is closed
      above n, the values of the context above n should not matter.
    -}
    tyExprClosedAbove : ∀{Γ Δ e t n} →
                    ClosedAboveExpr n e →
                    (∀{m} → m < n → Γ m ≡ Δ m) →
                    Γ ⊢ₑ e ∶ t →
                    Δ ⊢ₑ e ∶ t

    -- Weaking should be allowed.
    tyExprWk : ∀{Γ Δ e t} →
           (ξ : ℕ → ℕ) →
           (∀ n → Γ n ≡ Δ (ξ n)) →
           Γ ⊢ₑ e ∶ t →
           Δ ⊢ₑ renExpr e ξ ∶ t

    -- We have a type for booleans, and the appropriate judgments.
    boolTy : TypExpr
    tyExprTrue : ∀{Γ} → Γ ⊢ₑ trueExpr ∶ boolTy
    tyExprFalse : ∀{Γ} → Γ ⊢ₑ falseExpr ∶ boolTy

    -- Each boolean value is either true or false
    boolInversion : ∀{Γ v} →
                    Γ ⊢ₑ v ∶ boolTy →
                    ValExpr v →
                    (v ≡ trueExpr) ⊎ (v ≡ falseExpr)
  


    -- Progress and preservation must hold.
    preservationExpr : ∀{Γ e₁ e₂ t} →
                   Γ ⊢ₑ e₁ ∶ t →
                   StepExpr e₁ e₂ →
                   Γ ⊢ₑ e₂ ∶ t

    progressExpr : ∀{Γ e₁ t} →
               Γ ⊢ₑ e₁ ∶ t →
               ClosedExpr e₁ →
               (ValExpr e₁) ⊎ Σ[ e₂ ∈ _ ] StepExpr e₁ e₂

  {-
    A substitution σ changes context Γ to context Δ
    if for every variable n, σ assigns n to an expression
    which, under Δ, has the same type that Γ assigns to n.
  -}
  ChangesExpr : (ℕ → Expr) → (ℕ → TypExpr) → (ℕ → TypExpr) → Set
  ChangesExpr σ Γ Δ = ∀ n → Δ ⊢ₑ σ n ∶ Γ n

  field
    {-
      The typing judgment should respect substitutions
      which change contexts.
    -}
    tyExprChanges : ∀{σ Γ Δ e t} →
                ChangesExpr σ Γ Δ →
                Γ ⊢ₑ e ∶ t →
                Δ ⊢ₑ subExpr e σ ∶ t

  -- Deduced lemmas for convenience.

  -- The context is irrelevant when typing closed expressions.
  tyExprClosed : ∀{Γ Δ e t} → ClosedExpr e → Γ ⊢ₑ e ∶ t → Δ ⊢ₑ e ∶ t
  tyExprClosed closed Γ⊢e:t = tyExprClosedAbove closed (λ ()) Γ⊢e:t

  -- The context is irrelevant when typing values.
  tyExprVal : ∀{Γ Δ v t} → ValExpr v → Γ ⊢ₑ v ∶ t → Δ ⊢ₑ v ∶ t
  tyExprVal val Γ⊢v:t = tyExprClosed (valClosedExpr val) Γ⊢v:t

  -- The identity substitution changes any context to itself
  idSubExprChanges : (Γ : ℕ → TypExpr) → ChangesExpr idSubExpr Γ Γ
  idSubExprChanges Γ n = tyExprVar Γ n

  -- The identity substitution respects typing
  tyExprSubId : ∀{Γ e t} → Γ ⊢ₑ e ∶ t → Γ ⊢ₑ subExpr e idSubExpr ∶ t
  tyExprSubId Γ⊢e:t = tyExprChanges (idSubExprChanges _) Γ⊢e:t
