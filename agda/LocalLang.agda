{-# OPTIONS --safe --without-K #-}

open import Data.Empty
open import Data.Nat
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Function

{-
Module for expression-based local languages.
-}
module LocalLang where

-- Syntax and semantics of a local language
record Language : Set₁ where
  field
    -- Set of expressions in the language
    Expr : Set

    -- Expressions should have decidable equality
    ≡-dec-Expr : (e₁ e₂ : Expr) → Dec (e₁ ≡ e₂)

    -- de Bruijn indices are represented as natural numbers
    varExpr : ℕ → Expr
  
    -- Infinite variable renaming and substitution operators.
    renExpr : Expr → (ℕ → ℕ) → Expr
    subExpr : Expr → (ℕ → Expr) → Expr
      
    {-
      Expression closure predicate.
      An expression is closed above `n` if no variables above `n` appear free.
    -}
    ClosedAboveExpr : ℕ → Expr → Set
  
    -- Values of the language
    ValExpr : Expr → Set
  
    -- Small-step operational semantics
    StepExpr : Expr → Expr → Set

    -- There should be expressions for true and false.
    trueExpr falseExpr : Expr

  -- Derived functions for convenience

  -- An expression is closed if it has no free variables.
  ClosedExpr : Expr → Set
  ClosedExpr e = ClosedAboveExpr 0 e

  -- Identity variable renaming.
  idRenExpr : ℕ → ℕ
  idRenExpr n = n

  -- Identity substitution.
  idSubExpr : ℕ → Expr
  idSubExpr n = varExpr n

  {-
    `up` construction on substitutions and variable renamings.
    Used when going past a binder to ensure that counting is done correctly.
  -}
  upSubExpr : (ℕ → Expr) → ℕ → Expr
  upSubExpr σ zero = varExpr zero
  upSubExpr σ (suc n) = renExpr (σ n) suc

  upRenExpr : (ℕ → ℕ) → ℕ → ℕ
  upRenExpr ξ zero = zero
  upRenExpr ξ (suc n) = suc (ξ n)

-- Necessary properties of a local language
record LawfulLanguage (L : Language) : Set where
  open Language L
  field
    -- Substitution should respect extensional equality of substitutions.
    subExtExpr : ∀{e σ₁ σ₂} → (∀ n → σ₁ n ≡ σ₂ n) → subExpr e σ₁ ≡ subExpr e σ₂
    
    -- Substitution correctly replaces a variable
    subVarExpr : ∀ n σ → subExpr (varExpr n) σ ≡ σ n
    
    {-
      Treating a renaming as a substitution should have the same
      effect as using it directly as a renaming.
    -}
    subRenExpr : ∀ e ξ → subExpr e (varExpr ∘ ξ) ≡ renExpr e ξ
    
    -- Renaming twice has the same effect as using the composed renaming.
    renExpr∘ : ∀ n ξ₁ ξ₂ → renExpr n (ξ₂ ∘ ξ₁) ≡ renExpr (renExpr n ξ₁) ξ₂
    
    -- Renaming on the identity should have no effect.
    renIdExpr : ∀ n → renExpr n idRenExpr ≡ n
    
    -- Substituting on the identity should have no effect.
    subIdExpr : ∀ e → subExpr e idSubExpr ≡ e

    -- The property of being closed above should be monotonic
    closedAboveMonoExpr : ∀{m n e} → m < n → ClosedAboveExpr m e → ClosedAboveExpr n e
    
    -- A de Bruijn index m is considered closed above n for any n > m.
    varClosedExpr₁ : ∀{m n} → m < n → ClosedAboveExpr n (varExpr m)
    
    -- If de Bruijn index m is closed above n then necessarily n > m.
    varClosedExpr₂ : ∀{m n} → ClosedAboveExpr n (varExpr m) → m < n
    
    -- Values must have no free variables.
    valClosedExpr : ∀{v} → ValExpr v → ClosedExpr v

    {-
      For an expression which is closed above `n`, substitution on σ
      which acts as the identity below `n` should have no effect.
    -}
    subClosedAboveIdExpr : ∀{e σ n} →
                     ClosedAboveExpr n e →
                     (∀{m} → m < n → σ m ≡ varExpr m) →
                     subExpr e σ ≡ e

    {- 
      Substitution, renaming, and stepping should not change the fact that expressions are
      closed above some level.
    -}
    subClosedAboveExpr : ∀{e σ m n} →
                     ClosedAboveExpr n e →
                     (∀{k} → k < n → ClosedAboveExpr m (σ k)) →
                     ClosedAboveExpr m (subExpr e σ)
    renClosedAboveExpr : ∀{e ξ m n} →
                     ClosedAboveExpr n e →
                     (∀{k} → k < n → ξ k < m) →
                     ClosedAboveExpr m (renExpr e ξ)
    stepClosedAboveExpr : ∀{e₁ e₂ n} → StepExpr e₁ e₂ → ClosedAboveExpr n e₁ → ClosedAboveExpr n e₂

    -- Values cannot step.
    valNoStepExpr : ∀{v e} → ValExpr v → ¬ (StepExpr v e)

    -- True and false are disequal values.
    ttVal : ValExpr trueExpr
    ffVal : ValExpr falseExpr
    boolSep : ¬ (trueExpr ≡ falseExpr)

  -- Deduced lemmas for convenience.

  -- Renaming correctly replaces a variable.
  renVarExpr : ∀ n ξ → renExpr (varExpr n) ξ ≡ varExpr (ξ n)
  renVarExpr n ξ = trans (sym (subRenExpr (varExpr n) ξ)) (subVarExpr n (varExpr ∘ ξ))

  -- The `up` construction should have no extensional effect on the identity substitution
  upSubIdExpr : ∀ n → upSubExpr idSubExpr n ≡ varExpr n
  upSubIdExpr zero = refl
  upSubIdExpr (suc n) = renVarExpr n suc

  -- The `up` construction should have no extensional effect on the identity renaming.
  upRenIdExpr : ∀ n → upRenExpr idRenExpr n ≡ n
  upRenIdExpr zero = refl
  upRenIdExpr (suc n) = refl

  -- Substituting a closed expression has no effect.
  subClosedIdExpr : ∀ e σ → ClosedExpr e → subExpr e σ ≡ e
  subClosedIdExpr e σ closed = subClosedAboveIdExpr closed λ{ () }

  -- Stepping a closed expression remains closed.
  stepClosedExpr : ∀{e₁ e₂} → StepExpr e₁ e₂ → ClosedExpr e₁ → ClosedExpr e₂
  stepClosedExpr e₁⇒e₂ closed = stepClosedAboveExpr e₁⇒e₂ closed
