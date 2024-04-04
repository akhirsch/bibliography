{-# OPTIONS --safe #-}

open import Data.Empty
open import Data.Nat
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Function

open import Common
open import Locations

-- Module for expression-based local languages.
module LocalLang where

-- Syntax and semantics of a local language
record Language (L : Location) : Set₁ where
  open Location L

  infixr 6 _⇒ₑ_
  field
    -- Set of local expressions
    Expr : Set

    -- Expressions should have decidable equality
    ≡-dec-Expr : (e₁ e₂ : Expr) → Dec (e₁ ≡ e₂)

    -- de Bruijn indices are represented as natural numbers
    varₑ : ℕ → Expr
  
    -- Infinite variable renaming and substitution operators.
    renₑ : (ℕ → ℕ) → Expr → Expr
    subₑ : (ℕ → Expr) → Expr → Expr
      
    {-
      Expression closure predicate.
      An expression is closed above `n` if no variables above `n` appear free.
    -}
    ClosedAboveₑ : ℕ → Expr → Set
  
    -- Values of the language
    Valₑ : Expr → Set
  
    -- Small-step operational semantics
    _⇒ₑ_ : Expr → Expr → Set

    -- There should be expressions for true and false.
    ttₑ ffₑ : Expr

    -- There should be expressions for each location value.
    locₑ : LocVal → Expr

  -- Derived functions for convenience

  -- An expression is closed if it has no free variables.
  Closedₑ : Expr → Set
  Closedₑ e = ClosedAboveₑ 0 e

  -- Identity variable renaming.
  idRenₑ : ℕ → ℕ
  idRenₑ n = n

  -- Identity substitution.
  idSubₑ : ℕ → Expr
  idSubₑ n = varₑ n

  {-
    `up` construction on substitutions and variable renamings.
    Used when going past a binder to ensure that counting is done correctly.
  -}
  ↑σₑ : (ℕ → Expr) → ℕ → Expr
  ↑σₑ σ zero = varₑ zero
  ↑σₑ σ (suc n) = renₑ suc (σ n)

-- A local language that has extra "lawfulness" properties
record LawfulLanguage (L : Location) : Set₁ where
  open Location L

  field
    {{LL}} : Language L

  open Language LL public

  field
    -- Substitution should respect extensional equality.
    subExtₑ : ∀{σ1 σ2} → σ1 ≈ σ2 → subₑ σ1 ≈ subₑ σ2
    
    -- Substitution correctly replaces a variable
    subVarₑ : ∀ σ n → subₑ σ (varₑ n) ≡ σ n
    
    {-
      Treating a renaming as a substitution should have the same
      effect as using it directly as a renaming.
    -}
    subRenₑ : ∀ ξ e → subₑ (varₑ ∘ ξ) e ≡ renₑ ξ e
    
    -- Renaming enjoys fusion
    renFuseₑ : ∀ ξ1 ξ2 → renₑ (ξ1 ∘ ξ2) ≈ renₑ ξ1 ∘ renₑ ξ2
    
    -- Renaming respects the identity
    renIdₑ : ∀ e → renₑ idRenₑ e ≡ e
    
    -- Substituting respects the identity
    subIdₑ : ∀ e → subₑ idSubₑ e ≡ e

    -- The property of being closed above should be monotonic
    closedAboveMonoₑ : ∀{m n e} → m < n → ClosedAboveₑ m e → ClosedAboveₑ n e
    
    -- A de Bruijn index m is considered closed above n if n > m.
    <⇒varClosedₑ : ∀{m n} → m < n → ClosedAboveₑ n (varₑ m)
    
    -- If de Bruijn index m is closed above n then necessarily n > m.
    varClosedₑ⇒< : ∀{m n} → ClosedAboveₑ n (varₑ m) → m < n
    
    -- Values must have no free variables.
    valClosedₑ : ∀{v} → Valₑ v → Closedₑ v

    {-
      For an expression which is closed above `n`, substitution on σ
      which acts as the identity below `n` should have no effect.
    -}
    subClosedAboveIdₑ : ∀{e σ n} →
                     ClosedAboveₑ n e →
                     (∀{m} → m < n → σ m ≡ varₑ m) →
                     subₑ σ e ≡ e

    {- 
      Substitution, renaming, and stepping should not change the fact that expressions are
      closed above some level.
    -}
    subClosedAboveₑ : ∀{e σ m n} →
                     ClosedAboveₑ n e →
                     (∀{k} → k < n → ClosedAboveₑ m (σ k)) →
                     ClosedAboveₑ m (subₑ σ e)
    renClosedAboveₑ : ∀{e ξ m n} →
                     ClosedAboveₑ n e →
                     (∀{k} → k < n → ξ k < m) →
                     ClosedAboveₑ m (renₑ ξ e)
    stepClosedAboveₑ : ∀{e₁ e₂ n} → e₁ ⇒ₑ e₂ → ClosedAboveₑ n e₁ → ClosedAboveₑ n e₂

    -- Values cannot step.
    valNoStepₑ : ∀{v e} → Valₑ v → ¬ (v ⇒ₑ e)

    -- True and false are disequal values.
    ttValₑ : Valₑ ttₑ
    ffValₑ : Valₑ ffₑ
    ttₑ≠ffₑ : ¬ (ttₑ ≡ ffₑ)

    -- Location literals are unique values.
    locValₑ : (L : LocVal) → Valₑ (locₑ L)
    locₑ-inj : ∀{L1 L2} → locₑ L1 ≡ locₑ L2 → L1 ≡ L2

  -- Deduced lemmas for convenience.

  -- Renaming respects extensional equality.
  renExtₑ : ∀{ξ1 ξ2} → ξ1 ≈ ξ2 → renₑ ξ1 ≈ renₑ ξ2
  renExtₑ {ξ1} {ξ2} ξ1≈ξ2 e =
    renₑ ξ1 e          ≡⟨ sym (subRenₑ ξ1 e) ⟩
    subₑ (varₑ ∘ ξ1) e ≡⟨ subExtₑ (λ n → cong varₑ (ξ1≈ξ2 n)) e ⟩
    subₑ (varₑ ∘ ξ2) e ≡⟨ subRenₑ ξ2 e ⟩
    renₑ ξ2 e          ∎

  -- Renaming correctly replaces a variable.
  renVarₑ : ∀ ξ n → renₑ ξ (varₑ n) ≡ varₑ (ξ n)
  renVarₑ ξ n =
    renₑ ξ (varₑ n)          ≡⟨ sym (subRenₑ ξ (varₑ n)) ⟩
    subₑ (varₑ ∘ ξ) (varₑ n) ≡⟨ subVarₑ (varₑ ∘ ξ) n ⟩
    varₑ (ξ n)               ∎

  -- ↑ respects extensional equality
  ↑σExtₑ : ∀{σ1 σ2} → σ1 ≈ σ2 → ↑σₑ σ1 ≈ ↑σₑ σ2
  ↑σExtₑ σ1≈σ2 zero = refl
  ↑σExtₑ σ1≈σ2 (suc n) = cong (renₑ suc) (σ1≈σ2 n)

  -- ↑ respects the identity
  ↑σIdₑ : ↑σₑ idSubₑ ≈ idSubₑ
  ↑σIdₑ zero = refl
  ↑σIdₑ (suc n) = renVarₑ suc n

  -- Substituting a closed expression has no effect.
  subClosedIdₑ : ∀ σ e → Closedₑ e → subₑ σ e ≡ e
  subClosedIdₑ e σ closed = subClosedAboveIdₑ closed λ{ () }

  -- Stepping a closed expression remains closed.
  stepClosedₑ : ∀{e₁ e₂} → e₁ ⇒ₑ e₂ → Closedₑ e₁ → Closedₑ e₂
  stepClosedₑ e₁⇒e₂ closed = stepClosedAboveₑ e₁⇒e₂ closed