{-# OPTIONS --safe --without-K #-}

open import Data.Empty
open import Data.Nat
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Function

{-
Module for expression-based local languages.
-}
module LocalLang where

-- Syntax and semantics of a local language
record Language : Set₁ where
  infixr 6 _⇒ₑ_
  field
    -- Set of expressions in the language
    Expr : Set

    -- Expressions should have decidable equality
    ≡-dec-Expr : (e₁ e₂ : Expr) → Dec (e₁ ≡ e₂)

    -- de Bruijn indices are represented as natural numbers
    varₑ : ℕ → Expr
  
    -- Infinite variable renaming and substitution operators.
    renₑ : Expr → (ℕ → ℕ) → Expr
    subₑ : Expr → (ℕ → Expr) → Expr
      
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
  upSubₑ : (ℕ → Expr) → ℕ → Expr
  upSubₑ σ zero = varₑ zero
  upSubₑ σ (suc n) = renₑ (σ n) suc

  upRenₑ : (ℕ → ℕ) → ℕ → ℕ
  upRenₑ ξ zero = zero
  upRenₑ ξ (suc n) = suc (ξ n)

-- Necessary properties of a local language
record LawfulLanguage (L : Language) : Set where
  open Language L
  field
    -- Substitution should respect extensional equality.
    subExtₑ : ∀{σ₁ σ₂} → (∀ n → σ₁ n ≡ σ₂ n) → ∀ e → subₑ e σ₁ ≡ subₑ e σ₂
    
    -- Substitution correctly replaces a variable
    subVarₑ : ∀ n σ → subₑ (varₑ n) σ ≡ σ n
    
    {-
      Treating a renaming as a substitution should have the same
      effect as using it directly as a renaming.
    -}
    subRenₑ : ∀ ξ e → subₑ e (varₑ ∘ ξ) ≡ renₑ e ξ
    
    -- Renaming enjoys fusion
    ren∘ₑ : ∀ ξ₁ ξ₂ e → renₑ e (ξ₂ ∘ ξ₁) ≡ renₑ (renₑ e ξ₁) ξ₂
    
    -- Renaming respects the identity
    renIdₑ : ∀ e → renₑ e idRenₑ ≡ e
    
    -- Substituting respects the identity
    subIdₑ : ∀ e → subₑ e idSubₑ ≡ e

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
                     subₑ e σ ≡ e

    {- 
      Substitution, renaming, and stepping should not change the fact that expressions are
      closed above some level.
    -}
    subClosedAboveₑ : ∀{e σ m n} →
                     ClosedAboveₑ n e →
                     (∀{k} → k < n → ClosedAboveₑ m (σ k)) →
                     ClosedAboveₑ m (subₑ e σ)
    renClosedAboveₑ : ∀{e ξ m n} →
                     ClosedAboveₑ n e →
                     (∀{k} → k < n → ξ k < m) →
                     ClosedAboveₑ m (renₑ e ξ)
    stepClosedAboveₑ : ∀{e₁ e₂ n} → e₁ ⇒ₑ e₂ → ClosedAboveₑ n e₁ → ClosedAboveₑ n e₂

    -- Values cannot step.
    valNoStepₑ : ∀{v e} → Valₑ v → ¬ (v ⇒ₑ e)

    -- True and false are disequal values.
    ttValₑ : Valₑ ttₑ
    ffValₑ : Valₑ ffₑ
    ttₑ≠ffₑ : ¬ (ttₑ ≡ ffₑ)

  -- Deduced lemmas for convenience.

  -- Renaming respects extensional equality.
  renExtₑ : ∀{ξ1 ξ2} → (∀ n → ξ1 n ≡ ξ2 n) → ∀ e → renₑ e ξ1 ≡ renₑ e ξ2
  renExtₑ {ξ1} {ξ2} ξ1≈ξ2 e =
    renₑ e ξ1          ≡⟨ sym (subRenₑ ξ1 e) ⟩
    subₑ e (varₑ ∘ ξ1) ≡⟨ subExtₑ (λ n → cong varₑ (ξ1≈ξ2 n)) e ⟩
    subₑ e (varₑ ∘ ξ2) ≡⟨ subRenₑ ξ2 e ⟩
    renₑ e ξ2          ∎

  -- Renaming correctly replaces a variable.
  renVarₑ : ∀ n ξ → renₑ (varₑ n) ξ ≡ varₑ (ξ n)
  renVarₑ n ξ =
    renₑ (varₑ n) ξ          ≡⟨ sym (subRenₑ ξ (varₑ n)) ⟩
    subₑ (varₑ n) (varₑ ∘ ξ) ≡⟨ subVarₑ n (varₑ ∘ ξ) ⟩
    varₑ (ξ n)              ∎

  -- The `up` construction should have no extensional effect on the identity substitution
  upSubIdₑ : ∀ n → upSubₑ idSubₑ n ≡ varₑ n
  upSubIdₑ zero = refl
  upSubIdₑ (suc n) = renVarₑ n suc

  -- The `up` construction should respect extensional equality.
  upRenExtₑ : ∀{ξ1 ξ2} →
              (∀ n → ξ1 n ≡ ξ2 n) →
              ∀ n → upRenₑ ξ1 n ≡ upRenₑ ξ2 n
  upRenExtₑ ξ1≈ξ2 zero = refl
  upRenExtₑ ξ1≈ξ2 (suc n) = cong suc (ξ1≈ξ2 n)

  -- The `up` construction should have no extensional effect on the identity renaming.
  upRenIdₑ : ∀ n → upRenₑ idRenₑ n ≡ n
  upRenIdₑ zero = refl
  upRenIdₑ (suc n) = refl

  -- The `up` construction extensionally commutes with composition.
  upRen∘ₑ : ∀ ξ1 ξ2 n → upRenₑ (ξ2 ∘ ξ1) n ≡ upRenₑ ξ2 (upRenₑ ξ1 n)
  upRen∘ₑ ξ1 ξ2 zero = refl
  upRen∘ₑ ξ1 ξ2 (suc n) = refl
    
  -- Substituting a closed expression has no effect.
  subClosedIdₑ : ∀ e σ → Closedₑ e → subₑ e σ ≡ e
  subClosedIdₑ e σ closed = subClosedAboveIdₑ closed λ{ () }

  -- Stepping a closed expression remains closed.
  stepClosedₑ : ∀{e₁ e₂} → e₁ ⇒ₑ e₂ → Closedₑ e₁ → Closedₑ e₂
  stepClosedₑ e₁⇒e₂ closed = stepClosedAboveₑ e₁⇒e₂ closed
