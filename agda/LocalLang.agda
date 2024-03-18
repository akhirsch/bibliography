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

_∙_ : ∀{ℓ} {A : Set ℓ} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
p ∙ q = trans p q

-- Syntax and semantics of a local language
record Language : Set₁ where
  field
    -- Set of expressions in the language
    Expr : Set

    -- Expressions should have decidable equality
    decEq : (e₁ e₂ : Expr) → Dec (e₁ ≡ e₂)

    -- de Bruijn indices are represented as natural numbers
    var : ℕ → Expr
  
    -- Infinite variable renaming and substitution operators.
    ren : Expr → (ℕ → ℕ) → Expr
    sub : Expr → (ℕ → Expr) → Expr
      
    {-
      Expression closure predicate.
      An expression is closed above `n` if no variables above `n` appear free.
    -}
    ClosedAbove : ℕ → Expr → Set
  
    -- Values of the language
    Val : Expr → Set
  
    -- Small-step operational semantics
    Step : Expr → Expr → Set

    -- There should be expressions for true and false.
    tt ff : Expr

  -- Derived functions for convenience

  -- An expression is closed if it has no free variables.
  Closed : Expr → Set
  Closed e = ClosedAbove 0 e

  -- Identity variable renaming.
  idRen : ℕ → ℕ
  idRen n = n

  -- Identity substitution.
  idSub : ℕ → Expr
  idSub n = var n

  {-
    `up` construction on substitutions and variable renamings.
    Used when going past a binder to ensure that counting is done correctly.
  -}
  upSub : (ℕ → Expr) → ℕ → Expr
  upSub σ zero = var zero
  upSub σ (suc n) = ren (σ n) suc

  upRen : (ℕ → ℕ) → ℕ → ℕ
  upRen ξ zero = zero
  upRen ξ (suc n) = suc (ξ n)

-- Necessary properties of a local language
record LawfulLanguage (L : Language) : Set where
  open Language L
  field
    -- Substitution should respect extensional equality of substitutions.
    subExt : ∀{e σ₁ σ₂} → (∀ n → σ₁ n ≡ σ₂ n) → sub e σ₁ ≡ sub e σ₂
    
    -- Substitution correctly replaces a variable
    subVar : ∀ n σ → sub (var n) σ ≡ σ n
    
    {-
      Treating a renaming as a substitution should have the same
      effect as using it directly as a renaming.
    -}
    subRen : ∀ e ξ → sub e (var ∘ ξ) ≡ ren e ξ
    
    -- Renaming twice has the same effect as using the composed renaming.
    ren∘ : ∀ n ξ₁ ξ₂ → ren n (ξ₂ ∘ ξ₁) ≡ ren (ren n ξ₁) ξ₂
    
    -- Renaming on the identity should have no effect.
    renId : ∀ n → ren n idRen ≡ n
    
    -- Substituting on the identity should have no effect.
    subId : ∀ e → sub e idSub ≡ e

    -- The property of being closed above should be monotonic
    closedAboveMono : ∀{m n e} → m < n → ClosedAbove m e → ClosedAbove n e
    
    -- A de Bruijn index m is considered closed above n for any n > m.
    varClosed₁ : ∀{m n} → m < n → ClosedAbove n (var m)
    
    -- If de Bruijn index m is closed above n then necessarily n > m.
    varClosed₂ : ∀{m n} → ClosedAbove n (var m) → m < n
    
    -- Values must have no free variables.
    valClosed : ∀{v} → Val v → Closed v

    {-
      For an expression which is closed above `n`, substitution on σ
      which acts as the identity below `n` should have no effect.
    -}
    subClosedAboveId : ∀{e σ n} →
                     ClosedAbove n e →
                     (∀{m} → m < n → σ m ≡ var m) →
                     sub e σ ≡ e

    {- 
      Substitution, renaming, and stepping should not change the fact that expressions are
      closed above some level.
    -}
    subClosedAbove : ∀{e σ m n} →
                     ClosedAbove n e →
                     (∀{k} → k < n → ClosedAbove m (σ k)) →
                     ClosedAbove m (sub e σ)
    renClosedAbove : ∀{e ξ m n} →
                     ClosedAbove n e →
                     (∀{k} → k < n → ξ k < m) →
                     ClosedAbove m (ren e ξ)
    stepClosedAbove : ∀{e₁ e₂ n} → Step e₁ e₂ → ClosedAbove n e₁ → ClosedAbove n e₂

    -- Values cannot step.
    valNoStep : ∀{v e} → Val v → ¬ (Step v e)

    -- True and false are disequal values.
    ttVal : Val tt
    ffVal : Val ff
    boolSep : ¬ (tt ≡ ff)

  -- Deduced lemmas for convenience.

  -- Renaming correctly replaces a variable.
  renVar : ∀ n ξ → ren (var n) ξ ≡ var (ξ n)
  renVar n ξ = sym (subRen (var n) ξ) ∙ subVar n (var ∘ ξ)

  -- The `up` construction on substitutions should have no extensional effect.
  upSubId : ∀ n → upSub idSub n ≡ var n
  upSubId zero = refl
  upSubId (suc n) = renVar n suc

  -- The `up` construction on renamings should have no extensional effect.
  upRenId : ∀ n → upRen idRen n ≡ n
  upRenId zero = refl
  upRenId (suc n) = refl

  -- Substituting a closed expression has no effect.
  subClosedId : ∀ e σ → Closed e → sub e σ ≡ e
  subClosedId e σ closed = subClosedAboveId closed λ{ () }

  -- Stepping a closed expression remains closed.
  stepClosed : ∀{e₁ e₂} → Step e₁ e₂ → Closed e₁ → Closed e₂
  stepClosed e₁⇒e₂ closed = stepClosedAbove e₁⇒e₂ closed
