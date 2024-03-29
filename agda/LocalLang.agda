{-# OPTIONS --safe #-}

open import Data.Empty
open import Data.Nat
open import Data.Maybe
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Function

open import Common
open import Locations

-- Module for expression-based local languages.
module LocalLang where

-- Syntax and semantics of a local language
record Language
  (L : Location) : Set₁ where
  open Location L

  infixr 6 _⇒ₑ_
  field
    -- Set of local expressions
    Expr : Set

    -- Expressions should have decidable equality
    ≡-dec-Expr : (e₁ e₂ : Expr) → Dec (e₁ ≡ e₂)

    -- de Bruijn indices are represented as natural numbers
    varₑ : ℕ → Expr
  
    -- Infinite variable renaming and substitution operators
    renₑ : Expr → (ℕ → ℕ) → Expr
    subₑ : Expr → (ℕ → Expr) → Expr

    -- Partial variable renaming operator
    renMaybeₑ : Expr → (ℕ → Maybe ℕ) → Maybe Expr

    -- Partial substitution operator
    subMaybeₑ : Expr → (ℕ → Maybe Expr) → Maybe Expr
      
    {-
      Expression closure predicate.
      An expression is closed above `n` if no variables above `n` appear free
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

  -- Identity substitution.
  idSubₑ : ℕ → Expr
  idSubₑ n = varₑ n

  -- Substitution with the topmost variable instantiated
  _▸ₑ_ : (ℕ → Expr) → Expr → ℕ → Expr
  (σ ▸ₑ e) zero = e
  (σ ▸ₑ e) (suc n) = σ n

  -- Adding a topmost term respects extensional equality
  ▸Extₑ : ∀{σ1 σ2} → σ1 ≈ σ2 →
          ∀ e → σ1 ▸ₑ e ≈ σ2 ▸ₑ e
  ▸Extₑ σ1≈σ2 e zero = refl
  ▸Extₑ σ1≈σ2 e (suc n) = σ1≈σ2 n

  {-
    `up` construction on substitutions and variable renamings.
    Used when going past a binder to ensure that index counting is done correctly.
  -}
  ↑σₑ : (ℕ → Expr) → ℕ → Expr
  ↑σₑ σ = (λ n → renₑ (σ n) suc) ▸ₑ varₑ zero

  -- ↑ respects extensional equality
  ↑σExt : ∀{σ1 σ2} → σ1 ≈ σ2 → ↑σₑ σ1 ≈ ↑σₑ σ2
  ↑σExt σ1≈σ2 = ▸Extₑ (λ n → cong₂ renₑ (σ1≈σ2 n) refl) (varₑ zero)

  -- Inclusion from renamings to substitutions
  ιₑ : (ℕ → ℕ) → ℕ → Expr
  ιₑ ξ n = varₑ (ξ n)


-- A local language that has extra "lawfulness" properties
record LawfulLanguage
  (L : Location)
  (E : Language L) : Set₁ where
  open Location L
  open Language E

  field
    -- Substitution should respect extensional equality.
    subExtₑ : ∀{σ₁ σ₂} → (∀ n → σ₁ n ≡ σ₂ n) → ∀ e → subₑ e σ₁ ≡ subₑ e σ₂
    
    -- Substitution correctly replaces variables
    subVarₑ : ∀ n σ → subₑ (varₑ n) σ ≡ σ n
    
    -- Substitution respects the inclusion from renamings
    subRenₑ : ∀ ξ e → subₑ e (varₑ ∘ ξ) ≡ renₑ e ξ
    
    -- Renaming enjoys fusion
    renFuseₑ : ∀ ξ₁ ξ₂ e → renₑ e (ξ₂ ∘ ξ₁) ≡ renₑ (renₑ e ξ₁) ξ₂
    
    -- Renaming respects the identity
    renIdₑ : ∀ e → renₑ e idRen ≡ e
    
    -- Substituting respects the identity
    subIdₑ : ∀ e → subₑ e idSubₑ ≡ e

    -- Partial substitution respects the inclusion from renamings
    subMaybeRenₑ : ∀ ξ e → subMaybeₑ e (map varₑ ∘ ξ) ≡ renMaybeₑ e ξ

    -- Partial renaming correctly replaces variables
    renMaybeVarₑ : ∀ n ξ → renMaybeₑ (varₑ n) ξ ≡ map varₑ (ξ n)

    -- On fully-defined renamings, partial renaming should act as normal renaming
    renMaybeJustₑ : ∀ ξ e → renMaybeₑ e (just ∘ ξ) ≡ just (renₑ e ξ)

    -- On fully-defined substitutions, partial substitution should act as normal substitution
    subMaybeJustₑ : ∀ σ e → subMaybeₑ e (just ∘ σ) ≡ just (subₑ e σ)

    -- Partial renaming respects extensional equality
    renMaybeExtₑ : ∀{ξ1 ξ2} → ξ1 ≈ ξ2 → ∀ e → renMaybeₑ e ξ1 ≡ renMaybeₑ e ξ2

    -- Partial renaming is monotone with respect to definedness
    renMaybeMonoₑ : ∀{ξ1 ξ2} →
                    (∀ x → ξ1 x ≲ ξ2 x) →
                    ∀ e → renMaybeₑ e ξ1 ≲ renMaybeₑ e ξ2

    -- Partial renaming enjoys fusion
    renMaybeFuseₑ : ∀ ξ1 ξ2 e → renMaybeₑ e (λ x → maybe ξ2 nothing (ξ1 x)) ≡
                                maybe (λ e' → renMaybeₑ e' ξ2) nothing (renMaybeₑ e ξ1)

    -- The property of being closed above should be monotonic
    closedAboveMonoₑ : ∀{m n e} → m < n → ClosedAboveₑ m e → ClosedAboveₑ n e
    
    -- A de Bruijn index m is considered closed above n if n > m
    <⇒varClosedₑ : ∀{m n} → m < n → ClosedAboveₑ n (varₑ m)
    
    -- If de Bruijn index m is closed above n then necessarily n > m
    varClosedₑ⇒< : ∀{m n} → ClosedAboveₑ n (varₑ m) → m < n
    
    -- Values must have no free variables
    valClosedₑ : ∀{v} → Valₑ v → Closedₑ v

    {-
      For an expression which is closed above `n`, substitution respects
      extensional equality of substitutions which are equal below `n`.
    -}
    subClosedAboveExtₑ : ∀{e σ1 σ2 n} →
                         ClosedAboveₑ n e →
                         (∀{m} → m < n → σ1 m ≡ σ2 m) →
                         subₑ e σ1 ≡ subₑ e σ2

    subMaybeClosedAboveExtₑ : ∀{e σ1 σ2 n} →
                              ClosedAboveₑ n e →
                              (∀{m} → m < n → σ1 m ≲ σ2 m) →
                              subMaybeₑ e σ1 ≲ subMaybeₑ e σ2

    {- 
      Substitution, renaming, and stepping should not change
      the fact that expressions are closed above some level.
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

    {-
      If a partial operation is defined for all k < n,
      then then applying it to an expression closed above
      n must be defined.
    -}
    renMaybeClosedAboveₑ : ∀{e ξ n} →
                           ClosedAboveₑ n e →
                           (∀{k} → k < n → ↓ (ξ k)) →
                           ↓ (renMaybeₑ e ξ)
    subMaybeClosedAboveₑ : ∀{e σ n} →
                          ClosedAboveₑ n e →
                          (∀{k} → k < n → ↓ (σ k)) →
                          ↓ (subMaybeₑ e σ)

    -- Values cannot step.
    valNoStepₑ : ∀{v e} → Valₑ v → ¬ (v ⇒ₑ e)

    -- True and false are disequal values.
    ttValₑ : Valₑ ttₑ
    ffValₑ : Valₑ ffₑ
    ttₑ≠ffₑ : ¬ (ttₑ ≡ ffₑ)

    -- Location literals are unique values.
    locValₑ : (L : LocVal) → Valₑ (locₑ L)
    locₑ-inj : ∀{L1 L2} → locₑ L1 ≡ locₑ L2 → L1 ≡ L2

  -- Deduced lemmas for convenience

  -- True and false are closed
  ttClosedₑ : Closedₑ ttₑ
  ttClosedₑ = valClosedₑ ttValₑ

  ffClosedₑ : Closedₑ ffₑ
  ffClosedₑ = valClosedₑ ffValₑ

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
    varₑ (ξ n)               ∎

  -- ↑σ respects the identity
  ↑σIdₑ : ↑σₑ idSubₑ ≈ idSubₑ
  ↑σIdₑ zero = refl
  ↑σIdₑ (suc n) = renVarₑ n suc

  renClosedAboveExtₑ : ∀{e ξ1 ξ2 n} →
                      ClosedAboveₑ n e →
                      (∀{m} → m < n → ξ1 m ≡ ξ2 m) →
                      renₑ e ξ1 ≡ renₑ e ξ2
  renClosedAboveExtₑ {e} {ξ1} {ξ2} closed ξ1≈ξ2 =
    renₑ e ξ1          ≡⟨ sym (subRenₑ ξ1 e) ⟩
    subₑ e (varₑ ∘ ξ1) ≡⟨ subClosedAboveExtₑ closed (λ m<n → cong varₑ (ξ1≈ξ2 m<n)) ⟩
    subₑ e (varₑ ∘ ξ2) ≡⟨ subRenₑ ξ2 e ⟩
    renₑ e ξ2 ∎

  renMaybeClosedAboveExtₑ : ∀{e ξ1 ξ2 n} →
                            ClosedAboveₑ n e →
                            (∀{m} → m < n → ξ1 m ≲ ξ2 m) →
                            renMaybeₑ e ξ1 ≲ renMaybeₑ e ξ2
  renMaybeClosedAboveExtₑ {e} {ξ1} {ξ2} {n} closed ξ1≲ξ2 = e⟨ξ1⟩≲e⟨ξ2⟩
    where
    varₑ∘ξ1≲varₑ∘ξ2 : ∀{m} → m < n → map varₑ (ξ1 m) ≲ map varₑ (ξ2 m)
    varₑ∘ξ1≲varₑ∘ξ2 m<n = ≲-cong varₑ (ξ1≲ξ2 m<n)

    e⟨var∘ξ1⟩≲e⟨var∘ξ2⟩ : subMaybeₑ e (map varₑ ∘ ξ1) ≲ subMaybeₑ e (map varₑ ∘ ξ2)
    e⟨var∘ξ1⟩≲e⟨var∘ξ2⟩ = subMaybeClosedAboveExtₑ closed varₑ∘ξ1≲varₑ∘ξ2

    e⟨ξ1⟩≲e⟨ξ2⟩ : renMaybeₑ e ξ1 ≲ renMaybeₑ e ξ2
    e⟨ξ1⟩≲e⟨ξ2⟩ = subst₂ _≲_ (subMaybeRenₑ ξ1 e) (subMaybeRenₑ ξ2 e) e⟨var∘ξ1⟩≲e⟨var∘ξ2⟩

  subClosedAboveIdₑ : ∀{e σ n} →
                      ClosedAboveₑ n e →
                      (∀{m} → m < n → σ m ≡ varₑ m) →
                      subₑ e σ ≡ e
  subClosedAboveIdₑ {e} {σ} closed σ≈var =
    subₑ e σ    ≡⟨ subClosedAboveExtₑ closed σ≈var ⟩
    subₑ e varₑ ≡⟨ subIdₑ e ⟩
    e           ∎

  renClosedAboveIdₑ : ∀{e ξ n} →
                      ClosedAboveₑ n e →
                      (∀{m} → m < n → ξ m ≡ m) →
                      renₑ e ξ ≡ e
  renClosedAboveIdₑ {e} {ξ} closed ξ≈Id =
    renₑ e ξ     ≡⟨ renClosedAboveExtₑ closed ξ≈Id ⟩
    renₑ e idRen ≡⟨ renIdₑ e ⟩
    e            ∎

  -- Substituting a closed expression has no effect
  subClosedIdₑ : ∀ e σ → Closedₑ e → subₑ e σ ≡ e
  subClosedIdₑ e σ closed = subClosedAboveIdₑ closed (λ ())

  -- Partial renaming of a closed expression has no effect
  renMaybeClosedₑ : ∀ e ξ  → Closedₑ e → renMaybeₑ e ξ ≡ just e
  renMaybeClosedₑ e ξ closed =
    renMaybeₑ e ξ              ≡⟨ sym (e⟨id⟩≡e⟨ξ⟩) ⟩
    renMaybeₑ e (just ∘ idRen) ≡⟨ renMaybeJustₑ idRen e ⟩
    just (renₑ e idRen)        ≡⟨ cong just (renIdₑ e) ⟩
    just e                     ∎
    where
    e⟨id⟩≲e⟨ξ⟩ : renMaybeₑ e (just ∘ idRen) ≲ renMaybeₑ e ξ
    e⟨id⟩≲e⟨ξ⟩ = renMaybeClosedAboveExtₑ closed (λ ())

    ↓e⟨ξ⟩ : ↓ (renMaybeₑ e ξ)
    ↓e⟨ξ⟩ = renMaybeClosedAboveₑ {ξ = ξ} closed (λ ())

    e⟨id⟩≡e⟨ξ⟩ : renMaybeₑ e (just ∘ idRen) ≡ renMaybeₑ e ξ
    e⟨id⟩≡e⟨ξ⟩ = ≲↓⇒≡ e⟨id⟩≲e⟨ξ⟩ ↓e⟨ξ⟩
  
  -- Partial substitution of a closed expression has no effect
  subMaybeClosedₑ : ∀ e σ → Closedₑ e → subMaybeₑ e σ ≡ just e
  subMaybeClosedₑ e σ closed =
    subMaybeₑ e σ              ≡⟨ sym (e⟨id⟩≡e⟨σ⟩) ⟩
    subMaybeₑ e (just ∘ varₑ)  ≡⟨ subMaybeJustₑ varₑ e ⟩
    just (subₑ e varₑ)         ≡⟨ cong just (subIdₑ e) ⟩
    just e                     ∎
    where
    e⟨id⟩≲e⟨σ⟩ : subMaybeₑ e (just ∘ varₑ) ≲ subMaybeₑ e σ
    e⟨id⟩≲e⟨σ⟩ = subMaybeClosedAboveExtₑ closed (λ ())

    ↓e⟨σ⟩ : ↓ (subMaybeₑ e σ)
    ↓e⟨σ⟩ = subMaybeClosedAboveₑ {σ = σ} closed (λ ())

    e⟨id⟩≡e⟨σ⟩ : subMaybeₑ e (just ∘ varₑ) ≡ subMaybeₑ e σ
    e⟨id⟩≡e⟨σ⟩ = ≲↓⇒≡ e⟨id⟩≲e⟨σ⟩ ↓e⟨σ⟩

  -- Stepping a closed expression remains closed.
  stepClosedₑ : ∀{e₁ e₂} → e₁ ⇒ₑ e₂ → Closedₑ e₁ → Closedₑ e₂
  stepClosedₑ e₁⇒e₂ closed = stepClosedAboveₑ e₁⇒e₂ closed

  -- Fusion first with a total renaming and then a partial renaming
  renMaybeRenFuseₑ : ∀ ξ1 ξ2 e →
                     renMaybeₑ (renₑ e ξ1) ξ2 ≡
                     renMaybeₑ e (ξ2 ∘ ξ1)
  renMaybeRenFuseₑ ξ1 ξ2 e = 
    renMaybeₑ (renₑ e ξ1) ξ2
      ≡⟨ refl ⟩
    maybe′ (λ x → renMaybeₑ x ξ2) nothing (just (renₑ e ξ1))
      ≡⟨  cong (maybe′ (λ x → renMaybeₑ x ξ2) nothing) (sym (renMaybeJustₑ ξ1 e)) ⟩
    maybe′ (λ x → renMaybeₑ x ξ2) nothing (renMaybeₑ e (just ∘ ξ1))
      ≡⟨ sym (renMaybeFuseₑ (just ∘ ξ1) ξ2 e) ⟩
    renMaybeₑ e (ξ2 ∘ ξ1)    ∎

  -- Fusion first with a partial renaming and then a total renaming
  renMaybeFuseRenₑ  : ∀ ξ1 ξ2 e →
                      map (λ x → renₑ x ξ2) (renMaybeₑ e ξ1) ≡
                      renMaybeₑ e (map ξ2 ∘ ξ1)
  renMaybeFuseRenₑ ξ1 ξ2 e = 
    map (λ x → renₑ x ξ2) (renMaybeₑ e ξ1)
      ≡⟨ maybe-ext (λ x → sym (renMaybeJustₑ ξ2 x)) nothing (renMaybeₑ e ξ1) ⟩
    maybe′ (λ x → renMaybeₑ x (just ∘ ξ2)) nothing (renMaybeₑ e ξ1)
      ≡⟨ sym (renMaybeFuseₑ ξ1 (just ∘ ξ2) e) ⟩
    renMaybeₑ e (map ξ2 ∘ ξ1) ∎

  -- ↑ respects the inclusion
  ↑σιₑ : ∀ ξ → ↑σₑ (ιₑ ξ) ≈ ιₑ (↑ ξ)
  ↑σιₑ ξ zero = refl 
  ↑σιₑ ξ (suc n) = renVarₑ (ξ n) suc
