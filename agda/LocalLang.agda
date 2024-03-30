{-# OPTIONS --safe #-}

open import Data.Empty
open import Data.Nat
open import Data.Maybe
open import Data.Maybe.Properties
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
  
    -- Partial variable renaming and substitution operators
    renMaybeₑ : (ℕ → Maybe ℕ) → Expr → Maybe Expr
    subMaybeₑ : (ℕ → Maybe Expr) → Expr → Maybe Expr

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

  -- Partial substitution with the topmost variable instantiated
  _?▸ₑ_ : (ℕ → Maybe Expr) → Maybe Expr → ℕ → Maybe Expr
  (σ ?▸ₑ e) zero = e
  (σ ?▸ₑ e) (suc n) = σ n

  -- Adding a topmost term respects extensional equality
  ?▸Extₑ : ∀{σ1 σ2} → σ1 ≈ σ2 →
           ∀ e → σ1 ?▸ₑ e ≈ σ2 ?▸ₑ e
  ?▸Extₑ σ1≈σ2 e zero = refl
  ?▸Extₑ σ1≈σ2 e (suc n) = σ1≈σ2 n

  -- ↑ on partial substitutions
  ↑?σₑ : (ℕ → Maybe Expr) → ℕ → Maybe Expr
  ↑?σₑ σ = (renMaybeₑ (just ∘ suc) <=< σ) ?▸ₑ just (varₑ zero)

  -- ↑ respects extensional equality
  ↑?σExt : ∀{σ1 σ2} → σ1 ≈ σ2 → ↑?σₑ σ1 ≈ ↑?σₑ σ2
  ↑?σExt σ1≈σ2 = ?▸Extₑ (<=<-ext ≈-refl σ1≈σ2) (just (varₑ zero))

  -- Inclusion from partial renamings to partial substitutions
  ?ιₑ : (ℕ → Maybe ℕ) → ℕ → Maybe Expr
  ?ιₑ ξ = map varₑ ∘ ξ

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
    -- Substitution respects the inclusion from renamings
    subMaybeRenₑ : ∀ ξ → subMaybeₑ (?ιₑ ξ) ≈ renMaybeₑ ξ

    -- Substitution correctly replaces variables
    subMaybeVarₑ : ∀ σ → subMaybeₑ σ ∘ varₑ ≈ σ

    -- Renaming correctly replaces variables
    renMaybeVarₑ : ∀ ξ → renMaybeₑ ξ ∘ varₑ ≈ map varₑ ∘ ξ

    -- Renaming is total on fully-defined renamings
    renMaybeJustₑ : ∀ ξ e → ↓ (renMaybeₑ (just ∘ ξ) e)

    -- Substitution is total on fully-defined renamings
    subMaybeJustₑ : ∀ σ e → ↓ (subMaybeₑ (just ∘ σ) e)

    -- Substitution respects extensional equality
    subMaybeExtₑ : ∀{σ1 σ2} → σ1 ≈ σ2 → subMaybeₑ σ1 ≈ subMaybeₑ σ2

    -- Renaming respects extensional equality
    renMaybeExtₑ : ∀{ξ1 ξ2} → ξ1 ≈ ξ2 → renMaybeₑ ξ1 ≈ renMaybeₑ ξ2

    -- Renaming is monotone with respect to definedness
    renMaybeMonoₑ : ∀{ξ1 ξ2} →
                    (∀ x → ξ1 x ≲ ξ2 x) →
                    ∀ e → renMaybeₑ ξ1 e ≲ renMaybeₑ ξ2 e

    -- Renaming respects the identity
    renMaybeIdₑ : ∀ e → renMaybeₑ (just ∘ idRen) e ≡ just e

    -- Renaming enjoys fusion
    renMaybeFuseₑ : ∀ ξ1 ξ2 →
                    renMaybeₑ (ξ1 <=< ξ2) ≈
                    renMaybeₑ ξ1 <=< renMaybeₑ ξ2

    -- The property of being closed above is monotonic
    closedAboveMonoₑ : ∀{m n e} → m < n → ClosedAboveₑ m e → ClosedAboveₑ n e
    
    -- A de Bruijn index m is considered closed above n if n > m
    <⇒varClosedₑ : ∀{m n} → m < n → ClosedAboveₑ n (varₑ m)
    
    -- If de Bruijn index m is closed above n then necessarily n > m
    varClosedₑ⇒< : ∀{m n} → ClosedAboveₑ n (varₑ m) → m < n
    
    -- Values have no free variables
    valClosedₑ : ∀{v} → Valₑ v → Closedₑ v


    {-
      For an expression which is closed above `n`, substitution respects
      equality of substitutions which are equal below `n`.
    -}
    subMaybeClosedAboveExtₑ : ∀{e σ1 σ2 n} →
                          ClosedAboveₑ n e →
                          (∀{m} → m < n → σ1 m ≡ σ2 m) →
                          subMaybeₑ σ1 e ≡ subMaybeₑ σ2 e

       
    {-
      For an expression which is closed above `n`, definedness of substitution
      is monotone with respect to substitutions below `n`.
    -}               
    subMaybeClosedAboveMonoₑ : ∀{e σ1 σ2 n} →
                               ClosedAboveₑ n e →
                               (∀{m} → m < n → σ1 m ≲ σ2 m) →
                               subMaybeₑ σ1 e ≲ subMaybeₑ σ2 e

    {- 
      Substitution, renaming, and stepping should not change
      the fact that expressions are closed above some level.
    -}
    subMaybePresClosedAboveₑ : ∀{e e' σ m n} →
                          ClosedAboveₑ n e →
                          (∀{k} → k < n → ↓[ σ k ]⇒ λ x → ClosedAboveₑ m x) →
                          subMaybeₑ σ e ≡ just e' →
                          ClosedAboveₑ m e'
    renMaybePresClosedAboveₑ : ∀{e e' ξ m n} →
                          ClosedAboveₑ n e →
                          (∀{k} → k < n → ↓[ ξ k ]⇒ λ x → x < m) →
                          renMaybeₑ ξ e ≡ just e' →
                          ClosedAboveₑ m e'
    stepPresClosedAboveₑ : ∀{e₁ e₂ n} → e₁ ⇒ₑ e₂ → ClosedAboveₑ n e₁ → ClosedAboveₑ n e₂

    {-
      If a partial operation is defined for all k < n,
      then applying it to an expression closed above
      n must be defined.
    -}
    renMaybeClosedAboveₑ : ∀{e ξ n} →
                           ClosedAboveₑ n e →
                           (∀{k} → k < n → ↓ (ξ k)) →
                           ↓ (renMaybeₑ ξ e)
    subMaybeClosedAboveₑ : ∀{e σ n} →
                          ClosedAboveₑ n e →
                          (∀{k} → k < n → ↓ (σ k)) →
                          ↓ (subMaybeₑ σ e)
  
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

  -- ↑ respects the identity
  ↑?σIdₑ : ↑?σₑ (just ∘ idSubₑ) ≈ just ∘ idSubₑ
  ↑?σIdₑ zero = refl
  ↑?σIdₑ (suc n) = renMaybeVarₑ (just ∘ suc) n

  -- Total renaming
  renₑ : (ℕ → ℕ) → Expr → Expr
  renₑ ξ e = renMaybeJustₑ ξ e .fst

  -- Total substitution
  subₑ : (ℕ → Expr) → Expr → Expr
  subₑ σ e = subMaybeJustₑ σ e .fst

  -- Substitution respects extensional equality.
  subExtₑ : ∀{σ1 σ2} → σ1 ≈ σ2 → subₑ σ1 ≈ subₑ σ2
  subExtₑ {σ1} {σ2} σ1≈σ2 e = just-injective (
    just (subₑ σ1 e)        ≡⟨ sym (subMaybeJustₑ σ1 e .snd) ⟩
    subMaybeₑ (just ∘ σ1) e ≡⟨ subMaybeExtₑ (cong just ∘ σ1≈σ2) e ⟩
    subMaybeₑ (just ∘ σ2) e ≡⟨ subMaybeJustₑ σ2 e .snd ⟩
    just (subₑ σ2 e)        ∎)
    
  -- Substitution correctly replaces variables
  subVarₑ : ∀ σ → subₑ σ ∘ varₑ ≈ σ
  subVarₑ σ n = just-injective (
    just (subₑ σ (varₑ n))        ≡⟨ sym (subMaybeJustₑ σ (varₑ n) .snd) ⟩
    subMaybeₑ (just ∘ σ) (varₑ n) ≡⟨ subMaybeVarₑ (just ∘ σ) n ⟩
    just (σ n)                    ∎ )
    
  -- Substitution respects the inclusion from renamings
  subRenₑ : ∀ ξ → subₑ (varₑ ∘ ξ) ≈ renₑ ξ
  subRenₑ ξ e = just-injective (
    just (subMaybeJustₑ (varₑ ∘ ξ) e .fst) ≡⟨ sym (subMaybeJustₑ (varₑ ∘ ξ) e .snd) ⟩
    subMaybeₑ (just ∘ varₑ ∘ ξ) e          ≡⟨ subMaybeRenₑ (just ∘ ξ) e ⟩
    renMaybeₑ (just ∘ ξ) e                 ≡⟨ renMaybeJustₑ ξ e .snd ⟩
    just (renMaybeJustₑ ξ e .fst)          ∎)
    
  -- Renaming enjoys fusion
  renFuseₑ : ∀ ξ1 ξ2 → renₑ (ξ1 ∘ ξ2) ≈ renₑ ξ1 ∘ renₑ ξ2
  renFuseₑ ξ1 ξ2 e = just-injective (
    just (renMaybeJustₑ (ξ1 ∘ ξ2) e .fst)
      ≡⟨ sym (renMaybeJustₑ (ξ1 ∘ ξ2) e .snd) ⟩
    renMaybeₑ (just ∘ ξ1 ∘ ξ2) e
      ≡⟨ renMaybeFuseₑ (just ∘ ξ1) (just ∘ ξ2) e ⟩
    (renMaybeₑ (just ∘ ξ1) <=< renMaybeₑ (just ∘ ξ2)) e
      ≡⟨ <=<-ext (λ e → renMaybeJustₑ ξ1 e .snd) (λ e → renMaybeJustₑ ξ2 e .snd) e ⟩
    just (renMaybeJustₑ ξ1 (renMaybeJustₑ ξ2 e .fst) .fst) ∎)
  
  -- Renaming respects the identity
  renIdₑ : ∀ e → renₑ idRen e ≡ e
  renIdₑ e = just-injective (
    just (renMaybeJustₑ idRen e .fst) ≡⟨ sym (renMaybeJustₑ idRen e .snd) ⟩
    renMaybeₑ (just ∘ idRen) e        ≡⟨ renMaybeIdₑ e ⟩
    just e                            ∎ )
  
  -- Substituting respects the identity
  subIdₑ : ∀ e → subₑ idSubₑ e ≡ e
  subIdₑ e =
    subₑ (varₑ ∘ idRen) e ≡⟨ subRenₑ idRen e ⟩
    renₑ idRen e          ≡⟨ renIdₑ e ⟩
    e                     ∎

  -- Substitution with the topmost variable instantiated
  _▸ₑ_ : (ℕ → Expr) → Expr → ℕ → Expr
  (σ ▸ₑ e) zero = e
  (σ ▸ₑ e) (suc n) = σ n

  -- Adding a topmost term respects extensional equality
  ▸Extₑ : ∀{σ1 σ2} → σ1 ≈ σ2 →
           ∀ e → σ1 ▸ₑ e ≈ σ2 ▸ₑ e
  ▸Extₑ σ1≈σ2 e zero = refl
  ▸Extₑ σ1≈σ2 e (suc n) = σ1≈σ2 n

  -- ↑ on substitutions
  ↑σₑ : (ℕ → Expr) → ℕ → Expr
  ↑σₑ σ = (renₑ suc ∘ σ) ▸ₑ varₑ zero

  -- ↑ respects extensional equality
  ↑σExt : ∀{σ1 σ2} → σ1 ≈ σ2 → ↑σₑ σ1 ≈ ↑σₑ σ2
  ↑σExt σ1≈σ2 = ▸Extₑ (λ x → cong (renₑ suc) (σ1≈σ2 x)) (varₑ zero)

  -- True and false are closed
  ttClosedₑ : Closedₑ ttₑ
  ttClosedₑ = valClosedₑ ttValₑ

  ffClosedₑ : Closedₑ ffₑ
  ffClosedₑ = valClosedₑ ffValₑ

  -- Renaming respects extensional equality.
  renExtₑ : ∀{ξ1 ξ2} → ξ1 ≈ ξ2 → renₑ ξ1 ≈ renₑ ξ2
  renExtₑ {ξ1} {ξ2} ξ1≈ξ2 e = just-injective (
    just (renₑ ξ1 e)        ≡⟨ sym (renMaybeJustₑ ξ1 e .snd) ⟩
    renMaybeₑ (just ∘ ξ1) e ≡⟨ renMaybeExtₑ (cong just ∘ ξ1≈ξ2) e ⟩
    renMaybeₑ (just ∘ ξ2) e ≡⟨ renMaybeJustₑ ξ2 e .snd ⟩
    just (renₑ ξ2 e)        ∎)

  -- Renaming correctly replaces a variable.
  renVarₑ : ∀ ξ n → renₑ ξ (varₑ n) ≡ varₑ (ξ n)
  renVarₑ ξ n =
    renₑ ξ (varₑ n)          ≡⟨ sym (subRenₑ ξ (varₑ n)) ⟩
    subₑ (varₑ ∘ ξ) (varₑ n) ≡⟨ subVarₑ (varₑ ∘ ξ) n ⟩
    varₑ (ξ n)               ∎

  -- ↑σ respects the identity
  ↑σIdₑ : ↑σₑ idSubₑ ≈ idSubₑ
  ↑σIdₑ zero = refl
  ↑σIdₑ (suc n) = renVarₑ suc n

  {-
    For an expression which is closed above `n`, substitution respects
    extensional equality of substitutions which are equal below `n`.
  -}
  subClosedAboveExtₑ : ∀{σ1 σ2 e n} →
                        ClosedAboveₑ n e →
                        (∀{m} → m < n → σ1 m ≡ σ2 m) →
                        subₑ σ1 e ≡ subₑ σ2 e
  subClosedAboveExtₑ {σ1} {σ2} {e} closed σ1≡σ2 = just-injective (
    just (subₑ σ1 e)        ≡⟨ sym (subMaybeJustₑ σ1 e .snd) ⟩
    subMaybeₑ (just ∘ σ1) e ≡⟨ subMaybeClosedAboveExtₑ closed (λ m<n → cong just (σ1≡σ2 m<n)) ⟩
    subMaybeₑ (just ∘ σ2) e ≡⟨ subMaybeJustₑ σ2 e .snd ⟩
    just (subₑ σ2 e)        ∎ )

  renClosedAboveExtₑ : ∀{ξ1 ξ2 e n} →
                      ClosedAboveₑ n e →
                      (∀{m} → m < n → ξ1 m ≡ ξ2 m) →
                      renₑ ξ1 e ≡ renₑ ξ2 e
  renClosedAboveExtₑ {ξ1} {ξ2} {e} closed ξ1≈ξ2 =
    renₑ ξ1 e          ≡⟨ sym (subRenₑ ξ1 e) ⟩
    subₑ (varₑ ∘ ξ1) e ≡⟨ subClosedAboveExtₑ closed (λ m<n → cong varₑ (ξ1≈ξ2 m<n)) ⟩
    subₑ (varₑ ∘ ξ2) e ≡⟨ subRenₑ ξ2 e ⟩
    renₑ ξ2 e          ∎

  subClosedAboveIdₑ : ∀{σ e n} →
                      ClosedAboveₑ n e →
                      (∀{m} → m < n → σ m ≡ varₑ m) →
                      subₑ σ e ≡ e
  subClosedAboveIdₑ {σ} {e} closed σ≈var =
    subₑ σ e    ≡⟨ subClosedAboveExtₑ closed σ≈var ⟩
    subₑ varₑ e ≡⟨ subIdₑ e ⟩
    e           ∎
  
  renClosedAboveIdₑ : ∀{ξ e n} →
                      ClosedAboveₑ n e →
                      (∀{m} → m < n → ξ m ≡ m) →
                      renₑ ξ e ≡ e
  renClosedAboveIdₑ {ξ} {e} closed ξ≈Id =
    renₑ ξ e     ≡⟨ renClosedAboveExtₑ closed ξ≈Id ⟩
    renₑ idRen e ≡⟨ renIdₑ e ⟩
    e            ∎

  -- Substituting a closed expression has no effect
  subClosedIdₑ : ∀ σ e → Closedₑ e → subₑ σ e ≡ e
  subClosedIdₑ σ e closed = subClosedAboveIdₑ closed (λ ())

  {-
    For an expression which is closed above `n`, renaming respects
    equality of substitutions which are equal below `n`.
  -}
  renMaybeClosedAboveExtₑ : ∀{ξ1 ξ2 e n} →
                            ClosedAboveₑ n e →
                            (∀{m} → m < n → ξ1 m ≡ ξ2 m) →
                            renMaybeₑ ξ1 e ≡ renMaybeₑ ξ2 e
  renMaybeClosedAboveExtₑ {ξ1} {ξ2} {e} closed ξ1≡ξ2 =
    renMaybeₑ ξ1 e
      ≡⟨ sym (subMaybeRenₑ ξ1 e) ⟩
    subMaybeₑ (?ιₑ ξ1) e
      ≡⟨ subMaybeClosedAboveExtₑ closed (λ m<n → cong (maybe (just ∘ varₑ) nothing) (ξ1≡ξ2 m<n)) ⟩
    subMaybeₑ (?ιₑ ξ2) e
      ≡⟨ subMaybeRenₑ ξ2 e ⟩
    renMaybeₑ ξ2 e ∎    

  open ≲-Reasoning

  -- The definedness of ?ιₑ is monotone
  ?ιₑ-mono : ∀{ξ1 ξ2 x} →
             ξ1 x ≲ ξ2 x →
             ?ιₑ ξ1 x ≲ ?ιₑ ξ2 x
  ?ιₑ-mono ξ1≲ξ2 = ≲-cong varₑ ξ1≲ξ2

  renMaybeClosedAboveMonoₑ : ∀{ξ1 ξ2 e n} →
                             ClosedAboveₑ n e →
                             (∀{m} → m < n → ξ1 m ≲ ξ2 m) →
                             renMaybeₑ ξ1 e ≲ renMaybeₑ ξ2 e
  renMaybeClosedAboveMonoₑ {ξ1} {ξ2} {e} {n} closed ξ1≲ξ2 =
    renMaybeₑ ξ1 e       ≲≡⟨ sym (subMaybeRenₑ ξ1 e) ⟩
    subMaybeₑ (?ιₑ ξ1) e ≲⟨ subMaybeClosedAboveMonoₑ closed var∘ξ1≲var∘ξ2 ⟩
    subMaybeₑ (?ιₑ ξ2) e ≲≡⟨ subMaybeRenₑ ξ2 e ⟩
    renMaybeₑ ξ2 e ≲∎
    where
    var∘ξ1≲var∘ξ2 : ∀{m} → m < n → ?ιₑ ξ1 m ≲ ?ιₑ ξ2 m
    var∘ξ1≲var∘ξ2 {m} m<n = ?ιₑ-mono {ξ1} {ξ2} {m} (ξ1≲ξ2 m<n)

  -- Partial renaming of a closed expression has no effect
  renMaybeClosedₑ : ∀ ξ e  → Closedₑ e → renMaybeₑ ξ e ≡ just e
  renMaybeClosedₑ ξ e closed =
    renMaybeₑ ξ e              ≡⟨ sym e⟨id⟩≡e⟨ξ⟩ ⟩
    renMaybeₑ (just ∘ idRen) e ≡⟨ renMaybeJustₑ idRen e .snd ⟩
    just (renₑ idRen e)        ≡⟨ cong just (renIdₑ e) ⟩
    just e                     ∎
    where
    e⟨id⟩≲e⟨ξ⟩ : renMaybeₑ (just ∘ idRen) e ≲ renMaybeₑ ξ e
    e⟨id⟩≲e⟨ξ⟩ = renMaybeClosedAboveMonoₑ closed (λ ())

    ↓e⟨ξ⟩ : ↓ (renMaybeₑ ξ) e
    ↓e⟨ξ⟩ = renMaybeClosedAboveₑ {ξ = ξ} closed (λ ())

    e⟨id⟩≡e⟨ξ⟩ : renMaybeₑ (just ∘ idRen) e ≡ renMaybeₑ ξ e
    e⟨id⟩≡e⟨ξ⟩ = ≲↓⇒≡ e⟨id⟩≲e⟨ξ⟩ ↓e⟨ξ⟩
  

  -- Partial substitution of a closed expression has no effect
  subMaybeClosedₑ : ∀ σ e → Closedₑ e → subMaybeₑ σ e ≡ just e
  subMaybeClosedₑ σ e closed =
    subMaybeₑ σ e              ≡⟨ sym (e⟨id⟩≡e⟨σ⟩) ⟩
    subMaybeₑ (just ∘ varₑ) e  ≡⟨ subMaybeJustₑ varₑ e .snd ⟩
    just (subₑ varₑ e)         ≡⟨ cong just (subIdₑ e) ⟩
    just e                     ∎
    where
    e⟨id⟩≲e⟨σ⟩ : subMaybeₑ (just ∘ varₑ) e ≲ subMaybeₑ σ e
    e⟨id⟩≲e⟨σ⟩ = subMaybeClosedAboveMonoₑ closed (λ ())

    ↓e⟨σ⟩ : ↓ (subMaybeₑ σ e)
    ↓e⟨σ⟩ = subMaybeClosedAboveₑ {σ = σ} closed (λ ())

    e⟨id⟩≡e⟨σ⟩ : subMaybeₑ (just ∘ varₑ) e ≡ subMaybeₑ σ e
    e⟨id⟩≡e⟨σ⟩ = ≲↓⇒≡ e⟨id⟩≲e⟨σ⟩ ↓e⟨σ⟩

  -- Stepping a closed expression remains closed.
  stepClosedₑ : ∀{e1 e2} → e1 ⇒ₑ e2 → Closedₑ e1 → Closedₑ e2
  stepClosedₑ e1⇒e2 closed = stepPresClosedAboveₑ e1⇒e2 closed

  -- Fusion first with a total renaming and then a partial renaming
  renMaybeRenFuseₑ : ∀ ξ1 ξ2 →
                     renMaybeₑ ξ1 ∘ renₑ ξ2 ≈ renMaybeₑ (ξ1 ∘ ξ2)
  renMaybeRenFuseₑ ξ1 ξ2 e =
    (renMaybeₑ ξ1 <=< (just ∘ renₑ ξ2)) e
      ≡⟨ cong (maybe′ (renMaybeₑ ξ1) nothing) (sym (renMaybeJustₑ ξ2 e .snd)) ⟩
    maybe′ (renMaybeₑ ξ1) nothing (renMaybeₑ (just ∘ ξ2) e)
      ≡⟨ sym (renMaybeFuseₑ ξ1 (just ∘ ξ2) e) ⟩
    renMaybeₑ (ξ1 ∘ ξ2) e ∎

  -- Fusion first with a partial renaming and then a total renaming
  renMaybeFuseRenₑ  : ∀ ξ1 ξ2 →
                      map (renₑ ξ1) ∘ renMaybeₑ ξ2 ≈ renMaybeₑ (map ξ1 ∘ ξ2)
  renMaybeFuseRenₑ ξ1 ξ2 e = 
    map (renₑ ξ1) (renMaybeₑ ξ2 e)
      ≡⟨ maybe-ext (λ x → sym (renMaybeJustₑ ξ1 x .snd)) nothing (renMaybeₑ ξ2 e) ⟩
    maybe′ (renMaybeₑ (just ∘ ξ1)) nothing (renMaybeₑ ξ2 e)
      ≡⟨ sym (renMaybeFuseₑ (just ∘ ξ1) ξ2 e) ⟩
    renMaybeₑ (map ξ1 ∘ ξ2) e ∎

  -- ↑ respects the inclusion
  ↑σιₑ : ∀ ξ → ↑σₑ (ιₑ ξ) ≈ ιₑ (↑ ξ)
  ↑σιₑ ξ zero = refl 
  ↑σιₑ ξ (suc n) = renVarₑ suc (ξ n)