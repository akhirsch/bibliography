{-# OPTIONS --safe #-}

open import Data.Nat renaming (_≟_ to ≡-dec-ℕ)
open import Data.List
open import Data.List.Properties renaming (≡-dec to ≡-dec-List)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function

open import Common

module Locations where

record Location : Set₁ where
  field
    -- Literal location values
    LocVal : Set
    -- Literal locations should have decidable equality
    ≡-dec-LocVal : DecidableEquality LocVal

  -- Abstract locations are either a literal value or a variable
  data Loc : Set where
    Var : (x : ℕ) → Loc
    Lit : (L : LocVal) → Loc

  -- Locations have decidable equality
  ≡-dec-Loc : DecidableEquality Loc
  ≡-dec-Loc (Var x1) (Var x2) with ≡-dec-ℕ x1 x2
  ... | yes refl = yes refl
  ... | no x1≠x2 = no λ{ refl → x1≠x2 refl }
  ≡-dec-Loc (Var x) (Lit L) = no (λ ())
  ≡-dec-Loc (Lit L) (Var x) = no (λ ())
  ≡-dec-Loc (Lit L1) (Lit L2) with ≡-dec-LocVal L1 L2
  ... | yes refl = yes refl
  ... | no L1≠L2 = no λ{ refl → L1≠L2 refl }

  -- Injectivity of constructors
  Varₗ-inj : ∀{ℓ ℓ'} → Var ℓ ≡ Var ℓ' → ℓ ≡ ℓ'
  Varₗ-inj refl = refl

  Litₗ-inj : ∀{L L'} → Lit L ≡ Lit L' → L ≡ L'
  Litₗ-inj refl = refl

  -- Lists of locations
  LocList : Set
  LocList = List Loc

  -- Lists of locations have decidable equality
  ≡-dec-LocList : DecidableEquality LocList
  ≡-dec-LocList = ≡-dec-List ≡-dec-Loc

  ----------------
  --- RENAMING ---
  ----------------

  -- Rename location variables
  renₗ-Loc : Loc → (ℕ → ℕ) → Loc
  renₗ-Loc (Var x) ξ = Var (ξ x)
  renₗ-Loc (Lit L) ξ = Lit L

  -- Renaming location variables in a location respects extensional equality
  renExtₗ-Loc : ∀{ξ1 ξ2} →
                ξ1 ≈ ξ2 →
                ∀ ℓ → renₗ-Loc ℓ ξ1 ≡ renₗ-Loc ℓ ξ2
  renExtₗ-Loc ξ1≈ξ2 (Var x) = cong Var (ξ1≈ξ2 x)
  renExtₗ-Loc ξ1≈ξ2 (Lit L) = refl

  -- Renaming location variables in a location respects the identity
  renIdₗ-Loc : ∀ ℓ → renₗ-Loc ℓ idRen ≡ ℓ
  renIdₗ-Loc (Var x) = refl
  renIdₗ-Loc (Lit L) = refl

  -- Renaming location variables in a location enjoys fusion
  renFuseₗ-Loc : ∀ ξ1 ξ2 ℓ → renₗ-Loc ℓ (ξ1 ∘ ξ2) ≡ renₗ-Loc (renₗ-Loc ℓ ξ2) ξ1
  renFuseₗ-Loc ξ1 ξ2 (Var x) = refl
  renFuseₗ-Loc ξ1 ξ2 (Lit L) = refl

  -- Renaming preserves injectivity
  renInjₗ-Loc : ∀{ℓ ℓ' ξ} →
                Injective _≡_ _≡_ ξ →
                renₗ-Loc ℓ ξ ≡ renₗ-Loc ℓ' ξ →
                ℓ ≡ ℓ'
  renInjₗ-Loc {ℓ = Var x} {Var x'} ξ-inj Vξx≡Vξx' = cong Var (ξ-inj (Varₗ-inj Vξx≡Vξx'))
  renInjₗ-Loc {ℓ = Var x} {Lit L'} ξ-inj ()
  renInjₗ-Loc {ℓ = Lit L} {Var x'} ξ-inj ()
  renInjₗ-Loc {ℓ = Lit L} {Lit .L} ξ-inj refl = refl

  -- Rename location variables in a location list
  renₗ-List : LocList → (ℕ → ℕ) → LocList
  renₗ-List ρ ξ = Data.List.map (λ ℓ → renₗ-Loc ℓ ξ) ρ

  -- Renaming location variables in a location list respects extensional equality
  renExtₗ-List : ∀{ξ1 ξ2} →
                 ξ1 ≈ ξ2 →
                 ∀ ρ → renₗ-List ρ ξ1 ≡ renₗ-List ρ ξ2
  renExtₗ-List ξ1≈ξ2 [] = refl
  renExtₗ-List ξ1≈ξ2 (ℓ ∷ ρ) = cong₂ _∷_ (renExtₗ-Loc ξ1≈ξ2 ℓ) (renExtₗ-List ξ1≈ξ2 ρ)

  -- Renaming location variables in a location list respects the identity
  renIdₗ-List : ∀ ρ → renₗ-List ρ idRen ≡ ρ
  renIdₗ-List [] = refl
  renIdₗ-List (ℓ ∷ ρ) = cong₂ _∷_ (renIdₗ-Loc ℓ) (renIdₗ-List ρ)

  -- Renaming location variables in a location list enjoys fusion
  renFuseₗ-List : ∀ ξ1 ξ2 ρ → renₗ-List ρ (ξ1 ∘ ξ2) ≡ renₗ-List (renₗ-List ρ ξ2) ξ1
  renFuseₗ-List ξ1 ξ2 [] = refl
  renFuseₗ-List ξ1 ξ2 (ℓ ∷ ρ) = cong₂ _∷_ (renFuseₗ-Loc ξ1 ξ2 ℓ) (renFuseₗ-List ξ1 ξ2 ρ)

  --------------------
  --- SUBSTITUTION ---
  --------------------

  -- Substitute location variables
  subₗ-Loc : Loc → (ℕ → Loc) → Loc
  subₗ-Loc (Var x) σ = σ x
  subₗ-Loc (Lit L) σ = Lit L

  subₗ-List : LocList → (ℕ → Loc) → LocList
  subₗ-List [] σ = []
  subₗ-List (ℓ ∷ ρ) σ = subₗ-Loc ℓ σ ∷ subₗ-List ρ σ

  -- Substituting location variables respects extensional equality
  subExtₗ-Loc : ∀{σ1 σ2} →
                σ1 ≈ σ2 →
                ∀ ℓ → subₗ-Loc ℓ σ1 ≡ subₗ-Loc ℓ σ2
  subExtₗ-Loc σ1≈σ2 (Var x) = σ1≈σ2 x
  subExtₗ-Loc σ1≈σ2 (Lit L) = refl

  subExtₗ-List : ∀{σ1 σ2} →
                σ1 ≈ σ2 →
                ∀ ρ → subₗ-List ρ σ1 ≡ subₗ-List ρ σ2
  subExtₗ-List σ1≈σ2 [] = refl
  subExtₗ-List σ1≈σ2 (ℓ ∷ ρ) = cong₂ _∷_ (subExtₗ-Loc σ1≈σ2 ℓ) (subExtₗ-List σ1≈σ2 ρ)

  -- Identity location substitution
  idSubₗ : ℕ → Loc
  idSubₗ n = Var n

  -- Substituting location variables respects the identity
  subIdₗ-Loc : ∀ ℓ → subₗ-Loc ℓ idSubₗ ≡ ℓ
  subIdₗ-Loc (Var x) = refl
  subIdₗ-Loc (Lit L) = refl

  subIdₗ-List : ∀ ρ → subₗ-List ρ idSubₗ ≡ ρ
  subIdₗ-List [] = refl
  subIdₗ-List (ℓ ∷ ρ) = cong₂ _∷_ (subIdₗ-Loc ℓ) (subIdₗ-List ρ)

  -- Composition of location substitutions
  infixr 9 _•ₗ_
  _•ₗ_ : (σ1 σ2 : ℕ → Loc) → ℕ → Loc
  (σ1 •ₗ σ2) n = subₗ-Loc (σ2 n) σ1

  open ≡-Reasoning

  -- Composition respects extensional equality
  •Extₗ : ∀{σ1 σ1' σ2 σ2'} →
          σ1 ≈ σ1' →
          σ2 ≈ σ2' →
          σ1 •ₗ σ2 ≈ σ1' •ₗ σ2'
  •Extₗ {σ1} {σ1'} {σ2} {σ2'} σ1≈σ1' σ2≈σ2' n =
    subₗ-Loc (σ2 n) σ1   ≡⟨ subExtₗ-Loc σ1≈σ1' (σ2 n) ⟩
    subₗ-Loc (σ2 n) σ1'  ≡⟨ cong₂ subₗ-Loc (σ2≈σ2' n) refl ⟩
    subₗ-Loc (σ2' n) σ1' ∎

  -- Composition respects the identity
  •ₗ-idₗ : ∀ σ → idSubₗ •ₗ σ ≈ σ
  •ₗ-idₗ σ n = subIdₗ-Loc (σ n)

  •ₗ-idᵣ : ∀ σ → σ •ₗ idSubₗ ≈ σ
  •ₗ-idᵣ σ n = refl

  -- Substitution on locations enjoys fusion
  subFuseₗ-Loc : ∀ σ1 σ2 ℓ → subₗ-Loc ℓ (σ1 •ₗ σ2) ≡ subₗ-Loc (subₗ-Loc ℓ σ2) σ1
  subFuseₗ-Loc σ1 σ2 (Var x) = refl
  subFuseₗ-Loc σ1 σ2 (Lit L) = refl

  subFuseₗ-List : ∀ σ1 σ2 ρ → subₗ-List ρ (σ1 •ₗ σ2) ≡ subₗ-List (subₗ-List ρ σ2) σ1
  subFuseₗ-List σ1 σ2 [] = refl
  subFuseₗ-List σ1 σ2 (ℓ ∷ ρ) = cong₂ _∷_ (subFuseₗ-Loc σ1 σ2 ℓ) (subFuseₗ-List σ1 σ2 ρ)

  -- Composition is associative
  •ₗ-assoc : ∀ σ1 σ2 σ3 → (σ1 •ₗ σ2) •ₗ σ3 ≈ σ1 •ₗ σ2 •ₗ σ3
  •ₗ-assoc σ1 σ2 σ3 n = subFuseₗ-Loc σ1 σ2 (σ3 n)

  -- Location substitution with the topmost variable instantiated 
  _▸ₗ_ : (ℕ → Loc) → Loc → ℕ → Loc
  (σ ▸ₗ ℓ) zero = ℓ
  (σ ▸ₗ ℓ) (suc n) = σ n

  -- Adding a topmost term respects extensional equality
  ▸Extₗ : ∀{σ1 σ2} → σ1 ≈ σ2 → ∀ ℓ → σ1 ▸ₗ ℓ ≈ σ2 ▸ₗ ℓ
  ▸Extₗ σ1≈σ2 c zero = refl
  ▸Extₗ σ1≈σ2 c (suc n) = σ1≈σ2 n

  -- How adding a topmost variable acts on composition
  ▸•ₗ : ∀ σ1 σ2 ℓ → (σ1 •ₗ σ2) ▸ₗ subₗ-Loc ℓ σ1 ≈ (σ1 •ₗ (σ2 ▸ₗ ℓ))
  ▸•ₗ σ1 σ2 ℓ zero = refl
  ▸•ₗ σ1 σ2 ℓ (suc n) = refl

  -- Inclusion from renamings to location substitutions
  ιₗ : (ℕ → ℕ) → ℕ → Loc
  ιₗ ξ n = Var (ξ n)

  -- Substitution respects the inclusion
  subιₗ-Loc : ∀ ξ ℓ → subₗ-Loc ℓ (ιₗ ξ) ≡ renₗ-Loc ℓ ξ
  subιₗ-Loc ξ (Var x) = refl
  subιₗ-Loc ξ (Lit L) = refl

  subιₗ-List : ∀ ξ ρ → subₗ-List ρ (ιₗ ξ) ≡ renₗ-List ρ ξ
  subιₗ-List ξ [] = refl
  subιₗ-List ξ (ℓ ∷ ρ) = cong₂ _∷_ (subιₗ-Loc ξ ℓ) (subιₗ-List ξ ρ)

  -- The `up` construction on location substitutions
  ↑σₗ :  (ℕ → Loc) → ℕ → Loc
  ↑σₗ σ = (ιₗ suc •ₗ σ) ▸ₗ Var zero

  -- The `up` construction respects extensional equality
  ↑σExtₗ : ∀{σ1 σ2} → σ1 ≈ σ2 → ↑σₗ σ1 ≈ ↑σₗ σ2
  ↑σExtₗ σ1≈σ2 = ▸Extₗ (•Extₗ ≈-refl σ1≈σ2) (Var zero)
  
  -- The `up` construction respects the identity
  ↑σIdₗ : ↑σₗ idSubₗ ≈ idSubₗ
  ↑σIdₗ zero = refl
  ↑σIdₗ (suc n) = refl

  -- `up` distributes over composition
  ↑σ•ₗ : ∀ σ1 σ2 → ↑σₗ (σ1 •ₗ σ2) ≈ ↑σₗ σ1 •ₗ ↑σₗ σ2
  ↑σ•ₗ σ1 σ2 zero = refl
  ↑σ•ₗ σ1 σ2 (suc n) =
    subₗ-Loc (subₗ-Loc (σ2 n) σ1) (ιₗ suc)       ≡⟨ sym (subFuseₗ-Loc (ιₗ suc) σ1 (σ2 n)) ⟩
    subₗ-Loc (σ2 n) (ιₗ suc •ₗ σ1)               ≡⟨ subExtₗ-Loc (λ _ → refl) (σ2 n) ⟩
    subₗ-Loc (σ2 n) (↑σₗ σ1 •ₗ ιₗ suc)           ≡⟨ subFuseₗ-Loc (↑σₗ σ1) (ιₗ suc) (σ2 n) ⟩
    subₗ-Loc (subₗ-Loc (σ2 n) (ιₗ suc)) (↑σₗ σ1) ∎

  -- `up` construction commutes with the inclusion
  ↑σιₗ : ∀ ξ → ↑σₗ (ιₗ ξ) ≈ ιₗ (↑ ξ)
  ↑σιₗ ξ zero = refl
  ↑σιₗ ξ (suc n) = refl
 