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
    VarLoc : (x : ℕ) → Loc
    LitLoc : (L : LocVal) → Loc

  -- Locations have decidable equality
  ≡-dec-Loc : DecidableEquality Loc
  ≡-dec-Loc (VarLoc x1) (VarLoc x2) with ≡-dec-ℕ x1 x2
  ... | yes refl = yes refl
  ... | no x1≠x2 = no λ{ refl → x1≠x2 refl }
  ≡-dec-Loc (VarLoc x) (LitLoc L) = no (λ ())
  ≡-dec-Loc (LitLoc L) (VarLoc x) = no (λ ())
  ≡-dec-Loc (LitLoc L1) (LitLoc L2) with ≡-dec-LocVal L1 L2
  ... | yes refl = yes refl
  ... | no L1≠L2 = no λ{ refl → L1≠L2 refl }

  -- Injectivity of constructors
  VarLocₗ-inj : ∀{ℓ ℓ'} → VarLoc ℓ ≡ VarLoc ℓ' → ℓ ≡ ℓ'
  VarLocₗ-inj refl = refl

  LitLocₗ-inj : ∀{L L'} → LitLoc L ≡ LitLoc L' → L ≡ L'
  LitLocₗ-inj refl = refl

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
  renₗ-Loc : (ℕ → ℕ) → Loc → Loc
  renₗ-Loc ξ (VarLoc x) = VarLoc (ξ x)
  renₗ-Loc ξ (LitLoc L) = LitLoc L

  -- Weakening a location by one variable
  ↑ₗ : Loc → Loc
  ↑ₗ = renₗ-Loc suc

  -- Renaming location variables in a location respects extensional equality
  renExtₗ-Loc : ∀{ξ1 ξ2} →
                ξ1 ≈ ξ2 →
                renₗ-Loc ξ1 ≈ renₗ-Loc ξ2
  renExtₗ-Loc ξ1≈ξ2 (VarLoc x) = cong VarLoc (ξ1≈ξ2 x)
  renExtₗ-Loc ξ1≈ξ2 (LitLoc L) = refl

  -- Renaming location variables in a location respects the identity
  renIdₗ-Loc : ∀ ℓ → renₗ-Loc idRen ℓ ≡ ℓ
  renIdₗ-Loc (VarLoc x) = refl
  renIdₗ-Loc (LitLoc L) = refl

  -- Renaming location variables in a location enjoys fusion
  renFuseₗ-Loc : ∀ ξ1 ξ2 → renₗ-Loc (ξ1 ∘ ξ2) ≈ renₗ-Loc ξ1 ∘ renₗ-Loc ξ2
  renFuseₗ-Loc ξ1 ξ2 (VarLoc x) = refl
  renFuseₗ-Loc ξ1 ξ2 (LitLoc L) = refl

  -- Renaming preserves injectivity
  renInjₗ-Loc : ∀{ℓ ℓ' ξ} →
                Injective _≡_ _≡_ ξ →
                renₗ-Loc ξ ℓ ≡ renₗ-Loc ξ ℓ' →
                ℓ ≡ ℓ'
  renInjₗ-Loc {ℓ = VarLoc x} {VarLoc x'} ξ-inj Vξx≡Vξx' = cong VarLoc (ξ-inj (VarLocₗ-inj Vξx≡Vξx'))
  renInjₗ-Loc {ℓ = VarLoc x} {LitLoc L'} ξ-inj ()
  renInjₗ-Loc {ℓ = LitLoc L} {VarLoc x'} ξ-inj ()
  renInjₗ-Loc {ℓ = LitLoc L} {LitLoc .L} ξ-inj refl = refl

  -- Rename location variables in a location list
  renₗ-List : (ℕ → ℕ) → LocList → LocList
  renₗ-List ξ = Data.List.map (renₗ-Loc ξ)

  -- Renaming location variables in a location list respects extensional equality
  renExtₗ-List : ∀{ξ1 ξ2} →
                 ξ1 ≈ ξ2 →
                 ∀ ρ → renₗ-List ξ1 ρ ≡ renₗ-List ξ2 ρ
  renExtₗ-List ξ1≈ξ2 [] = refl
  renExtₗ-List ξ1≈ξ2 (ℓ ∷ ρ) = cong₂ _∷_ (renExtₗ-Loc ξ1≈ξ2 ℓ) (renExtₗ-List ξ1≈ξ2 ρ)

  -- Renaming location variables in a location list respects the identity
  renIdₗ-List : ∀ ρ → renₗ-List idRen ρ ≡ ρ
  renIdₗ-List [] = refl
  renIdₗ-List (ℓ ∷ ρ) = cong₂ _∷_ (renIdₗ-Loc ℓ) (renIdₗ-List ρ)

  -- Renaming location variables in a location list enjoys fusion
  renFuseₗ-List : ∀ ξ1 ξ2 → renₗ-List (ξ1 ∘ ξ2) ≈ renₗ-List ξ1 ∘ renₗ-List ξ2
  renFuseₗ-List ξ1 ξ2 [] = refl
  renFuseₗ-List ξ1 ξ2 (ℓ ∷ ρ) = cong₂ _∷_ (renFuseₗ-Loc ξ1 ξ2 ℓ) (renFuseₗ-List ξ1 ξ2 ρ)

  --------------------
  --- SUBSTITUTION ---
  --------------------

  -- Substitute location variables
  subₗ-Loc : (ℕ → Loc) → Loc → Loc
  subₗ-Loc σ (VarLoc x) = σ x
  subₗ-Loc σ (LitLoc L) = LitLoc L
  
  subₗ-List : (ℕ → Loc) → LocList → LocList
  subₗ-List σ = Data.List.map (subₗ-Loc σ)

  -- Substituting location variables respects extensional equality
  subExtₗ-Loc : ∀{σ1 σ2} →
                σ1 ≈ σ2 →
                ∀ ℓ → subₗ-Loc σ1 ℓ ≡ subₗ-Loc σ2 ℓ
  subExtₗ-Loc σ1≈σ2 (VarLoc x) = σ1≈σ2 x
  subExtₗ-Loc σ1≈σ2 (LitLoc L) = refl

  subExtₗ-List : ∀{σ1 σ2} →
                σ1 ≈ σ2 →
                subₗ-List σ1 ≈ subₗ-List σ2
  subExtₗ-List σ1≈σ2 [] = refl
  subExtₗ-List σ1≈σ2 (ℓ ∷ ρ) = cong₂ _∷_ (subExtₗ-Loc σ1≈σ2 ℓ) (subExtₗ-List σ1≈σ2 ρ)

  -- Identity location substitution
  idSubₗ : ℕ → Loc
  idSubₗ = VarLoc

  -- Substituting location variables respects the identity
  subIdₗ-Loc : ∀ ℓ → subₗ-Loc idSubₗ ℓ ≡ ℓ
  subIdₗ-Loc (VarLoc x) = refl
  subIdₗ-Loc (LitLoc L) = refl

  subIdₗ-List : ∀ ρ → subₗ-List idSubₗ ρ ≡ ρ
  subIdₗ-List [] = refl
  subIdₗ-List (ℓ ∷ ρ) = cong₂ _∷_ (subIdₗ-Loc ℓ) (subIdₗ-List ρ)

  -- Composition of location substitutions
  infixr 9 _•ₗ_
  _•ₗ_ : (σ1 σ2 : ℕ → Loc) → ℕ → Loc
  (σ1 •ₗ σ2) n = subₗ-Loc σ1 (σ2 n)

  open ≡-Reasoning

  -- Composition respects extensional equality
  •Extₗ : ∀{σ1 σ1' σ2 σ2'} →
          σ1 ≈ σ1' →
          σ2 ≈ σ2' →
          σ1 •ₗ σ2 ≈ σ1' •ₗ σ2'
  •Extₗ {σ1} {σ1'} {σ2} {σ2'} σ1≈σ1' σ2≈σ2' n =
    subₗ-Loc σ1 (σ2 n)   ≡⟨ subExtₗ-Loc σ1≈σ1' (σ2 n) ⟩
    subₗ-Loc σ1' (σ2 n)  ≡⟨ cong₂ subₗ-Loc refl (σ2≈σ2' n) ⟩
    subₗ-Loc σ1' (σ2' n) ∎

  -- Composition respects the identity
  •ₗ-idₗ : ∀ σ → idSubₗ •ₗ σ ≈ σ
  •ₗ-idₗ σ n = subIdₗ-Loc (σ n)

  •ₗ-idᵣ : ∀ σ → σ •ₗ idSubₗ ≈ σ
  •ₗ-idᵣ σ n = refl

  -- Substitution on locations enjoys fusion
  subFuseₗ-Loc : ∀ σ1 σ2 ℓ → subₗ-Loc (σ1 •ₗ σ2) ℓ ≡ subₗ-Loc σ1 (subₗ-Loc σ2 ℓ)
  subFuseₗ-Loc σ1 σ2 (VarLoc x) = refl
  subFuseₗ-Loc σ1 σ2 (LitLoc L) = refl

  subFuseₗ-List : ∀ σ1 σ2 → subₗ-List (σ1 •ₗ σ2) ≈ subₗ-List σ1 ∘ subₗ-List σ2
  subFuseₗ-List σ1 σ2 [] = refl
  subFuseₗ-List σ1 σ2 (ℓ ∷ ρ) = cong₂ _∷_ (subFuseₗ-Loc σ1 σ2 ℓ) (subFuseₗ-List σ1 σ2 ρ)

  -- Composition is associative
  •ₗ-assoc : ∀ σ1 σ2 σ3 → (σ1 •ₗ σ2) •ₗ σ3 ≈ σ1 •ₗ σ2 •ₗ σ3
  •ₗ-assoc σ1 σ2 σ3 n = subFuseₗ-Loc σ1 σ2 (σ3 n)

  -- How adding a topmost variable acts on composition
  ▸•ₗ : ∀ σ1 σ2 ℓ → (σ1 •ₗ σ2) ▸ subₗ-Loc σ1 ℓ ≈ (σ1 •ₗ (σ2 ▸ ℓ))
  ▸•ₗ σ1 σ2 ℓ zero = refl
  ▸•ₗ σ1 σ2 ℓ (suc n) = refl

  -- Inclusion from renamings to location substitutions
  ιₗ : (ℕ → ℕ) → ℕ → Loc
  ιₗ ξ n = VarLoc (ξ n)

  -- Substitution respects the inclusion
  subιₗ-Loc : ∀ ξ ℓ → subₗ-Loc (ιₗ ξ) ℓ ≡ renₗ-Loc ξ ℓ
  subιₗ-Loc ξ (VarLoc x) = refl
  subιₗ-Loc ξ (LitLoc L) = refl

  subιₗ-List : ∀ ξ → subₗ-List (ιₗ ξ) ≈ renₗ-List ξ
  subιₗ-List ξ [] = refl
  subιₗ-List ξ (ℓ ∷ ρ) = cong₂ _∷_ (subιₗ-Loc ξ ℓ) (subιₗ-List ξ ρ)

  -- Substituting over the inclusion preserves injectivity
  subInjₗ-Loc : ∀{ℓ ℓ' ξ} →
                Injective _≡_ _≡_ ξ →
                subₗ-Loc (ιₗ ξ) ℓ ≡ subₗ-Loc (ιₗ ξ) ℓ' →
                ℓ ≡ ℓ'
  subInjₗ-Loc {ℓ} {ℓ'} {ξ} ξ-inj p = renInjₗ-Loc ξ-inj ℓ⟨ξ⟩≡ℓ'⟨ξ⟩
    where
    ℓ⟨ξ⟩≡ℓ'⟨ξ⟩ : renₗ-Loc ξ ℓ ≡ renₗ-Loc ξ ℓ'
    ℓ⟨ξ⟩≡ℓ'⟨ξ⟩ =
      renₗ-Loc ξ ℓ       ≡⟨ sym (subιₗ-Loc ξ ℓ) ⟩
      subₗ-Loc (ιₗ ξ) ℓ  ≡⟨ p ⟩
      subₗ-Loc (ιₗ ξ) ℓ' ≡⟨ subιₗ-Loc ξ ℓ' ⟩
      renₗ-Loc ξ ℓ'      ∎

  -- The `up` construction on location substitutions
  ↑σₗ :  (ℕ → Loc) → ℕ → Loc
  ↑σₗ σ = (ιₗ suc •ₗ σ) ▸ VarLoc zero

  -- The `up` construction respects extensional equality
  ↑σExtₗ : ∀{σ1 σ2} → σ1 ≈ σ2 → ↑σₗ σ1 ≈ ↑σₗ σ2
  ↑σExtₗ σ1≈σ2 = ▸Ext (•Extₗ ≈-refl σ1≈σ2) (VarLoc zero)
  
  -- The `up` construction respects the identity
  ↑σIdₗ : ↑σₗ idSubₗ ≈ idSubₗ
  ↑σIdₗ zero = refl
  ↑σIdₗ (suc n) = refl

  -- `up` distributes over composition
  ↑σ•ₗ : ∀ σ1 σ2 → ↑σₗ (σ1 •ₗ σ2) ≈ ↑σₗ σ1 •ₗ ↑σₗ σ2
  ↑σ•ₗ σ1 σ2 zero = refl
  ↑σ•ₗ σ1 σ2 (suc n) =
    subₗ-Loc (ιₗ suc) (subₗ-Loc σ1 (σ2 n))       ≡⟨ sym (subFuseₗ-Loc (ιₗ suc) σ1 (σ2 n)) ⟩
    subₗ-Loc (ιₗ suc •ₗ σ1) (σ2 n)               ≡⟨ subExtₗ-Loc (λ _ → refl) (σ2 n) ⟩
    subₗ-Loc (↑σₗ σ1 •ₗ ιₗ suc) (σ2 n)           ≡⟨ subFuseₗ-Loc (↑σₗ σ1) (ιₗ suc) (σ2 n) ⟩
    subₗ-Loc (↑σₗ σ1) (subₗ-Loc (ιₗ suc) (σ2 n)) ∎

  -- `up` construction commutes with the inclusion
  ↑σιₗ : ∀ ξ → ↑σₗ (ιₗ ξ) ≈ ιₗ (↑ ξ)
  ↑σιₗ ξ zero = refl
  ↑σιₗ ξ (suc n) = refl
 