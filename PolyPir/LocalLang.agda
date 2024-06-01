{-# OPTIONS --safe #-}

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.List
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Bool
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Function

open ≡-Reasoning

open import Common
open import SecondOrderSignatures
open import ThirdOrderSignatures
open import ThirdOrderLanguage

module PolyPir.LocalLang where

-- Binding signature and extra requirements for a local language
record LocalLang (Loc : Set) : Set₁ where
  field
    -- Binding signature of the language
    {{⅀ₑ}} : ThirdOrderSignature

    -- Kind of local types
    TyKnd : ⅀ₑ .⅀₂ .Knd

    -- Inherently type-preserving ground semantics
    _⇒ₑ_ : ∀{t} (e₁ e₂ : Tm ⅀ₑ [] [] t) → Set
    -- Values
    Valₑ : ∀{t} (e : Tm ⅀ₑ [] [] t) → Set
    -- Values cannot step
    valNoStepₑ : ∀{t} {e₁ e₂ : Tm ⅀ₑ [] [] t} → Valₑ e₁ → ¬ (e₁ ⇒ₑ e₂)
    -- We have type safety
    progress : ∀{t} (e : Tm ⅀ₑ [] [] t) →
               (Valₑ e) ⊎ (Σ[ e' ∈ _ ] (e ⇒ₑ e'))

    -- Local type for booleans
    Boolₑ : Ty ⅀ₑ [] TyKnd
    -- True and false are values
    ttₑ : Tm ⅀ₑ [] [] (TyKnd , Boolₑ)
    tt-Valₑ : Valₑ ttₑ
    ffₑ : Tm ⅀ₑ [] [] (TyKnd , Boolₑ)
    ff-Valₑ : Valₑ ffₑ
    -- The only ground values are true and false
    invertBoolₑ : ∀ e → Valₑ e → e ≡ ttₑ ⊎ e ≡ ffₑ

    -- Local type for locations
    Locₑ : Ty ⅀ₑ [] TyKnd
    -- Each location has a value
    litLocₑ : Loc → Tm ⅀ₑ [] [] (TyKnd , Locₑ)
    litLoc-Valₑ : ∀ L → Valₑ (litLocₑ L)
    -- The only ground values are literals
    invertLocₑ : ∀ e → Valₑ e → Σ[ L ∈ Loc ] (e ≡ litLocₑ L)

    -- Local type for representations of local types of a given kind
    TyRepₑ : ⅀ₑ .⅀₂ .Knd → Ty ⅀ₑ [] TyKnd
    -- Each type has a representation
    litTyRepₑ : (κₑ : ⅀ₑ .⅀₂ .Knd) → Ty ⅀ₑ [] κₑ → Tm ⅀ₑ [] [] (TyKnd , TyRepₑ κₑ)
    litTyRep-Valₑ : ∀ κₑ t → Valₑ (litTyRepₑ κₑ t)
    -- The only ground values are literals
    invertTyRepₑ : ∀ κₑ tᵣ → Valₑ tᵣ → Σ[ t ∈ Ty ⅀ₑ [] κₑ ] (tᵣ ≡ litTyRepₑ κₑ t)

open LocalLang public