{-# OPTIONS --safe #-}

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.List
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Bool
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function

open ≡-Reasoning

open import Common
open import KindSignatures
open import TypeSignatures
open import Types
open import Kinding
open import Terms
open import Typing

module PolyPir.LocalLang where

-- Type signature and extra requirements for a local language
record LocalLang (Loc : Set) : Set₁ where
  field
    -- Type signature of the language
    ⅀ₑ : TypeSignature

    -- Kinds have decidable equality
    ≡-dec-Kndₑ : DecidableEquality (⅀ₑ .⅀ₖ .Knd)

    -- Type constructor symbols have decidable equality
    ≡-dec-TySymbₑ : DecidableEquality (⅀ₑ .⅀ₖ .TySymb)

    -- Kind of local types
    TyKnd : ⅀ₑ .⅀ₖ .Knd

    -- Semantics
    _⇒ₑ_ : Tm ⅀ₑ → Tm ⅀ₑ → Set
    -- Values
    Valₑ : Tm ⅀ₑ → Set
    -- Only well-typed ground-terms can be values
    ⊢Valₑ : ∀{e} → Valₑ e → Σ[ t ∈ _ ] (typed ⅀ₑ [] [] e t)
    -- Values cannot step
    valNoStepₑ : ∀{e1 e2} → Valₑ e1 → ¬ (e1 ⇒ₑ e2)
    -- We have type safety
    preservationₑ : ∀{e1 e2 t} →
                    typed ⅀ₑ [] [] e1 t →
                    e1 ⇒ₑ e2 →
                    typed ⅀ₑ [] [] e2 t
    progressₑ : ∀{e1 t} →
                typed ⅀ₑ [] [] e1 t →
                (Valₑ e1) ⊎ (Σ[ e2 ∈ Tm ⅀ₑ ] e1 ⇒ₑ e2)

    -- Boolean type
    Boolₑ : Ty (⅀ₑ .⅀ₖ)
    ⊢Boolₑ : kinded (⅀ₑ .⅀ₖ) [] Boolₑ TyKnd
    -- True and false are boolean values
    ttₑ : Tm ⅀ₑ
    ⊢ttₑ : typed ⅀ₑ [] [] ttₑ (TyKnd , Boolₑ)
    tt-Valₑ : Valₑ ttₑ
    ffₑ : Tm ⅀ₑ
    ⊢ffₑ : typed ⅀ₑ [] [] ffₑ (TyKnd , Boolₑ)
    ff-Valₑ : Valₑ ffₑ
    -- The only ground boolean values are true and false
    invertBoolₑ : ∀{e} → typed ⅀ₑ [] [] e (TyKnd , Boolₑ) → Valₑ e → e ≡ ttₑ ⊎ e ≡ ffₑ

    -- Location type
    Locₑ : Ty (⅀ₑ .⅀ₖ)
    ⊢Locₑ : kinded (⅀ₑ .⅀ₖ) [] Locₑ TyKnd
    -- Each location has a corresponding literal value
    litLocₑ : Loc → Tm ⅀ₑ
    ⊢litLocₑ : (L : Loc) → typed ⅀ₑ [] [] (litLocₑ L) (TyKnd , Locₑ)
    litLoc-Valₑ : (L : Loc) → Valₑ (litLocₑ L)
    -- The only ground location values are literals
    invertLocₑ : ∀{e} → typed ⅀ₑ [] [] e (TyKnd , Locₑ) → Valₑ e → Σ[ L ∈ Loc ] (e ≡ litLocₑ L)

    -- Type for representations of local types
    TyRepₑ : Ty (⅀ₑ .⅀ₖ)
    ⊢TyRepₑ : kinded (⅀ₑ .⅀ₖ) [] TyRepₑ TyKnd
    Elₑ : ∀{e} → typed ⅀ₑ [] [] e (TyKnd , TyRepₑ) → Valₑ e →
          Σ[ t ∈ Ty (⅀ₑ .⅀ₖ) ] kinded (⅀ₑ .⅀ₖ) [] t TyKnd

open LocalLang public
