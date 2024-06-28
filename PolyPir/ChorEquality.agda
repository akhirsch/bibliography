{-# OPTIONS --safe #-}

open import Level renaming (zero to ℓ-zero; suc to ℓ-suc; _⊔_ to ℓ-max)
open import Data.Empty
open import Data.Unit
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map; _<*>_)
open import Data.Product.Properties
open import Data.Bool
open import Data.Bool.Properties renaming (_≟_ to ≡-dec-Bool)
open import Data.Nat hiding (_⊔_) renaming (_≟_ to ≡-dec-ℕ)
open import Data.List
open import Data.List.Properties
open import Data.Maybe renaming (map to mmap)
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr) hiding (map)
open import Relation.Nullary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality
open import Function

open ≡-Reasoning

open import Common
open import Common
open import KindSignatures
open import TypeSignatures
open import TypeContexts
open import Types
open import Kinding
open import TypeEquality
open import TermEquality
open import PolyPir.LocalLang

module PolyPir.ChorEquality
  -- Location values
  (Loc : Set)
  -- Locations should have decidable equality
  (≡-dec-Loc : DecidableEquality Loc)

  -- Local language
  (𝕃 : LocalLang Loc)
  where

open import PolyPir.ChorTypes Loc ≡-dec-Loc 𝕃
open import PolyPir.ChorTerms Loc ≡-dec-Loc 𝕃

≡-dec-ChorKnd : DecidableEquality ChorKnd
≡-dec-ChorKnd (LocKnd κ1ₑ) (LocKnd κ2ₑ)
  with 𝕃 .≡-dec-Kndₑ κ1ₑ κ2ₑ
... | yes p = yes $ cong LocKnd p
... | no ¬p = no λ{ refl → ¬p refl }
≡-dec-ChorKnd (LocKnd κₑ) (Bnd κₑ₁) = no (λ ())
≡-dec-ChorKnd (LocKnd κₑ) * = no (λ ())
≡-dec-ChorKnd (LocKnd κₑ) *ₗ = no (λ ())
≡-dec-ChorKnd (LocKnd κₑ) *ₛ = no (λ ())
≡-dec-ChorKnd (Bnd κₑ) (LocKnd κₑ₁) = no (λ ())
≡-dec-ChorKnd (Bnd κ1ₑ) (Bnd κ2ₑ)
  with 𝕃 .≡-dec-Kndₑ κ1ₑ κ2ₑ
... | yes p = yes $ cong Bnd p
... | no ¬p = no λ{ refl → ¬p refl }
≡-dec-ChorKnd (Bnd κₑ) * = no (λ ())
≡-dec-ChorKnd (Bnd κₑ) *ₗ = no (λ ())
≡-dec-ChorKnd (Bnd κₑ) *ₛ = no (λ ())
≡-dec-ChorKnd * (LocKnd κₑ) = no (λ ())
≡-dec-ChorKnd * (Bnd κₑ) = no (λ ())
≡-dec-ChorKnd * * = yes refl
≡-dec-ChorKnd * *ₗ = no (λ ())
≡-dec-ChorKnd * *ₛ = no (λ ())
≡-dec-ChorKnd *ₗ (LocKnd κₑ) = no (λ ())
≡-dec-ChorKnd *ₗ (Bnd κₑ) = no (λ ())
≡-dec-ChorKnd *ₗ * = no (λ ())
≡-dec-ChorKnd *ₗ *ₗ = yes refl
≡-dec-ChorKnd *ₗ *ₛ = no (λ ())
≡-dec-ChorKnd *ₛ (LocKnd κₑ) = no (λ ())
≡-dec-ChorKnd *ₛ (Bnd κₑ) = no (λ ())
≡-dec-ChorKnd *ₛ * = no (λ ())
≡-dec-ChorKnd *ₛ *ₗ = no (λ ())
≡-dec-ChorKnd *ₛ *ₛ = yes refl

≡-dec-ChorTySymb : DecidableEquality ChorTySymb
≡-dec-ChorTySymb (EmbLocalTyS s1ₑ) (EmbLocalTyS s2ₑ)
  with 𝕃 .≡-dec-TySymbₑ s1ₑ s2ₑ
... | yes p = yes $ cong EmbLocalTyS p
... | no ¬p = no λ{ refl → ¬p refl }
≡-dec-ChorTySymb (EmbLocalTyS sₑ) (LocalS κₑ) = no (λ ())
≡-dec-ChorTySymb (EmbLocalTyS sₑ) AtS = no (λ ())
≡-dec-ChorTySymb (EmbLocalTyS sₑ) FunS = no (λ ())
≡-dec-ChorTySymb (EmbLocalTyS sₑ) (AllS κ ∀κ) = no (λ ())
≡-dec-ChorTySymb (EmbLocalTyS sₑ) (LitLocS L) = no (λ ())
≡-dec-ChorTySymb (EmbLocalTyS sₑ) EmpS = no (λ ())
≡-dec-ChorTySymb (EmbLocalTyS sₑ) SngS = no (λ ())
≡-dec-ChorTySymb (EmbLocalTyS sₑ) UnionS = no (λ ())
≡-dec-ChorTySymb (LocalS κₑ) (EmbLocalTyS sₑ) = no (λ ())
≡-dec-ChorTySymb (LocalS κ1ₑ) (LocalS κ2ₑ)
  with 𝕃 .≡-dec-Kndₑ κ1ₑ κ2ₑ
... | yes p = yes $ cong LocalS p
... | no ¬p = no λ{ refl → ¬p refl }
≡-dec-ChorTySymb (LocalS κₑ) AtS = no (λ ())
≡-dec-ChorTySymb (LocalS κₑ) FunS = no (λ ())
≡-dec-ChorTySymb (LocalS κₑ) (AllS κ ∀κ) = no (λ ())
≡-dec-ChorTySymb (LocalS κₑ) (LitLocS L) = no (λ ())
≡-dec-ChorTySymb (LocalS κₑ) EmpS = no (λ ())
≡-dec-ChorTySymb (LocalS κₑ) SngS = no (λ ())
≡-dec-ChorTySymb (LocalS κₑ) UnionS = no (λ ())
≡-dec-ChorTySymb AtS (EmbLocalTyS sₑ) = no (λ ())
≡-dec-ChorTySymb AtS (LocalS κₑ) = no (λ ())
≡-dec-ChorTySymb AtS AtS = yes refl
≡-dec-ChorTySymb AtS FunS = no (λ ())
≡-dec-ChorTySymb AtS (AllS κ ∀κ) = no (λ ())
≡-dec-ChorTySymb AtS (LitLocS L) = no (λ ())
≡-dec-ChorTySymb AtS EmpS = no (λ ())
≡-dec-ChorTySymb AtS SngS = no (λ ())
≡-dec-ChorTySymb AtS UnionS = no (λ ())
≡-dec-ChorTySymb FunS (EmbLocalTyS sₑ) = no (λ ())
≡-dec-ChorTySymb FunS (LocalS κₑ) = no (λ ())
≡-dec-ChorTySymb FunS AtS = no (λ ())
≡-dec-ChorTySymb FunS FunS = yes refl
≡-dec-ChorTySymb FunS (AllS κ ∀κ) = no (λ ())
≡-dec-ChorTySymb FunS (LitLocS L) = no (λ ())
≡-dec-ChorTySymb FunS EmpS = no (λ ())
≡-dec-ChorTySymb FunS SngS = no (λ ())
≡-dec-ChorTySymb FunS UnionS = no (λ ())
≡-dec-ChorTySymb (AllS κ ∀κ) (EmbLocalTyS sₑ) = no (λ ())
≡-dec-ChorTySymb (AllS κ ∀κ) (LocalS κₑ) = no (λ ())
≡-dec-ChorTySymb (AllS κ ∀κ) AtS = no (λ ())
≡-dec-ChorTySymb (AllS κ ∀κ) FunS = no (λ ())
≡-dec-ChorTySymb (AllS κ1 ∀κ1) (AllS κ2 ∀κ2) with ≡-dec-ChorKnd κ1 κ2
... | yes refl = yes $ cong (AllS κ1) $ canAbstract-isProp κ1 ∀κ1 ∀κ2
... | no  ¬p   = no λ{ refl → ¬p refl }
≡-dec-ChorTySymb (AllS κ ∀κ) (LitLocS L) = no (λ ())
≡-dec-ChorTySymb (AllS κ ∀κ) EmpS = no (λ ())
≡-dec-ChorTySymb (AllS κ ∀κ) SngS = no (λ ())
≡-dec-ChorTySymb (AllS κ ∀κ) UnionS = no (λ ())
≡-dec-ChorTySymb (LitLocS L) (EmbLocalTyS sₑ) = no (λ ())
≡-dec-ChorTySymb (LitLocS L) (LocalS κₑ) = no (λ ())
≡-dec-ChorTySymb (LitLocS L) AtS = no (λ ())
≡-dec-ChorTySymb (LitLocS L) FunS = no (λ ())
≡-dec-ChorTySymb (LitLocS L) (AllS κ ∀κ) = no (λ ())
≡-dec-ChorTySymb (LitLocS L1) (LitLocS L2) with ≡-dec-Loc L1 L2
... | yes p = yes $ cong LitLocS p
... | no ¬p = no λ{ refl → ¬p refl }
≡-dec-ChorTySymb (LitLocS L) EmpS = no (λ ())
≡-dec-ChorTySymb (LitLocS L) SngS = no (λ ())
≡-dec-ChorTySymb (LitLocS L) UnionS = no (λ ())
≡-dec-ChorTySymb EmpS (EmbLocalTyS sₑ) = no (λ ())
≡-dec-ChorTySymb EmpS (LocalS κₑ) = no (λ ())
≡-dec-ChorTySymb EmpS AtS = no (λ ())
≡-dec-ChorTySymb EmpS FunS = no (λ ())
≡-dec-ChorTySymb EmpS (AllS κ ∀κ) = no (λ ())
≡-dec-ChorTySymb EmpS (LitLocS L) = no (λ ())
≡-dec-ChorTySymb EmpS EmpS = yes refl
≡-dec-ChorTySymb EmpS SngS = no (λ ())
≡-dec-ChorTySymb EmpS UnionS = no (λ ())
≡-dec-ChorTySymb SngS (EmbLocalTyS sₑ) = no (λ ())
≡-dec-ChorTySymb SngS (LocalS κₑ) = no (λ ())
≡-dec-ChorTySymb SngS AtS = no (λ ())
≡-dec-ChorTySymb SngS FunS = no (λ ())
≡-dec-ChorTySymb SngS (AllS κ ∀κ) = no (λ ())
≡-dec-ChorTySymb SngS (LitLocS L) = no (λ ())
≡-dec-ChorTySymb SngS EmpS = no (λ ())
≡-dec-ChorTySymb SngS SngS = yes refl
≡-dec-ChorTySymb SngS UnionS = no (λ ())
≡-dec-ChorTySymb UnionS (EmbLocalTyS sₑ) = no (λ ())
≡-dec-ChorTySymb UnionS (LocalS κₑ) = no (λ ())
≡-dec-ChorTySymb UnionS AtS = no (λ ())
≡-dec-ChorTySymb UnionS FunS = no (λ ())
≡-dec-ChorTySymb UnionS (AllS κ ∀κ) = no (λ ())
≡-dec-ChorTySymb UnionS (LitLocS L) = no (λ ())
≡-dec-ChorTySymb UnionS EmpS = no (λ ())
≡-dec-ChorTySymb UnionS SngS = no (λ ())
≡-dec-ChorTySymb UnionS UnionS = yes refl

≡-dec-CTy : DecidableEquality CTy
≡-dec-CTy = ≡-dec-Ty C⅀ₖ ≡-dec-ChorTySymb

≡-dec-ChorTmSymb : DecidableEquality ChorTmSymb
≡-dec-ChorTmSymb (LocalTmS s1ₑ) (LocalTmS s2ₑ) with 𝕃 .≡-dec-TmSymbₑ s1ₑ s2ₑ
... | yes refl = yes refl
... | no ¬p = no λ{ refl → ¬p refl }
≡-dec-ChorTmSymb (LocalTmS sₑ) DoneS = no (λ ())
≡-dec-ChorTmSymb (LocalTmS sₑ) LamS = no (λ ())
≡-dec-ChorTmSymb (LocalTmS sₑ) FixS = no (λ ())
≡-dec-ChorTmSymb (LocalTmS sₑ) AppS = no (λ ())
≡-dec-ChorTmSymb (LocalTmS sₑ) (AbsS κ ∀κ) = no (λ ())
≡-dec-ChorTmSymb (LocalTmS sₑ) (AppTyS κ ∀κ) = no (λ ())
≡-dec-ChorTmSymb (LocalTmS sₑ) SendS = no (λ ())
≡-dec-ChorTmSymb (LocalTmS sₑ) (SyncS d) = no (λ ())
≡-dec-ChorTmSymb (LocalTmS sₑ) ITES = no (λ ())
≡-dec-ChorTmSymb (LocalTmS sₑ) LocalLetS = no (λ ())
≡-dec-ChorTmSymb (LocalTmS sₑ) TellTyS = no (λ ())
≡-dec-ChorTmSymb (LocalTmS sₑ) TellLocS = no (λ ())
≡-dec-ChorTmSymb DoneS (LocalTmS sₑ) = no (λ ())
≡-dec-ChorTmSymb DoneS DoneS = yes refl
≡-dec-ChorTmSymb DoneS LamS = no (λ ())
≡-dec-ChorTmSymb DoneS FixS = no (λ ())
≡-dec-ChorTmSymb DoneS AppS = no (λ ())
≡-dec-ChorTmSymb DoneS (AbsS κ ∀κ) = no (λ ())
≡-dec-ChorTmSymb DoneS (AppTyS κ ∀κ) = no (λ ())
≡-dec-ChorTmSymb DoneS SendS = no (λ ())
≡-dec-ChorTmSymb DoneS (SyncS d) = no (λ ())
≡-dec-ChorTmSymb DoneS ITES = no (λ ())
≡-dec-ChorTmSymb DoneS LocalLetS = no (λ ())
≡-dec-ChorTmSymb DoneS TellTyS = no (λ ())
≡-dec-ChorTmSymb DoneS TellLocS = no (λ ())
≡-dec-ChorTmSymb LamS (LocalTmS sₑ) = no (λ ())
≡-dec-ChorTmSymb LamS DoneS = no (λ ())
≡-dec-ChorTmSymb LamS LamS = yes refl
≡-dec-ChorTmSymb LamS FixS = no (λ ())
≡-dec-ChorTmSymb LamS AppS = no (λ ())
≡-dec-ChorTmSymb LamS (AbsS κ ∀κ) = no (λ ())
≡-dec-ChorTmSymb LamS (AppTyS κ ∀κ) = no (λ ())
≡-dec-ChorTmSymb LamS SendS = no (λ ())
≡-dec-ChorTmSymb LamS (SyncS d) = no (λ ())
≡-dec-ChorTmSymb LamS ITES = no (λ ())
≡-dec-ChorTmSymb LamS LocalLetS = no (λ ())
≡-dec-ChorTmSymb LamS TellTyS = no (λ ())
≡-dec-ChorTmSymb LamS TellLocS = no (λ ())
≡-dec-ChorTmSymb FixS (LocalTmS sₑ) = no (λ ())
≡-dec-ChorTmSymb FixS DoneS = no (λ ())
≡-dec-ChorTmSymb FixS LamS = no (λ ())
≡-dec-ChorTmSymb FixS FixS = yes refl
≡-dec-ChorTmSymb FixS AppS = no (λ ())
≡-dec-ChorTmSymb FixS (AbsS κ ∀κ) = no (λ ())
≡-dec-ChorTmSymb FixS (AppTyS κ ∀κ) = no (λ ())
≡-dec-ChorTmSymb FixS SendS = no (λ ())
≡-dec-ChorTmSymb FixS (SyncS d) = no (λ ())
≡-dec-ChorTmSymb FixS ITES = no (λ ())
≡-dec-ChorTmSymb FixS LocalLetS = no (λ ())
≡-dec-ChorTmSymb FixS TellTyS = no (λ ())
≡-dec-ChorTmSymb FixS TellLocS = no (λ ())
≡-dec-ChorTmSymb AppS (LocalTmS sₑ) = no (λ ())
≡-dec-ChorTmSymb AppS DoneS = no (λ ())
≡-dec-ChorTmSymb AppS LamS = no (λ ())
≡-dec-ChorTmSymb AppS FixS = no (λ ())
≡-dec-ChorTmSymb AppS AppS = yes refl
≡-dec-ChorTmSymb AppS (AbsS κ ∀κ) = no (λ ())
≡-dec-ChorTmSymb AppS (AppTyS κ ∀κ) = no (λ ())
≡-dec-ChorTmSymb AppS SendS = no (λ ())
≡-dec-ChorTmSymb AppS (SyncS d) = no (λ ())
≡-dec-ChorTmSymb AppS ITES = no (λ ())
≡-dec-ChorTmSymb AppS LocalLetS = no (λ ())
≡-dec-ChorTmSymb AppS TellTyS = no (λ ())
≡-dec-ChorTmSymb AppS TellLocS = no (λ ())
≡-dec-ChorTmSymb (AbsS κ ∀κ) (LocalTmS sₑ) = no (λ ())
≡-dec-ChorTmSymb (AbsS κ ∀κ) DoneS = no (λ ())
≡-dec-ChorTmSymb (AbsS κ ∀κ) LamS = no (λ ())
≡-dec-ChorTmSymb (AbsS κ ∀κ) FixS = no (λ ())
≡-dec-ChorTmSymb (AbsS κ ∀κ) AppS = no (λ ())
≡-dec-ChorTmSymb (AbsS κ1 ∀κ1) (AbsS κ2 ∀κ2) with ≡-dec-ChorKnd κ1 κ2
... | yes refl = yes (cong (AbsS κ1) (canAbstract-isProp κ1 ∀κ1 ∀κ2))
... | no ¬p = no λ{ refl → ¬p refl }
≡-dec-ChorTmSymb (AbsS κ ∀κ) (AppTyS κ₁ ∀κ₁) = no (λ ())
≡-dec-ChorTmSymb (AbsS κ ∀κ) SendS = no (λ ())
≡-dec-ChorTmSymb (AbsS κ ∀κ) (SyncS d) = no (λ ())
≡-dec-ChorTmSymb (AbsS κ ∀κ) ITES = no (λ ())
≡-dec-ChorTmSymb (AbsS κ ∀κ) LocalLetS = no (λ ())
≡-dec-ChorTmSymb (AbsS κ ∀κ) TellTyS = no (λ ())
≡-dec-ChorTmSymb (AbsS κ ∀κ) TellLocS = no (λ ())
≡-dec-ChorTmSymb (AppTyS κ ∀κ) (LocalTmS sₑ) = no (λ ())
≡-dec-ChorTmSymb (AppTyS κ ∀κ) DoneS = no (λ ())
≡-dec-ChorTmSymb (AppTyS κ ∀κ) LamS = no (λ ())
≡-dec-ChorTmSymb (AppTyS κ ∀κ) FixS = no (λ ())
≡-dec-ChorTmSymb (AppTyS κ ∀κ) AppS = no (λ ())
≡-dec-ChorTmSymb (AppTyS κ ∀κ) (AbsS κ₁ ∀κ₁) = no (λ ())
≡-dec-ChorTmSymb (AppTyS κ1 ∀κ1) (AppTyS κ2 ∀κ2) with ≡-dec-ChorKnd κ1 κ2
... | yes refl = yes (cong (AppTyS κ1) (canAbstract-isProp κ1 ∀κ1 ∀κ2))
... | no ¬p = no λ{ refl → ¬p refl }
≡-dec-ChorTmSymb (AppTyS κ ∀κ) SendS = no (λ ())
≡-dec-ChorTmSymb (AppTyS κ ∀κ) (SyncS d) = no (λ ())
≡-dec-ChorTmSymb (AppTyS κ ∀κ) ITES = no (λ ())
≡-dec-ChorTmSymb (AppTyS κ ∀κ) LocalLetS = no (λ ())
≡-dec-ChorTmSymb (AppTyS κ ∀κ) TellTyS = no (λ ())
≡-dec-ChorTmSymb (AppTyS κ ∀κ) TellLocS = no (λ ())
≡-dec-ChorTmSymb SendS (LocalTmS sₑ) = no (λ ())
≡-dec-ChorTmSymb SendS DoneS = no (λ ())
≡-dec-ChorTmSymb SendS LamS = no (λ ())
≡-dec-ChorTmSymb SendS FixS = no (λ ())
≡-dec-ChorTmSymb SendS AppS = no (λ ())
≡-dec-ChorTmSymb SendS (AbsS κ ∀κ) = no (λ ())
≡-dec-ChorTmSymb SendS (AppTyS κ ∀κ) = no (λ ())
≡-dec-ChorTmSymb SendS SendS = yes refl
≡-dec-ChorTmSymb SendS (SyncS d) = no (λ ())
≡-dec-ChorTmSymb SendS ITES = no (λ ())
≡-dec-ChorTmSymb SendS LocalLetS = no (λ ())
≡-dec-ChorTmSymb SendS TellTyS = no (λ ())
≡-dec-ChorTmSymb SendS TellLocS = no (λ ())
≡-dec-ChorTmSymb (SyncS d) (LocalTmS sₑ) = no (λ ())
≡-dec-ChorTmSymb (SyncS d) DoneS = no (λ ())
≡-dec-ChorTmSymb (SyncS d) LamS = no (λ ())
≡-dec-ChorTmSymb (SyncS d) FixS = no (λ ())
≡-dec-ChorTmSymb (SyncS d) AppS = no (λ ())
≡-dec-ChorTmSymb (SyncS d) (AbsS κ ∀κ) = no (λ ())
≡-dec-ChorTmSymb (SyncS d) (AppTyS κ ∀κ) = no (λ ())
≡-dec-ChorTmSymb (SyncS d) SendS = no (λ ())
≡-dec-ChorTmSymb (SyncS d1) (SyncS d2) with ≡-dec-Bool d1 d2
... | yes refl = yes refl
... | no ¬p = no λ{ refl → ¬p refl }
≡-dec-ChorTmSymb (SyncS d) ITES = no (λ ())
≡-dec-ChorTmSymb (SyncS d) LocalLetS = no (λ ())
≡-dec-ChorTmSymb (SyncS d) TellTyS = no (λ ())
≡-dec-ChorTmSymb (SyncS d) TellLocS = no (λ ())
≡-dec-ChorTmSymb ITES (LocalTmS sₑ) = no (λ ())
≡-dec-ChorTmSymb ITES DoneS = no (λ ())
≡-dec-ChorTmSymb ITES LamS = no (λ ())
≡-dec-ChorTmSymb ITES FixS = no (λ ())
≡-dec-ChorTmSymb ITES AppS = no (λ ())
≡-dec-ChorTmSymb ITES (AbsS κ ∀κ) = no (λ ())
≡-dec-ChorTmSymb ITES (AppTyS κ ∀κ) = no (λ ())
≡-dec-ChorTmSymb ITES SendS = no (λ ())
≡-dec-ChorTmSymb ITES (SyncS d) = no (λ ())
≡-dec-ChorTmSymb ITES ITES = yes refl
≡-dec-ChorTmSymb ITES LocalLetS = no (λ ())
≡-dec-ChorTmSymb ITES TellTyS = no (λ ())
≡-dec-ChorTmSymb ITES TellLocS = no (λ ())
≡-dec-ChorTmSymb LocalLetS (LocalTmS sₑ) = no (λ ())
≡-dec-ChorTmSymb LocalLetS DoneS = no (λ ())
≡-dec-ChorTmSymb LocalLetS LamS = no (λ ())
≡-dec-ChorTmSymb LocalLetS FixS = no (λ ())
≡-dec-ChorTmSymb LocalLetS AppS = no (λ ())
≡-dec-ChorTmSymb LocalLetS (AbsS κ ∀κ) = no (λ ())
≡-dec-ChorTmSymb LocalLetS (AppTyS κ ∀κ) = no (λ ())
≡-dec-ChorTmSymb LocalLetS SendS = no (λ ())
≡-dec-ChorTmSymb LocalLetS (SyncS d) = no (λ ())
≡-dec-ChorTmSymb LocalLetS ITES = no (λ ())
≡-dec-ChorTmSymb LocalLetS LocalLetS = yes refl
≡-dec-ChorTmSymb LocalLetS TellTyS = no (λ ())
≡-dec-ChorTmSymb LocalLetS TellLocS = no (λ ())
≡-dec-ChorTmSymb TellTyS (LocalTmS sₑ) = no (λ ())
≡-dec-ChorTmSymb TellTyS DoneS = no (λ ())
≡-dec-ChorTmSymb TellTyS LamS = no (λ ())
≡-dec-ChorTmSymb TellTyS FixS = no (λ ())
≡-dec-ChorTmSymb TellTyS AppS = no (λ ())
≡-dec-ChorTmSymb TellTyS (AbsS κ ∀κ) = no (λ ())
≡-dec-ChorTmSymb TellTyS (AppTyS κ ∀κ) = no (λ ())
≡-dec-ChorTmSymb TellTyS SendS = no (λ ())
≡-dec-ChorTmSymb TellTyS (SyncS d) = no (λ ())
≡-dec-ChorTmSymb TellTyS ITES = no (λ ())
≡-dec-ChorTmSymb TellTyS LocalLetS = no (λ ())
≡-dec-ChorTmSymb TellTyS TellTyS = yes refl
≡-dec-ChorTmSymb TellTyS TellLocS = no (λ ())
≡-dec-ChorTmSymb TellLocS (LocalTmS sₑ) = no (λ ())
≡-dec-ChorTmSymb TellLocS DoneS = no (λ ())
≡-dec-ChorTmSymb TellLocS LamS = no (λ ())
≡-dec-ChorTmSymb TellLocS FixS = no (λ ())
≡-dec-ChorTmSymb TellLocS AppS = no (λ ())
≡-dec-ChorTmSymb TellLocS (AbsS κ ∀κ) = no (λ ())
≡-dec-ChorTmSymb TellLocS (AppTyS κ ∀κ) = no (λ ())
≡-dec-ChorTmSymb TellLocS SendS = no (λ ())
≡-dec-ChorTmSymb TellLocS (SyncS d) = no (λ ())
≡-dec-ChorTmSymb TellLocS ITES = no (λ ())
≡-dec-ChorTmSymb TellLocS LocalLetS = no (λ ())
≡-dec-ChorTmSymb TellLocS TellTyS = no (λ ())
≡-dec-ChorTmSymb TellLocS TellLocS = yes refl

≡-dec-CTm : DecidableEquality CTm
≡-dec-CTm = ≡-dec-Tm C⅀ ≡-dec-ChorTySymb ≡-dec-ChorTmSymb
