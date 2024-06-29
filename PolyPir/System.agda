{-# OPTIONS --safe #-}

open import Level renaming (zero to ℓ-zero; suc to ℓ-suc; _⊔_ to ℓ-max)
open import Data.Empty
open import Data.Unit
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map; _<*>_)
open import Data.Product.Properties
open import Data.Bool
open import Data.Nat hiding (_⊔_) renaming (_≟_ to ≡-dec-ℕ)
open import Data.List
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
open import Terms
open import Kinding
open import PolyPir.LocalLang

module PolyPir.System
  -- Location values
  (Loc : Set)
  -- Locations should have decidable equality
  (≡-dec-Loc : DecidableEquality Loc)

  -- Local language
  (𝕃 : LocalLang Loc)
  where

open import PolyPir.ChorTypes Loc ≡-dec-Loc 𝕃
open import PolyPir.TypeOperations Loc ≡-dec-Loc 𝕃
open import PolyPir.ChorTerms Loc ≡-dec-Loc 𝕃
open import PolyPir.TermOperations Loc ≡-dec-Loc 𝕃
open import PolyPir.ChorEquality Loc ≡-dec-Loc 𝕃
open import PolyPir.CtrlLang Loc ≡-dec-Loc 𝕃
open import PolyPir.CtrlSemantics Loc ≡-dec-Loc 𝕃

System : Set
System = Loc → Ctrl

_∈_ : Loc → List Loc → Set
L ∈ [] = ⊥
L ∈ (L' ∷ ρ) = L ≡ L' ⊎ L ∈ ρ

_?∈_ : (L : Loc) (ρ : List Loc) → Dec (L ∈ ρ)
L ?∈ [] = no id
L ?∈ (L1 ∷ Ls) with ≡-dec-Loc L L1 | L ?∈ Ls
... | yes p | _     = yes (inl p)
... | no ¬p | yes q = yes (inr q)
... | no ¬p | no ¬q = no λ{ (inl p) → ¬p p ; (inr q) → ¬q q }

Dec-rec : ∀{a b} {A : Set a} {B : Set b} →
          Dec A → (A → B) → (¬ A → B) → B
Dec-rec (yes x) f g = f x
Dec-rec (no ¬x) f g = g ¬x

Dec-rec-ind : ∀{a b ℓ} {A : Set a} {B : Set b}
              (P : B → Set ℓ)
              (d : Dec A) {f : A → B} {g : ¬ A → B} →
              ((x : A) → P (f x)) →
              ((¬x : ¬ A) → P (g ¬x)) →
              P (Dec-rec d f g)
Dec-rec-ind P (yes x) f g = f x
Dec-rec-ind P (no ¬x) f g = g ¬x

Dec-rec-ind₂ : ∀{a b1 b2 ℓ} {A : Set a} {B1 : Set b1} {B2 : Set b2}
              (P : B1 → B2 → Set ℓ)
              (d : Dec A)
              {f1 : A → B1} {g1 : ¬ A → B1}
              {f2 : A → B2} {g2 : ¬ A → B2} →
              ((x : A) → P (f1 x) (f2 x)) →
              ((¬x : ¬ A) → P (g1 ¬x) (g2 ¬x)) →
              P (Dec-rec d f1 g1) (Dec-rec d f2 g2)
Dec-rec-ind₂ P (yes x) f g = f x
Dec-rec-ind₂ P (no ¬x) f g = g ¬x

_[_:=_] : System → Loc → Ctrl → System
(Π [ L := E ]) L' = Dec-rec (≡-dec-Loc L L') (λ _ → E) (λ _ → Π L')

_[_*:=_] : System → List Loc → System → System
(Π [ ρ *:= Π' ]) L = Dec-rec (L ?∈ ρ) (λ _ → Π' L) (λ _ → Π L)

_≼S_ : System → System → Set
Π1 ≼S Π2 = ∀ L → Π1 L ≼ Π2 L

:=-≼S' : ∀{Π1 Π2 E1 E2 L} →
        (∀ L' → L' ≢ L → Π1 L' ≼ Π2 L') →
        E1 ≼ E2 →
        (Π1 [ L := E1 ]) ≼S (Π2 [ L := E2 ])
:=-≼S' {L = L} Π1≼Π2 E1≼E2 L' with ≡-dec-Loc L L' | inspect (≡-dec-Loc L) L'
... | yes L≡L' | _ = E1≼E2
... | no ¬L≡L' | _ = Π1≼Π2 L' (¬L≡L' ∘ sym)

:=-≼S : ∀{Π1 Π2 E1 E2 L} →
        Π1 ≼S Π2 →
        E1 ≼ E2 →
        (Π1 [ L := E1 ]) ≼S (Π2 [ L := E2 ])
:=-≼S Π1≼Π2 = :=-≼S' (λ L' _ → Π1≼Π2 L')

*:=-≼S' : ∀{Π1 Π2 ρ Π1' Π2'} →
          ((L : Loc) → ¬ (L ∈ ρ) → Π1 L ≼ Π2 L) →
          ((L : Loc) → L ∈ ρ → Π1' L ≼ Π2' L) →
          (Π1 [ ρ *:= Π1' ]) ≼S (Π2 [ ρ *:= Π2' ])
*:=-≼S' {ρ = ρ} Π1≼Π2 Π1'≼Π2' L with L ?∈ ρ | inspect (_?∈_ L) ρ
... | yes L∈ρ | _ = Π1'≼Π2' L L∈ρ
... | no ¬L∈ρ | _ = Π1≼Π2 L ¬L∈ρ

*:=-≼S : ∀{Π1 Π2 ρ Π1' Π2'} →
          Π1 ≼S Π2 →
          ((L : Loc) → L ∈ ρ → Π1' L ≼ Π2' L) →
          (Π1 [ ρ *:= Π1' ]) ≼S (Π2 [ ρ *:= Π2' ])
*:=-≼S Π1≼Π2 = *:=-≼S' (λ L _ → Π1≼Π2 L)

-- System semantics
data SysLabel : Set where
  ιL ιSyncL : SysLabel
  SendRecvL : (L1 : Loc) (v : Tmₑ) (L2 : Loc) → SysLabel
  SyncL : (L1 : Loc) (d : Bool) (L2 : Loc) → SysLabel
  SendRecvLocL : (L : Loc) (Lv : Loc) (ρ : List Loc) → SysLabel
  SendRecvTyL : (L : Loc) (t : Tyₑ) (ρ : List Loc) → SysLabel

data _⇒S[_]_ : System → SysLabel → System → Set where
  ιStep : ∀{Π L E} →
          Π L ⇒E[ ιL ⨾ L ] E →
          Π ⇒S[ ιL ] (Π [ L := E ])
  ιSyncStep : ∀{Π Π'} →
              (∀ L → Π L ⇒E[ ιSyncL ⨾ L ] Π' L) →
              Π ⇒S[ ιSyncL ] Π'
  CommStep : ∀{Π L1 L2 v E1 E2} →
             L1 ≢ L2 →
             Π L1 ⇒E[ SendL v L2 ⨾ L1 ] E1 →
             Π L2 ⇒E[ RecvL L1 v ⨾ L2 ] E2 →
             Π ⇒S[ SendRecvL L1 v L2 ] ((Π [ L1 := E1 ]) [ L2 := E2 ])
  SyncStep : ∀{Π L1 L2 d E1 E2} →
             L1 ≢ L2 →
             Π L1 ⇒E[ SendSyncL d L2 ⨾ L1 ] E1 →
             Π L2 ⇒E[ RecvSyncL L1 d ⨾ L2 ] E2 →
             Π ⇒S[ SyncL L1 d L2 ] ((Π [ L1 := E1 ]) [ L2 := E2 ])
  CommTyStep : ∀{Π ρ Π' L tₑ E1} →
              Π L ⇒E[ SendTyL tₑ ρ ⨾ L ] E1 →
              ((L' : Loc) → L' ≢ L → L' ∈ ρ → Π L' ⇒E[ RecvTyL L tₑ ⨾ L' ] Π' L') →
              Π ⇒S[ SendRecvTyL L tₑ ρ ] ((Π [ ρ *:= Π' ]) [ L := E1 ])
  CommLocStep : ∀{Π ρ Π' L Lv E1} →
                  Π L ⇒E[ SendLocL Lv ρ ⨾ L ] E1 →
                  ((L' : Loc) → L' ≢ L → L' ∈ ρ → Π L' ⇒E[ RecvLocL L Lv ⨾ L' ] Π' L') →
                  Π ⇒S[ SendRecvLocL L Lv ρ ] ((Π [ ρ *:= Π' ]) [ L := E1 ])

Π-⇒-Lifts : ∀{Π1 Π1' Π2 lS} →
              Π1 ≼S Π2 →
              Π1 ⇒S[ lS ] Π1' →
              Σ[ Π2' ∈ System ]
              Π1' ≼S Π2' ×
              Π2 ⇒S[ lS ] Π2'
Π-⇒-Lifts {Π1} {Π2 = Π2} Π1≼Π2 (ιStep {L = L} {E1} Π1-L⇒E2)
  with ⇒-Lifts-ι (Π1≼Π2 L) Π1-L⇒E2
... | (E2 , E1≼E2 , Π2-L⇒E2) =
  (Π2 [ L := E2 ]) , :=-≼S Π1≼Π2 E1≼E2 , ιStep Π2-L⇒E2
Π-⇒-Lifts {Π1} {Π2 = Π2} Π1≼Π2 (ιSyncStep {Π' = Π1'} Π1⇒Π1') =
  (λ L → ⇒-Lifts-ιSync (Π1≼Π2 L) (Π1⇒Π1' L) .fst) ,
  (λ L → ⇒-Lifts-ιSync (Π1≼Π2 L) (Π1⇒Π1' L) .snd .fst) ,
  ιSyncStep λ L → ⇒-Lifts-ιSync (Π1≼Π2 L) (Π1⇒Π1' L) .snd .snd
Π-⇒-Lifts {Π1} {Π2 = Π2} Π1≼Π2
  (CommStep {L1 = L1} {L2} {v} {E1} {E2} L1≢L2 Π1-L1⇒E1 Π1-L2⇒E2)
  with ⇒-Lifts-Send (Π1≼Π2 L1) Π1-L1⇒E1 | ⇒-Lifts-Recv (Π1≼Π2 L2) Π1-L2⇒E2
... | (E1' , E1≼E1' , Π2-L1⇒E1') | (E2' , E2≼E2' , Π2-L2⇒E2') =
  ((Π2 [ L1 := E1' ]) [ L2 := E2' ]) ,
  :=-≼S (:=-≼S Π1≼Π2 E1≼E1') E2≼E2' ,
  CommStep L1≢L2 Π2-L1⇒E1' Π2-L2⇒E2'
Π-⇒-Lifts {Π1} {Π2 = Π2} Π1≼Π2
  (SyncStep {L1 = L1} {L2} {d} {E1} {E2} L1≢L2 Π1-L1⇒E1 Π1-L2⇒E2)
  with ⇒-Lifts-SendSync (Π1≼Π2 L1) Π1-L1⇒E1 | ⇒-Lifts-RecvSync (Π1≼Π2 L2) Π1-L2⇒E2
... | (E1' , E1≼E1' , Π2-L1⇒E1') | (E2' , E2≼E2' , Π2-L2⇒E2') =
  ((Π2 [ L1 := E1' ]) [ L2 := E2' ]) ,
  :=-≼S (:=-≼S Π1≼Π2 E1≼E1') E2≼E2' ,
  SyncStep L1≢L2 Π2-L1⇒E1' Π2-L2⇒E2'
Π-⇒-Lifts {Π1} {Π2 = Π2} Π1≼Π2
  (CommTyStep {ρ = ρ} {Π1'} {L} {tₑ} {E1} Π1-L⇒E1 ρ\L-Π1⇒Π1')
  with ⇒-Lifts-SendTy (Π1≼Π2 L) Π1-L⇒E1
... | (E2 , E1≼E2 , Π2-L⇛E2) =
  ((Π2 [ ρ *:= (λ L' → Dec-rec (≡-dec-Loc L' L)
    (λ L'≡L → E2)
    (λ L'≢L → Dec-rec (L' ?∈ ρ)
      (λ L'∈ρ → ⇒-Lifts-RecvTy (Π1≼Π2 L') (ρ\L-Π1⇒Π1' L' L'≢L L'∈ρ) .fst)
      λ L'∉ρ → Π2 L')) ])
    [ L := E2 ]) ,
  :=-≼S'
    (λ L' L'≢L → Dec-rec-ind₂ _≼_ (L' ?∈ ρ)
      (λ L'∈ρ → Dec-rec-ind (Π1' L' ≼_) (≡-dec-Loc L' L)
        (λ L'≡L → ⊥-elim $ L'≢L L'≡L)
        λ L'≢L → Dec-rec-ind (Π1' L' ≼_) (L' ?∈ ρ)
          (λ L'∈ρ → ⇒-Lifts-RecvTy (Π1≼Π2 L') (ρ\L-Π1⇒Π1' L' L'≢L L'∈ρ) .snd .fst)
          λ L'∉ρ → ⊥-elim $ L'∉ρ L'∈ρ)
      λ L'∉ρ → Π1≼Π2 L')
    E1≼E2 ,
  CommTyStep
    Π2-L⇛E2
    λ L' L'≢L L'∈ρ → Dec-rec-ind (Π2 L' ⇒E[ RecvTyL L tₑ ⨾ L' ]_) (≡-dec-Loc L' L)
      (λ L'≡L → ⊥-elim $ L'≢L L'≡L)
      λ L'≢L-2 → Dec-rec-ind (Π2 L' ⇒E[ RecvTyL L tₑ ⨾ L' ]_) (L' ?∈ ρ)
        (λ L'∈ρ-2 → ⇒-Lifts-RecvTy (Π1≼Π2 L') (ρ\L-Π1⇒Π1' L' L'≢L-2 L'∈ρ-2) .snd .snd)
        λ L'∉ρ → ⊥-elim $ L'∉ρ L'∈ρ
Π-⇒-Lifts {Π1} {Π2 = Π2} Π1≼Π2 (CommLocStep {ρ = ρ} {Π1'} {L} {Lv} {E1} Π1-L⇒E1 ρ\L-Π1⇒Π1')
  with ⇒-Lifts-SendLoc (Π1≼Π2 L) Π1-L⇒E1
... | (E2 , E1≼E2 , Π2-L⇛E2) =
  ((Π2 [ ρ *:= (λ L' → Dec-rec (≡-dec-Loc L' L)
    (λ L'≡L → E2)
    (λ L'≢L → Dec-rec (L' ?∈ ρ)
      (λ L'∈ρ → ⇒-Lifts-RecvLoc (Π1≼Π2 L') (ρ\L-Π1⇒Π1' L' L'≢L L'∈ρ) .fst)
      λ L'∉ρ → Π2 L')) ])
    [ L := E2 ]) ,
  :=-≼S'
    (λ L' L'≢L → Dec-rec-ind₂ _≼_ (L' ?∈ ρ)
      (λ L'∈ρ → Dec-rec-ind (Π1' L' ≼_) (≡-dec-Loc L' L)
        (λ L'≡L → ⊥-elim $ L'≢L L'≡L)
        λ L'≢L → Dec-rec-ind (Π1' L' ≼_) (L' ?∈ ρ)
          (λ L'∈ρ → ⇒-Lifts-RecvLoc (Π1≼Π2 L') (ρ\L-Π1⇒Π1' L' L'≢L L'∈ρ) .snd .fst)
          λ L'∉ρ → ⊥-elim $ L'∉ρ L'∈ρ)
      λ L'∉ρ → Π1≼Π2 L')
    E1≼E2 ,
  CommLocStep
    Π2-L⇛E2
    λ L' L'≢L L'∈ρ → Dec-rec-ind (Π2 L' ⇒E[ RecvLocL L Lv ⨾ L' ]_) (≡-dec-Loc L' L)
      (λ L'≡L → ⊥-elim $ L'≢L L'≡L)
      λ L'≢L-2 → Dec-rec-ind (Π2 L' ⇒E[ RecvLocL L Lv ⨾ L' ]_) (L' ?∈ ρ)
        (λ L'∈ρ-2 → ⇒-Lifts-RecvLoc (Π1≼Π2 L') (ρ\L-Π1⇒Π1' L' L'≢L-2 L'∈ρ-2) .snd .snd)
        λ L'∉ρ → ⊥-elim $ L'∉ρ L'∈ρ