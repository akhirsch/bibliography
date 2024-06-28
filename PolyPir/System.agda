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

System : Set
System = Loc → Ctrl

_∈_ : Loc → List Loc → Set
L ∈ [] = ⊥
L ∈ (L1 ∷ Ls) = L ≡ L1 ⊎ L ∈ Ls

_[_:=_] : System → Loc → Ctrl → System
(Π [ L := E ]) L' with ≡-dec-Loc L L'
... | yes _ = E
... | no  _ = Π L'

_[_*:=_] : System → List Loc → System → System
Π [ [] *:= Π' ] = Π
Π [ L ∷ ρ *:= Π' ] = (Π [ L := Π' L ]) [ ρ *:= Π' ]

_≼S_ : System → System → Set
Π1 ≼S Π2 = ∀ L → Π1 L ≼ Π2 L

:=-≼S : ∀{Π1 Π2 E1 E2 L} →
        Π1 ≼S Π2 →
        E1 ≼ E2 →
        (Π1 [ L := E1 ]) ≼S (Π2 [ L := E2 ])
:=-≼S {L = L} Π1≼Π2 E1≼E2 L' with ≡-dec-Loc L L'
... | yes _ = E1≼E2
... | no  _ = Π1≼Π2 L'

{-
System semantics
-}
data SysLabel : Set where
  ιL ιSyncL : SysLabel
  SendRecvL : (L1 : Loc) (v : Tmₑ) (L2 : Loc) → SysLabel
  SyncL : (L1 : Loc) (d : Bool) (L2 : Loc) → SysLabel
  SendRecvLocL : (L : Loc) (Lv : Loc) (ρ : List Loc) → SysLabel
  SendRecvTyL : (L : Loc) (t : Tyₑ) (ρ : List Loc) → SysLabel

data _⇒S[_]_ : System → SysLabel → System → Set where
  ιStep : ∀{Π} L E →
          Π L ⇒E[ ιL ⨾ L ] E →
          Π ⇒S[ ιL ] (Π [ L := E ])
  ιSyncStep : ∀{Π} Π' →
              (∀ L → Π L ⇒E[ ιSyncL ⨾ L ] Π' L) →
              Π ⇒S[ ιSyncL ] Π'
  CommStep : ∀{Π} L1 L2 v E1 E2 →
             L1 ≢ L2 →
             Π L1 ⇒E[ SendL v L2 ⨾ L1 ] E1 →
             Π L2 ⇒E[ RecvL L1 v ⨾ L2 ] E2 →
             Π ⇒S[ SendRecvL L1 v L2 ] ((Π [ L1 := E1 ]) [ L2 := E2 ])
  SyncStep : ∀{Π} L1 L2 d E1 E2 →
             L1 ≢ L2 →
             Π L1 ⇒E[ SendSyncL d L2 ⨾ L1 ] E1 →
             Π L2 ⇒E[ RecvSyncL L1 d ⨾ L2 ] E2 →
             Π ⇒S[ SyncL L1 d L2 ] ((Π [ L1 := E1 ]) [ L2 := E2 ])
  CommTyStep : ∀{Π} Π' L ρ tₑ E1 →
              Π L ⇒E[ SendTyL tₑ ρ ⨾ L ] E1 →
              (∀ L' → L' ∈ ρ → Π L' ⇒E[ RecvTyL L' tₑ ⨾ L' ] Π' L') →
              Π ⇒S[ SendRecvTyL L tₑ ρ ] (Π [ ρ *:= Π' ])

Lifting : ∀{Π1 Π1' Π2 lS} →
          Π1 ≼S Π2 →
          Π1 ⇒S[ lS ] Π1' →
          Σ[ Π2' ∈ System ]
          Π1' ≼S Π2' ×
          Π2 ⇒S[ lS ] Π2'
Lifting {Π1} {Π2 = Π2} Π1≼Π2 (ιStep L E1 Π1-L⇒E1)
  with ι-Lift (Π1≼Π2 L) Π1-L⇒E1
... | (E2 , E1≼E2 , Π2-L⇒E2) =
  (Π2 [ L := E2 ]) ,
  :=-≼S Π1≼Π2 E1≼E2 ,
  ιStep L E2 Π2-L⇒E2 
Lifting Π1≼Π2 (ιSyncStep Π1' Π1-L⇒Π1'-L) =
  let Π2' = λ L → ιSync-Lift (Π1≼Π2 L) (Π1-L⇒Π1'-L L) .fst in
  Π2' ,
  (λ L → ιSync-Lift (Π1≼Π2 L) (Π1-L⇒Π1'-L L) .snd .fst) ,
  ιSyncStep Π2' λ L → ιSync-Lift (Π1≼Π2 L) (Π1-L⇒Π1'-L L) .snd .snd
Lifting {Π2 = Π2} Π1≼Π2 (CommStep L1 L2 v E1 E2 L1≢L2 Π1-L1⇒E1 Π1-L2⇒E2)
  with Send-Lift (Π1≼Π2 L1) (Π1≼Π2 L2) Π1-L1⇒E1 Π1-L2⇒E2 L1≢L2
... | (E1' , E2' , E1≼E1' , E2≼E2' , Π2-L1⇒E1' , Π2-L2⇒E2') =
  ((Π2 [ L1 := E1' ]) [ L2 := E2' ]) ,
  :=-≼S (:=-≼S Π1≼Π2 E1≼E1') E2≼E2' ,
  CommStep L1 L2 v E1' E2' L1≢L2 Π2-L1⇒E1' Π2-L2⇒E2'
Lifting {Π2 = Π2} Π1≼Π2 (SyncStep L1 L2 d E1 E2 L1≢L2 Π1-L1⇒E1 Π1-L2⇒E2)
  with Sync-Lift (Π1≼Π2 L1) (Π1≼Π2 L2) Π1-L1⇒E1 Π1-L2⇒E2 L1≢L2
... | (E1' , E2' , E1≼E1' , E2≼E2' , Π2-L1⇒E1' , Π2-L2⇒E2') =
  ((Π2 [ L1 := E1' ]) [ L2 := E2' ]) ,
  :=-≼S (:=-≼S Π1≼Π2 E1≼E1') E2≼E2' ,
  SyncStep L1 L2 d E1' E2' L1≢L2 Π2-L1⇒E1' Π2-L2⇒E2'
Lifting Π1≼Π2 (CommTyStep Π1' L ρ tₑ E1 Π1-L⇒E1 Π1-L⇒Π1'-L) = {!   !}