{-# OPTIONS --safe #-}

open import Level renaming (zero to ℓ-zero; suc to ℓ-suc; _⊔_ to ℓ-max)
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.List
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (map; _<*>_)
open import Data.Maybe renaming (map to mmap)
open import Data.Maybe.Properties
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

module PolyPir.EPP
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

with-dec : ∀{a b} {A : Set a} {B : Set b} →
          Dec A →
          (A → B) →
          (¬ A → B) →
          B
with-dec (yes x) f g = f x
with-dec (no ¬x) f g = g ¬x

Handler : ∀{a} → List (Set a) → Set a → Set a
Handler [] B = B
Handler (A ∷ A*) B = (A → Handler A* B) × (¬ A → Handler A* B)

data HVec {a ℓ} {A : Set a} (P : A → Set ℓ) : List A → Set (ℓ-max a ℓ) where
  [] : HVec P []
  _∷_ : ∀{x xs} → P x → HVec P xs → HVec P (x ∷ xs)

with-dec*-impl : ∀{a} {A* : List (Set a)} {B : Set a} →
                  HVec Dec A* →
                  Handler A* B →
                  B
with-dec*-impl {A* = []} [] y = y
with-dec*-impl {A* = A ∷ A*} (A-Dec ∷ A*-Dec) (f , g) =
  with-dec A-Dec
    (λ x → with-dec*-impl A*-Dec (f x))
    (λ ¬x → with-dec*-impl A*-Dec (g ¬x))

HVec-++ : ∀{a ℓ} {A : Set a} {P : A → Set ℓ} {xs ys : List A} →
          HVec P (xs ++ ys) →
          HVec P xs × HVec P ys
HVec-++ {xs = []} {ys} Pys = [] , Pys
HVec-++ {xs = x ∷ xs} {ys} (Px ∷ Pxs++ys) =
  let (Pxs , Pys) = HVec-++ {xs = xs} {ys} Pxs++ys
  in Px ∷ Pxs , Pys

Handlers : ∀{a} → List (Set a) → Set a → List (Set a)
Handlers [] B = B ∷ []
Handlers (A ∷ A*) B =
  let Hs = Handlers A* B
  in map (λ H → A → H) Hs ++ map (λ H → ¬ A → H) Hs

ap-HVec : ∀{a} {A : Set a}
          {Ts : List (Set a)} →
          HVec id (map (λ X → A → X) Ts) →
          A → HVec id Ts
ap-HVec {Ts = []} [] x = []
ap-HVec {Ts = T ∷ Ts} (f ∷ fs) x = f x ∷ ap-HVec fs x

Handlers⇒Handler : ∀{a} {A* : List (Set a)} {B : Set a} →
                   HVec id (Handlers A* B) → Handler A* B
Handlers⇒Handler {A* = []} (y ∷ []) = y
Handlers⇒Handler {A* = A ∷ A*} {B} Hs =
  (λ x → Handlers⇒Handler {A* = A*} $
          ap-HVec
          (HVec-++
            {xs = map (λ H → A → H) (Handlers A* B)}
            {map (λ H → ¬ A → H) (Handlers A* B)}
            Hs .fst)
          x) ,
  λ ¬x → Handlers⇒Handler {A* = A*} $
          ap-HVec
          (HVec-++
            {xs = map (λ H → A → H) (Handlers A* B)}
            {map (λ H → ¬ A → H) (Handlers A* B)}
            Hs .snd)
          ¬x

with-dec* : ∀{a} {A* : List (Set a)} {B : Set a} →
            HVec Dec A* →
            HVec id (Handlers A* B) →
            B
with-dec* {A* = A*} A*-dec Hs =
  with-dec*-impl A*-dec (Handlers⇒Handler {A* = A*} Hs)

{-
Endpoint projection relation

⟦ C ⟧↓ Γ Δ L E

Denotes that the choreography C with
type variables from Γ and choreographic variables
from Δ projects to E at the location L.
We need to know the current context as it
is relevant for extracting local terms correctly.
-}
data ⟦_⟧↓ : CTm → List Bool → List Bool → Loc → Ctrl → Set where
  VarProj : ∀{Γ Δ L x} → ⟦ var x ⟧↓ Γ Δ L (var x)
  DoneProj≡ : ∀{Γ Δ tₑ L ℓ e} →
             ℓ ≡ LitLoc L →
             ⟦ Done tₑ ℓ e ⟧↓ Γ Δ L (Ret (proj Γ Δ e))
  DoneProj≢ : ∀{Γ Δ tₑ L ℓ e} →
              ℓ ≢ LitLoc L →
              ⟦ Done tₑ ℓ e ⟧↓ Γ Δ L Unit
  LamProj : ∀{Γ Δ τ1 τ2 L C E} →
              ⟦ C ⟧↓ Γ (false ∷ Δ) L E →
              ⟦ Lam τ1 τ2 C ⟧↓ Γ Δ L (CtrlLam E)
  AppProj : ∀{Γ Δ τ1 τ2 L C1 C2 E1 E2} →
            ⟦ C1 ⟧↓ Γ Δ L E1 →
            ⟦ C2 ⟧↓ Γ Δ L E2 →
            ⟦ App τ1 τ2 C1 C2 ⟧↓ Γ Δ L (CtrlApp E1 E2)            
  FixProj : ∀{Γ Δ τ L C E} →
            ⟦ C ⟧↓ Γ (false ∷ Δ) L E →
            ⟦ Fix τ C ⟧↓ Γ Δ L (CtrlFix E)
  AbsProj*ₑ : ∀{Γ Δ κₑ τ L C E} →
            ⟦ C ⟧↓ (true ∷ Γ) Δ L E →
            ⟦ Abs {LocKnd κₑ} tt τ C ⟧↓ Γ Δ L (CtrlTAbs E)
  AbsProj* : ∀{Γ Δ τ L C E} →
            ⟦ C ⟧↓ (false ∷ Γ) Δ L E →
            ⟦ Abs {*} tt τ C ⟧↓ Γ Δ L (CtrlTAbs E)
  AbsProj*ₗ : ∀{Γ Δ τ L C E E[L]} →
            ⟦ tySub C⅀ (tyVar ▸ LitLoc L) C ⟧↓ Γ Δ L E[L] →
            ⟦ C ⟧↓ (false ∷ Γ) Δ L E →
            ⟦ Abs {*ₗ} tt τ C ⟧↓ Γ Δ L (CtrlTAbs (AmI (tyVar 0) (tyRenCtrl suc E[L]) E))
  AbsProj*ₛ : ∀{Γ Δ τ L C E E[L]} →
            ⟦ tySub C⅀ (tyVar ▸ LitLoc L) C ⟧↓ Γ Δ L E[L] →
            ⟦ C ⟧↓ (false ∷ Γ) Δ L E →
            ⟦ Abs {*ₛ} tt τ C ⟧↓ Γ Δ L (CtrlTAbs (AmIIn (tyVar 0) (tyRenCtrl suc E[L]) E))
  TAppProj : ∀{Γ Δ C τ t κ ∀κ L E} →
            ⟦ C ⟧↓ Γ Δ L E →
            ⟦ AppTy {κ} ∀κ C τ t ⟧↓ Γ Δ L (CtrlTApp E t)
  SendRecvProj : ∀{Γ Δ ℓ1 ℓ2 tₑ C L E} →
                 ℓ1 ≡ LitLoc L →
                 ℓ2 ≡ LitLoc L →
                 ⟦ C ⟧↓ Γ Δ L E → 
                 ⟦ Send ℓ1 C tₑ ℓ2 ⟧↓ Γ Δ L E
  SendProj : ∀{Γ Δ ℓ1 ℓ2 tₑ C L E} →
                 ℓ1 ≡ LitLoc L →
                 ℓ2 ≢ LitLoc L →
                 ⟦ C ⟧↓ Γ Δ L E → 
                 ⟦ Send ℓ1 C tₑ ℓ2 ⟧↓ Γ Δ L (SendTo E ℓ2)
  RecvProj : ∀{Γ Δ ℓ1 ℓ2 tₑ C L E} →
              ℓ1 ≢ LitLoc L →
              ℓ2 ≡ LitLoc L →
              ⟦ C ⟧↓ Γ Δ L E → 
              ⟦ Send ℓ1 C tₑ ℓ2 ⟧↓ Γ Δ L (Seq E (Recv ℓ1))
  SendProj≢ : ∀{Γ Δ ℓ1 ℓ2 tₑ C L E} →
              ℓ1 ≢ LitLoc L →
              ℓ2 ≢ LitLoc L →
              ⟦ C ⟧↓ Γ Δ L E → 
              ⟦ Send ℓ1 C tₑ ℓ2 ⟧↓ Γ Δ L E
  SyncSendRecvProj : ∀{Γ Δ ℓ1 ℓ2 d C τ L E} →
                      ℓ1 ≡ LitLoc L →
                      ℓ2 ≡ LitLoc L →
                      ⟦ C ⟧↓ Γ Δ L E → 
                      ⟦ Sync ℓ1 d ℓ2 C τ ⟧↓ Γ Δ L E
  SyncSendProj : ∀{Γ Δ ℓ1 ℓ2 d C τ L E} →
                 ℓ1 ≡ LitLoc L →
                 ℓ2 ≢ LitLoc L →
                 ⟦ C ⟧↓ Γ Δ L E → 
                 ⟦ Sync ℓ1 d ℓ2 C τ ⟧↓ Γ Δ L (Choose d ℓ2 E)
  SyncRecvLProj : ∀{Γ Δ ℓ1 ℓ2 C τ L E} →
                  ℓ1 ≢ LitLoc L →
                  ℓ2 ≡ LitLoc L →
                  ⟦ C ⟧↓ Γ Δ L E → 
                  ⟦ Sync ℓ1 true ℓ2 C τ ⟧↓ Γ Δ L (Allow ℓ1 (′ E) ？)
  SyncRecvRProj : ∀{Γ Δ ℓ1 ℓ2 C τ L E} →
                  ℓ1 ≢ LitLoc L →
                  ℓ2 ≡ LitLoc L →
                  ⟦ C ⟧↓ Γ Δ L E → 
                  ⟦ Sync ℓ1 false ℓ2 C τ ⟧↓ Γ Δ L (Allow ℓ1 ？ (′ E))
  SyncProj≢ : ∀{Γ Δ ℓ1 ℓ2 d C τ L E} →
              ℓ1 ≢ LitLoc L →
              ℓ2 ≢ LitLoc L →
              ⟦ C ⟧↓ Γ Δ L E → 
              ⟦ Sync ℓ1 d ℓ2 C τ ⟧↓ Γ Δ L E
  ITEProj≡ : ∀{Γ Δ ℓ C1 C2 C3 τ L E1 E2 E3} →
              ℓ ≡ LitLoc L →
              ⟦ C1 ⟧↓ Γ Δ L E1 →
              ⟦ C2 ⟧↓ Γ Δ L E2 →
              ⟦ C3 ⟧↓ Γ Δ L E3 →
              ⟦ ITE ℓ C1 C2 C3 τ ⟧↓ Γ Δ L (CtrlITE E1 E2 E3)
  ITEProj≢ : ∀{Γ Δ ℓ C1 C2 C3 τ L E1 E2 E3 E2⊔E3} →
              ℓ ≢ LitLoc L →
              ⟦ C1 ⟧↓ Γ Δ L E1 →
              ⟦ C2 ⟧↓ Γ Δ L E2 →
              ⟦ C3 ⟧↓ Γ Δ L E3 →
              E2 ⊔ E3 ≡ just E2⊔E3 →
              ⟦ ITE ℓ C1 C2 C3 τ ⟧↓ Γ Δ L (Seq E1 E2⊔E3)
  LocalLetProj≡ : ∀{Γ Δ ℓ C1 tₑ C2 τ L E1 E2} →
                  ℓ ≡ LitLoc L →
                  ⟦ C1 ⟧↓ Γ Δ L E1 →
                  ⟦ C2 ⟧↓ Γ (true ∷ Δ) L E2 →
                  ⟦ LocalLet ℓ C1 tₑ C2 τ ⟧↓ Γ Δ L (LetRet E1 E2)
  LocalLetProj≢ : ∀{Γ Δ ℓ C1 tₑ C2 τ L E1 E2} →
                  ℓ ≢ LitLoc L →
                  ⟦ C1 ⟧↓ Γ Δ L E1 →
                  ⟦ C2 ⟧↓ Γ (false ∷ Δ) L E2 →
                  ⟦ LocalLet ℓ C1 tₑ C2 τ ⟧↓ Γ Δ L (Seq E1 E2)
  TellTySendProj : ∀{Γ Δ C1 C2 ℓ ρ τ L E1 E2} →
                  ℓ ≡ LitLoc L →
                  ⟦ C1 ⟧↓ Γ Δ L E1 →
                  ⟦ C2 ⟧↓ (false ∷ Γ) Δ L E2 →
                  ⟦ TellTy ℓ C1 ρ C2 τ ⟧↓ Γ Δ L (SendTy *ₑ E1 ρ E2)
  TellTyRecvProj : ∀{Γ Δ C1 C2 ℓ ρ τ L E1 E2} →
                    ℓ ≢ LitLoc L →
                    L ∈ₛ ρ →
                    ⟦ C1 ⟧↓ Γ Δ L E1 →
                    ⟦ C2 ⟧↓ (false ∷ Γ) Δ L E2 →
                    ⟦ TellTy ℓ C1 ρ C2 τ ⟧↓ Γ Δ L (Seq E1 (RecvTy *ₑ ℓ E2))
  TellTyProj≢ : ∀{Γ Δ C1 C2 ℓ ρ τ L E1 E2} →
                    ℓ ≢ LitLoc L →
                    ¬ (L ∈ₛ ρ) →
                    notFreeTyInCtrl 0 E2 →
                    ⟦ C1 ⟧↓ Γ Δ L E1 →
                    ⟦ C2 ⟧↓ (false ∷ Γ) Δ L E2 →
                    ⟦ TellTy ℓ C1 ρ C2 τ ⟧↓ Γ Δ L (Seq E1 (tyRenCtrl pred E2))
  TellLocSendProj : ∀{Γ Δ C1 C2 ℓ ρ τ L E1 E2[L] E2} →
                    ℓ ≡ LitLoc L →
                    ⟦ C1 ⟧↓ Γ Δ L E1 →
                    ⟦ tySub C⅀ (tyVar ▸ LitLoc L) C2 ⟧↓ Γ Δ L E2[L] →
                    ⟦ C2 ⟧↓ (false ∷ Γ) Δ L E2 →
                    ⟦ TellLoc ℓ C1 ρ C2 τ ⟧↓ Γ Δ L (SendTy *ₗ E1 ρ (AmI (tyVar 0) (tyRenCtrl suc E2[L]) E2))
  TellLocRecvProj : ∀{Γ Δ C1 C2 ℓ ρ τ L E1 E2[L] E2} →
                    ℓ ≢ LitLoc L →
                    L ∈ₛ ρ →
                    ⟦ C1 ⟧↓ Γ Δ L E1 →
                    ⟦ tySub C⅀ (tyVar ▸ LitLoc L) C2 ⟧↓ Γ Δ L E2[L] →
                    ⟦ C2 ⟧↓ (false ∷ Γ) Δ L E2 →
                    ⟦ TellLoc ℓ C1 ρ C2 τ ⟧↓ Γ Δ L (Seq E1 (RecvTy *ₗ ℓ (AmI (tyVar 0) (tyRenCtrl suc E2[L]) E2)))
  TellLocProj≢ : ∀{Γ Δ C1 C2 ℓ ρ τ L E1 E2} →
                  ℓ ≢ LitLoc L →
                  ¬ (L ∈ₛ ρ) →
                  notFreeTyInCtrl 0 E2 →
                  ⟦ C1 ⟧↓ Γ Δ L E1 →
                  ⟦ C2 ⟧↓ (false ∷ Γ) Δ L E2 →
                  ⟦ TellLoc ℓ C1 ρ C2 τ ⟧↓ Γ Δ L (Seq E1 (tyRenCtrl pred E2))

-- The endpoint projection relation is functional
EPP-uniq : ∀{C Γ Δ L E1 E2} →
           ⟦ C ⟧↓ Γ Δ L E1 →
           ⟦ C ⟧↓ Γ Δ L E2 →
           E1 ≡ E2
EPP-uniq VarProj VarProj = refl
EPP-uniq (DoneProj≡ x) (DoneProj≡ x₁) = refl
EPP-uniq (DoneProj≡ x) (DoneProj≢ x₁) = ⊥-elim (x₁ x)
EPP-uniq (DoneProj≢ x) (DoneProj≡ x₁) = ⊥-elim (x x₁)
EPP-uniq (DoneProj≢ x) (DoneProj≢ x₁) = refl
EPP-uniq (LamProj p1) (LamProj p2) = cong CtrlLam (EPP-uniq p1 p2)
EPP-uniq (AppProj p1 p2) (AppProj p3 p4) = cong₂ CtrlApp (EPP-uniq p1 p3) (EPP-uniq p2 p4)
EPP-uniq (FixProj p1) (FixProj p2) = cong CtrlFix (EPP-uniq p1 p2)
EPP-uniq (AbsProj*ₑ p1) (AbsProj*ₑ p2) = cong CtrlTAbs (EPP-uniq p1 p2)
EPP-uniq (AbsProj* p1) (AbsProj* p2) = cong CtrlTAbs (EPP-uniq p1 p2)
EPP-uniq (AbsProj*ₗ p1 p2) (AbsProj*ₗ p3 p4) =
  cong₂ (λ x y → CtrlTAbs (AmI (tyVar 0) (tyRenCtrl suc x) y))
    (EPP-uniq p1 p3)
    (EPP-uniq p2 p4)
EPP-uniq (AbsProj*ₛ p1 p2) (AbsProj*ₛ p3 p4) =
  cong₂ (λ x y → CtrlTAbs (AmIIn (tyVar 0) (tyRenCtrl suc x) y))
    (EPP-uniq p1 p3)
    (EPP-uniq p2 p4)
EPP-uniq (TAppProj p1) (TAppProj p2) = cong (flip CtrlTApp _) (EPP-uniq p1 p2)
EPP-uniq (SendRecvProj x x₁ p1) (SendRecvProj x₂ x₃ p2) = EPP-uniq p1 p2
EPP-uniq (SendRecvProj x x₁ p1) (SendProj x₂ x₃ p2) = ⊥-elim $ x₃ x₁
EPP-uniq (SendRecvProj x x₁ p1) (RecvProj x₂ x₃ p2) = ⊥-elim $ x₂ x
EPP-uniq (SendRecvProj x x₁ p1) (SendProj≢ x₂ x₃ p2) = ⊥-elim $ x₂ x
EPP-uniq (SendProj x x₁ p1) (SendRecvProj x₂ x₃ p2) = ⊥-elim $ x₁ x₃
EPP-uniq (SendProj x x₁ p1) (SendProj x₂ x₃ p2) = cong (flip SendTo _) (EPP-uniq p1 p2)
EPP-uniq (SendProj x x₁ p1) (RecvProj x₂ x₃ p2) = ⊥-elim $ x₁ x₃
EPP-uniq (SendProj x x₁ p1) (SendProj≢ x₂ x₃ p2) = ⊥-elim $ x₂ x
EPP-uniq (RecvProj x x₁ p1) (SendRecvProj x₂ x₃ p2) = ⊥-elim $ x x₂
EPP-uniq (RecvProj x x₁ p1) (SendProj x₂ x₃ p2) = ⊥-elim $ x x₂
EPP-uniq (RecvProj x x₁ p1) (RecvProj x₂ x₃ p2) = cong (flip Seq _) (EPP-uniq p1 p2)
EPP-uniq (RecvProj x x₁ p1) (SendProj≢ x₂ x₃ p2) = ⊥-elim $ x₃ x₁
EPP-uniq (SendProj≢ x x₁ p1) (SendRecvProj x₂ x₃ p2) = ⊥-elim $ x x₂
EPP-uniq (SendProj≢ x x₁ p1) (SendProj x₂ x₃ p2) = ⊥-elim $ x x₂
EPP-uniq (SendProj≢ x x₁ p1) (RecvProj x₂ x₃ p2) = ⊥-elim $ x₁ x₃
EPP-uniq (SendProj≢ x x₁ p1) (SendProj≢ x₂ x₃ p2) = EPP-uniq p1 p2
EPP-uniq (SyncSendRecvProj x x₁ p1) (SyncSendRecvProj x₂ x₃ p2) = EPP-uniq p1 p2
EPP-uniq (SyncSendRecvProj x x₁ p1) (SyncSendProj x₂ x₃ p2) = ⊥-elim $ x₃ x₁
EPP-uniq (SyncSendRecvProj x x₁ p1) (SyncRecvLProj x₂ x₃ p2) = ⊥-elim $ x₂ x
EPP-uniq (SyncSendRecvProj x x₁ p1) (SyncRecvRProj x₂ x₃ p2) = ⊥-elim $ x₂ x
EPP-uniq (SyncSendRecvProj x x₁ p1) (SyncProj≢ x₂ x₃ p2) = ⊥-elim $ x₂ x
EPP-uniq (SyncSendProj x x₁ p1) (SyncSendRecvProj x₂ x₃ p2) = ⊥-elim $ x₁ x₃
EPP-uniq (SyncSendProj x x₁ p1) (SyncSendProj x₂ x₃ p2) = cong (Choose _ _) $ EPP-uniq p1 p2
EPP-uniq (SyncSendProj x x₁ p1) (SyncRecvLProj x₂ x₃ p2) = ⊥-elim $ x₁ x₃
EPP-uniq (SyncSendProj x x₁ p1) (SyncRecvRProj x₂ x₃ p2) = ⊥-elim $ x₂ x
EPP-uniq (SyncSendProj x x₁ p1) (SyncProj≢ x₂ x₃ p2) = ⊥-elim $ x₂ x
EPP-uniq (SyncRecvLProj x x₁ p1) (SyncSendRecvProj x₂ x₃ p2) = ⊥-elim $ x x₂
EPP-uniq (SyncRecvLProj x x₁ p1) (SyncSendProj x₂ x₃ p2) = ⊥-elim $ x x₂
EPP-uniq (SyncRecvLProj x x₁ p1) (SyncRecvLProj x₂ x₃ p2) = cong (λ x → Allow _ (′ x) ？) (EPP-uniq p1 p2)
EPP-uniq (SyncRecvLProj x x₁ p1) (SyncProj≢ x₂ x₃ p2) = ⊥-elim $ x₃ x₁
EPP-uniq (SyncRecvRProj x x₁ p1) (SyncSendRecvProj x₂ x₃ p2) = ⊥-elim $ x x₂
EPP-uniq (SyncRecvRProj x x₁ p1) (SyncSendProj x₂ x₃ p2) = ⊥-elim $ x x₂
EPP-uniq (SyncRecvRProj x x₁ p1) (SyncRecvRProj x₂ x₃ p2) = cong (λ x → Allow _ ？ (′ x)) (EPP-uniq p1 p2)
EPP-uniq (SyncRecvRProj x x₁ p1) (SyncProj≢ x₂ x₃ p2) = ⊥-elim $ x₃ x₁
EPP-uniq (SyncProj≢ x x₁ p1) (SyncSendRecvProj x₂ x₃ p2) = ⊥-elim $ x x₂
EPP-uniq (SyncProj≢ x x₁ p1) (SyncSendProj x₂ x₃ p2) = ⊥-elim $ x x₂
EPP-uniq (SyncProj≢ x x₁ p1) (SyncRecvLProj x₂ x₃ p2) = ⊥-elim $ x₁ x₃
EPP-uniq (SyncProj≢ x x₁ p1) (SyncRecvRProj x₂ x₃ p2) = ⊥-elim $ x₁ x₃
EPP-uniq (SyncProj≢ x x₁ p1) (SyncProj≢ x₂ x₃ p2) = EPP-uniq p1 p2
EPP-uniq (ITEProj≡ x p1 p2 p3) (ITEProj≡ x₁ p4 p5 p6) =
  cong₃ CtrlITE (EPP-uniq p1 p4) (EPP-uniq p2 p5) (EPP-uniq p3 p6)
EPP-uniq (ITEProj≡ x p1 p2 p3) (ITEProj≢ x₁ p4 p5 p6 x₂) = ⊥-elim $ x₁ x
EPP-uniq (ITEProj≢ x p1 p2 p3 x₁) (ITEProj≡ x₂ p4 p5 p6) = ⊥-elim $ x x₂
EPP-uniq (ITEProj≢ x p1 p2 p3 x₁) (ITEProj≢ x₂ p4 p5 p6 x₃) =
  cong₂ Seq (EPP-uniq p1 p4)
    (just-injective (sym x₁ ∙ cong₂ _⊔_ (EPP-uniq p2 p5) (EPP-uniq p3 p6) ∙ x₃))
EPP-uniq (LocalLetProj≡ x p1 p2) (LocalLetProj≡ x₁ p3 p4) =
  cong₂ LetRet (EPP-uniq p1 p3) (EPP-uniq p2 p4)
EPP-uniq (LocalLetProj≡ x p1 p2) (LocalLetProj≢ x₁ p3 p4) = ⊥-elim $ x₁ x
EPP-uniq (LocalLetProj≢ x p1 p2) (LocalLetProj≡ x₁ p3 p4) = ⊥-elim $ x x₁
EPP-uniq (LocalLetProj≢ x p1 p2) (LocalLetProj≢ x₁ p3 p4) =
  cong₂ Seq (EPP-uniq p1 p3) (EPP-uniq p2 p4)
EPP-uniq (TellTySendProj x p1 p2) (TellTySendProj x₁ p3 p4) =
  cong₂ (λ x y → SendTy *ₑ x _ y)
    (EPP-uniq p1 p3)
    (EPP-uniq p2 p4)
EPP-uniq (TellTySendProj x p1 p2) (TellTyRecvProj x₁ x₂ p3 p4) = ⊥-elim $ x₁ x
EPP-uniq (TellTySendProj x p1 p2) (TellTyProj≢ x₁ x₂ x₃ p3 p4) = ⊥-elim $ x₁ x
EPP-uniq (TellTyRecvProj x x₁ p1 p2) (TellTySendProj x₂ p3 p4) = ⊥-elim $ x x₂
EPP-uniq (TellTyRecvProj x x₁ p1 p2) (TellTyRecvProj x₂ x₃ p3 p4) =
  cong₂ (λ x y → Seq x (RecvTy *ₑ _ y))
    (EPP-uniq p1 p3) (EPP-uniq p2 p4)
EPP-uniq (TellTyRecvProj x x₁ p1 p2) (TellTyProj≢ x₂ x₃ x₄ p3 p4) = ⊥-elim $ x₃ x₁
EPP-uniq (TellTyProj≢ x x₁ x₂ p1 p2) (TellTySendProj x₃ p3 p4) = ⊥-elim $ x x₃
EPP-uniq (TellTyProj≢ x x₁ x₂ p1 p2) (TellTyRecvProj x₃ x₄ p3 p4) = ⊥-elim $ x₁ x₄
EPP-uniq (TellTyProj≢ x x₁ x₂ p1 p2) (TellTyProj≢ x₃ x₄ x₅ p3 p4) =
  cong₂ (λ x y → Seq x (tyRenCtrl pred y))
    (EPP-uniq p1 p3) (EPP-uniq p2 p4)
EPP-uniq (TellLocSendProj x p1 p2 p3) (TellLocSendProj x₁ p4 p5 p6) =
  cong₃ (λ x y z → SendTy *ₗ x _ (AmI (tyVar 0) (tyRenCtrl suc y) z))
    (EPP-uniq p1 p4) (EPP-uniq p2 p5) (EPP-uniq p3 p6)
EPP-uniq (TellLocSendProj x p1 p2 p3) (TellLocRecvProj x₁ x₂ p4 p5 p6) = ⊥-elim $ x₁ x
EPP-uniq (TellLocSendProj x p1 p2 p3) (TellLocProj≢ x₁ x₂ v p4 p5) = ⊥-elim $ x₁ x
EPP-uniq (TellLocRecvProj x x₁ p1 p2 p3) (TellLocSendProj x₃ p4 p5 p6) = ⊥-elim $ x x₃
EPP-uniq (TellLocRecvProj x x₁ p1 p2 p3) (TellLocRecvProj x₃ x₄ p4 p5 p6) =
  cong₃ (λ x y z → Seq x (RecvTy *ₗ _ (AmI (tyVar 0) (tyRenCtrl suc y) z)))
    (EPP-uniq p1 p4) (EPP-uniq p2 p5) (EPP-uniq p3 p6)
EPP-uniq (TellLocRecvProj x x₁ p1 p2 p3) (TellLocProj≢ x₃ x₄ v p4 p5) = ⊥-elim $ x₄ x₁
EPP-uniq (TellLocProj≢ x x₁ a p1 p2) (TellLocSendProj x₂ p3 p4 p5) = ⊥-elim $ x x₂
EPP-uniq (TellLocProj≢ x x₁ a p1 p2) (TellLocRecvProj x₂ x₃ p3 p4 p5) = ⊥-elim $ x₁ x₃
EPP-uniq (TellLocProj≢ x x₁ a p1 p2) (TellLocProj≢ x₂ x₃ v p3 p4) =
  cong₂ (λ x y → Seq x (tyRenCtrl pred y))
    (EPP-uniq p1 p3) (EPP-uniq p2 p4)

-- Predicates for which we can decide whether ∃x.P(x) or ∀x.¬P(x)
data Dec∃ {a ℓ} {A : Set a} (P : A → Set ℓ) : Set (ℓ-max a ℓ) where
  yes' : (x : A) (Px : P x) → Dec∃ P
  no'  : ((x : A) → ¬ (P x)) → Dec∃ P 

with-dec∃ : ∀{a b ℓ} {A : Set a} {P : A → Set ℓ} {B : Set b} →
            Dec∃ P →
            ((x : A) → P x → B) →
            (((x : A) → ¬ (P x)) → B) →
            B
with-dec∃ (yes' x Px) f g = f x Px
with-dec∃ (no' ¬Px) f g = g ¬Px


just≢nothing : ∀{a} {A : Set a} {x : A} →
               just x ≢ nothing
just≢nothing ()

nothing≢just : ∀{a} {A : Set a} {x : A} →
               nothing ≢ just x
nothing≢just ()

{-
The endpoint projection relation is decidable

We need to allow for the type substitution
as an extra argument because we have to
project terms of the form ⟦C[α ↦ L]⟧L which
would otherwise not be structurally recursive.
-}
⟦_⟧σ?↓ : (C : CTm) (σ : TySub C⅀ₖ)
         (Γ Δ : List Bool) (L : Loc) →
         Dec∃ (⟦ tySub C⅀ σ C ⟧↓ Γ Δ L)
⟦ var x ⟧σ?↓ σ Γ Δ L = yes' (var x) (VarProj {Γ} {Δ} {L} {x})
⟦ constr DoneS ((tₑ , 0) ∷ (ℓ , 0) ∷ []) ((e , 0 , 0) ∷ []) ⟧σ?↓ σ Γ Δ L =
  with-dec (≡-dec-CTy (subTy C⅀ₖ σ ℓ) (LitLoc L))
    (λ ⟨σ⟩ℓ≡L → yes' _ (DoneProj≡ ⟨σ⟩ℓ≡L))
    (λ ⟨σ⟩ℓ≢L → yes' _ (DoneProj≢ ⟨σ⟩ℓ≢L))
⟦ constr LamS ((τ1 , 0) ∷ (τ2 , 0) ∷ []) ((C , 0 , 1) ∷ []) ⟧σ?↓ σ Γ Δ L =
  with-dec∃ (⟦ C ⟧σ?↓ σ Γ (false ∷ Δ) L)
    (λ E C↓E → yes' (CtrlLam E) (LamProj C↓E))
    (λ C↑ → no' λ{ .(CtrlLam _) (LamProj C↓E) → C↑ _ C↓E })
⟦ constr FixS ((τ , 0) ∷ []) ((C , 0 , 1) ∷ []) ⟧σ?↓ σ Γ Δ L =
  with-dec∃ (⟦ C ⟧σ?↓ σ Γ (false ∷ Δ) L)
    (λ E C↓E → yes' (CtrlFix E) (FixProj C↓E))
    (λ C↑ → no' λ{ .(CtrlFix _) (FixProj C↓E) → C↑ _ C↓E })
⟦ constr AppS ((τ1 , 0) ∷ (τ2 , 0) ∷ []) ((C1 , 0 , 0) ∷ (C2 , 0 , 0) ∷ []) ⟧σ?↓ σ Γ Δ L =
  with-dec∃ (⟦ C1 ⟧σ?↓ σ Γ Δ L)
    (λ E1 C1↓E1 →
      with-dec∃ (⟦ C2 ⟧σ?↓ σ Γ Δ L)
        (λ E2 C2↓E2 → yes' (CtrlApp E1 E2) (AppProj C1↓E1 C2↓E2))
        λ C2↑ → no' λ{ (CtrlApp _ E2) (AppProj _ C2↓E2) → C2↑ E2 C2↓E2 })
    λ C1↑ → no' λ{ (CtrlApp E1 _) (AppProj C1↓E1 _) → C1↑ E1 C1↓E1 }
⟦ constr (AbsS (LocKnd κₑ) tt) ((τ , 1) ∷ []) ((C , 1 , 0) ∷ []) ⟧σ?↓ σ Γ Δ L =
  with-dec∃ (⟦ C ⟧σ?↓ (TyKeepSub C⅀ₖ σ) (true ∷ Γ) Δ L)
    (λ E ↓E → yes' _ (AbsProj*ₑ ↓E))
    (λ C↑ → no' λ{ .(CtrlTAbs _) (AbsProj*ₑ ↓E) → C↑ _ ↓E })
⟦ constr (AbsS * tt) ((τ , 1) ∷ []) ((C , 1 , 0) ∷ []) ⟧σ?↓ σ Γ Δ L =
  with-dec∃ (⟦ C ⟧σ?↓ (TyKeepSub C⅀ₖ σ) (false ∷ Γ) Δ L)
    (λ E ↓E → yes' _ (AbsProj* ↓E))
    (λ C↑ → no' λ{ .(CtrlTAbs _) (AbsProj* ↓E) → C↑ _ ↓E })
⟦ constr (AbsS *ₗ tt) ((τ , 1) ∷ []) ((C , 1 , 0) ∷ []) ⟧σ?↓ σ Γ Δ L =
  with-dec∃ (⟦ C ⟧σ?↓ (subTy C⅀ₖ (tyVar ▸ LitLoc L) ∘ TyKeepSub C⅀ₖ σ) Γ Δ L)
    (λ E1 ↓E1 →
      with-dec∃ (⟦ C ⟧σ?↓ (TyKeepSub C⅀ₖ σ) (false ∷ Γ) Δ L)
        (λ E2 ↓E2 →
            yes' _ (AbsProj*ₗ
              (subst (λ x → ⟦ x ⟧↓ Γ Δ L E1)
                (sym $ tySub◦ₜ C⅀ (tyVar ▸ LitLoc L) (TyKeepSub C⅀ₖ σ) C)
                ↓E1)
              ↓E2))
        (λ C2↑ → no'
          λ{ .(CtrlTAbs (AmI (tyVar 0) (tyRenCtrl suc _) _)) (AbsProj*ₗ {E[L] = E[L]} ↓E1 ↓E2) →
              C2↑ _ ↓E2 }))
    (λ C1↑ → no'
      λ{ .(CtrlTAbs (AmI (tyVar 0) (tyRenCtrl suc _) _)) (AbsProj*ₗ {E[L] = E[L]} ↓E1 ↓E2) →
        C1↑ _ $
          subst (λ x → ⟦ x ⟧↓ Γ Δ L E[L])
          (tySub◦ₜ C⅀ (tyVar ▸ LitLoc L) (TyKeepSub C⅀ₖ σ) C)
          ↓E1 })
⟦ constr (AbsS *ₛ tt) ((τ , 1) ∷ []) ((C , 1 , 0) ∷ []) ⟧σ?↓ σ Γ Δ L =
  with-dec∃ (⟦ C ⟧σ?↓ (subTy C⅀ₖ (tyVar ▸ LitLoc L) ∘ TyKeepSub C⅀ₖ σ) Γ Δ L)
    (λ E1 ↓E1 →
      with-dec∃ (⟦ C ⟧σ?↓ (TyKeepSub C⅀ₖ σ) (false ∷ Γ) Δ L)
        (λ E2 ↓E2 → yes' _
          (AbsProj*ₛ
            (subst (λ x → ⟦ x ⟧↓ Γ Δ L E1)
              (sym $ tySub◦ₜ C⅀ (tyVar ▸ LitLoc L) (TyKeepSub C⅀ₖ σ) C)
              ↓E1)
            ↓E2))
        (λ C2↑ → no'
          λ{ .(CtrlTAbs (AmIIn (tyVar 0) (tyRenCtrl suc _) _)) (AbsProj*ₛ {E[L] = E[L]} ↓E1 ↓E2) →
            C2↑ _ ↓E2 }))
    (λ C1↑ → no'
      λ{ .(CtrlTAbs (AmIIn (tyVar 0) (tyRenCtrl suc _) _)) (AbsProj*ₛ {E[L] = E[L]} ↓E1 ↓E2) →
        C1↑ _ $
          subst (λ x → ⟦ x ⟧↓ Γ Δ L E[L])
          (tySub◦ₜ C⅀ (tyVar ▸ LitLoc L) (TyKeepSub C⅀ₖ σ) C)
          ↓E1 })
⟦ constr (AppTyS κ ∀κ) ((τ , 1) ∷ (t , 0) ∷ []) ((C , 0 , 0) ∷ []) ⟧σ?↓ σ Γ Δ L =
  with-dec∃ (⟦ C ⟧σ?↓ σ Γ Δ L)
    (λ _ ↓E → yes' _ (TAppProj ↓E))
    (λ C↑ → no' λ{ .(CtrlTApp _ (subTy C⅀ₖ σ t)) (TAppProj ↓E) → C↑ _ ↓E })
⟦ constr SendS ((ℓ1 , 0) ∷ (ℓ2 , 0) ∷ (tₑ , 0) ∷ []) ((C , 0 , 0) ∷ []) ⟧σ?↓ σ Γ Δ L =
  with-dec* (≡-dec-CTy (subTy C⅀ₖ σ ℓ1) (LitLoc L) ∷
                ≡-dec-CTy (subTy C⅀ₖ σ ℓ2) (LitLoc L) ∷ [])
      ((λ ⟨σ⟩ℓ1≡L ⟨σ⟩ℓ2≡L → with-dec∃ (⟦ C ⟧σ?↓ σ Γ Δ L)
            (λ E ↓E → yes' _ (SendRecvProj ⟨σ⟩ℓ1≡L ⟨σ⟩ℓ2≡L ↓E))
            λ ↑C → no' λ{ E (SendRecvProj p q ↓E) → ↑C E ↓E
                        ; _ (SendProj p q ↓E) → q ⟨σ⟩ℓ2≡L
                        ; _ (RecvProj p q ↓E) → p ⟨σ⟩ℓ1≡L
                        ; E (SendProj≢ p q ↓E) → p ⟨σ⟩ℓ1≡L }) ∷
      (λ ⟨σ⟩ℓ1≡L ⟨σ⟩ℓ2≢L → with-dec∃ (⟦ C ⟧σ?↓ σ Γ Δ L)
            (λ E ↓E → yes' _ (SendProj ⟨σ⟩ℓ1≡L ⟨σ⟩ℓ2≢L ↓E))
            λ ↑C → no' λ{ E (SendRecvProj p q ↓E) → ⟨σ⟩ℓ2≢L q
                        ; _ (SendProj p q ↓E) → ↑C _ ↓E
                        ; _ (RecvProj p q ↓E) → ⟨σ⟩ℓ2≢L q
                        ; E (SendProj≢ p q ↓E) → p ⟨σ⟩ℓ1≡L }) ∷
      (λ ⟨σ⟩ℓ1≢L ⟨σ⟩ℓ2≡L → with-dec∃ (⟦ C ⟧σ?↓ σ Γ Δ L)
            (λ E ↓E → yes' _ (RecvProj ⟨σ⟩ℓ1≢L ⟨σ⟩ℓ2≡L ↓E))
            λ ↑C → no' λ{ E (SendRecvProj p q ↓E) → ⟨σ⟩ℓ1≢L p
                        ; _ (SendProj p q ↓E) → ⟨σ⟩ℓ1≢L p
                        ; _ (RecvProj p q ↓E) → ↑C _ ↓E
                        ; E (SendProj≢ p q ↓E) → q ⟨σ⟩ℓ2≡L }) ∷
      ((λ ⟨σ⟩ℓ1≢L ⟨σ⟩ℓ2≢L → with-dec∃ (⟦ C ⟧σ?↓ σ Γ Δ L)
            (λ E ↓E → yes' _ (SendProj≢ ⟨σ⟩ℓ1≢L ⟨σ⟩ℓ2≢L ↓E))
            λ ↑C → no' λ{ E (SendRecvProj p q ↓E) → ⟨σ⟩ℓ1≢L p
                        ; _ (SendProj p q ↓E) → ⟨σ⟩ℓ1≢L p
                        ; _ (RecvProj p q ↓E) → ⟨σ⟩ℓ2≢L q
                        ; E (SendProj≢ p q ↓E) → ↑C _ ↓E }) ∷ []))
⟦ constr (SyncS true) ((ℓ1 , 0) ∷ (ℓ2 , 0) ∷ (τ , 0) ∷ []) ((C , 0 , 0) ∷ []) ⟧σ?↓ σ Γ Δ L =
  with-dec* (≡-dec-CTy (subTy C⅀ₖ σ ℓ1) (LitLoc L) ∷
             ≡-dec-CTy (subTy C⅀ₖ σ ℓ2) (LitLoc L) ∷ [])
      ((λ ⟨σ⟩ℓ1≡L ⟨σ⟩ℓ2≡L → with-dec∃ (⟦ C ⟧σ?↓ σ Γ Δ L)
            (λ E ↓E → yes' _ (SyncSendRecvProj ⟨σ⟩ℓ1≡L ⟨σ⟩ℓ2≡L ↓E))
            λ ↑C → no' λ{ E (SyncSendRecvProj p q ↓E) → ↑C E ↓E
                        ; _ (SyncSendProj p q ↓E) → q ⟨σ⟩ℓ2≡L
                        ; _ (SyncRecvLProj p q ↓E) → p ⟨σ⟩ℓ1≡L
                        ; E (SyncProj≢ p q ↓E) → p ⟨σ⟩ℓ1≡L }) ∷
      (λ ⟨σ⟩ℓ1≡L ⟨σ⟩ℓ2≢L → with-dec∃ (⟦ C ⟧σ?↓ σ Γ Δ L)
            (λ E ↓E → yes' _ (SyncSendProj ⟨σ⟩ℓ1≡L ⟨σ⟩ℓ2≢L ↓E))
            λ ↑C → no' λ{ E (SyncSendRecvProj p q ↓E) → ⟨σ⟩ℓ2≢L q
                        ; _ (SyncSendProj p q ↓E) → ↑C _ ↓E
                        ; _ (SyncRecvLProj p q ↓E) → ⟨σ⟩ℓ2≢L q
                        ; E (SyncProj≢ p q ↓E) → p ⟨σ⟩ℓ1≡L }) ∷
      (λ ⟨σ⟩ℓ1≢L ⟨σ⟩ℓ2≡L → with-dec∃ (⟦ C ⟧σ?↓ σ Γ Δ L)
            (λ E ↓E → yes' _ (SyncRecvLProj ⟨σ⟩ℓ1≢L ⟨σ⟩ℓ2≡L ↓E))
            (λ ↑C → no' λ{ E (SyncSendRecvProj p q ↓E) → ⟨σ⟩ℓ1≢L p
                        ; _ (SyncSendProj p q ↓E) → ⟨σ⟩ℓ1≢L p
                        ; _ (SyncRecvLProj p q ↓E) → ↑C _ ↓E
                        ; E (SyncProj≢ p q ↓E) → q ⟨σ⟩ℓ2≡L })) ∷
      ((λ ⟨σ⟩ℓ1≢L ⟨σ⟩ℓ2≢L → with-dec∃ (⟦ C ⟧σ?↓ σ Γ Δ L)
            (λ E ↓E → yes' _ (SyncProj≢ ⟨σ⟩ℓ1≢L ⟨σ⟩ℓ2≢L ↓E))
            λ ↑C → no' λ{ E (SyncSendRecvProj p q ↓E) → ⟨σ⟩ℓ1≢L p
                        ; _ (SyncSendProj p q ↓E) → ⟨σ⟩ℓ1≢L p
                        ; _ (SyncRecvLProj p q ↓E) → ⟨σ⟩ℓ2≢L q
                        ; E (SyncProj≢ p q ↓E) → ↑C _ ↓E }) ∷ []))
⟦ constr (SyncS false) ((ℓ1 , 0) ∷ (ℓ2 , 0) ∷ (τ , 0) ∷ []) ((C , 0 , 0) ∷ []) ⟧σ?↓ σ Γ Δ L =
  with-dec* (≡-dec-CTy (subTy C⅀ₖ σ ℓ1) (LitLoc L) ∷
             ≡-dec-CTy (subTy C⅀ₖ σ ℓ2) (LitLoc L) ∷ [])
      ((λ ⟨σ⟩ℓ1≡L ⟨σ⟩ℓ2≡L → with-dec∃ (⟦ C ⟧σ?↓ σ Γ Δ L)
            (λ E ↓E → yes' _ (SyncSendRecvProj ⟨σ⟩ℓ1≡L ⟨σ⟩ℓ2≡L ↓E))
            λ ↑C → no' λ{ E (SyncSendRecvProj p q ↓E) → ↑C E ↓E
                        ; _ (SyncSendProj p q ↓E) → q ⟨σ⟩ℓ2≡L
                        ; _ (SyncRecvRProj p q ↓E) → p ⟨σ⟩ℓ1≡L
                        ; E (SyncProj≢ p q ↓E) → p ⟨σ⟩ℓ1≡L }) ∷
      (λ ⟨σ⟩ℓ1≡L ⟨σ⟩ℓ2≢L → with-dec∃ (⟦ C ⟧σ?↓ σ Γ Δ L)
            (λ E ↓E → yes' _ (SyncSendProj ⟨σ⟩ℓ1≡L ⟨σ⟩ℓ2≢L ↓E))
            λ ↑C → no' λ{ E (SyncSendRecvProj p q ↓E) → ⟨σ⟩ℓ2≢L q
                        ; _ (SyncSendProj p q ↓E) → ↑C _ ↓E
                        ; _ (SyncRecvRProj p q ↓E) → ⟨σ⟩ℓ2≢L q
                        ; E (SyncProj≢ p q ↓E) → p ⟨σ⟩ℓ1≡L }) ∷
      (λ ⟨σ⟩ℓ1≢L ⟨σ⟩ℓ2≡L → with-dec∃ (⟦ C ⟧σ?↓ σ Γ Δ L)
            (λ E ↓E → yes' _ (SyncRecvRProj ⟨σ⟩ℓ1≢L ⟨σ⟩ℓ2≡L ↓E))
            (λ ↑C → no' λ{ E (SyncSendRecvProj p q ↓E) → ⟨σ⟩ℓ1≢L p
                        ; _ (SyncSendProj p q ↓E) → ⟨σ⟩ℓ1≢L p
                        ; _ (SyncRecvRProj p q ↓E) → ↑C _ ↓E
                        ; E (SyncProj≢ p q ↓E) → q ⟨σ⟩ℓ2≡L })) ∷
      ((λ ⟨σ⟩ℓ1≢L ⟨σ⟩ℓ2≢L → with-dec∃ (⟦ C ⟧σ?↓ σ Γ Δ L)
            (λ E ↓E → yes' _ (SyncProj≢ ⟨σ⟩ℓ1≢L ⟨σ⟩ℓ2≢L ↓E))
            λ ↑C → no' λ{ E (SyncSendRecvProj p q ↓E) → ⟨σ⟩ℓ1≢L p
                        ; _ (SyncSendProj p q ↓E) → ⟨σ⟩ℓ1≢L p
                        ; _ (SyncRecvRProj p q ↓E) → ⟨σ⟩ℓ2≢L q
                        ; E (SyncProj≢ p q ↓E) → ↑C _ ↓E }) ∷ []))                       
⟦ constr ITES ((ℓ , 0) ∷ (τ , 0) ∷ []) ((C1 , 0 , 0) ∷ (C2 , 0 , 0) ∷ (C3 , 0 , 0) ∷ []) ⟧σ?↓ σ Γ Δ L =
  with-dec (≡-dec-CTy (subTy C⅀ₖ σ ℓ) (LitLoc L))
    (λ ⟨σ⟩ℓ≡L → with-dec∃ (⟦ C1 ⟧σ?↓ σ Γ Δ L)
      (λ E1 ↓E1 → with-dec∃ (⟦ C2 ⟧σ?↓ σ Γ Δ L)
        (λ E2 ↓E2 → with-dec∃ (⟦ C3 ⟧σ?↓ σ Γ Δ L)
          (λ E3 ↓E3 → yes' _ (ITEProj≡ ⟨σ⟩ℓ≡L ↓E1 ↓E2 ↓E3))
          (λ ↑C3 → no' λ{ _ (ITEProj≡ p ↓E1 ↓E2 ↓E3) → ↑C3 _ ↓E3
                        ; _ (ITEProj≢ p ↓E1 ↓E2 ↓E3 q) → p ⟨σ⟩ℓ≡L }))
        (λ ↑C2 → no' λ{ _ (ITEProj≡ p ↓E1 ↓E2 ↓E3) → ↑C2 _ ↓E2
                      ; _ (ITEProj≢ p ↓E1 ↓E2 ↓E3 q) → p ⟨σ⟩ℓ≡L }))
      (λ ↑C1 → no' λ{ _ (ITEProj≡ p ↓E1 ↓E2 ↓E3) → ↑C1 _ ↓E1
                    ; _ (ITEProj≢ p ↓E1 ↓E2 ↓E3 q) → p ⟨σ⟩ℓ≡L }))
    (λ ⟨σ⟩ℓ≢L → with-dec∃ (⟦ C1 ⟧σ?↓ σ Γ Δ L)
      (λ E1 ↓E1 → with-dec∃ (⟦ C2 ⟧σ?↓ σ Γ Δ L)
        (λ E2 ↓E2 → with-dec∃ (⟦ C3 ⟧σ?↓ σ Γ Δ L)
          (λ E3 ↓E3 → maybe {B = λ m → m ≡ E2 ⊔ E3 → _}
                (λ E2⊔E3 eq → yes' _ (ITEProj≢  ⟨σ⟩ℓ≢L ↓E1 ↓E2 ↓E3 (sym eq)))
                (λ eq → no' λ{ _ (ITEProj≡ p ↓E1 ↓E2 ↓E3) → ⟨σ⟩ℓ≢L p
                             ; _ (ITEProj≢ p ↓E1' ↓E2' ↓E3' q) →
                              nothing≢just (eq ∙ cong₂ _⊔_ (EPP-uniq ↓E2 ↓E2') (EPP-uniq ↓E3 ↓E3') ∙ q) })
                (E2 ⊔ E3) refl)
          (λ ↑C3 → no' λ{ _ (ITEProj≡ p ↓E1 ↓E2 ↓E3) → ⟨σ⟩ℓ≢L p
                        ; _ (ITEProj≢ p ↓E1 ↓E2 ↓E3 q) → ↑C3 _ ↓E3 }))
        (λ ↑C2 → no' λ{ _ (ITEProj≡ p ↓E1 ↓E2 ↓E3) → ⟨σ⟩ℓ≢L p
                      ; _ (ITEProj≢ p ↓E1 ↓E2 ↓E3 q) → ↑C2 _ ↓E2 }))
      (λ ↑C1 → no' λ{ _ (ITEProj≡ p ↓E1 ↓E2 ↓E3) → ⟨σ⟩ℓ≢L p
                    ; _ (ITEProj≢ p ↓E1 ↓E2 ↓E3 q) → ↑C1 _ ↓E1 }))
⟦ constr LocalLetS ((ℓ , 0) ∷ (tₑ , 0) ∷ (τ , 0) ∷ []) ((C1 , 0 , 0) ∷ (C2 , 0 , 1) ∷ []) ⟧σ?↓ σ Γ Δ L =
  with-dec (≡-dec-CTy (subTy C⅀ₖ σ ℓ) (LitLoc L))
    (λ ⟨σ⟩ℓ≡L → with-dec∃ (⟦ C1 ⟧σ?↓ σ Γ Δ L)
      (λ E1 ↓E1 → with-dec∃ (⟦ C2 ⟧σ?↓ σ Γ (true ∷ Δ) L)
        (λ E2 ↓E2 → yes' _ (LocalLetProj≡ ⟨σ⟩ℓ≡L ↓E1 ↓E2))
        (λ ↑C2 → no' λ{ .(LetRet _ _) (LocalLetProj≡ x _ ↓E2) → ↑C2 _ ↓E2
                      ; .(Seq _ _) (LocalLetProj≢ x _ ↓E2) → x ⟨σ⟩ℓ≡L }) )
      (λ ↑C1 → no' λ{ .(LetRet _ _) (LocalLetProj≡ x ↓E1 ↓E2) → ↑C1 _ ↓E1
                    ; .(Seq _ _) (LocalLetProj≢ x ↓E1 ↓E2) → x ⟨σ⟩ℓ≡L }))
    (λ ⟨σ⟩ℓ≢L → with-dec∃ (⟦ C1 ⟧σ?↓ σ Γ Δ L)
      (λ E1 ↓E1 → with-dec∃ (⟦ C2 ⟧σ?↓ σ Γ (false ∷ Δ) L)
        (λ E2 ↓E2 → yes' _ (LocalLetProj≢ ⟨σ⟩ℓ≢L ↓E1 ↓E2))
        (λ ↑C2 → no' λ{ .(LetRet _ _) (LocalLetProj≡ x _ ↓E2) → ⟨σ⟩ℓ≢L x
                      ; .(Seq _ _) (LocalLetProj≢ x _ ↓E2) → ↑C2 _ ↓E2 }) )
      (λ ↑C1 → no' λ{ .(LetRet _ _) (LocalLetProj≡ x ↓E1 ↓E2) → ⟨σ⟩ℓ≢L x
                    ; .(Seq _ _) (LocalLetProj≢ x ↓E1 ↓E2) → ↑C1 _ ↓E1 }))
⟦ constr TellTyS ((ℓ , 0) ∷ (ρ , 0) ∷ (τ , 0) ∷ []) ((C1 , 0 , 0) ∷ (C2 , 1 , 0) ∷ []) ⟧σ?↓ σ Γ Δ L =
  with-dec (≡-dec-CTy (subTy C⅀ₖ σ ℓ) (LitLoc L))
    (λ ⟨σ⟩ℓ≡L → with-dec∃ (⟦ C1 ⟧σ?↓ σ Γ Δ L)
      (λ E1 ↓E1 → with-dec∃ (⟦ C2 ⟧σ?↓ (TyKeepSub C⅀ₖ σ) (false ∷ Γ) Δ L)
        (λ E2 ↓E2 → yes' _ (TellTySendProj ⟨σ⟩ℓ≡L ↓E1 ↓E2))
        (λ ↑C2 → no' λ{ _ (TellTySendProj p ↓E1 ↓E2) → ↑C2 _ ↓E2
                      ; _ (TellTyRecvProj p q ↓E1 ↓E2) → p ⟨σ⟩ℓ≡L
                      ; _ (TellTyProj≢ p q r ↓E1 ↓E2) → p ⟨σ⟩ℓ≡L }))
      (λ ↑C1 → no' λ{ _ (TellTySendProj p ↓E1 ↓E2) → ↑C1 _ ↓E1
                    ; _ (TellTyRecvProj p q ↓E1 ↓E2) → p ⟨σ⟩ℓ≡L
                    ; _ (TellTyProj≢ p q r ↓E1 ↓E2) → p ⟨σ⟩ℓ≡L }))
    (λ ⟨σ⟩ℓ≢L → with-dec (L ?∈ₛ subTy C⅀ₖ σ ρ)
      (λ L∈⟨σ⟩ρ → with-dec∃ (⟦ C1 ⟧σ?↓ σ Γ Δ L)
        (λ E1 ↓E1 → with-dec∃ (⟦ C2 ⟧σ?↓ (TyKeepSub C⅀ₖ σ) (false ∷ Γ) Δ L)
          (λ E2 ↓E2 → yes' _ (TellTyRecvProj ⟨σ⟩ℓ≢L L∈⟨σ⟩ρ ↓E1 ↓E2))
          (λ ↑C2 → no' λ{ _ (TellTySendProj p ↓E1 ↓E2) → ⟨σ⟩ℓ≢L p
                        ; _ (TellTyRecvProj p q ↓E1 ↓E2) → ↑C2 _ ↓E2
                        ; _ (TellTyProj≢ p q r ↓E1 ↓E2) → q L∈⟨σ⟩ρ }))
        (λ ↑C1 → no' λ{ _ (TellTySendProj p ↓E1 ↓E2) → ⟨σ⟩ℓ≢L p
                      ; _ (TellTyRecvProj p q ↓E1 ↓E2) → ↑C1 _ ↓E1
                      ; _ (TellTyProj≢ p q r ↓E1 ↓E2) → q L∈⟨σ⟩ρ }))
      (λ L∉⟨σ⟩ρ → with-dec∃ (⟦ C1 ⟧σ?↓ σ Γ Δ L)
        (λ E1 ↓E1 → with-dec∃ (⟦ C2 ⟧σ?↓ (TyKeepSub C⅀ₖ σ) (false ∷ Γ) Δ L)
          (λ E2 ↓E2 → with-dec (?notFreeTyInCtrl 0 E2)
            (λ 0∉E2 → yes' _ (TellTyProj≢ ⟨σ⟩ℓ≢L L∉⟨σ⟩ρ 0∉E2 ↓E1 ↓E2))
            (λ 0∈E2 → no' λ{ _ (TellTySendProj p ↓E1 ↓E2) → ⟨σ⟩ℓ≢L p
                        ; _ (TellTyRecvProj p q ↓E1 ↓E2) → L∉⟨σ⟩ρ q
                        ; _ (TellTyProj≢ {E2 = E2'} p q r ↓E1 ↓E2') →
                        0∈E2 (subst (notFreeTyInCtrl 0) (sym $ EPP-uniq ↓E2 ↓E2') r) }))
          (λ ↑C2 → no' λ{ _ (TellTySendProj p ↓E1 ↓E2) → ⟨σ⟩ℓ≢L p
                        ; _ (TellTyRecvProj p q ↓E1 ↓E2) → L∉⟨σ⟩ρ q
                        ; _ (TellTyProj≢ p q r ↓E1 ↓E2) → ↑C2 _ ↓E2 }))
        (λ ↑C1 → no' λ{ _ (TellTySendProj p ↓E1 ↓E2) → ⟨σ⟩ℓ≢L p
                      ; _ (TellTyRecvProj p q ↓E1 ↓E2) → L∉⟨σ⟩ρ q
                      ; _ (TellTyProj≢ p q r ↓E1 ↓E2) → ↑C1 _ ↓E1 })))
⟦ constr TellLocS ((ℓ , 0) ∷ (ρ , 0) ∷ (τ , 0) ∷ []) ((C1 , 0 , 0) ∷ (C2 , 1 , 0) ∷ []) ⟧σ?↓ σ Γ Δ L =
  with-dec (≡-dec-CTy (subTy C⅀ₖ σ ℓ) (LitLoc L))
    (λ ⟨σ⟩ℓ≡L → with-dec∃ (⟦ C1 ⟧σ?↓ σ Γ Δ L)
      (λ E1 ↓E1 → with-dec∃ (⟦ C2 ⟧σ?↓ (subTy C⅀ₖ (tyVar ▸ LitLoc L) ∘ TyKeepSub C⅀ₖ σ) Γ Δ L)
        (λ E2 ↓E2 → with-dec∃ (⟦ C2 ⟧σ?↓ (TyKeepSub C⅀ₖ σ) (false ∷ Γ) Δ L)
          (λ E3 ↓E3 →
            yes' _ (TellLocSendProj ⟨σ⟩ℓ≡L ↓E1
              (subst (λ x → ⟦ x ⟧↓ Γ Δ L E2) (sym $ tySub◦ₜ C⅀ (tyVar ▸ LitLoc L) (TyKeepSub C⅀ₖ σ) C2) ↓E2)
              ↓E3))
          (λ ↑C3 → no' λ{ _ (TellLocSendProj p ↓E1 ↓E2 ↓E3) → ↑C3 _ ↓E3
                        ; _ (TellLocRecvProj p q ↓E1 ↓E2 ↓E3) → p ⟨σ⟩ℓ≡L
                        ; _ (TellLocProj≢ p q r ↓E1 ↓E2) → p ⟨σ⟩ℓ≡L }))
        (λ ↑C2 → no' λ{ _ (TellLocSendProj p ↓E1 ↓E2 ↓E3) → ↑C2 _
                          (subst (λ x → ⟦ x ⟧↓ Γ Δ L _) (tySub◦ₜ C⅀ (tyVar ▸ LitLoc L) (TyKeepSub C⅀ₖ σ) C2) ↓E2)
                    ; _ (TellLocRecvProj p q ↓E1 ↓E2 ↓E3) → p ⟨σ⟩ℓ≡L
                    ; _ (TellLocProj≢ p q r ↓E1 ↓E2) → p ⟨σ⟩ℓ≡L }))
      (λ ↑C1 → no' λ{ _ (TellLocSendProj p ↓E1 ↓E2 ↓E3) → ↑C1 _ ↓E1
                    ; _ (TellLocRecvProj p q ↓E1 ↓E2 ↓E3) → p ⟨σ⟩ℓ≡L
                    ; _ (TellLocProj≢ p q r ↓E1 ↓E2) → p ⟨σ⟩ℓ≡L }))
    (λ ⟨σ⟩ℓ≢L → with-dec (L ?∈ₛ subTy C⅀ₖ σ ρ)
      (λ L∈⟨σ⟩ρ → with-dec∃ (⟦ C1 ⟧σ?↓ σ Γ Δ L)
        (λ E1 ↓E1 → with-dec∃ (⟦ C2 ⟧σ?↓ (subTy C⅀ₖ (tyVar ▸ LitLoc L) ∘ TyKeepSub C⅀ₖ σ) Γ Δ L)
          (λ E2 ↓E2 → with-dec∃ (⟦ C2 ⟧σ?↓ (TyKeepSub C⅀ₖ σ) (false ∷ Γ) Δ L)
            (λ E3 ↓E3 →
              yes' _ (TellLocRecvProj ⟨σ⟩ℓ≢L L∈⟨σ⟩ρ ↓E1
                (subst (λ x → ⟦ x ⟧↓ Γ Δ L E2) (sym $ tySub◦ₜ C⅀ (tyVar ▸ LitLoc L) (TyKeepSub C⅀ₖ σ) C2) ↓E2)
                ↓E3))
            (λ ↑C3 → no' λ{ _ (TellLocSendProj p ↓E1 ↓E2 ↓E3) → ⟨σ⟩ℓ≢L p
                          ; _ (TellLocRecvProj p q ↓E1 ↓E2 ↓E3) → ↑C3 _ ↓E3
                          ; _ (TellLocProj≢ p q r ↓E1 ↓E2) → q L∈⟨σ⟩ρ }))
          (λ ↑C2 → no' λ{ _ (TellLocSendProj p ↓E1 ↓E2 ↓E3) → ⟨σ⟩ℓ≢L p
                      ; _ (TellLocRecvProj p q ↓E1 ↓E2 ↓E3) → ↑C2 _
                        (subst (λ x → ⟦ x ⟧↓ Γ Δ L _) (tySub◦ₜ C⅀ (tyVar ▸ LitLoc L) (TyKeepSub C⅀ₖ σ) C2) ↓E2)
                      ; _ (TellLocProj≢ p q r ↓E1 ↓E2) → q L∈⟨σ⟩ρ }))
        (λ ↑C1 → no' λ{ _ (TellLocSendProj p ↓E1 ↓E2 ↓E3) → ⟨σ⟩ℓ≢L p
                      ; _ (TellLocRecvProj p q ↓E1 ↓E2 ↓E3) → ↑C1 _ ↓E1
                      ; _ (TellLocProj≢ p q r ↓E1 ↓E2) → q L∈⟨σ⟩ρ }))
      (λ L∉⟨σ⟩ρ → with-dec∃ (⟦ C1 ⟧σ?↓ σ Γ Δ L)
        (λ E1 ↓E1 → with-dec∃ (⟦ C2 ⟧σ?↓ (TyKeepSub C⅀ₖ σ) (false ∷ Γ) Δ L)
          (λ E2 ↓E2 → with-dec (?notFreeTyInCtrl 0 E2)
            (λ 0∉E2 → yes' _ (TellLocProj≢ ⟨σ⟩ℓ≢L L∉⟨σ⟩ρ 0∉E2 ↓E1 ↓E2))
            (λ 0∈E2 → no' λ{ _ (TellLocSendProj p ↓E1 ↓E2 ↓E3) → ⟨σ⟩ℓ≢L p
                      ; _ (TellLocRecvProj p q ↓E1 ↓E2 ↓E3) → L∉⟨σ⟩ρ q
                      ; _ (TellLocProj≢ p q r ↓E1 ↓E2') → 
                        0∈E2 $ subst (notFreeTyInCtrl 0) (sym $ EPP-uniq ↓E2 ↓E2') r }))
          (λ ↑C2 → no' λ{ _ (TellLocSendProj p ↓E1 ↓E2 ↓E3) → ⟨σ⟩ℓ≢L p
                      ; _ (TellLocRecvProj p q ↓E1 ↓E2 ↓E3) → L∉⟨σ⟩ρ q
                      ; _ (TellLocProj≢ p q r ↓E1 ↓E2) → ↑C2 _ ↓E2 }))
        (λ ↑C1 → no' λ{ _ (TellLocSendProj p ↓E1 ↓E2 ↓E3) → ⟨σ⟩ℓ≢L p
                      ; _ (TellLocRecvProj p q ↓E1 ↓E2 ↓E3) → L∉⟨σ⟩ρ q
                      ; _ (TellLocProj≢ p q r ↓E1 ↓E2) → ↑C1 _ ↓E1 })))
⟦ constr (LocalTmS sₑ) ts es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr DoneS [] es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr DoneS ((t1 , k1) ∷ []) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr DoneS ((t1 , 0) ∷ (t2 , suc k2) ∷ []) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr DoneS ((t1 , suc k1) ∷ (t2 , 0) ∷ []) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr DoneS ((t1 , suc k1) ∷ (t2 , suc k2) ∷ []) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr DoneS ((t1 , k1) ∷ (t2 , k2) ∷ (t3 , k3) ∷ ts) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr DoneS ((t1 , 0) ∷ (t2 , 0) ∷ []) [] ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr DoneS ((t1 , 0) ∷ (t2 , 0) ∷ []) ((e1 , m1 , n1) ∷ (e2 , m2 , n2) ∷ es) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr DoneS ((t1 , 0) ∷ (t2 , 0) ∷ []) ((e1 , suc m1 , n1) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr DoneS ((t1 , 0) ∷ (t2 , 0) ∷ []) ((e1 , 0 , suc n1) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr LamS [] es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr LamS ((t1 , k1) ∷ []) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr LamS ((t1 , 0) ∷ (t2 , suc k2) ∷ []) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr LamS ((t1 , suc k1) ∷ (t2 , 0) ∷ []) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr LamS ((t1 , suc k1) ∷ (t2 , suc k2) ∷ []) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr LamS ((t1 , k1) ∷ (t2 , k2) ∷ (t3 , k3) ∷ ts) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr LamS ((t1 , 0) ∷ (t2 , 0) ∷ []) [] ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr LamS ((t1 , 0) ∷ (t2 , 0) ∷ []) ((e1 , m1 , n1) ∷ (e2 , m2 , n2) ∷ es) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr LamS ((t1 , 0) ∷ (t2 , 0) ∷ []) ((e1 , suc m1 , n1) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr LamS ((t1 , 0) ∷ (t2 , 0) ∷ []) ((e1 , 0 , suc (suc n1)) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr LamS ((t1 , 0) ∷ (t2 , 0) ∷ []) ((e1 , 0 , 0) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr FixS [] es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr FixS ((t1 , suc k) ∷ []) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr FixS ((t1 , k1) ∷ (t2 , k2) ∷ ts) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr FixS ((t1 , 0) ∷ []) [] ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr FixS ((t1 , 0) ∷ []) ((e1 , m1 , n1) ∷ (e2 , m2 , n2) ∷ es) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr FixS ((t1 , 0) ∷ []) ((e1 , suc m1 , n1) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr FixS ((t1 , 0) ∷ []) ((e1 , 0 , suc (suc n1)) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr FixS ((t1 , 0) ∷ []) ((e1 , 0 , 0) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr AppS [] es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr AppS ((t1 , k1) ∷ []) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr AppS ((t1 , k1) ∷ (t2 , k2) ∷ (t3 , k3) ∷ ts) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr AppS ((t1 , 0) ∷ (t2 , suc k2) ∷ []) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr AppS ((t1 , suc k1) ∷ (t2 , 0) ∷ []) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr AppS ((t1 , suc k1) ∷ (t2 , suc k2) ∷ []) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr AppS ((t1 , 0) ∷ (t2 , 0) ∷ []) [] ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr AppS ((t1 , 0) ∷ (t2 , 0) ∷ []) (e1 ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr AppS ((t1 , 0) ∷ (t2 , 0) ∷ []) (e1 ∷ e2 ∷ e3 ∷ es) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr AppS ((t1 , 0) ∷ (t2 , 0) ∷ []) ((e1 , suc m1 , n1) ∷ (e2 , m2 , n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr AppS ((t1 , 0) ∷ (t2 , 0) ∷ []) ((e1 , m1 , suc n1) ∷ (e2 , m2 , n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr AppS ((t1 , 0) ∷ (t2 , 0) ∷ []) ((e1 , m1 , n1) ∷ (e2 , suc m2 , n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr AppS ((t1 , 0) ∷ (t2 , 0) ∷ []) ((e1 , m1 , n1) ∷ (e2 , m2 , suc n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (AbsS κ ∀κ) [] es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (AbsS κ ∀κ) (t1 ∷ t2 ∷ ts) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (AbsS κ ∀κ) (t1 ∷ []) [] ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (AbsS κ ∀κ) (t1 ∷ []) (e1 ∷ e2 ∷ es) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (AbsS κ ∀κ) ((t1 , 0) ∷ []) (e1 ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (AbsS κ ∀κ) ((t1 , suc (suc k1)) ∷ []) (e1 ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (AbsS κ ∀κ) ((t1 , 1) ∷ []) ((e1 , 0 , n1) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (AbsS κ ∀κ) ((t1 , 1) ∷ []) ((e1 , suc (suc m1) , n1) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (AbsS κ ∀κ) ((t1 , 1) ∷ []) ((e1 , 1 , suc n1) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (AppTyS κ ∀κ) [] es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (AppTyS κ ∀κ) (t1 ∷ []) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (AppTyS κ ∀κ) (t1 ∷ t2 ∷ t3 ∷ ts) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (AppTyS κ ∀κ) (t1 ∷ t2 ∷ []) [] ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (AppTyS κ ∀κ) (t1 ∷ t2 ∷ []) (e1 ∷ e2 ∷ es) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (AppTyS κ ∀κ) ((t1 , 0) ∷ (t2 , k2) ∷ []) ((e1 , m1 , n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (AppTyS κ ∀κ) ((t1 , suc (suc k1)) ∷ (t2 , k2) ∷ []) ((e1 , m1 , n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (AppTyS κ ∀κ) ((t1 , 1) ∷ (t2 , suc k2) ∷ []) ((e1 , m1 , n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (AppTyS κ ∀κ) ((t1 , 1) ∷ (t2 , 0) ∷ []) ((e1 , suc m1 , n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (AppTyS κ ∀κ) ((t1 , 1) ∷ (t2 , 0) ∷ []) ((e1 , 0 , suc n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr SendS [] es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr SendS (t1 ∷ []) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr SendS (t1 ∷ t2 ∷ []) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr SendS (t1 ∷ t2 ∷ t3 ∷ t4 ∷ ts) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr SendS (t1 ∷ t2 ∷ t3 ∷ []) [] ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr SendS (t1 ∷ t2 ∷ t3 ∷ []) (e1 ∷ e2 ∷ es) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr SendS ((t1 , suc k1) ∷ (t2 , k2) ∷ (t3 , k3) ∷ []) ((e1 , m1 , n1) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr SendS ((t1 , k1) ∷ (t2 , suc k2) ∷ (t3 , k3) ∷ []) ((e1 , m1 , n1) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr SendS ((t1 , k1) ∷ (t2 , k2) ∷ (t3 , suc k3) ∷ []) ((e1 , m1 , n1) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr SendS ((t1 , k1) ∷ (t2 , k2) ∷ (t3 , k3) ∷ []) ((e1 , suc m1 , n1) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr SendS ((t1 , k1) ∷ (t2 , k2) ∷ (t3 , k3) ∷ []) ((e1 , m1 , suc n1) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (SyncS d) [] es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (SyncS d) (t1 ∷ []) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (SyncS d) (t1 ∷ t2 ∷ []) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (SyncS d) (t1 ∷ t2 ∷ t3 ∷ t4 ∷ ts) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (SyncS d) (t1 ∷ t2 ∷ t3 ∷ []) [] ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (SyncS d) (t1 ∷ t2 ∷ t3 ∷ []) (e1 ∷ e2 ∷ es) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (SyncS d) ((t1 , suc k1) ∷ (t2 , k2) ∷ (t3 , k3) ∷ []) ((e1 , m1 , n1) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (SyncS d) ((t1 , k1) ∷ (t2 , suc k2) ∷ (t3 , k3) ∷ []) ((e1 , m1 , n1) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (SyncS d) ((t1 , k1) ∷ (t2 , k2) ∷ (t3 , suc k3) ∷ []) ((e1 , m1 , n1) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (SyncS d) ((t1 , k1) ∷ (t2 , k2) ∷ (t3 , k3) ∷ []) ((e1 , suc m1 , n1) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr (SyncS d) ((t1 , k1) ∷ (t2 , k2) ∷ (t3 , k3) ∷ []) ((e1 , m1 , suc n1) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr ITES [] es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr ITES (t1 ∷ []) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr ITES (t1 ∷ t2 ∷ t3 ∷ ts) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr ITES (t1 ∷ t2 ∷ []) [] ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr ITES (t1 ∷ t2 ∷ []) (e1 ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr ITES (t1 ∷ t2 ∷ []) (e1 ∷ e2 ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr ITES (t1 ∷ t2 ∷ []) (e1 ∷ e2 ∷ e3 ∷ e4 ∷ es) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr ITES ((t1 , suc k1) ∷ (t2 , k2) ∷ []) ((e1 , m1 , n1) ∷ (e2 , m2 , n2) ∷ (e3 , m3 , n3) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr ITES ((t1 , k1) ∷ (t2 , suc k2) ∷ []) ((e1 , m1 , n1) ∷ (e2 , m2 , n2) ∷ (e3 , m3 , n3) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr ITES ((t1 , k1) ∷ (t2 , k2) ∷ []) ((e1 , suc m1 , n1) ∷ (e2 , m2 , n2) ∷ (e3 , m3 , n3) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr ITES ((t1 , k1) ∷ (t2 , k2) ∷ []) ((e1 , m1 , suc n1) ∷ (e2 , m2 , n2) ∷ (e3 , m3 , n3) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr ITES ((t1 , k1) ∷ (t2 , k2) ∷ []) ((e1 , m1 , n1) ∷ (e2 , suc m2 , n2) ∷ (e3 , m3 , n3) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr ITES ((t1 , k1) ∷ (t2 , k2) ∷ []) ((e1 , m1 , n1) ∷ (e2 , m2 , suc n2) ∷ (e3 , m3 , n3) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr ITES ((t1 , k1) ∷ (t2 , k2) ∷ []) ((e1 , m1 , n1) ∷ (e2 , m2 , n2) ∷ (e3 , suc m3 , n3) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr ITES ((t1 , k1) ∷ (t2 , k2) ∷ []) ((e1 , m1 , n1) ∷ (e2 , m2 , n2) ∷ (e3 , m3 , suc n3) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr LocalLetS [] es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr LocalLetS (t1 ∷ []) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr LocalLetS (t1 ∷ t2 ∷ []) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr LocalLetS (t1 ∷ t2 ∷ t3 ∷ t4 ∷ ts) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr LocalLetS (t1 ∷ t2 ∷ t3 ∷ []) [] ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr LocalLetS (t1 ∷ t2 ∷ t3 ∷ []) (e1 ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr LocalLetS (t1 ∷ t2 ∷ t3 ∷ []) (e1 ∷ e2 ∷ e3 ∷ es) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr LocalLetS ((t1 , suc k1) ∷ (t2 , k2) ∷ (t3 , k3) ∷ []) ((e1 , m1 , n1) ∷ (e2 , m2 , n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr LocalLetS ((t1 , k1) ∷ (t2 , suc k2) ∷ (t3 , k3) ∷ []) ((e1 , m1 , n1) ∷ (e2 , m2 , n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr LocalLetS ((t1 , k1) ∷ (t2 , k2) ∷ (t3 , suc k3) ∷ []) ((e1 , m1 , n1) ∷ (e2 , m2 , n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr LocalLetS ((t1 , k1) ∷ (t2 , k2) ∷ (t3 , k3) ∷ []) ((e1 , suc m1 , n1) ∷ (e2 , m2 , n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr LocalLetS ((t1 , k1) ∷ (t2 , k2) ∷ (t3 , k3) ∷ []) ((e1 , m1 , suc n1) ∷ (e2 , m2 , n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr LocalLetS ((t1 , k1) ∷ (t2 , k2) ∷ (t3 , k3) ∷ []) ((e1 , m1 , n1) ∷ (e2 , suc m2 , n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr LocalLetS ((t1 , k1) ∷ (t2 , k2) ∷ (t3 , k3) ∷ []) ((e1 , m1 , n1) ∷ (e2 , m2 , 0) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr LocalLetS ((t1 , k1) ∷ (t2 , k2) ∷ (t3 , k3) ∷ []) ((e1 , m1 , n1) ∷ (e2 , m2 , suc (suc n2)) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellTyS [] es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellTyS (t1 ∷ []) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellTyS (t1 ∷ t2 ∷ []) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellTyS (t1 ∷ t2 ∷ t3 ∷ t4 ∷ ts) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellTyS (t1 ∷ t2 ∷ t3 ∷ []) [] ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellTyS (t1 ∷ t2 ∷ t3 ∷ []) (e1 ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellTyS (t1 ∷ t2 ∷ t3 ∷ []) (e1 ∷ e2 ∷ e3 ∷ es) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellTyS ((t1 , suc k1) ∷ (t2 , k2) ∷ (t3 , k3) ∷ []) ((e1 , m1 , n1) ∷ (e2 , m2 , n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellTyS ((t1 , k1) ∷ (t2 , suc k2) ∷ (t3 , k3) ∷ []) ((e1 , m1 , n1) ∷ (e2 , m2 , n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellTyS ((t1 , k1) ∷ (t2 , k2) ∷ (t3 , suc k3) ∷ []) ((e1 , m1 , n1) ∷ (e2 , m2 , n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellTyS ((t1 , k1) ∷ (t2 , k2) ∷ (t3 , k3) ∷ []) ((e1 , suc m1 , n1) ∷ (e2 , m2 , n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellTyS ((t1 , k1) ∷ (t2 , k2) ∷ (t3 , k3) ∷ []) ((e1 , m1 , suc n1) ∷ (e2 , m2 , n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellTyS ((t1 , k1) ∷ (t2 , k2) ∷ (t3 , k3) ∷ []) ((e1 , m1 , n1) ∷ (e2 , 0 , n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellTyS ((t1 , k1) ∷ (t2 , k2) ∷ (t3 , k3) ∷ []) ((e1 , m1 , n1) ∷ (e2 , m2 , suc n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellTyS ((t1 , k1) ∷ (t2 , k2) ∷ (t3 , k3) ∷ []) ((e1 , m1 , n1) ∷ (e2 , suc (suc m2) , n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellLocS [] es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellLocS (t1 ∷ []) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellLocS (t1 ∷ t2 ∷ []) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellLocS (t1 ∷ t2 ∷ t3 ∷ t4 ∷ ts) es ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellLocS (t1 ∷ t2 ∷ t3 ∷ []) [] ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellLocS (t1 ∷ t2 ∷ t3 ∷ []) (e1 ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellLocS (t1 ∷ t2 ∷ t3 ∷ []) (e1 ∷ e2 ∷ e3 ∷ es) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellLocS ((t1 , suc k1) ∷ (t2 , k2) ∷ (t3 , k3) ∷ []) ((e1 , m1 , n1) ∷ (e2 , m2 , n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellLocS ((t1 , k1) ∷ (t2 , suc k2) ∷ (t3 , k3) ∷ []) ((e1 , m1 , n1) ∷ (e2 , m2 , n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellLocS ((t1 , k1) ∷ (t2 , k2) ∷ (t3 , suc k3) ∷ []) ((e1 , m1 , n1) ∷ (e2 , m2 , n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellLocS ((t1 , k1) ∷ (t2 , k2) ∷ (t3 , k3) ∷ []) ((e1 , suc m1 , n1) ∷ (e2 , m2 , n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellLocS ((t1 , k1) ∷ (t2 , k2) ∷ (t3 , k3) ∷ []) ((e1 , m1 , suc n1) ∷ (e2 , m2 , n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellLocS ((t1 , k1) ∷ (t2 , k2) ∷ (t3 , k3) ∷ []) ((e1 , m1 , n1) ∷ (e2 , 0 , n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellLocS ((t1 , k1) ∷ (t2 , k2) ∷ (t3 , k3) ∷ []) ((e1 , m1 , n1) ∷ (e2 , m2 , suc n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()
⟦ constr TellLocS ((t1 , k1) ∷ (t2 , k2) ∷ (t3 , k3) ∷ []) ((e1 , m1 , n1) ∷ (e2 , suc (suc m2) , n2) ∷ []) ⟧σ?↓ σ Γ Δ L = no' λ E ()

⟦_⟧?↓ : (C : CTm) (Γ Δ : List Bool) (L : Loc) →
         Dec∃ (⟦ C ⟧↓ Γ Δ L)
⟦ C ⟧?↓ Γ Δ L =
  subst (λ x → Dec∃ (⟦ x ⟧↓ Γ Δ L))
    (tySubId C⅀ C)
    (⟦ C ⟧σ?↓ tyVar Γ Δ L)
