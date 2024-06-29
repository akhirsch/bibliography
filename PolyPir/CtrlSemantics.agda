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

module PolyPir.CtrlSemantics
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

-- Control language labels
data CtrlLabel : Set where
  ιL ιSyncL : CtrlLabel
  SendL : (v : Tmₑ) (L : Loc) → CtrlLabel
  RecvL : (L : Loc) (v : Tmₑ) → CtrlLabel
  SendSyncL : (d : Bool) (L : Loc) → CtrlLabel
  RecvSyncL : (L : Loc) (d : Bool) → CtrlLabel
  SendLocL : (Lv : Loc) (ρ : List Loc) → CtrlLabel
  RecvLocL : (L : Loc) (Lv : Loc) → CtrlLabel
  SendTyL : (t : Tyₑ) (ρ : List Loc) → CtrlLabel
  RecvTyL : (L : Loc) (t : Tyₑ) → CtrlLabel

-- Reduction rules
data _⟶E[_⨾_]_ : Ctrl → CtrlLabel → Loc → Ctrl → Set where
  RetStep : ∀{L e1 e2} →
            e1 ⇒ₑ e2 →
            Ret e1 ⟶E[ ιL ⨾ L ] Ret e2
  SeqVStep : ∀{L V E} →
             CtrlVal V →
             Seq V E ⟶E[ ιL ⨾ L ] E
  AppStep : ∀{L E V} →
            CtrlVal V →
            CtrlApp (CtrlLam E) V ⟶E[ ιSyncL ⨾ L ] subCtrl (var ▸ V) E
  RecStep : ∀{L E} →
            CtrlFix E ⟶E[ ιSyncL ⨾ L ] subCtrl (var ▸ CtrlFix E) E
  SendVStep : ∀{L L' v} →
              𝕃 .Valₑ v →
              L' ≢ L →
              SendTo (Ret v) (LitLoc L') ⟶E[ SendL v L' ⨾ L ] Unit      
  RecvStep : ∀{L L' v} →
              𝕃 .Valₑ v →
              L' ≢ L →
              Recv (LitLoc L') ⟶E[ RecvL L' v ⨾ L ] Ret v
  ChooseStep : ∀{L L' d E} →
               L' ≢ L →
               Choose d (LitLoc L') E ⟶E[ SendSyncL d L' ⨾ L ] E
  AllowLStep : ∀{L L' E1 ?E2} →
                L' ≢ L →
                Allow (LitLoc L') (′ E1) ?E2 ⟶E[ RecvSyncL L' true ⨾ L ] E1
  AllowRStep : ∀{L L' ?E1 E2} →
                L' ≢ L →
                Allow (LitLoc L') ?E1 (′ E2) ⟶E[ RecvSyncL L' false ⨾ L ] E2
  IfTStep : ∀{L E1 E2} →
            CtrlITE (Ret (𝕃 .ttₑ)) E1 E2 ⟶E[ ιL ⨾ L ] E1
  IfFStep : ∀{L E1 E2} →
            CtrlITE (Ret (𝕃 .ffₑ)) E1 E2 ⟶E[ ιL ⨾ L ] E2
  AppTStep : ∀{L E t} →
              CtrlTApp (CtrlTAbs E) t ⟶E[ ιSyncL ⨾ L ] tySubCtrl (tyVar ▸ t) E
  LetRetVStep : ∀{L v E} →
                𝕃 .Valₑ v →
                LetRet (Ret v) E ⟶E[ ιL ⨾ L ] localSub (var ▸ v) E
  SendTyLocStep : ∀{ρ L Lv E} →
                  SendTy *ₗ (Ret (𝕃 .litLocₑ Lv)) (LitSet ρ) E
                    ⟶E[ SendLocL Lv ρ ⨾ L ]
                  tySubCtrl (tyVar ▸ LitLoc Lv) E
  RecvTyLocStep : ∀{L L' Lv E} →
                  L' ≢ L →
                  RecvTy *ₗ (LitLoc L') E
                    ⟶E[ RecvLocL L' Lv ⨾ L ]
                  tySubCtrl (tyVar ▸ LitLoc Lv) E        
  SendLocalTyStep : ∀{ρ L v E} →
                    𝕃 .Valₑ v →
                    SendTy *ₑ (Ret v) (LitSet ρ) E
                      ⟶E[ SendTyL (𝕃 .Elₑ v) ρ ⨾ L ]
                    tySubCtrl (tyVar ▸ injTy (𝕃 .Elₑ v)) E
  RecvLocalTyStep : ∀{L L' v E} →
                    𝕃 .Valₑ v →
                    L' ≢ L →
                    RecvTy *ₑ (LitLoc L') E
                      ⟶E[ RecvTyL L' (𝕃 .Elₑ v) ⨾ L ]
                    tySubCtrl (tyVar ▸ injTy (𝕃 .Elₑ v)) E
  AmILStep : ∀{L E1 E2} →
             AmI (LitLoc L) E1 E2 ⟶E[ ιL ⨾ L ] E1
  AmIRStep : ∀{L ℓ E1 E2} →
             ℓ ≢ LitLoc L →
             AmI ℓ E1 E2 ⟶E[ ιL ⨾ L ] E2
  AmIInLStep : ∀{L ρ E1 E2} →
               L ∈ₛ ρ →
               AmIIn ρ E1 E2 ⟶E[ ιL ⨾ L ] E1
  AmIInRStep : ∀{L ρ E1 E2} →
               ¬ (L ∈ₛ ρ) →
               AmIIn ρ E1 E2 ⟶E[ ιL ⨾ L ] E2

{-
Evaluation contexts

η ::= [•]
    | η ; E2 | E1 η | η E2
    | send η to ℓ
    | if η then E1 else E2
    | η t
    | let ret(x) := η in E2
    | send α∷κ := η to ρ in E2
-}
data CtrlECtx : Set where
  [•] : CtrlECtx
  SeqCtx : (η : CtrlECtx) (E2 : Ctrl) → CtrlECtx
  IfCtx : (η : CtrlECtx) (E1 E2 : Ctrl) → CtrlECtx
  SendCtx : (η : CtrlECtx) (ℓ : CTy) → CtrlECtx
  FunCtx : (η : CtrlECtx) (E2 : Ctrl) → CtrlECtx
  ArgCtx : (E1 : Ctrl) (η : CtrlECtx) → CtrlECtx
  TFunCtx : (η : CtrlECtx) (t : CTy) → CtrlECtx
  LetRetCtx :  (η : CtrlECtx) (E2 : Ctrl) → CtrlECtx
  SendTyCtx : (κ : ChorKnd) (η : CtrlECtx) (ρ : CTy) (E2 : Ctrl) → CtrlECtx

-- Composition of evaluation contexts
_∘ECtx_ : (η1 η2 : CtrlECtx) → CtrlECtx
[•] ∘ECtx η2 = η2
SeqCtx η1 E2 ∘ECtx η2 = SeqCtx (η1 ∘ECtx η2) E2
IfCtx η1 E1 E2 ∘ECtx η2 = IfCtx (η1 ∘ECtx η2) E1 E2
SendCtx η1 ℓ ∘ECtx η2 = SendCtx (η1 ∘ECtx η2) ℓ
FunCtx η1 E2 ∘ECtx η2 = FunCtx (η1 ∘ECtx η2) E2
ArgCtx E1 η1 ∘ECtx η2 = ArgCtx E1 (η1 ∘ECtx η2)
TFunCtx η1 t ∘ECtx η2 = TFunCtx (η1 ∘ECtx η2) t
LetRetCtx η1 E2 ∘ECtx η2 = LetRetCtx (η1 ∘ECtx η2) E2
SendTyCtx κ η1 ρ E2 ∘ECtx η2 = SendTyCtx κ (η1 ∘ECtx η2) ρ E2

-- Substituting into an evaluation context
evalCtx : CtrlECtx → Ctrl → Ctrl
evalCtx [•] E = E
evalCtx (SeqCtx η E2) E = Seq (evalCtx η E) E2
evalCtx (IfCtx η E1 E2) E = CtrlITE (evalCtx η E) E1 E2
evalCtx (SendCtx η ℓ) E = SendTo (evalCtx η E) ℓ
evalCtx (FunCtx η E2) E = CtrlApp (evalCtx η E) E2
evalCtx (ArgCtx E1 η) E = CtrlApp E1 (evalCtx η E)
evalCtx (TFunCtx η t) E = CtrlTApp (evalCtx η E) t
evalCtx (LetRetCtx η E2) E = LetRet (evalCtx η E) E2
evalCtx (SendTyCtx κ η ρ E2) E = SendTy κ (evalCtx η E) ρ E2

evalCtx∘ : (η1 η2 : CtrlECtx) → evalCtx (η1 ∘ECtx η2) ≗ evalCtx η1 ∘ evalCtx η2
evalCtx∘ [•] η2 E = refl
evalCtx∘ (SeqCtx η1 E2) η2 E = cong (flip Seq E2) (evalCtx∘ η1 η2 E)
evalCtx∘ (IfCtx η1 E1 E2) η2 E = cong (λ x → CtrlITE x E1 E2) (evalCtx∘ η1 η2 E)
evalCtx∘ (SendCtx η1 ℓ) η2 E = cong (flip SendTo ℓ) (evalCtx∘ η1 η2 E)
evalCtx∘ (FunCtx η1 E2) η2 E = cong (flip CtrlApp E2) (evalCtx∘ η1 η2 E)
evalCtx∘ (ArgCtx E1 η1) η2 E = cong (CtrlApp E1) (evalCtx∘ η1 η2 E)
evalCtx∘ (TFunCtx η1 t) η2 E = cong (flip CtrlTApp t) (evalCtx∘ η1 η2 E)
evalCtx∘ (LetRetCtx η1 E2) η2 E = cong (flip LetRet E2) (evalCtx∘ η1 η2 E)
evalCtx∘ (SendTyCtx κ η1 ρ E2) η2 E = cong (λ x → SendTy κ x ρ E2) (evalCtx∘ η1 η2 E)

-- Evaluation contexts preserve the less-nondeterminism relation
≼-evalCtx : ∀{E1 E2} (η : CtrlECtx) → E1 ≼ E2 → evalCtx η E1 ≼ evalCtx η E2
≼-evalCtx [•] E1≼E2 = E1≼E2
≼-evalCtx (SeqCtx η E2) E1≼E2 = ≼Seq (≼-evalCtx η E1≼E2) (≼-refl E2)
≼-evalCtx (IfCtx η E1 E2) E1≼E2 = ≼ITE (≼-evalCtx η E1≼E2) (≼-refl E1) (≼-refl E2)
≼-evalCtx (SendCtx η ℓ) E1≼E2 = ≼Send (≼-evalCtx η E1≼E2) ℓ
≼-evalCtx (FunCtx η E2) E1≼E2 = ≼App (≼-evalCtx η E1≼E2) (≼-refl E2)
≼-evalCtx (ArgCtx E1 η) E1≼E2 = ≼App (≼-refl E1) (≼-evalCtx η E1≼E2)
≼-evalCtx (TFunCtx η t) E1≼E2 = ≼TApp (≼-evalCtx η E1≼E2) t
≼-evalCtx (LetRetCtx η E2) E1≼E2 = ≼LetRet (≼-evalCtx η E1≼E2) (≼-refl E2)
≼-evalCtx (SendTyCtx κ η ρ E2) E1≼E2 = ≼SendTy κ (≼-evalCtx η E1≼E2) ρ (≼-refl E2)

{-
Control language semantics

  E1 ⟶[l⨾L] E2
------------------
η[E1] ⇒[l⨾L] η[E2]
-}
data _⇒E[_⨾_]_ : Ctrl → CtrlLabel → Loc → Ctrl → Set where
  ηStep : ∀{E1 E2 L l} (η : CtrlECtx) →
          E1 ⟶E[ l ⨾ L ] E2 →
          evalCtx η E1 ⇒E[ l ⨾ L ] evalCtx η E2

-- If E ⇒ E' then η[E] ⇒ η[E']
η-⇒ : ∀{E E' l L} (η : CtrlECtx) →
      E ⇒E[ l ⨾ L ] E' →
      (evalCtx η E) ⇒E[ l ⨾ L ] (evalCtx η E')
η-⇒ {l = l} {L} η1 (ηStep {E1} {E2} η2 E⟶E') =
  subst₂ (λ x y → x ⇒E[ l ⨾ L ] y)
    (evalCtx∘ η1 η2 E1)
    (evalCtx∘ η1 η2 E2)
    (ηStep (η1 ∘ECtx η2) E⟶E')

{-
⟶ lifts the label l at location L if whenever we
have a E1, E1', and E2 such that
-- E1 ≼ E2
-- E1 ⟶[l⨾L] E1'
then there is some E2' such that
-- E1' ≼ E2'
-- E2 ⟶[l⨾L] E2'

E1 ⟶E[l⨾L] E1'
≼          ≼
E2 ⟶E[l⨾L] E2'
-}
⟶-Lifts : CtrlLabel → Loc → Set
⟶-Lifts l L =
  ∀{E1 E1' E2} → 
  E1 ≼ E2 →
  E1 ⟶E[ l ⨾ L ] E1' →
  Σ[ E2' ∈ Ctrl ]
  E1' ≼ E2' ×
  E2 ⟶E[ l ⨾ L ] E2'

{-
⇒ lifts the label l at location L if whenever we
have a E1, E1', and E2 such that
-- E1 ≼ E2
-- E1 ⇒[l⨾L] E1'
then there is some E2' such that
-- E1' ≼ E2'
-- E2 ⇒[l⨾L] E2'

E1 ⇒E[l⨾L] E1'
≼          ≼
E2 ⇒E[l⨾L] E2'
-}
⇒-Lifts : CtrlLabel → Loc → Set
⇒-Lifts l L =
  ∀{E1 E1' E2} → 
  E1 ≼ E2 →
  E1 ⇒E[ l ⨾ L ] E1' →
  Σ[ E2' ∈ Ctrl ]
  E1' ≼ E2' ×
  E2 ⇒E[ l ⨾ L ] E2'

-- If ⟶ lifts l at L, then ⇒ lifts l at L
η-Lifts-impl
  : ∀{l L E1 E1' E2} →
    ⟶-Lifts l L →
    (η : CtrlECtx) →
    evalCtx η E1 ≼ E2 →
    E1 ⟶E[ l ⨾ L ] E1' →
    Σ[ E2' ∈ Ctrl ]
    evalCtx η E1' ≼ E2' ×
    E2 ⇒E[ l ⨾ L ] E2'
η-Lifts-impl f [•] p step with f p step
... | (E2' , p2 , q2) = E2' , p2 , ηStep [•] q2
η-Lifts-impl f (SeqCtx η E2) (≼Seq p q) step
  with η-Lifts-impl f η p step
... | (.(evalCtx η' _) , p2 , ηStep η' step') =
  Seq _ _ , ≼Seq p2 q , ηStep (SeqCtx η' _) step'
η-Lifts-impl f (IfCtx η E1 E2) (≼ITE p q r) step
  with η-Lifts-impl f η p step
... | (.(evalCtx η' _) , p2 , ηStep η' step') =
  CtrlITE _ _ _ , ≼ITE p2 q r , ηStep (IfCtx η' _ _) step'
η-Lifts-impl f (SendCtx η ℓ) (≼Send p .ℓ) step
  with η-Lifts-impl f η p step
... | (.(evalCtx η' _) , p2 , ηStep η' step') =
  SendTo _ ℓ , ≼Send p2 ℓ , ηStep (SendCtx η' ℓ) step'
η-Lifts-impl f (FunCtx η E2) (≼App p q) step
  with η-Lifts-impl f η p step
... | (.(evalCtx η' _) , p2 , ηStep η' step') =
  CtrlApp _ _ , ≼App p2 q , ηStep (FunCtx η' _) step'
η-Lifts-impl f (ArgCtx E1 η) (≼App p q) step
  with η-Lifts-impl f η q step
... | .(evalCtx η' _) , p2 , ηStep η' step' =
  CtrlApp _ _ , ≼App p p2 , ηStep (ArgCtx _ η') step'
η-Lifts-impl f (TFunCtx η t) (≼TApp p .t) step
  with η-Lifts-impl f η p step
... | .(evalCtx η' _) , p2 , ηStep η' step' =
  CtrlTApp _ t , ≼TApp p2 t , ηStep (TFunCtx η' t) step'
η-Lifts-impl f (LetRetCtx η E2) (≼LetRet p q) step
  with η-Lifts-impl f η p step
... | .(evalCtx η' _) , p2 , ηStep η' step' =
  LetRet _ _ , ≼LetRet p2 q , ηStep (LetRetCtx η' _) step'
η-Lifts-impl f (SendTyCtx κ η ρ E2) (≼SendTy .κ p .ρ q) step
  with η-Lifts-impl f η p step
... | .(evalCtx η' _) , p2 , ηStep η' step' =
  SendTy κ _ ρ _ , ≼SendTy κ p2 ρ q , ηStep (SendTyCtx κ η' ρ _) step'

η-Lifts : ∀{l L} → ⟶-Lifts l L → ⇒-Lifts l L
η-Lifts f p (ηStep η q) = η-Lifts-impl f η p q

⟶-Lifts-ι : ∀{L} → ⟶-Lifts ιL L
⟶-Lifts-ι (≼Ret e1) (RetStep {e2 = e2} e1⇒e2) = Ret e2 , ≼Ret e2 , RetStep e1⇒e2
⟶-Lifts-ι (≼Seq E11≼E21 E12≼E22) (SeqVStep E11-Val) with V≼ E11-Val E11≼E21
... | refl = _ , E12≼E22 , SeqVStep E11-Val
⟶-Lifts-ι (≼ITE (≼Ret .(𝕃 .ttₑ)) E12≼E22 E13≼E23) IfTStep =
  _ , E12≼E22 , IfTStep
⟶-Lifts-ι (≼ITE (≼Ret .(𝕃 .ffₑ)) E12≼E22 E13≼E23) IfFStep =
  _ , E13≼E23 , IfFStep
⟶-Lifts-ι (≼LetRet (≼Ret v) E1≼E2) (LetRetVStep v-Val) =
  _ , ≼-localSub (var ▸ v) E1≼E2 , LetRetVStep v-Val
⟶-Lifts-ι (≼AmI .(LitLoc _) E11≼E21 E12≼E22) AmILStep =
  _ , E11≼E21 , AmILStep
⟶-Lifts-ι (≼AmI ℓ E11≼E21 E12≼E22) (AmIRStep ℓ≢L) =
  _ , E12≼E22 , AmIRStep ℓ≢L
⟶-Lifts-ι (≼AmIIn ρ E11≼E21 E12≼E22) (AmIInLStep L∈ρ) =
  _ , E11≼E21 , AmIInLStep L∈ρ
⟶-Lifts-ι (≼AmIIn ρ E11≼E21 E12≼E22) (AmIInRStep L∉ρ) =
  _ , E12≼E22 , AmIInRStep L∉ρ

⇒-Lifts-ι : ∀{L} → ⇒-Lifts ιL L
⇒-Lifts-ι = η-Lifts ⟶-Lifts-ι

⟶-Lifts-ιSync : ∀{L} → ⟶-Lifts ιSyncL L
⟶-Lifts-ιSync (≼Rec E) RecStep = subCtrl (var ▸ CtrlFix E) E , ≼-refl _ , RecStep
⟶-Lifts-ιSync (≼App (≼Abs E) q) (AppStep {V = V} V-Val) with V≼ V-Val q
... | refl = subCtrl (var ▸ V) E , ≼-refl _ , AppStep V-Val
⟶-Lifts-ιSync (≼TApp (≼TAbs E) t) AppTStep =
  tySubCtrl (tyVar ▸ t) E , ≼-refl _ , AppTStep

⇒-Lifts-ιSync : ∀{L} → ⇒-Lifts ιSyncL L
⇒-Lifts-ιSync = η-Lifts ⟶-Lifts-ιSync

⟶-Lifts-Send : ∀{v L1 L2} → ⟶-Lifts (SendL v L2) L1
⟶-Lifts-Send (≼Send (≼Ret _) .(LitLoc _)) (SendVStep v-Val L2≢L1) = Unit , ≼Unit , SendVStep v-Val L2≢L1

⇒-Lifts-Send : ∀{v L1 L2} → ⇒-Lifts (SendL v L2) L1
⇒-Lifts-Send = η-Lifts ⟶-Lifts-Send

⟶-Lifts-Recv : ∀{v L1 L2} → ⟶-Lifts (RecvL L1 v) L2
⟶-Lifts-Recv (≼Recv .(LitLoc _)) (RecvStep v-Val L1≢L2) =
  _ , ≼Ret _ , RecvStep v-Val L1≢L2

⇒-Lifts-Recv : ∀{v L1 L2} → ⇒-Lifts (RecvL L1 v) L2
⇒-Lifts-Recv = η-Lifts ⟶-Lifts-Recv

⟶-Lifts-SendSync : ∀{d L1 L2} → ⟶-Lifts (SendSyncL d L2) L1
⟶-Lifts-SendSync (≼Choose d .(LitLoc _) p) (ChooseStep L2≢L1) =
  _ , p , ChooseStep L2≢L1

⇒-Lifts-SendSync : ∀{d L1 L2} → ⇒-Lifts (SendSyncL d L2) L1
⇒-Lifts-SendSync = η-Lifts ⟶-Lifts-SendSync

⟶-Lifts-RecvSync : ∀{d L1 L2} → ⟶-Lifts (RecvSyncL L1 d) L2
⟶-Lifts-RecvSync (≼Allow .(LitLoc _) (′≼′ p) q) (AllowLStep L1≢L2) =
  _ , p , AllowLStep L1≢L2
⟶-Lifts-RecvSync (≼Allow .(LitLoc _) p (′≼′ q)) (AllowRStep L1≢L2) =
  _ , q , AllowRStep L1≢L2

⇒-Lifts-RecvSync : ∀{d L1 L2} → ⇒-Lifts (RecvSyncL L1 d) L2
⇒-Lifts-RecvSync = η-Lifts ⟶-Lifts-RecvSync

⟶-Lifts-SendLoc : ∀{Lv ρ L} → ⟶-Lifts (SendLocL Lv ρ) L
⟶-Lifts-SendLoc {Lv} (≼SendTy *ₗ (≼Ret .(𝕃 .litLocₑ _)) .(LitSet _) p) SendTyLocStep =
  _ , ≼-tySubCtrl (tyVar ▸ LitLoc Lv) p , SendTyLocStep

⇒-Lifts-SendLoc : ∀{Lv ρ L} → ⇒-Lifts (SendLocL Lv ρ) L
⇒-Lifts-SendLoc = η-Lifts ⟶-Lifts-SendLoc

⟶-Lifts-RecvLoc : ∀{Lv L1 L2} → ⟶-Lifts (RecvLocL L1 Lv) L2
⟶-Lifts-RecvLoc {Lv} (≼RecvTy *ₗ .(LitLoc _) p) (RecvTyLocStep L1≢L2) =
  _ , ≼-tySubCtrl (tyVar  ▸ LitLoc Lv) p , RecvTyLocStep L1≢L2

⇒-Lifts-RecvLoc : ∀{Lv L1 L2} → ⇒-Lifts (RecvLocL L1 Lv) L2
⇒-Lifts-RecvLoc = η-Lifts ⟶-Lifts-RecvLoc

⟶-Lifts-SendTy : ∀{L tₑ ρ} → ⟶-Lifts (SendTyL tₑ ρ) L
⟶-Lifts-SendTy (≼SendTy .*ₑ (≼Ret _) .(LitSet _) p) (SendLocalTyStep {v = v} v-Val) =
  _ , ≼-tySubCtrl (tyVar ▸ injTy (𝕃 .Elₑ v)) p , SendLocalTyStep v-Val

⇒-Lifts-SendTy : ∀{L tₑ ρ} → ⇒-Lifts (SendTyL tₑ ρ) L
⇒-Lifts-SendTy = η-Lifts ⟶-Lifts-SendTy

⟶-Lifts-RecvTy : ∀{L1 L2 tₑ} → ⟶-Lifts (RecvTyL L1 tₑ) L2
⟶-Lifts-RecvTy (≼RecvTy .*ₑ .(LitLoc _) p) (RecvLocalTyStep {v = v} v-Val L1≢L2) =
  _ , ≼-tySubCtrl (tyVar ▸ injTy (𝕃 .Elₑ v)) p , RecvLocalTyStep v-Val L1≢L2

⇒-Lifts-RecvTy : ∀{L1 L2 tₑ} → ⇒-Lifts (RecvTyL L1 tₑ) L2
⇒-Lifts-RecvTy = η-Lifts ⟶-Lifts-RecvTy

{-
⟶ lowers the label l at location L if whenever we
have a E1, E2, and E2' such that
-- E1 ≼ E2
-- E2 ⟶[l⨾L] E2'
then there is some E1' such that
-- E1' ≼ E2'
-- E1 ⟶[l⨾L] E1'

E1 ⟶E[l⨾L] E1'
≼          ≼
E2 ⟶E[l⨾L] E2'
-}
⟶-Lowers : CtrlLabel → Loc → Set
⟶-Lowers l L =
  ∀{E1 E2 E2'} →
  E1 ≼ E2 →
  E2 ⟶E[ l ⨾ L ] E2' →
  Σ[ E1' ∈ Ctrl ]
  E1' ≼ E2' ×
  E1 ⟶E[ l ⨾ L ] E1'

{-
⇒ lowers the label l at location L if whenever we
have a E1, E2, and E2' such that
-- E1 ≼ E2
-- E2 ⇒[l⨾L] E2'
then there is some E1' such that
-- E1' ≼ E2'
-- E1 ⇒[l⨾L] E1'

E1 ⇒E[l⨾L] E1'
≼          ≼
E2 ⇒E[l⨾L] E2'
-}
⇒-Lowers : CtrlLabel → Loc → Set
⇒-Lowers l L =
  ∀{E1 E2 E2'} →
  E1 ≼ E2 →
  E2 ⇒E[ l ⨾ L ] E2' →
  Σ[ E1' ∈ Ctrl ]
  E1' ≼ E2' ×
  E1 ⇒E[ l ⨾ L ] E1'

-- If ⟶ lowers l at L, then ⇒ lowers l at L
η-Lowers-impl
  : ∀{l L E1 E2 E2'} →
    ⟶-Lowers l L →
    (η : CtrlECtx) →
    E1 ≼ evalCtx η E2 →
    E2 ⟶E[ l ⨾ L ] E2' →
    Σ[ E1' ∈ Ctrl ]
    E1' ≼ evalCtx η E2' ×
    E1 ⇒E[ l ⨾ L ] E1'
η-Lowers-impl f [•] p step with f p step
... | (E2' , p2 , q2) = E2' , p2 , ηStep [•] q2
η-Lowers-impl f (SeqCtx η E2) (≼Seq p q) step
  with η-Lowers-impl f η p step
... | (.(evalCtx η' _) , p2 , ηStep η' step') =
  Seq _ _ , ≼Seq p2 q , ηStep (SeqCtx η' _) step'
η-Lowers-impl f (IfCtx η E1 E2) (≼ITE p q r) step
  with η-Lowers-impl f η p step
... | (.(evalCtx η' _) , p2 , ηStep η' step') =
  CtrlITE _ _ _ , ≼ITE p2 q r , ηStep (IfCtx η' _ _) step'
η-Lowers-impl f (SendCtx η ℓ) (≼Send p .ℓ) step
  with η-Lowers-impl f η p step
... | (.(evalCtx η' _) , p2 , ηStep η' step') =
  SendTo _ ℓ , ≼Send p2 ℓ , ηStep (SendCtx η' ℓ) step'
η-Lowers-impl f (FunCtx η E2) (≼App p q) step
  with η-Lowers-impl f η p step
... | (.(evalCtx η' _) , p2 , ηStep η' step') =
  CtrlApp _ _ , ≼App p2 q , ηStep (FunCtx η' _) step'
η-Lowers-impl f (ArgCtx E1 η) (≼App p q) step
  with η-Lowers-impl f η q step
... | .(evalCtx η' _) , p2 , ηStep η' step' =
  CtrlApp _ _ , ≼App p p2 , ηStep (ArgCtx _ η') step'
η-Lowers-impl f (TFunCtx η t) (≼TApp p .t) step with η-Lowers-impl f η p step
... | .(evalCtx η' _) , p2 , ηStep η' step' =
  CtrlTApp _ t , ≼TApp p2 t , ηStep (TFunCtx η' t) step'
η-Lowers-impl f (LetRetCtx η E2) (≼LetRet p q) step with η-Lowers-impl f η p step
... | .(evalCtx η' _) , p2 , ηStep η' step' =
  LetRet _ _ , ≼LetRet p2 q , ηStep (LetRetCtx η' _) step'
η-Lowers-impl f (SendTyCtx κ η ρ E2) (≼SendTy .κ p .ρ q) step
  with η-Lowers-impl f η p step
... | .(evalCtx η' _) , p2 , ηStep η' step' =
  SendTy κ _ ρ _ , ≼SendTy κ p2 ρ q , ηStep (SendTyCtx κ η' ρ _) step'

η-Lowers : ∀{l L} → ⟶-Lowers l L → ⇒-Lowers l L
η-Lowers f p (ηStep η q) = η-Lowers-impl f η p q

⟶-Lowers-ι : ∀{L} → ⟶-Lowers ιL L
⟶-Lowers-ι (≼Ret e1) (RetStep {e2 = e2} e1⇒e2) = Ret e2 , ≼Ret e2 , RetStep e1⇒e2
⟶-Lowers-ι (≼Seq E11≼E21 E12≼E22) (SeqVStep E11-Val)
  with ≼V E11-Val E11≼E21
... | refl = _ , E12≼E22 , SeqVStep E11-Val
⟶-Lowers-ι (≼ITE (≼Ret .(𝕃 .ttₑ)) E12≼E22 E13≼E23) IfTStep =
  _ , E12≼E22 , IfTStep
⟶-Lowers-ι (≼ITE (≼Ret .(𝕃 .ffₑ)) E12≼E22 E13≼E23) IfFStep =
  _ , E13≼E23 , IfFStep
⟶-Lowers-ι (≼LetRet (≼Ret v) E1≼E2) (LetRetVStep v-Val) =
  _ , ≼-localSub (var ▸ v) E1≼E2 , LetRetVStep v-Val
⟶-Lowers-ι (≼AmI .(LitLoc _) E11≼E21 E12≼E22) AmILStep =
  _ , E11≼E21 , AmILStep
⟶-Lowers-ι (≼AmI ℓ E11≼E21 E12≼E22) (AmIRStep ℓ≢L) =
  _ , E12≼E22 , AmIRStep ℓ≢L
⟶-Lowers-ι (≼AmIIn ρ E11≼E21 E12≼E22) (AmIInLStep L∈ρ) =
  _ , E11≼E21 , AmIInLStep L∈ρ
⟶-Lowers-ι (≼AmIIn ρ E11≼E21 E12≼E22) (AmIInRStep L∉ρ) =
  _ , E12≼E22 , AmIInRStep L∉ρ

⇒-Lowers-ι : ∀{L} → ⇒-Lowers ιL L
⇒-Lowers-ι = η-Lowers ⟶-Lowers-ι

⟶-Lowers-ιSync : ∀{L} → ⟶-Lowers ιSyncL L
⟶-Lowers-ιSync (≼Rec E) RecStep = 
  subCtrl (var ▸ CtrlFix E) E , ≼-refl _ , RecStep
⟶-Lowers-ιSync (≼App (≼Abs E) q) (AppStep {V = V} V-Val) with ≼V V-Val q
... | refl = subCtrl (var ▸ V) E , ≼-refl _ , AppStep V-Val
⟶-Lowers-ιSync (≼TApp (≼TAbs E) t) AppTStep =
  tySubCtrl (tyVar ▸ t) E , ≼-refl _ , AppTStep

⇒-Lowers-ιSync : ∀{L} → ⇒-Lowers ιSyncL L
⇒-Lowers-ιSync = η-Lowers ⟶-Lowers-ιSync

⟶-Lowers-Send : ∀{v L1 L2} → ⟶-Lowers (SendL v L2) L1
⟶-Lowers-Send (≼Send (≼Ret _) .(LitLoc _)) (SendVStep v-Val L2≢L1) =
  Unit , ≼Unit , SendVStep v-Val L2≢L1
 
⇒-Lowers-Send : ∀{v L1 L2} → ⇒-Lowers (SendL v L2) L1
⇒-Lowers-Send = η-Lowers ⟶-Lowers-Send

⟶-Lowers-Recv : ∀{v L1 L2} → ⟶-Lowers (RecvL L1 v) L2
⟶-Lowers-Recv (≼Recv .(LitLoc _)) (RecvStep v-Val L1≢L2) =
  _ , ≼Ret _ , RecvStep v-Val L1≢L2

⇒-Lowers-Recv : ∀{v L1 L2} → ⇒-Lowers (RecvL L1 v) L2
⇒-Lowers-Recv = η-Lowers ⟶-Lowers-Recv

⟶-Lowers-SendSync : ∀{d L1 L2} → ⟶-Lowers (SendSyncL d L2) L1
⟶-Lowers-SendSync (≼Choose d .(LitLoc _) p) (ChooseStep L2≢L1) =
  _ , p , ChooseStep L2≢L1

⇒-Lowers-SendSync : ∀{d L1 L2} → ⇒-Lowers (SendSyncL d L2) L1
⇒-Lowers-SendSync = η-Lowers ⟶-Lowers-SendSync

⟶-Lowers-SendLoc : ∀{Lv ρ L} → ⟶-Lowers (SendLocL Lv ρ) L
⟶-Lowers-SendLoc {Lv} (≼SendTy *ₗ (≼Ret .(𝕃 .litLocₑ _)) .(LitSet _) p) SendTyLocStep =
  _ , ≼-tySubCtrl (tyVar ▸ LitLoc Lv) p , SendTyLocStep

⇒-Lowers-SendLoc : ∀{Lv ρ L} → ⇒-Lowers (SendLocL Lv ρ) L
⇒-Lowers-SendLoc = η-Lowers ⟶-Lowers-SendLoc

⟶-Lowers-RecvLoc : ∀{Lv L1 L2} → ⟶-Lowers (RecvLocL L1 Lv) L2
⟶-Lowers-RecvLoc {Lv} (≼RecvTy *ₗ .(LitLoc _) p) (RecvTyLocStep L1≢L2) =
  _ , ≼-tySubCtrl (tyVar  ▸ LitLoc Lv) p , RecvTyLocStep L1≢L2

⇒-Lowers-RecvLoc : ∀{Lv L1 L2} → ⇒-Lowers (RecvLocL L1 Lv) L2
⇒-Lowers-RecvLoc = η-Lowers ⟶-Lowers-RecvLoc

⟶-Lowers-SendTy : ∀{L tₑ ρ} → ⟶-Lowers (SendTyL tₑ ρ) L
⟶-Lowers-SendTy (≼SendTy .*ₑ (≼Ret _) .(LitSet _) p) (SendLocalTyStep {v = v} v-Val) =
  _ , ≼-tySubCtrl (tyVar ▸ injTy (𝕃 .Elₑ v)) p , SendLocalTyStep v-Val

⇒-Lowers-SendTy : ∀{L tₑ ρ} → ⇒-Lowers (SendTyL tₑ ρ) L
⇒-Lowers-SendTy = η-Lowers ⟶-Lowers-SendTy

⟶-Lowers-RecvTy : ∀{L1 L2 tₑ} → ⟶-Lowers (RecvTyL L1 tₑ) L2
⟶-Lowers-RecvTy (≼RecvTy .*ₑ .(LitLoc _) p) (RecvLocalTyStep {v = v} v-Val L1≢L2) =
  _ , ≼-tySubCtrl (tyVar ▸ injTy (𝕃 .Elₑ v)) p , RecvLocalTyStep v-Val L1≢L2

⇒-Lowers-RecvTy : ∀{L1 L2 tₑ} → ⇒-Lowers (RecvTyL L1 tₑ) L2
⇒-Lowers-RecvTy = η-Lowers ⟶-Lowers-RecvTy
