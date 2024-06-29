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

module PolyPir.CtrlLang
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

_⇒ₑ_ = 𝕃 .Stepₑ

{-
Control expression syntax
 
E ::= X | () | ret(e)
    | E1 ; E2 | λX.E | μX.E | E1 E2
    | send E to ℓ | recv from ℓ
    | choose d for ℓ; E
    | allow ℓ choice (L ⇒ ?E1) (R ⇒ ?E1)
    | if E then E1 else E2
    | Λα.E | E t
    | let ret(x) := E1 in E2
    | send α∷κ := E1 to ρ in E2
    | recv α∷κ from ℓ in E
    | AmI ℓ then E1 else E2
-}
data Ctrl : Set

data ?Ctrl : Set where
  ？ : ?Ctrl
  ′_ : Ctrl → ?Ctrl

data Ctrl where
  var : (x : ℕ) → Ctrl
  Unit : Ctrl
  Ret : (e : Tmₑ) → Ctrl
  Seq : (E1 E2 : Ctrl) → Ctrl
  CtrlLam CtrlFix : (E : Ctrl) → Ctrl
  CtrlApp : (E1 E2 : Ctrl) → Ctrl
  SendTo : (E : Ctrl) (ℓ : CTy) → Ctrl
  Recv : (ℓ : CTy) → Ctrl
  Choose : (d : Bool) (ℓ : CTy) (E : Ctrl) → Ctrl
  Allow : (ℓ : CTy) (?E1 ?E2 : ?Ctrl) → Ctrl
  CtrlITE : (E E1 E2 : Ctrl) → Ctrl
  CtrlTAbs : (E : Ctrl) → Ctrl
  CtrlTApp : (E : Ctrl) (t : CTy) → Ctrl
  LetRet : (E1 E2 : Ctrl) → Ctrl
  SendTy : (κ : ChorKnd) (E1 : Ctrl) (ρ : CTy) (E2 : Ctrl) → Ctrl
  RecvTy : (κ : ChorKnd) (ℓ : CTy) (E : Ctrl) → Ctrl
  AmI : (ℓ : CTy) (E1 E2 : Ctrl) → Ctrl
  AmIIn : (ρ : CTy) (E1 E2 : Ctrl) → Ctrl


{-
Control expression values

V ::= () | Ret v | λX.E | Λα.E
-}
data CtrlVal : Ctrl → Set where
  ValUnit : CtrlVal Unit
  ValRet : ∀{v} (v-Val : 𝕃 .Valₑ v) → CtrlVal (Ret v)
  ValAbs : (E : Ctrl) → CtrlVal (CtrlLam E)
  ValTAbs : (E : Ctrl) → CtrlVal (CtrlTAbs E)

-- Renaming and substitution operations
renCtrl : Ren → Ctrl → Ctrl
renCtrl? : Ren → ?Ctrl → ?Ctrl

renCtrl ξ (var x) = var (ξ x)
renCtrl ξ Unit = Unit
renCtrl ξ (Ret e) = Ret e
renCtrl ξ (Seq E1 E2) = Seq (renCtrl ξ E1) (renCtrl ξ E2)
renCtrl ξ (CtrlLam E) = CtrlLam (renCtrl (Keep ξ) E)
renCtrl ξ (CtrlFix E) = CtrlFix (renCtrl (Keep ξ) E)
renCtrl ξ (CtrlApp E1 E2) = CtrlApp (renCtrl ξ E1) (renCtrl ξ E2)
renCtrl ξ (SendTo E ℓ) = SendTo (renCtrl ξ E) ℓ
renCtrl ξ (Recv ℓ) = Recv ℓ
renCtrl ξ (Choose d ℓ E) = Choose d ℓ (renCtrl ξ E)
renCtrl ξ (Allow ℓ ?E1 ?E2) =
  Allow ℓ (renCtrl? ξ ?E1) (renCtrl? ξ ?E2)
renCtrl ξ (CtrlITE E E1 E2) =
  CtrlITE (renCtrl ξ E) (renCtrl ξ E1) (renCtrl ξ E2)
renCtrl ξ (CtrlTAbs E) = CtrlTAbs (renCtrl ξ E)
renCtrl ξ (CtrlTApp E t) = CtrlTApp (renCtrl ξ E) t
renCtrl ξ (LetRet E1 E2) = LetRet (renCtrl ξ E1) (renCtrl ξ E2)
renCtrl ξ (SendTy κ E1 ρ E2) =
  SendTy κ (renCtrl ξ E1) ρ (renCtrl ξ E2)
renCtrl ξ (RecvTy κ ℓ E) = RecvTy κ ℓ (renCtrl ξ E)
renCtrl ξ (AmI ℓ E1 E2) = AmI ℓ (renCtrl ξ E1) (renCtrl ξ E2)
renCtrl ξ (AmIIn ρ E1 E2) = AmIIn ρ (renCtrl ξ E1) (renCtrl ξ E2)

renCtrl? ξ ？ = ？
renCtrl? ξ (′ E) = ′ (renCtrl ξ E)

subCtrl : (ℕ → Ctrl) → Ctrl → Ctrl
subCtrl? : (ℕ → Ctrl) → ?Ctrl → ?Ctrl

subCtrl σ (var x) = σ x
subCtrl σ Unit = Unit
subCtrl σ (Ret e) = Ret e
subCtrl σ (Seq E1 E2) = Seq (subCtrl σ E1) (subCtrl σ E2)
subCtrl σ (CtrlLam E) = CtrlLam (subCtrl (renCtrl (Keep id) ∘ σ) E)
subCtrl σ (CtrlFix E) = CtrlFix (subCtrl (renCtrl (Keep id) ∘ σ) E)
subCtrl σ (CtrlApp E1 E2) = CtrlApp (subCtrl σ E1) (subCtrl σ E2)
subCtrl σ (SendTo E ℓ) = SendTo (subCtrl σ E) ℓ
subCtrl σ (Recv ℓ) = Recv ℓ
subCtrl σ (Choose d ℓ E) = Choose d ℓ (subCtrl σ E)
subCtrl σ (Allow ℓ ?E1 ?E2) =
  Allow ℓ (subCtrl? σ ?E1) (subCtrl? σ ?E2)
subCtrl σ (CtrlITE E E1 E2) =
  CtrlITE (subCtrl σ E) (subCtrl σ E1) (subCtrl σ E2)
subCtrl σ (CtrlTAbs E) = CtrlTAbs (subCtrl σ E)
subCtrl σ (CtrlTApp E t) = CtrlTApp (subCtrl σ E) t
subCtrl σ (LetRet E1 E2) = LetRet (subCtrl σ E1) (subCtrl σ E2)
subCtrl σ (SendTy κ E1 ρ E2) =
  SendTy κ (subCtrl σ E1) ρ (subCtrl σ E2)
subCtrl σ (RecvTy κ ℓ E) = RecvTy κ ℓ (subCtrl σ E)
subCtrl σ (AmI ℓ E1 E2) = AmI ℓ (subCtrl σ E1) (subCtrl σ E2)
subCtrl σ (AmIIn ρ E1 E2) = AmIIn ρ (subCtrl σ E1) (subCtrl σ E2)

subCtrl? σ ？ = ？
subCtrl? σ (′ E) = ′ (subCtrl σ E)

tyRenCtrl : (ℕ → ℕ) → Ctrl → Ctrl
tyRenCtrl? : (ℕ → ℕ) → ?Ctrl → ?Ctrl

tyRenCtrl ξ (var x) = var x
tyRenCtrl ξ Unit = Unit
tyRenCtrl ξ (Ret e) = Ret e
tyRenCtrl ξ (Seq E1 E2) = Seq (tyRenCtrl ξ E1) (tyRenCtrl ξ E2)
tyRenCtrl ξ (CtrlLam E) = CtrlLam (tyRenCtrl ξ E)
tyRenCtrl ξ (CtrlFix E) = CtrlFix (tyRenCtrl ξ E)
tyRenCtrl ξ (CtrlApp E1 E2) = CtrlApp (tyRenCtrl ξ E1) (tyRenCtrl ξ E2)
tyRenCtrl ξ (SendTo E ℓ) = SendTo (tyRenCtrl ξ E) (renTy C⅀ₖ ξ ℓ)
tyRenCtrl ξ (Recv ℓ) = Recv (renTy C⅀ₖ ξ ℓ)
tyRenCtrl ξ (Choose d ℓ E) = Choose d (renTy C⅀ₖ ξ ℓ) (tyRenCtrl ξ E)
tyRenCtrl ξ (Allow ℓ ?E1 ?E2) =
  Allow (renTy C⅀ₖ ξ ℓ) (tyRenCtrl? ξ ?E1) (tyRenCtrl? ξ ?E2)
tyRenCtrl ξ (CtrlITE E E1 E2) =
  CtrlITE (tyRenCtrl ξ E) (tyRenCtrl ξ E1) (tyRenCtrl ξ E2)
tyRenCtrl ξ (CtrlTAbs E) = CtrlTAbs (tyRenCtrl (Keep ξ) E)
tyRenCtrl ξ (CtrlTApp E t) = CtrlTApp (tyRenCtrl ξ E) (renTy C⅀ₖ ξ t)
tyRenCtrl ξ (LetRet E1 E2) = LetRet (tyRenCtrl ξ E1) (tyRenCtrl ξ E2)
tyRenCtrl ξ (SendTy κ E1 ρ E2) =
  SendTy κ (tyRenCtrl ξ E1) (renTy C⅀ₖ ξ ρ) (tyRenCtrl ξ E2)
tyRenCtrl ξ (RecvTy κ ℓ E) = RecvTy κ (renTy C⅀ₖ ξ ℓ) (tyRenCtrl (Keep ξ) E)
tyRenCtrl ξ (AmI ℓ E1 E2) = AmI (renTy C⅀ₖ ξ ℓ) (tyRenCtrl ξ E1) (tyRenCtrl ξ E2)
tyRenCtrl ξ (AmIIn ρ E1 E2) = AmIIn (renTy C⅀ₖ ξ ρ) (tyRenCtrl ξ E1) (tyRenCtrl ξ E2)

tyRenCtrl? ξ ？ = ？
tyRenCtrl? ξ (′ E) = ′ (tyRenCtrl ξ E)

tySubCtrl : (ℕ → CTy) → Ctrl → Ctrl
tySubCtrl? : (ℕ → CTy) → ?Ctrl → ?Ctrl

tySubCtrl σ (var x) = var x
tySubCtrl σ Unit = Unit
tySubCtrl σ (Ret e) = Ret e
tySubCtrl σ (Seq E1 E2) = Seq (tySubCtrl σ E1) (tySubCtrl σ E2)
tySubCtrl σ (CtrlLam E) = CtrlLam (tySubCtrl σ E)
tySubCtrl σ (CtrlFix E) = CtrlFix (tySubCtrl σ E)
tySubCtrl σ (CtrlApp E1 E2) = CtrlApp (tySubCtrl σ E1) (tySubCtrl σ E2)
tySubCtrl σ (SendTo E ℓ) = SendTo (tySubCtrl σ E) (subTy C⅀ₖ σ ℓ)
tySubCtrl σ (Recv ℓ) = Recv (subTy C⅀ₖ σ ℓ)
tySubCtrl σ (Choose d ℓ E) = Choose d (subTy C⅀ₖ σ ℓ) (tySubCtrl σ E)
tySubCtrl σ (Allow ℓ ?E1 ?E2) =
  Allow (subTy C⅀ₖ σ ℓ) (tySubCtrl? σ ?E1) (tySubCtrl? σ ?E2)
tySubCtrl σ (CtrlITE E E1 E2) =
  CtrlITE (tySubCtrl σ E) (tySubCtrl σ E1) (tySubCtrl σ E2)
tySubCtrl σ (CtrlTAbs E) = CtrlTAbs (tySubCtrl (TyKeepSub C⅀ₖ σ) E)
tySubCtrl σ (CtrlTApp E t) = CtrlTApp (tySubCtrl σ E) (subTy C⅀ₖ σ t)
tySubCtrl σ (LetRet E1 E2) = LetRet (tySubCtrl σ E1) (tySubCtrl σ E2)
tySubCtrl σ (SendTy κ E1 ρ E2) =
  SendTy κ (tySubCtrl σ E1) (subTy C⅀ₖ σ ρ) (tySubCtrl σ E2)
tySubCtrl σ (RecvTy κ ℓ E) = RecvTy κ (subTy C⅀ₖ σ ℓ) (tySubCtrl (TyKeepSub C⅀ₖ σ) E)
tySubCtrl σ (AmI ℓ E1 E2) = AmI (subTy C⅀ₖ σ ℓ) (tySubCtrl σ E1) (tySubCtrl σ E2)
tySubCtrl σ (AmIIn ρ E1 E2) = AmIIn (subTy C⅀ₖ σ ρ) (tySubCtrl σ E1) (tySubCtrl σ E2)

tySubCtrl? σ ？ = ？
tySubCtrl? σ (′ E) = ′ (tySubCtrl σ E)

localSub : (ℕ → Tmₑ) → Ctrl → Ctrl
localSub? : (ℕ → Tmₑ) → ?Ctrl → ?Ctrl

localSub σ (var x) = var x
localSub σ Unit = Unit
localSub σ (Ret e) = Ret (sub (𝕃 .⅀ₑ) σ e)
localSub σ (Seq E1 E2) = Seq (localSub σ E1) (localSub σ E2)
localSub σ (CtrlLam E) = CtrlLam (localSub σ E)
localSub σ (CtrlFix E) = CtrlFix (localSub σ E)
localSub σ (CtrlApp E1 E2) =
  CtrlApp (localSub σ E1) (localSub σ E2)
localSub σ (SendTo E ℓ) = SendTo (localSub σ E) ℓ
localSub σ (Recv ℓ) = Recv ℓ
localSub σ (Choose d ℓ E) = Choose d ℓ (localSub σ E)
localSub σ (Allow ℓ ?E1 ?E2) =
  Allow ℓ (localSub? σ ?E1) (localSub? σ ?E2)
localSub σ (CtrlITE E E1 E2) =
  CtrlITE (localSub σ E) (localSub σ E1) (localSub σ E2)
localSub σ (CtrlTAbs E) = CtrlTAbs (localSub σ E)
localSub σ (CtrlTApp E t) = CtrlTApp (localSub σ E) t
localSub σ (LetRet E1 E2) =
  LetRet (localSub σ E1) (localSub (KeepSub (𝕃 .⅀ₑ) σ) E2)
localSub σ (SendTy κ E1 ρ E2) =
  SendTy κ (localSub σ E1) ρ (localSub σ E2)
localSub σ (RecvTy κ ℓ E) = RecvTy κ ℓ (localSub σ E)
localSub σ (AmI ℓ E1 E2) = AmI ℓ (localSub σ E1) (localSub σ E2)
localSub σ (AmIIn ρ E1 E2) = AmIIn ρ (localSub σ E1) (localSub σ E2)

localSub? σ ？ = ？
localSub? σ (′ E) = ′ (localSub σ E)

{-
The less nondeterministic relation
-}
data _≼_ : Ctrl → Ctrl → Set

data _≼?_ : ?Ctrl → ?Ctrl → Set where
  ？≼？ : ？ ≼? ？
  ?≼′ : (E : Ctrl) → ？ ≼? (′ E)
  ′≼′ : ∀{E1 E2} → E1 ≼ E2 → (′ E1) ≼? (′ E2)

data _≼_ where
  ≼var : (x : ℕ) → var x ≼ var x
  ≼Unit : Unit ≼ Unit
  ≼Ret : (e : Tmₑ) → Ret e ≼ Ret e
  ≼Seq : ∀{E11 E12 E21 E22} →
         E11 ≼ E21 →
         E12 ≼ E22 →
         Seq E11 E12 ≼ Seq E21 E22
  ≼Abs : (E : Ctrl) → CtrlLam E ≼ CtrlLam E
  ≼Rec : (E : Ctrl) → CtrlFix E ≼ CtrlFix E
  ≼App : ∀{E11 E12 E21 E22} →
         E11 ≼ E21 →
         E12 ≼ E22 →
         CtrlApp E11 E12 ≼ CtrlApp E21 E22
  ≼Send : ∀{E1 E2} →
          E1 ≼ E2 →
          (ℓ : CTy) →
          SendTo E1 ℓ ≼ SendTo E2 ℓ
  ≼Recv : (ℓ : CTy) → Recv ℓ ≼ Recv ℓ
  ≼Choose : ∀{E1 E2} →
            (d : Bool) (ℓ : CTy) →
            E1 ≼ E2 →
            Choose d ℓ E1 ≼ Choose d ℓ E2
  ≼Allow : ∀{E11 E12 E21 E22} →
            (ℓ : CTy) →
            E11 ≼? E21 →
            E12 ≼? E22 →
            Allow ℓ E11 E12 ≼ Allow ℓ E21 E22
  ≼ITE : ∀{E1 E11 E12 E2 E21 E22} →
         E1 ≼ E2 →
         E11 ≼ E21 →
         E12 ≼ E22 →
         CtrlITE E1 E11 E12 ≼ CtrlITE E2 E21 E22
  ≼TAbs : (E : Ctrl) → CtrlTAbs E ≼ CtrlTAbs E
  ≼TApp : ∀{E1 E2} →
          E1 ≼ E2 →
          (t : CTy) →
          CtrlTApp E1 t ≼ CtrlTApp E2 t
  ≼LetRet : ∀{E11 E12 E21 E22} →
            E11 ≼ E21 →
            E12 ≼ E22 →
            LetRet E11 E12 ≼ LetRet E21 E22
  ≼SendTy : ∀{E11 E12 E21 E22} →
            (κ : ChorKnd) →
            E11 ≼ E21 →
            (ρ : CTy) →
            E12 ≼ E22 →
            SendTy κ E11 ρ E12 ≼ SendTy κ E21 ρ E22
  ≼RecvTy : ∀{E1 E2} →
            (κ : ChorKnd) →
            (ℓ : CTy) →
            E1 ≼ E2 →
            RecvTy κ ℓ E1 ≼ RecvTy κ ℓ E2
  ≼AmI : ∀{E11 E12 E21 E22} →
          (ℓ : CTy) →
          E11 ≼ E21 →
          E12 ≼ E22 →
          AmI ℓ E11 E12 ≼ AmI ℓ E21 E22
  ≼AmIIn : ∀{E11 E12 E21 E22} →
            (ρ : CTy) →
            E11 ≼ E21 →
            E12 ≼ E22 →
            AmIIn ρ E11 E12 ≼ AmIIn ρ E21 E22
        
≼-refl : (E : Ctrl) → E ≼ E
≼?-refl : (E : ?Ctrl) → E ≼? E

≼-refl (var x) = ≼var x
≼-refl Unit = ≼Unit
≼-refl (Ret e) = ≼Ret e 
≼-refl (Seq E1 E2) = ≼Seq (≼-refl E1) (≼-refl E2)
≼-refl (CtrlLam E) = ≼Abs E
≼-refl (CtrlFix E) = ≼Rec E
≼-refl (CtrlApp E1 E2) = ≼App (≼-refl E1) (≼-refl E2)
≼-refl (SendTo E ℓ) = ≼Send (≼-refl E) ℓ
≼-refl (Recv ℓ) = ≼Recv ℓ
≼-refl (Choose d ℓ E) = ≼Choose d ℓ (≼-refl E)
≼-refl (Allow ℓ ?E1 ?E2) = ≼Allow ℓ (≼?-refl ?E1) (≼?-refl ?E2)
≼-refl (CtrlITE E E1 E2) = ≼ITE (≼-refl E) (≼-refl E1) (≼-refl E2)
≼-refl (CtrlTAbs E) = ≼TAbs E
≼-refl (CtrlTApp E t) = ≼TApp (≼-refl E) t
≼-refl (LetRet E1 E2) = ≼LetRet (≼-refl E1) (≼-refl E2)
≼-refl (SendTy κ E1 ρ E2) = ≼SendTy κ (≼-refl E1) ρ (≼-refl E2)
≼-refl (RecvTy κ ℓ E) = ≼RecvTy κ ℓ (≼-refl E)
≼-refl (AmI ℓ E1 E2) = ≼AmI ℓ (≼-refl E1) (≼-refl E2)
≼-refl (AmIIn ρ E1 E2) = ≼AmIIn ρ (≼-refl E1) (≼-refl E2)

≼?-refl ？ = ？≼？
≼?-refl (′ E) = ′≼′ (≼-refl E)

≼-trans : ∀{E1 E2 E3} → E1 ≼ E2 → E2 ≼ E3 → E1 ≼ E3
≼?-trans : ∀{E1 E2 E3} → E1 ≼? E2 → E2 ≼? E3 → E1 ≼? E3

≼-trans (≼var x) (≼var .x) = ≼var x
≼-trans ≼Unit ≼Unit = ≼Unit 
≼-trans (≼Ret e) (≼Ret .e) = ≼Ret e
≼-trans (≼Seq E1≼E2 E1≼E3) (≼Seq E2≼E3 E2≼E4) =
  ≼Seq (≼-trans E1≼E2 E2≼E3) (≼-trans E1≼E3 E2≼E4)
≼-trans (≼Abs E) (≼Abs .E) = ≼Abs E
≼-trans (≼Rec E) (≼Rec .E) = ≼Rec E
≼-trans (≼App E1≼E2 E1≼E3) (≼App E2≼E3 E2≼E4) =
  ≼App (≼-trans E1≼E2 E2≼E3) (≼-trans E1≼E3 E2≼E4)
≼-trans (≼Send E1≼E2 ℓ) (≼Send E2≼E3 .ℓ) =
  ≼Send (≼-trans E1≼E2 E2≼E3) ℓ
≼-trans (≼Recv ℓ) (≼Recv .ℓ) = ≼Recv ℓ
≼-trans (≼Choose d ℓ E1≼E2) (≼Choose .d .ℓ E2≼E3) =
  ≼Choose d ℓ (≼-trans E1≼E2 E2≼E3)
≼-trans (≼Allow ℓ p1 q1) (≼Allow .ℓ p2 q2) =
  ≼Allow ℓ (≼?-trans p1 p2) (≼?-trans q1 q2)
≼-trans (≼ITE p1 q1 r1) (≼ITE p2 q2 r2) =
  ≼ITE (≼-trans p1 p2) (≼-trans q1 q2) (≼-trans r1 r2)
≼-trans (≼TAbs E) (≼TAbs .E) = ≼TAbs E
≼-trans (≼TApp E1≼E2 t) (≼TApp E2≼E3 .t) =
  ≼TApp (≼-trans E1≼E2 E2≼E3) t
≼-trans (≼LetRet E1≼E2 E1≼E3) (≼LetRet E2≼E3 E2≼E4) =
  ≼LetRet (≼-trans E1≼E2 E2≼E3) (≼-trans E1≼E3 E2≼E4)
≼-trans (≼SendTy κ p1 ρ q1) (≼SendTy .κ p2 .ρ q2) =
  ≼SendTy κ (≼-trans p1 p2) ρ (≼-trans q1 q2)
≼-trans (≼RecvTy κ ℓ E1≼E2) (≼RecvTy .κ .ℓ E2≼E3) =
  ≼RecvTy κ ℓ (≼-trans E1≼E2 E2≼E3)
≼-trans (≼AmI ℓ E1≼E2 E1≼E3) (≼AmI .ℓ E2≼E3 E2≼E4) =
  ≼AmI ℓ (≼-trans E1≼E2 E2≼E3) (≼-trans E1≼E3 E2≼E4)
≼-trans (≼AmIIn ρ E1≼E2 E1≼E3) (≼AmIIn .ρ E2≼E3 E2≼E4) =
  ≼AmIIn ρ (≼-trans E1≼E2 E2≼E3) (≼-trans E1≼E3 E2≼E4)

≼?-trans ？≼？ ？≼？ = ？≼？ 
≼?-trans ？≼？ (?≼′ E) = ?≼′ E
≼?-trans (?≼′ E1) (′≼′ {E2 = E2} E1≼E2) = ?≼′ E2
≼?-trans (′≼′ E1≼E2) (′≼′ E2≼E3) = ′≼′ (≼-trans E1≼E2 E2≼E3)

≼-irrefl : ∀{E1 E2} → E1 ≼ E2 → E2 ≼ E1 → E1 ≡ E2
≼?-irrefl : ∀{E1 E2} → E1 ≼? E2 → E2 ≼? E1 → E1 ≡ E2

≼-irrefl (≼var x) (≼var .x) = refl
≼-irrefl ≼Unit ≼Unit = refl
≼-irrefl (≼Ret e) (≼Ret .e) = refl
≼-irrefl (≼Seq p1 q1) (≼Seq p2 q2) = cong₂ Seq (≼-irrefl p1 p2) (≼-irrefl q1 q2)
≼-irrefl (≼Abs E) (≼Abs .E) = refl
≼-irrefl (≼Rec E) (≼Rec .E) = refl
≼-irrefl (≼App p1 q1) (≼App p2 q2) = cong₂ CtrlApp (≼-irrefl p1 p2) (≼-irrefl q1 q2)
≼-irrefl (≼Send p1 ℓ) (≼Send p2 .ℓ) = cong₂ SendTo (≼-irrefl p1 p2) refl
≼-irrefl (≼Recv ℓ) (≼Recv .ℓ) = refl
≼-irrefl (≼Choose d ℓ p1) (≼Choose .d .ℓ p2) = cong (Choose d ℓ) (≼-irrefl p1 p2)
≼-irrefl (≼Allow ℓ p1 q1) (≼Allow .ℓ p2 q2) = cong₂ (Allow ℓ) (≼?-irrefl p1 p2) (≼?-irrefl q1 q2)
≼-irrefl (≼ITE p1 q1 r1) (≼ITE p2 q2 r2) = cong₃ CtrlITE (≼-irrefl p1 p2) (≼-irrefl q1 q2) (≼-irrefl r1 r2)
≼-irrefl (≼TAbs E) (≼TAbs .E) = refl
≼-irrefl (≼TApp p1 t) (≼TApp p2 .t) = cong₂ CtrlTApp (≼-irrefl p1 p2) refl
≼-irrefl (≼LetRet p1 q1) (≼LetRet p2 q2) = cong₂ LetRet (≼-irrefl p1 p2) (≼-irrefl q1 q2)
≼-irrefl (≼SendTy κ p1 ρ q1) (≼SendTy .κ p2 .ρ q2) = cong₃ (SendTy κ) (≼-irrefl p1 p2) refl (≼-irrefl q1 q2)
≼-irrefl (≼RecvTy κ ℓ p1) (≼RecvTy .κ .ℓ p2) = cong (RecvTy κ ℓ) (≼-irrefl p1 p2)
≼-irrefl (≼AmI ℓ p1 q1) (≼AmI .ℓ p2 q2) = cong₂ (AmI ℓ) (≼-irrefl p1 p2) (≼-irrefl q1 q2)
≼-irrefl (≼AmIIn ρ p1 q1) (≼AmIIn .ρ p2 q2) = cong₂ (AmIIn ρ) (≼-irrefl p1 p2) (≼-irrefl q1 q2)

≼?-irrefl ？≼？ ？≼？ = refl
≼?-irrefl (′≼′ p) (′≼′ q) = cong ′_ $ ≼-irrefl p q

≼-localSub
  : ∀{E1 E2} (σ : ℕ → Tmₑ) →
    E1 ≼ E2 →
    localSub σ E1 ≼ localSub σ E2
≼?-localSub
  : ∀{E1 E2} (σ : ℕ → Tmₑ) →
    E1 ≼? E2 →
    localSub? σ E1 ≼? localSub? σ E2

≼-localSub σ (≼var x) = ≼var x
≼-localSub σ ≼Unit = ≼Unit
≼-localSub σ (≼Ret e) = ≼Ret (sub (𝕃 .⅀ₑ) σ e)
≼-localSub σ (≼Seq p q) = ≼Seq (≼-localSub σ p) (≼-localSub σ q)
≼-localSub σ (≼Abs E) = ≼Abs (localSub σ E)
≼-localSub σ (≼Rec E) = ≼Rec (localSub σ E)
≼-localSub σ (≼App p q) = ≼App (≼-localSub σ p) (≼-localSub σ q)
≼-localSub σ (≼Send p ℓ) = ≼Send (≼-localSub σ p) ℓ
≼-localSub σ (≼Recv ℓ) = ≼Recv ℓ
≼-localSub σ (≼Choose d ℓ p) = ≼Choose d ℓ (≼-localSub σ p)
≼-localSub σ (≼Allow ℓ p q) = ≼Allow ℓ (≼?-localSub σ p) (≼?-localSub σ q)
≼-localSub σ (≼ITE p q r) =
  ≼ITE (≼-localSub σ p) (≼-localSub σ q) (≼-localSub σ r)
≼-localSub σ (≼TAbs E) = ≼TAbs (localSub σ E)
≼-localSub σ (≼TApp p t) = ≼TApp (≼-localSub σ p) t
≼-localSub σ (≼LetRet p q) =
  ≼LetRet (≼-localSub σ p) (≼-localSub (KeepSub (𝕃 .⅀ₑ) σ) q)
≼-localSub σ (≼SendTy κ p ρ q) =
  ≼SendTy κ (≼-localSub σ p) ρ (≼-localSub σ q)
≼-localSub σ (≼RecvTy κ ℓ p) =
  ≼RecvTy κ ℓ (≼-localSub σ p)
≼-localSub σ (≼AmI ℓ p q) =
  ≼AmI ℓ (≼-localSub σ p) (≼-localSub σ q)
≼-localSub σ (≼AmIIn ρ p q) =
  ≼AmIIn ρ (≼-localSub σ p) (≼-localSub σ q)

≼?-localSub σ ？≼？ = ？≼？
≼?-localSub σ (?≼′ E) = ?≼′ (localSub σ E)
≼?-localSub σ (′≼′ p) = ′≼′ (≼-localSub σ p)

≼-tySubCtrl
  : ∀{E1 E2} (σ : ℕ → CTy) →
    E1 ≼ E2 →
    tySubCtrl σ E1 ≼ tySubCtrl σ E2
≼?-tySubCtrl
  : ∀{E1 E2} (σ : ℕ → CTy) →
    E1 ≼? E2 →
    tySubCtrl? σ E1 ≼? tySubCtrl? σ E2

≼-tySubCtrl σ (≼var x) = ≼var x
≼-tySubCtrl σ ≼Unit = ≼Unit
≼-tySubCtrl σ (≼Ret e) = ≼Ret e
≼-tySubCtrl σ (≼Seq p q) =
  ≼Seq (≼-tySubCtrl σ p) (≼-tySubCtrl σ q)
≼-tySubCtrl σ (≼Abs E) = ≼Abs (tySubCtrl σ E)
≼-tySubCtrl σ (≼Rec E) = ≼Rec (tySubCtrl σ E)
≼-tySubCtrl σ (≼App p q) = ≼App (≼-tySubCtrl σ p) (≼-tySubCtrl σ q)
≼-tySubCtrl σ (≼Send p ℓ) = ≼Send (≼-tySubCtrl σ p) (subTy C⅀ₖ σ ℓ)
≼-tySubCtrl σ (≼Recv ℓ) = ≼Recv (subTy C⅀ₖ σ ℓ)
≼-tySubCtrl σ (≼Choose d ℓ p) = ≼Choose d (subTy C⅀ₖ σ ℓ) (≼-tySubCtrl σ p)
≼-tySubCtrl σ (≼Allow ℓ p q) = ≼Allow (subTy C⅀ₖ σ ℓ) (≼?-tySubCtrl σ p) (≼?-tySubCtrl σ q)
≼-tySubCtrl σ (≼ITE p q r) = ≼ITE (≼-tySubCtrl σ p) (≼-tySubCtrl σ q) (≼-tySubCtrl σ r)
≼-tySubCtrl σ (≼TAbs E) = ≼TAbs (tySubCtrl (TyKeepSub C⅀ₖ σ) E) -- ≼TAbs (tySubCtrl σ E)
≼-tySubCtrl σ (≼TApp p t) = ≼TApp (≼-tySubCtrl σ p) (subTy C⅀ₖ σ t)
≼-tySubCtrl σ (≼LetRet p q) = ≼LetRet (≼-tySubCtrl σ p) (≼-tySubCtrl σ q)
≼-tySubCtrl σ (≼SendTy κ p ρ q) = ≼SendTy κ (≼-tySubCtrl σ p) (subTy C⅀ₖ σ ρ) (≼-tySubCtrl σ q)
≼-tySubCtrl σ (≼RecvTy κ ℓ p) = ≼RecvTy κ (subTy C⅀ₖ σ ℓ) (≼-tySubCtrl (TyKeepSub C⅀ₖ σ) p)
≼-tySubCtrl σ (≼AmI ℓ p q) = ≼AmI (subTy C⅀ₖ σ ℓ) (≼-tySubCtrl σ p) (≼-tySubCtrl σ q)
≼-tySubCtrl σ (≼AmIIn ρ p q) = ≼AmIIn (subTy C⅀ₖ σ ρ) (≼-tySubCtrl σ p) (≼-tySubCtrl σ q)

≼?-tySubCtrl σ ？≼？ = ？≼？
≼?-tySubCtrl σ (?≼′ E) = ?≼′ (tySubCtrl σ E)
≼?-tySubCtrl σ (′≼′ E1≼E2) = ′≼′ (≼-tySubCtrl σ E1≼E2)

-- Control values are determined
V≼ : ∀{V E} → CtrlVal V → V ≼ E → E ≡ V
V≼ ValUnit ≼Unit = refl
V≼ (ValRet v-Val) (≼Ret _) = refl
V≼ (ValAbs E) (≼Abs .E) = refl
V≼ (ValTAbs E) (≼TAbs .E) = refl

≼V : ∀{V E} → CtrlVal V → E ≼ V → E ≡ V
≼V ValUnit ≼Unit = refl
≼V (ValRet v-Val) (≼Ret _) = refl
≼V (ValAbs E) (≼Abs .E) = refl
≼V (ValTAbs E) (≼TAbs .E) = refl

pure : ∀{a} {A : Set a} → A → Maybe A
pure = just

_<*>_ : ∀{a b} {A : Set a} {B : Set b} →
        Maybe (A → B) →
        Maybe A →
        Maybe B
just f <*> just x = just (f x)
just f <*> nothing = nothing
nothing <*> x = nothing

{-
Control expression merging
-}
_⊔_ : Ctrl → Ctrl → Maybe Ctrl
_⊔?_ : ?Ctrl → ?Ctrl → Maybe ?Ctrl

var x1 ⊔ var x2 with ≡-dec-ℕ x1 x2
... | yes _ = just (var x1)
... | no  _ = nothing
Unit ⊔ Unit = just Unit
Ret e1 ⊔ Ret e2 with ≡-dec-Tmₑ 𝕃 e1 e2
... | yes _ = just (Ret e1)
... | no  _ = nothing
Seq E11 E21 ⊔ Seq E12 E22 = ⦇ Seq (E11 ⊔ E12) (E21 ⊔ E22) ⦈
CtrlLam E1 ⊔ CtrlLam E2 = ⦇ CtrlLam (E1 ⊔ E2) ⦈ 
CtrlFix E1 ⊔ CtrlFix E2 = ⦇ CtrlFix (E1 ⊔ E2) ⦈
CtrlApp E11 E21 ⊔ CtrlApp E12 E22 = ⦇ CtrlApp (E11 ⊔ E12) (E21 ⊔ E22) ⦈
SendTo E1 ℓ1 ⊔ SendTo E2 ℓ2 with ≡-dec-CTy ℓ1 ℓ2
... | yes p = ⦇ SendTo (E1 ⊔ E2) (just ℓ1) ⦈
... | no ¬p = nothing
Recv ℓ1 ⊔ Recv ℓ2 with ≡-dec-CTy ℓ1 ℓ2
... | yes p = just (Recv ℓ1)
... | no ¬p = nothing
Choose d1 ℓ1 E1 ⊔ Choose d2 ℓ2 E2
  with ≡-dec-Bool d1 d2 | ≡-dec-CTy ℓ1 ℓ2
... | yes p | yes q = ⦇ Choose (just d1) (just ℓ1) (E1 ⊔ E2) ⦈
... | yes p | no ¬q = nothing
... | no ¬p | _     = nothing
Allow ℓ1 ?E11 ?E21 ⊔ Allow ℓ2 ?E12 ?E22 with ≡-dec-CTy ℓ1 ℓ2
... | yes p = ⦇ Allow (just ℓ1) (?E11 ⊔? ?E12) (?E21 ⊔? ?E22) ⦈
... | no ¬p = nothing
CtrlITE E11 E21 E31 ⊔ CtrlITE E12 E22 E32 =
  ⦇ CtrlITE (E11 ⊔ E12) (E21 ⊔ E22) (E31 ⊔ E32) ⦈
CtrlTAbs E1 ⊔ CtrlTAbs E2 = ⦇ CtrlTAbs (E1 ⊔ E2) ⦈
CtrlTApp E1 t1 ⊔ CtrlTApp E2 t2 with ≡-dec-CTy t1 t2
... | yes p = ⦇ CtrlTApp (E1 ⊔ E2) (just t1) ⦈
... | no ¬p = nothing
LetRet E11 E21 ⊔ LetRet E12 E22 = ⦇ LetRet (E11 ⊔ E12) (E21 ⊔ E22) ⦈
SendTy κ1 E11 ρ1 E21 ⊔ SendTy κ2 E12 ρ2 E22
  with ≡-dec-ChorKnd κ1 κ2 | ≡-dec-CTy ρ1 ρ2
... | yes p | yes q = ⦇ SendTy (just κ1) (E11 ⊔ E12) (just ρ1) (E21 ⊔ E22) ⦈
... | yes p | no ¬q = nothing
... | no ¬p | _     = nothing
RecvTy κ1 ℓ1 E1 ⊔ RecvTy κ2 ℓ2 E2 with ≡-dec-ChorKnd κ1 κ2 | ≡-dec-CTy ℓ1 ℓ2
... | yes p | yes q = ⦇ RecvTy (just κ1) (just ℓ1) (E1 ⊔ E2) ⦈
... | yes p | no ¬q = nothing
... | no ¬p | _     = nothing
AmI ℓ1 E11 E21 ⊔ AmI ℓ2 E12 E22 with ≡-dec-CTy ℓ1 ℓ2
... | yes p = ⦇ AmI (just ℓ1) (E11 ⊔ E12) (E21 ⊔ E22) ⦈
... | no ¬p = nothing
AmIIn ρ1 E11 E21 ⊔ AmIIn ρ2 E12 E22 with ≡-dec-CTy ρ1 ρ2
... | yes p = ⦇ AmIIn (just ρ1) (E11 ⊔ E12) (E21 ⊔ E22) ⦈
... | no ¬p = nothing
_ ⊔ _ = nothing

？ ⊔? ?E2 = just ?E2 
(′ E1) ⊔? ？ = just (′ E1) 
(′ E1) ⊔? (′ E2) = ⦇ ′ (E1 ⊔ E2) ⦈

⊔-idempotent : (E : Ctrl) → E ⊔ E ≡ just E
⊔?-idempotent : (?E : ?Ctrl) → ?E ⊔? ?E ≡ just ?E

⊔-idempotent (var x) with ≡-dec-ℕ x x
... | yes p = refl
... | no ¬p = ⊥-elim $ ¬p refl
⊔-idempotent Unit = refl
⊔-idempotent (Ret e) with ≡-dec-Tmₑ 𝕃 e e
... | yes p = refl
... | no ¬p = ⊥-elim $ ¬p refl
⊔-idempotent (Seq E1 E2) =
  cong₂ (λ x y → ⦇ Seq x y ⦈) 
    (⊔-idempotent E1)
    (⊔-idempotent E2)
⊔-idempotent (CtrlLam E) =
  cong (λ x → ⦇ CtrlLam x ⦈) (⊔-idempotent E)
⊔-idempotent (CtrlFix E) =
  cong (λ x → ⦇ CtrlFix x ⦈) (⊔-idempotent E)
⊔-idempotent (CtrlApp E1 E2) =
  cong₂ (λ x y → ⦇ CtrlApp x y ⦈) 
    (⊔-idempotent E1)
    (⊔-idempotent E2)
⊔-idempotent (SendTo E ℓ) with ≡-dec-CTy ℓ ℓ
... | yes p = cong (λ x → ⦇ SendTo x (just ℓ) ⦈) (⊔-idempotent E)
... | no ¬p = ⊥-elim $ ¬p refl
⊔-idempotent (Recv ℓ) with ≡-dec-CTy ℓ ℓ
... | yes p = refl
... | no ¬p = ⊥-elim $ ¬p refl
⊔-idempotent (Choose d ℓ E) with ≡-dec-Bool d d | ≡-dec-CTy ℓ ℓ
... | yes p | yes q =
  cong (λ x → ⦇ Choose (just d) (just ℓ) x ⦈) (⊔-idempotent E)
... | yes p | no ¬q = ⊥-elim $ ¬q refl
... | no ¬p | _ = ⊥-elim $ ¬p refl
⊔-idempotent (Allow ℓ ?E1 ?E2) with ≡-dec-CTy ℓ ℓ
... | yes p =
  cong₂ (λ x y → ⦇ Allow (just ℓ) x y ⦈)
    (⊔?-idempotent ?E1)
    (⊔?-idempotent ?E2)
... | no ¬p = ⊥-elim $ ¬p refl
⊔-idempotent (CtrlITE E E1 E2) =
  cong₃ (λ x y z → ⦇ CtrlITE x y z ⦈)
    (⊔-idempotent E)
    (⊔-idempotent E1)
    (⊔-idempotent E2)
⊔-idempotent (CtrlTAbs E) =
  cong (λ x → ⦇ CtrlTAbs x ⦈) (⊔-idempotent E)
⊔-idempotent (CtrlTApp E t) with ≡-dec-CTy t t
... | yes p =
  cong (λ x → ⦇ CtrlTApp x (just t) ⦈) (⊔-idempotent E)
... | no ¬p = ⊥-elim $ ¬p refl
⊔-idempotent (LetRet E1 E2) =
  cong₂ (λ x y → ⦇ LetRet x y ⦈)
    (⊔-idempotent E1)
    (⊔-idempotent E2)
⊔-idempotent (SendTy κ E1 ρ E2) with ≡-dec-ChorKnd κ κ | ≡-dec-CTy ρ ρ
... | yes p | yes q =
  cong₂ (λ x y → ⦇ SendTy (just κ) x (just ρ) y ⦈)
    (⊔-idempotent E1)  
    (⊔-idempotent E2)
... | yes p | no ¬q = ⊥-elim $ ¬q refl
... | no ¬p | _ = ⊥-elim $ ¬p refl
⊔-idempotent (RecvTy κ ℓ E) with ≡-dec-ChorKnd κ κ | ≡-dec-CTy ℓ ℓ
... | yes p | yes q =
  cong (λ x → ⦇ RecvTy (just κ) (just ℓ) x ⦈) (⊔-idempotent E)
... | yes p | no ¬q = ⊥-elim $ ¬q refl
... | no ¬p | _ = ⊥-elim $ ¬p refl
⊔-idempotent (AmI ℓ E1 E2) with ≡-dec-CTy ℓ ℓ
... | yes p =
  cong₂ (λ x y → ⦇ AmI (just ℓ) x y ⦈)
    (⊔-idempotent E1)
    (⊔-idempotent E2)
... | no ¬p = ⊥-elim $ ¬p refl
⊔-idempotent (AmIIn ρ E1 E2) with ≡-dec-CTy ρ ρ
... | yes p =
  cong₂ (λ x y → ⦇ AmIIn (just ρ) x y ⦈)
    (⊔-idempotent E1)
    (⊔-idempotent E2)
... | no ¬p = ⊥-elim $ ¬p refl

⊔?-idempotent ？ = refl
⊔?-idempotent (′ E) = cong (λ x → ⦇ ′ x ⦈) (⊔-idempotent E)

-- Whether a type variable occurs freely in a control expression
notFreeTyInCtrl : ℕ → Ctrl → Set
notFreeTyIn?Ctrl : ℕ → ?Ctrl → Set

notFreeTyInCtrl x (var y) = ⊤
notFreeTyInCtrl x Unit = ⊤
notFreeTyInCtrl x (Ret e) = notFreeTyInTm (𝕃 .⅀ₑ) x e
notFreeTyInCtrl x (Seq E1 E2) =
  notFreeTyInCtrl x E1 × notFreeTyInCtrl x E2
notFreeTyInCtrl x (CtrlLam E) =
  notFreeTyInCtrl x E
notFreeTyInCtrl x (CtrlFix E) =
  notFreeTyInCtrl x E
notFreeTyInCtrl x (CtrlApp E1 E2) =
  notFreeTyInCtrl x E1 × notFreeTyInCtrl x E2
notFreeTyInCtrl x (SendTo E ℓ) =
  notFreeTyInCtrl x E × notFreeInTy C⅀ₖ x ℓ
notFreeTyInCtrl x (Recv ℓ) = notFreeInTy C⅀ₖ x ℓ
notFreeTyInCtrl x (Choose d ℓ E) =
  notFreeInTy C⅀ₖ x ℓ × notFreeTyInCtrl x E
notFreeTyInCtrl x (Allow ℓ ?E1 ?E2) =
    notFreeInTy C⅀ₖ x ℓ ×
    notFreeTyIn?Ctrl x ?E1 ×
    notFreeTyIn?Ctrl x ?E2
notFreeTyInCtrl x (CtrlITE E E1 E2) =
  notFreeTyInCtrl x E ×
  notFreeTyInCtrl x E1 ×
  notFreeTyInCtrl x E2
notFreeTyInCtrl x (CtrlTAbs E) =
  notFreeTyInCtrl (suc x) E
notFreeTyInCtrl x (CtrlTApp E t) =
  notFreeTyInCtrl x E ×
  notFreeInTy C⅀ₖ x t
notFreeTyInCtrl x (LetRet E1 E2) =
  notFreeTyInCtrl x E1 ×
  notFreeTyInCtrl x E2
notFreeTyInCtrl x (SendTy κ E1 ρ E2) =
  notFreeTyInCtrl x E1 ×
  notFreeInTy C⅀ₖ x ρ ×
  notFreeTyInCtrl (suc x) E2
notFreeTyInCtrl x (RecvTy κ ℓ E) =
  notFreeInTy C⅀ₖ x ℓ ×
  notFreeTyInCtrl (suc x) E
notFreeTyInCtrl x (AmI ℓ E1 E2) =
  notFreeInTy C⅀ₖ x ℓ ×
  notFreeTyInCtrl x E1 ×
  notFreeTyInCtrl x E2
notFreeTyInCtrl x (AmIIn ρ E1 E2) =
  notFreeInTy C⅀ₖ x ρ ×
  notFreeTyInCtrl x E1 ×
  notFreeTyInCtrl x E2

notFreeTyIn?Ctrl x ？ = ⊤
notFreeTyIn?Ctrl x (′ E) = notFreeTyInCtrl x E

infixr 2 _?×_
_?×_ : ∀{a b} {A : Set a} {B : Set b} →
       Dec A → Dec B → Dec (A × B)
_?×_ (yes x) (yes y) = yes (x , y)
_?×_ (yes x) (no ¬y) = no λ{ (_ , y) → ¬y y }
_?×_ (no ¬x) _       = no λ{ (x , _) → ¬x x }

?notFreeTyInCtrl : (x : ℕ) (E : Ctrl) → Dec (notFreeTyInCtrl x E)
?notFreeTyIn?Ctrl : (x : ℕ) (E : ?Ctrl) → Dec (notFreeTyIn?Ctrl x E)

?notFreeTyInCtrl x (var y) = yes tt
?notFreeTyInCtrl x Unit = yes tt
?notFreeTyInCtrl x (Ret e) = ?notFreeTyInTm (𝕃 .⅀ₑ) x e
?notFreeTyInCtrl x (Seq E1 E2) =
  ?notFreeTyInCtrl x E1 ?×
  ?notFreeTyInCtrl x E2
?notFreeTyInCtrl x (CtrlLam E) = ?notFreeTyInCtrl x E
?notFreeTyInCtrl x (CtrlFix E) = ?notFreeTyInCtrl x E
?notFreeTyInCtrl x (CtrlApp E1 E2) =
  ?notFreeTyInCtrl x E1 ?×
  ?notFreeTyInCtrl x E2
?notFreeTyInCtrl x (SendTo E ℓ) =
  ?notFreeTyInCtrl x E ?×
  ?notFreeInTy C⅀ₖ x ℓ
?notFreeTyInCtrl x (Recv ℓ) = ?notFreeInTy C⅀ₖ x ℓ
?notFreeTyInCtrl x (Choose d ℓ E) =
  ?notFreeInTy C⅀ₖ x ℓ ?×
  ?notFreeTyInCtrl x E
?notFreeTyInCtrl x (Allow ℓ ?E1 ?E2) =
  ?notFreeInTy C⅀ₖ x ℓ ?×
  ?notFreeTyIn?Ctrl x ?E1 ?×
  ?notFreeTyIn?Ctrl x ?E2
?notFreeTyInCtrl x (CtrlITE E E1 E2) =
  ?notFreeTyInCtrl x E ?×
  ?notFreeTyInCtrl x E1 ?×
  ?notFreeTyInCtrl x E2
?notFreeTyInCtrl x (CtrlTAbs E) =
  ?notFreeTyInCtrl (suc x) E
?notFreeTyInCtrl x (CtrlTApp E t) =
  ?notFreeTyInCtrl x E ?×
  ?notFreeInTy C⅀ₖ x t
?notFreeTyInCtrl x (LetRet E1 E2) =
  ?notFreeTyInCtrl x E1 ?×
  ?notFreeTyInCtrl x E2
?notFreeTyInCtrl x (SendTy κ E1 ρ E2) =
  ?notFreeTyInCtrl x E1 ?×
  ?notFreeInTy C⅀ₖ x ρ ?×
  ?notFreeTyInCtrl (suc x) E2
?notFreeTyInCtrl x (RecvTy κ ℓ E) =
  ?notFreeInTy C⅀ₖ x ℓ ?×
  ?notFreeTyInCtrl (suc x) E
?notFreeTyInCtrl x (AmI ℓ E1 E2) =
  ?notFreeInTy C⅀ₖ x ℓ ?×
  ?notFreeTyInCtrl x E1 ?×
  ?notFreeTyInCtrl x E2
?notFreeTyInCtrl x (AmIIn ρ E1 E2) =
  ?notFreeInTy C⅀ₖ x ρ ?×
  ?notFreeTyInCtrl x E1 ?×
  ?notFreeTyInCtrl x E2

?notFreeTyIn?Ctrl x ？ = yes tt
?notFreeTyIn?Ctrl x (′ E) = ?notFreeTyInCtrl x E