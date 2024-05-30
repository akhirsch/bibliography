{-# OPTIONS --safe #-}

open import Level hiding (zero; suc)
open import Data.Empty
open import Data.Unit
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.List hiding (map)
open import Data.Fin
open import Data.Maybe
open import Data.Maybe.Properties
open import Data.Product hiding (map)
open import Relation.Nullary
open import Relation.Unary hiding (_∈_; _∉_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function

module Common where

_∈_ : ∀{a} {A : Set a} → A → List A → Set a
a ∈ xs = Σ[ i ∈ Fin (length xs) ] lookup xs i ≡ a

_∉_ : ∀{a} {A : Set a} → A → List A → Set a
a ∉ xs = ¬ (a ∈ xs)

module DecInList {a} {A : Set a} (≡-dec-A : DecidableEquality A) where
  _?∈_ : (a : A) (xs : List A) → Dec (a ∈ xs)
  a ?∈ [] = no λ{ (() , _) }
  a ?∈ (x ∷ xs) with ≡-dec-A x a | a ?∈ xs
  ... | yes refl | _            = yes (zero , refl)
  ... | no  ¬p   | yes (i , eq) = yes (suc i , eq)
  ... | no  ¬p   | no ¬q        = no λ{ (zero , eq) → ¬p eq
                                      ; (suc i , eq) → ¬q (i , eq) }

-- Transporting across equal types
transport : ∀{a} {A B : Set a} →
            A ≡ B → A → B
transport refl x = x

-- Synonym for transitivity
infixr 30 _∙_
_∙_ : ∀{a} {A : Set a} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
p ∙ q = trans p q

-- Extensional function equality
module FunExt {a b} {A : Set a} {B : A → Set b} where
  infix 4 _≈_
  _≈_ : (f g : (x : A) → B x) → Set (a ⊔ b)
  f ≈ g = ∀ x → f x ≡ g x

  ≈-refl : Reflexive _≈_
  ≈-refl x = refl

  ≈-sym : Symmetric _≈_
  ≈-sym p x = sym (p x)

  ≈-trans : Transitive _≈_
  ≈-trans p q x = trans (p x) (q x)

  ≈-isEquiv : IsEquivalence _≈_
  IsEquivalence.refl ≈-isEquiv = ≈-refl
  IsEquivalence.sym ≈-isEquiv = ≈-sym
  IsEquivalence.trans ≈-isEquiv = ≈-trans

  ≈-Setoid : Setoid (a ⊔ b) (a ⊔ b)
  Setoid.Carrier ≈-Setoid = (x : A) → B x
  Setoid._≈_ ≈-Setoid = _≈_
  Setoid.isEquivalence ≈-Setoid = ≈-isEquiv
  
open FunExt public

≈-Setoid′ : ∀{a b} (A : Set a) (B : Set b) → Setoid (a ⊔ b) (a ⊔ b)
≈-Setoid′ A B = ≈-Setoid {A = A} {B = λ _ → B}

-- Two-argument extensional function equality
module FunExt₂ {a b c} {A : Set a} {B : A → Set b} {C : (x : A) (y : B x) → Set c} where
  infix 4 _≈₂_
  _≈₂_ : (f g : (x : A) (y : B x) → C x y) → Set (a ⊔ b ⊔ c)
  f ≈₂ g = ∀ x y → f x y ≡ g x y

  ≈₂-refl : Reflexive _≈₂_
  ≈₂-refl x y = refl

  ≈₂-sym : Symmetric _≈₂_
  ≈₂-sym p x y = sym (p x y)

  ≈₂-trans : Transitive _≈₂_
  ≈₂-trans p q x y = trans (p x y) (q x y)

  ≈₂-isEquiv : IsEquivalence _≈₂_
  IsEquivalence.refl ≈₂-isEquiv = ≈₂-refl
  IsEquivalence.sym ≈₂-isEquiv = ≈₂-sym
  IsEquivalence.trans ≈₂-isEquiv = ≈₂-trans

  ≈₂-Setoid : Setoid (a ⊔ b ⊔ c) (a ⊔ b ⊔ c)
  Setoid.Carrier ≈₂-Setoid = (x : A) (y : B x) → C x y
  Setoid._≈_ ≈₂-Setoid = _≈₂_
  Setoid.isEquivalence ≈₂-Setoid = ≈₂-isEquiv

open FunExt₂ public

≈₂-Setoid′ : ∀{a b c} (A : Set a) (B : Set b) (C : Set c) → Setoid (a ⊔ b ⊔ c) (a ⊔ b ⊔ c)
≈₂-Setoid′ A B C = ≈₂-Setoid {A = A} {B = λ _ → B} {C = λ _ _ → C}

-- Composition respects extensional equality
∘Ext : ∀{a b c} {A : Set a} {B : Set b} {C : Set c}
       (ξ1 ξ1' : B → C) (ξ2 ξ2' : A → B) →
       ξ1 ≈ ξ1' → ξ2 ≈ ξ2' →
       ξ1 ∘ ξ2 ≈ ξ1' ∘ ξ2'
∘Ext ξ1 ξ1' ξ2 ξ2' ξ1≈ξ1' ξ2≈ξ2' x = ξ1≈ξ1' (ξ2 x) ∙ cong ξ1' (ξ2≈ξ2' x)

-- Identity renaming
idRen : ℕ → ℕ
idRen n = n

-- ↑ on variable renamings
↑ : (ξ : ℕ → ℕ) → ℕ → ℕ
↑ ξ zero = zero
↑ ξ (suc n) = suc (ξ n)

-- ↑ respects the identity
↑Id : ∀ n → ↑ idRen n ≡ idRen n
↑Id zero = refl
↑Id (suc n) = refl

-- ↑ respects extensional equality
↑Ext : ∀{ξ1 ξ2} → ξ1 ≈ ξ2 → ↑ ξ1 ≈ ↑ ξ2
↑Ext ξ1≈ξ2 zero = refl
↑Ext ξ1≈ξ2 (suc n) = cong suc (ξ1≈ξ2 n)

-- ↑ distributes over composition
↑Fuse : ∀ ξ1 ξ2 → ↑ (ξ1 ∘ ξ2) ≈ ↑ ξ1 ∘ ↑ ξ2
↑Fuse ξ1 ξ2 zero = refl
↑Fuse ξ1 ξ2 (suc n) = refl

-- ↑ preserves injectivity
↑Inj : ∀{ξ} → Injective _≡_ _≡_ ξ → Injective _≡_ _≡_ (↑ ξ)
↑Inj ξ-inj {x = zero} {zero} refl = refl
↑Inj ξ-inj {x = zero} {suc y} ()
↑Inj ξ-inj {x = suc x} {zero} ()
↑Inj ξ-inj {x = suc x} {suc y} sξx≡sξy = cong suc (ξ-inj (suc-injective sξx≡sξy))

{-
  Applying ↑ ξ after increasing all variables is
  identical to applying ξ and then increasing all variables
-}
↑∘suc : ∀ ξ → ↑ ξ ∘ suc ≈ suc ∘ ξ
↑∘suc ξ zero = refl
↑∘suc ξ (suc n) = refl

mapExt : ∀{a b} {A : Set a} {B : Set b} {f g : A → B} →
         f ≈ g → map f ≈ map g
mapExt f≈g (just x) = cong just (f≈g x)
mapExt f≈g nothing = refl

map∘ : ∀{a b c} {A : Set a} {B : Set b} {C : Set c}
       (f : B → C) (g : A → B) →
       map (f ∘ g) ≈ map f ∘ map g
map∘ f g (just x) = refl
map∘ f g nothing = refl

map≡just⇒just : ∀{a b} {A : Set a} {B : Set b}
                (f : A → B) (m : Maybe A) (y : B) →
                map f m ≡ just y →
                Σ[ x ∈ A ] (f x ≡ y)
map≡just⇒just f (just x) .(f x) refl = x , refl

-- Extended congruence methods as the standard library only goes up to cong₂
cong₃ : ∀{a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {a1 a2 : A} {b1 b2 : B} {c1 c2 : C} →
        a1 ≡ a2 → b1 ≡ b2 → c1 ≡ c2 →
        f a1 b1 c1 ≡ f a2 b2 c2
cong₃ f refl refl refl = refl

cong₄ : ∀{a b c d e} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e}
        (f : A → B → C → D → E) {a1 a2 : A} {b1 b2 : B} {c1 c2 : C} {d1 d2 : D} →
        a1 ≡ a2 → b1 ≡ b2 → c1 ≡ c2 → d1 ≡ d2 →
        f a1 b1 c1 d1 ≡ f a2 b2 c2 d2
cong₄ f refl refl refl refl = refl

cong₅ : ∀{a b c d e f} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e} {F : Set f}
        (α : A → B → C → D → E → F) {a1 a2 : A} {b1 b2 : B} {c1 c2 : C} {d1 d2 : D} {e1 e2 : E} →
        a1 ≡ a2 → b1 ≡ b2 → c1 ≡ c2 → d1 ≡ d2 → e1 ≡ e2 →
        α a1 b1 c1 d1 e1 ≡ α a2 b2 c2 d2 e2
cong₅ α refl refl refl refl refl = refl

 -- Instantiate topmost variable in a substitution
_▸_ : ∀{a} {A : Set a} →
      (σ : ℕ → A) → A → ℕ → A
(σ ▸ x) zero = x
(σ ▸ x) (suc n) = σ n

▸Ext : ∀{a} {A : Set a} {σ1 σ2 : ℕ → A} →
       σ1 ≈ σ2 → (x : A) → σ1 ▸ x ≈ σ2 ▸ x
▸Ext eq x zero = refl
▸Ext eq x (suc n) = eq n

-- Choose a different value for 0 or suc
ifZeroElse : ∀{a} {A : Set a} →
             A → (ℕ → A) → ℕ → A
ifZeroElse x f zero = x
ifZeroElse x f (suc n) = f n

-- Composing ifZeroElse with suc just chooses the suc case
ifZeroElse∘suc : ∀{a} {A : Set a}
                 (x : A) (f : ℕ → A) →
                 ifZeroElse x f ∘ suc ≈ f
ifZeroElse∘suc x f zero = refl
ifZeroElse∘suc x f (suc n) = refl
 