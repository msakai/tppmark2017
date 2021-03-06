------------------------------------------------------------------------
-- TPPmark2017 problem.
-- See <https://aigarashi.github.io/TPP2017/> for details.
--
-- Checked with Agda 2.5.3 and Agda standard library 0.14
--
-- Latest version is available at <https://github.com/msakai/tppmark2017>.
------------------------------------------------------------------------

module LCS where

import Level using (zero)
open import Data.Empty
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Function
open import Induction.Nat
open import Induction.WellFounded
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

infix 4 _⊑_ _⊰_

------------------------------------------------------------------------
-- Naïve implementation of LCS (longest common subsequence) problem without DP

longest : ∀ {ℓ} {A : Set ℓ} → List A → List A → List A
longest xs ys with length xs ≤? length ys
... | yes xs≤ys = ys
... | no  xs≰ys = xs

LCS : List ℕ → List ℕ → List ℕ
LCS [] _ = []
LCS (_ ∷ _) [] = []
LCS (x ∷ xs) (y ∷ ys) with x ≟ y
... | yes x≡y = x ∷ LCS xs ys
... | no x≢y  = longest (LCS (x ∷ xs) ys) (LCS xs (y ∷ ys))

------------------------------------------------------------------------
-- 'is-subsequence-of' relation and some of its properties

data _⊑_ {ℓ} {A : Set ℓ} : List A → List A → Set ℓ where
  empty : ∀ {xs} → [] ⊑ xs
  here  : ∀ {xs ys x} → xs ⊑ ys → (x ∷ xs) ⊑ (x ∷ ys)
  there : ∀ {xs ys y} → xs ⊑ ys → xs ⊑ (y ∷ ys)

tail-⊑ : ∀ {ℓ} {A : Set ℓ} {x : A} {xs} {ys} → x ∷ xs ⊑ ys → xs ⊑ ys
tail-⊑ (here xs⊑ys) = there xs⊑ys
tail-⊑ {_} {_} {_} {[]} (there [x]⊑ys) = empty
tail-⊑ {_} {_} {_} {x' ∷ xs} (there x∷x'∷xs⊑ys) = there (tail-⊑ x∷x'∷xs⊑ys)

tail-⊑-tail : ∀ {ℓ} {A : Set ℓ} {x : A} {xs} {ys} → x ∷ xs ⊑ x ∷ ys → xs ⊑ ys
tail-⊑-tail (here xs⊑ys) = xs⊑ys
tail-⊑-tail (there x∷xs⊑ys) = tail-⊑ x∷xs⊑ys

length-⊑ : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} → xs ⊑ ys → length xs ≤ length ys
length-⊑ empty = z≤n
length-⊑ (here xs⊑ys) = s≤s (length-⊑ xs⊑ys)
length-⊑ (there xs⊑y∷ys) = ≤-step (length-⊑ xs⊑y∷ys)

⊑-refl : ∀ {ℓ} {A : Set ℓ} {xs : List A} → xs ⊑ xs
⊑-refl {_} {_} {[]} = empty
⊑-refl {_} {_} {_ ∷ _} = here ⊑-refl

⊑-trans : ∀ {ℓ} {A : Set ℓ} {xs ys zs : List A} → xs ⊑ ys → ys ⊑ zs → xs ⊑ zs
⊑-trans empty ys⊑zs = empty
⊑-trans (there xs⊑ys) y∷ys⊑zs = ⊑-trans xs⊑ys (tail-⊑ y∷ys⊑zs)
⊑-trans (here xs⊑ys) (here    ys⊑zs) = here  (⊑-trans xs⊑ys ys⊑zs)
⊑-trans (here xs⊑ys) (there x∷ys⊑zs) = there (⊑-trans (here xs⊑ys) x∷ys⊑zs)

_is-common-subsequence-of_ : ∀ {ℓ} {A : Set ℓ} → List A → List A × List A → Set ℓ
_is-common-subsequence-of_ zs (xs , ys) = (zs ⊑ xs) × (zs ⊑ ys)

-- ---------------------------------------------------------------------------
-- Lemmas about the 'longest' function

longest-either : ∀ {ℓ₁} {A : Set ℓ₁} {ℓ₂} (P : List A → Set ℓ₂) {xs ys : List A} → P xs → P ys → P (longest xs ys)
longest-either P {xs} {ys} Pxs Pys with length xs ≤? length ys
... | yes xs≤ys = Pys
... | no  xs≰ys = Pxs

longest-left : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) → length xs ≤ length (longest xs ys)
longest-left xs ys with length xs ≤? length ys
... | yes xs≤ys = xs≤ys
... | no  xs≰ys = ≤-refl

longest-right : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) → length ys ≤ length (longest xs ys)
longest-right xs ys with length xs ≤? length ys
... | yes xs≤ys = ≤-refl
... | no  xs≰ys =
        begin
          length ys
        ≤⟨ n≤1+n (length ys) ⟩
          suc (length ys)
        ≤⟨ ≰⇒> xs≰ys ⟩
          length xs
        ∎
  where open ≤-Reasoning

-- ---------------------------------------------------------------------------

LCS-⊑-left : ∀ xs ys → LCS xs ys ⊑ xs
LCS-⊑-left [] _     = empty
LCS-⊑-left (_ ∷ _) [] = empty
LCS-⊑-left (x ∷ xs) (y ∷ ys) with x ≟ y
... | yes x≡y = here (LCS-⊑-left xs ys)
... | no  x≢y = longest-either (\zs → zs ⊑ x ∷ xs) (LCS-⊑-left (x ∷ xs) ys) (there (LCS-⊑-left xs (y ∷ ys)))

LCS-⊑-right : ∀ xs ys → LCS xs ys ⊑ ys
LCS-⊑-right [] _       = empty
LCS-⊑-right (_ ∷ _) [] = empty
LCS-⊑-right (x ∷ xs) (y  ∷ ys) with x ≟ y
LCS-⊑-right (x ∷ xs) (.x ∷ ys) | yes refl = here (LCS-⊑-right xs ys)
LCS-⊑-right (x ∷ xs) (y  ∷ ys) | no  x≢y  = longest-either (\zs → zs ⊑ y ∷ ys) (there (LCS-⊑-right (x ∷ xs) ys)) (LCS-⊑-right xs (y ∷ ys))

thereom-1 : ∀ xs ys → LCS xs ys is-common-subsequence-of (xs , ys)
thereom-1 xs ys = (LCS-⊑-left xs ys , LCS-⊑-right xs ys)

-- ---------------------------------------------------------------------------
-- To prove the 'theorem-2' we first prepare for well-founded induction on pair of lists.

sum-length : ∀ {A : Set} → List A × List A → ℕ
sum-length (xs , ys) = length xs + length ys

_⊰_ : ∀ {A : Set} → Rel (List A × List A) Level.zero
_⊰_ = _<_ on sum-length

⊰-well-founded : ∀ {A : Set} → Well-founded (_⊰_ {A})
⊰-well-founded = Inverse-image.well-founded sum-length <-well-founded

module _ {ℓ} {A} where
  open All (⊰-well-founded {A}) ℓ public
    renaming ( wfRec-builder to ⊰-rec-builder
             ; wfRec to ⊰-rec
             )

⊰-left : ∀ {A} (x : A) (xs ys : List A) → (xs , ys) ⊰ (x ∷ xs , ys)
⊰-left x xs ys = ≤-reflexive lem
  where
    open ≡-Reasoning
    lem =
      begin
        suc (length xs + length ys)
      ≡⟨ refl ⟩
        suc (length xs) + length ys
      ≡⟨ refl ⟩
        length (x ∷ xs) + length ys
      ∎

⊰-right : ∀ {A} (xs : List A) (y : A) (ys : List A) → (xs , ys) ⊰ (xs , y ∷ ys)
⊰-right xs y ys = ≤-reflexive (sym lem)
  where
    open ≡-Reasoning
    lem =
      begin
        length xs + length (y ∷ ys)
      ≡⟨ refl ⟩
        length xs + suc (length ys)
      ≡⟨ +-suc (length xs) (length ys) ⟩
        suc (length xs + length ys)
      ∎

⊰-both : ∀ {A} (x : A) (xs : List A) (y : A) (ys : List A) → (xs , ys) ⊰ (x ∷ xs , y ∷ ys)
⊰-both x xs y ys = <-trans lem1 lem2
  where
    lem1 : (xs , ys) ⊰ (x ∷ xs , ys)
    lem1 = ⊰-left x xs ys
    lem2 : (x ∷ xs , ys) ⊰ (x ∷ xs , y ∷ ys)
    lem2 = ⊰-right (x ∷ xs) y ys

-- ---------------------------------------------------------------------------

P : ∀ p → Set
P (xs , ys) = ∀ zs → zs is-common-subsequence-of (xs , ys) → length zs ≤ length (LCS xs ys)

step : ∀ p → (∀ q → q ⊰ p → P q) → P p
step ([]    , _ ) rec .[] (empty , _) = ≤-refl
step (_ ∷ _ , []) rec .[] (_ , empty) = ≤-refl
step (x ∷ xs ,  y ∷ ys) rec zs (zs⊑x∷xs , zs⊑y∷ys ) with x ≟ y
step (x ∷ xs ,  y ∷ ys) rec [] _ | yes _ = z≤n
step (x ∷ xs , .x ∷ ys) rec (.x ∷ zs) (here zs⊑xs  , x∷zs⊑x∷ys  ) | yes refl = s≤s (rec (xs , ys) (⊰-both x xs x ys) zs (zs⊑xs , tail-⊑-tail x∷zs⊑x∷ys))
step (x ∷ xs , .x ∷ ys) rec (.x ∷ zs) (x∷zs⊑x∷xs   , here  zs⊑ys) | yes refl = s≤s (rec (xs , ys) (⊰-both x xs x ys) zs (tail-⊑-tail x∷zs⊑x∷xs , zs⊑ys))
step (x ∷ xs , .x ∷ ys) rec zs        (there zs⊑xs , there zs⊑ys) | yes refl = ≤-step (rec (xs , ys) (⊰-both x xs x ys) zs (zs⊑xs , zs⊑ys))
step (x ∷ xs ,  y ∷ ys) rec [] _ | no _ = z≤n
step (x ∷ xs , .x ∷ ys) rec (.x ∷ zs) (here zs⊑xs , here zs⊑ys) | no x≢x = ⊥-elim (x≢x refl)
step (x ∷ xs ,  y ∷ ys) rec zs (zs⊑x∷xs , there zs⊑ys) | no x≢y =
  begin
    length zs
  ≤⟨ rec (x ∷ xs , ys) (⊰-right (x ∷ xs) y ys) zs (zs⊑x∷xs , zs⊑ys) ⟩
    length (LCS (x ∷ xs) ys)
  ≤⟨ longest-left (LCS (x ∷ xs) ys) (LCS xs (y ∷ ys)) ⟩
    length (longest (LCS (x ∷ xs) ys) (LCS xs (y ∷ ys)))
  ∎
  where open ≤-Reasoning
step (x ∷ xs ,  y ∷ ys) rec zs (there zs⊑xs , zs⊑y∷ys) | no x≢y =
  begin
    length zs
  ≤⟨ rec (xs , y ∷ ys) (⊰-left x xs (y ∷ ys)) zs (zs⊑xs , zs⊑y∷ys) ⟩
    length (LCS xs (y ∷ ys))
  ≤⟨ longest-right (LCS (x ∷ xs) ys) (LCS xs (y ∷ ys)) ⟩
    length (longest (LCS (x ∷ xs) ys) (LCS xs (y ∷ ys)))
  ∎
  where open ≤-Reasoning

theorem-2 : ∀ xs ys zs → zs is-common-subsequence-of (xs , ys) → length zs ≤ length (LCS xs ys)
theorem-2 xs ys = ⊰-rec P step (xs , ys)

-- ---------------------------------------------------------------------------
