------------------------------------------------------------------------
-- TPPmark2017 problem.
-- See <https://aigarashi.github.io/TPP2017/> for details.
--
-- Latest version is available at <https://github.com/msakai/tppmark2017>.
------------------------------------------------------------------------

module LCS where

import Level using (zero)
open import Data.Empty
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Product
open import Function
open import Induction.Nat
open import Induction.WellFounded
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open DecTotalOrder decTotalOrder using () renaming (refl to ≤-refl)

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
... | no ¬xs≤ys = Pxs

longest-left : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) → length xs ≤ length (longest xs ys)
longest-left xs ys with length xs ≤? length ys
... | yes xs≤ys = xs≤ys
... | no _      = ≤-refl

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
LCS-⊑-right (_ ∷ _) {[]} = empty
LCS-⊑-right (x ∷ xs) (y  ∷ ys) with x ≟ y
LCS-⊑-right (x ∷ xs) (.x ∷ ys) | yes refl = here (LCS-⊑-right xs ys)
LCS-⊑-right (x ∷ xs) (y  ∷ ys) | no  x≢y  = longest-either (\zs → zs ⊑ y ∷ ys) (there (LCS-⊑-right (x ∷ xs) ys)) (LCS-⊑-right xs (y ∷ ys))

thereom-1 : ∀ {p} → LCS (proj₁ p) (proj₂ p) is-common-subsequence-of p
thereom-1 {(xs , ys)} = (LCS-⊑-left xs ys , LCS-⊑-right xs ys)

-- ---------------------------------------------------------------------------
-- To prove the 'theorem-2' we first prepare for well-founded induction on pair of lists.

sum-length : ∀ {A : Set} → List A × List A → ℕ
sum-length (xs , ys) = length xs + length ys

_⊰_ : ∀ {A : Set} → Rel (List A × List A) Level.zero
_⊰_ = _<′_ on sum-length

⊰-well-founded : ∀ {A : Set} → Well-founded (_⊰_ {A})
⊰-well-founded = Inverse-image.well-founded sum-length <-well-founded

module _ {ℓ} {A} where
  open All (⊰-well-founded {A}) ℓ public
    renaming ( wfRec-builder to ⊰-rec-builder
             ; wfRec to ⊰-rec
             )

≤-reflexive : ∀ {n} {m} → n ≡ m → n ≤ m
≤-reflexive {n} {.n} refl = ≤-refl

⊰-left : ∀ {A} (x : A) (xs ys : List A) → (xs , ys) ⊰ (x ∷ xs , ys)
⊰-left x xs ys = ≤⇒≤′ (≤-reflexive lem)
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
⊰-right {_} xs y ys = ≤⇒≤′ (≤-reflexive (sym lem))
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
⊰-both x xs y ys = ≤⇒≤′ (<-trans (≤′⇒≤ lem1) (≤′⇒≤ lem2))
  where
    lem1 : (xs , ys) ⊰ (x ∷ xs , ys)
    lem1 = ⊰-left x xs ys
    lem2 : (x ∷ xs , ys) ⊰ (x ∷ xs , y ∷ ys)
    lem2 = ⊰-right (x ∷ xs) y ys

-- ---------------------------------------------------------------------------

step-P : ∀ p → Set
step-P p = ∀ zs → zs is-common-subsequence-of p → length zs ≤ length (LCS (proj₁ p) (proj₂ p))

step : ∀ p → (∀ q → q ⊰ p → step-P q) → step-P p
step ([] , ys) step-H .[] (empty , []⊑ys) = ≤-refl
{-
step ([] ,      []) step-H .[] (empty , empty) = ≤-refl
step ([] , (_ ∷ _)) step-H .[] (empty , []⊑ys) = ≤-refl
-}
step (_ ∷ _ , []) step-H .[] ([]⊑xs , empty) = ≤-refl
step (x ∷ xs ,  y ∷ ys) step-H [] _ = z≤n
step (x ∷ xs ,  y ∷ ys) step-H (z  ∷ zs) (z∷zs⊑x∷xs     , z∷zs⊑y∷ys ) with x ≟ y
step (x ∷ xs , .x ∷ ys) step-H (.x ∷ zs) (here zs⊑xs    , x∷zs⊑x∷ys ) | yes refl = s≤s (step-H (xs , ys) (⊰-both x xs x ys) zs (zs⊑xs , tail-⊑-tail x∷zs⊑x∷ys))
step (x ∷ xs , .x ∷ ys) step-H (.x ∷ zs) (x∷zs⊑x∷xs     , here zs⊑ys) | yes refl = s≤s (step-H (xs , ys) (⊰-both x xs x ys) zs (tail-⊑-tail x∷zs⊑x∷xs , zs⊑ys))
step (x ∷ xs , .x ∷ ys) step-H (z  ∷ zs) (there z∷zs⊑xs , there z∷zs⊑ys) | yes refl = ≤-step (step-H (xs , ys) (⊰-both x xs x ys) (z ∷ zs) (z∷zs⊑xs , z∷zs⊑ys))
step (x ∷ xs , .x ∷ ys) step-H (.x ∷ zs) (here    zs⊑xs , here    zs⊑ys) | no x≢x = ⊥-elim (x≢x refl)
step (x ∷ xs ,  y ∷ ys) step-H (z  ∷ zs) (there z∷zs⊑xs , there z∷zs⊑ys) | no x≢y = lem3
  where
    lem1 : length (z ∷ zs) ≤ length (LCS (x ∷ xs) ys)
    lem1 = step-H (x ∷ xs , ys) (⊰-right (x ∷ xs) y ys) (z ∷ zs) (there z∷zs⊑xs , z∷zs⊑ys)
    lem2 : length (z ∷ zs) ≤ length (LCS xs (y ∷ ys))
    lem2 = step-H (xs , y ∷ ys) (⊰-left x xs (y ∷ ys)) (z ∷ zs) (z∷zs⊑xs , there z∷zs⊑ys)
    lem3 : length (z ∷ zs) ≤ length (longest (LCS (x ∷ xs) ys) (LCS xs (y ∷ ys)))
    lem3 = longest-either (\ws → length (z ∷ zs) ≤ length ws) {LCS (x ∷ xs) ys} {LCS xs (y ∷ ys)} lem1 lem2
step (x ∷ xs , y ∷ ys) step-H (.x ∷ zs) (here zs⊑xs , there x∷zs⊑ys) | no x≢y =
  begin
    length (x ∷ zs)
  ≤⟨ step-H (x ∷ xs , ys) (⊰-right (x ∷ xs) y ys) (x ∷ zs) (here zs⊑xs , x∷zs⊑ys) ⟩
    length (LCS (x ∷ xs) ys)
  ≤⟨ longest-left (LCS (x ∷ xs) ys) (LCS xs (y ∷ ys)) ⟩
    length (longest (LCS (x ∷ xs) ys) (LCS xs (y ∷ ys)))
  ∎
  where open ≤-Reasoning
step (x ∷ xs , y ∷ ys) step-H (.y ∷ zs) (there y∷zs⊑xs , here zs⊑ys) | no x≢y =
  begin
    length (x ∷ zs)
  ≤⟨ step-H (xs , y ∷ ys) (⊰-left x xs (y ∷ ys)) (y ∷ zs) (y∷zs⊑xs , here zs⊑ys) ⟩
    length (LCS xs (y ∷ ys))
  ≤⟨ longest-right (LCS (x ∷ xs) ys) (LCS xs (y ∷ ys)) ⟩
    length (longest (LCS (x ∷ xs) ys) (LCS xs (y ∷ ys)))
  ∎
  where open ≤-Reasoning

theorem-2 : ∀ p zs → zs is-common-subsequence-of p → length zs ≤ length (LCS (proj₁ p) (proj₂ p))
theorem-2 p = ⊰-rec step-P step p

-- ---------------------------------------------------------------------------
