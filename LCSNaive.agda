module LCSNaive where

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

open ≤-Reasoning
open DecTotalOrder decTotalOrder using () renaming (refl to ≤-refl)

infix 4 _⊑_ _⊰_

-- is-subsequence-of relation
data _⊑_ {a} {A : Set a} : List A → List A → Set a where
  empty : ∀ {xs} → [] ⊑ xs
  here  : ∀ {xs ys x} → xs ⊑ ys → (x ∷ xs) ⊑ (x ∷ ys)
  there : ∀ {xs ys y} → xs ⊑ ys → xs ⊑ (y ∷ ys)

longest : ∀ {a} {A : Set a} → List A → List A → List A
longest xs ys with length xs ≤? length ys
... | yes xs≤ys = ys
... | no  xs≰ys = xs

lcs : List ℕ → List ℕ → List ℕ
lcs [] _ = []
lcs (_ ∷ _) [] = []
lcs (x ∷ xs) (y ∷ ys) with x ≟ y
... | yes x≡y = x ∷ lcs xs ys
... | no x≢y  = longest (lcs (x ∷ xs) ys) (lcs xs (y ∷ ys))

longest-either : ∀ {a} {A : Set a} {b} (P : List A → Set b) {xs ys : List A} → P xs → P ys → P (longest xs ys)
longest-either P {xs} {ys} Pxs Pys with length xs ≤? length ys
... | yes xs≤ys = Pys
... | no ¬xs≤ys = Pxs

longest-left : ∀ {a} {A : Set a} (xs ys : List A) → length xs ≤ length (longest xs ys)
longest-left xs ys with length xs ≤? length ys
... | yes xs≤ys = xs≤ys
... | no _      = ≤-refl

longest-right : ∀ {a} {A : Set a} (xs ys : List A) → length ys ≤ length (longest xs ys)
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

lcs-lemma-1 : ∀ {xs} ys → lcs xs ys ⊑ xs
lcs-lemma-1 {[]} _     = empty
lcs-lemma-1 {_ ∷ _} [] = empty
lcs-lemma-1 {x ∷ xs} (y ∷ ys) with x ≟ y
... | yes x≡y = here (lcs-lemma-1 ys)
... | no  x≢y = longest-either (\zs → zs ⊑ x ∷ xs) (lcs-lemma-1 ys) ((there (lcs-lemma-1 (y ∷ ys))))

lcs-lemma-2 : ∀ xs {ys} → lcs xs ys ⊑ ys
lcs-lemma-2 [] {_}       = empty
lcs-lemma-2 (_ ∷ _) {[]} = empty
lcs-lemma-2 (x ∷ xs) {y ∷ ys} with x ≟ y
lcs-lemma-2 (x ∷ xs) {.x ∷ ys} | yes refl = here (lcs-lemma-2 xs)
lcs-lemma-2 (x ∷ xs) {y ∷ ys}  | no  x≢y = longest-either (\zs → zs ⊑ y ∷ ys) (there (lcs-lemma-2 (x ∷ xs))) (lcs-lemma-2 xs)

_is-CS-of_ : ∀ {A : Set} → List A → List A × List A → Set
_is-CS-of_ zs (xs , ys) = (zs ⊑ xs) × (zs ⊑ ys)

thereom-1 : ∀ {p} → lcs (proj₁ p) (proj₂ p) is-CS-of p
thereom-1 {(xs , ys)} = (lcs-lemma-1 ys , lcs-lemma-2 xs)

tail-⊑ : ∀ {a} {A : Set a} {x : A} {xs} {ys} → x ∷ xs ⊑ ys → xs ⊑ ys
tail-⊑ (here xs⊑ys) = there xs⊑ys
tail-⊑ {_} {_} {_} {[]} (there [x]⊑ys) = empty
tail-⊑ {_} {_} {_} {x' ∷ xs} (there x∷x'∷xs⊑ys) = there (tail-⊑ x∷x'∷xs⊑ys)

tail-⊑-tail : ∀ {a} {A : Set a} {x : A} {xs} {ys} → x ∷ xs ⊑ x ∷ ys → xs ⊑ ys
tail-⊑-tail (here xs⊑ys) = xs⊑ys
tail-⊑-tail (there x∷xs⊑ys) = tail-⊑ x∷xs⊑ys

length-⊑ : ∀ {a} {A : Set a} {xs ys : List A} → xs ⊑ ys → length xs ≤ length ys
length-⊑ empty = z≤n
length-⊑ (here xs⊑ys) = s≤s (length-⊑ xs⊑ys)
length-⊑ (there xs⊑y∷ys) = ≤-step (length-⊑ xs⊑y∷ys)

⊑-refl : ∀ {a} {A : Set a} {xs : List A} → xs ⊑ xs
⊑-refl {_} {_} {[]} = empty
⊑-refl {_} {_} {x ∷ xs} = here ⊑-refl

⊑-trans : ∀ {a} {A : Set a} {xs ys zs : List A} → xs ⊑ ys → ys ⊑ zs → xs ⊑ zs
⊑-trans {a} {A} {[]} {ys} {zs} empty ys⊑zs = empty
⊑-trans {a} {A} {xs} {y ∷ ys} {zs} (there xs⊑ys) y∷ys⊑zs = ⊑-trans xs⊑ys (tail-⊑ y∷ys⊑zs)
⊑-trans {a} {A} {x ∷ xs} {.x ∷ ys} {.x ∷ zs} (here xs⊑ys) (here    ys⊑zs) = here  (⊑-trans xs⊑ys ys⊑zs)
⊑-trans {a} {A} {x ∷ xs} {.x ∷ ys} {z ∷ zs}  (here xs⊑ys) (there x∷ys⊑zs) = there (⊑-trans (here xs⊑ys) x∷ys⊑zs)

sum-length : ∀ {A : Set} → List A × List A → ℕ
sum-length (xs , ys) = length xs + length ys

_⊰_ : ∀ {A : Set} → List A × List A → List A × List A → Set
_⊰_ = _<′_ on sum-length

⊰-well-founded : ∀ {A : Set} → Well-founded (_⊰_ {A})
⊰-well-founded = Inverse-image.well-founded sum-length <-well-founded

module _ {ℓ} {A} where
  open All (⊰-well-founded {A}) ℓ public
    renaming ( wfRec-builder to ⊰-rec-builder
             ; wfRec to ⊰-rec
             )

⊰-both : ∀ {A} {x y : A} {xs ys : List A} → (xs , ys) ⊰ (x ∷ xs , y ∷ ys)
⊰-both {_} {x} {y} {xs} {ys} = {!!}

⊰-left : ∀ {A} {x : A} {xs ys : List A} → (xs , ys) ⊰ (x ∷ xs , ys)
⊰-left {_} {x} {xs} {ys} = {!!}

⊰-right : ∀ {A} {y : A} {xs ys : List A} → (xs , ys) ⊰ (xs , y ∷ ys)
⊰-right {_} {y} {xs} {ys} = {!!}

step-P : ∀ p → Set
step-P p = ∀ zs → zs is-CS-of p → length zs ≤ length (lcs (proj₁ p) (proj₂ p))

step : ∀ p → (∀ q → q ⊰ p → step-P q) → step-P p
step ([] , ys) step-H .[] (empty , []⊑ys) = ≤-refl
{-
step ([] ,      []) step-H .[] (empty , empty) = ≤-refl
step ([] , (_ ∷ _)) step-H .[] (empty , []⊑ys) = ≤-refl
-}
step (_ ∷ _ , []) step-H .[] ([]⊑xs , empty) = ≤-refl
step (x ∷ xs ,  y ∷ ys) step-H [] _ = z≤n
step (x ∷ xs ,  y ∷ ys) step-H (z  ∷ zs) (z∷zs⊑x∷xs     , z∷zs⊑y∷ys ) with x ≟ y
step (x ∷ xs , .x ∷ ys) step-H (.x ∷ zs) (here zs⊑xs    , x∷zs⊑x∷ys ) | yes refl = s≤s (step-H (xs , ys) (⊰-both {_} {x} {x} {xs} {ys}) zs (zs⊑xs , tail-⊑-tail x∷zs⊑x∷ys))
step (x ∷ xs , .x ∷ ys) step-H (.x ∷ zs) (x∷zs⊑x∷xs     , here zs⊑ys) | yes refl = s≤s (step-H (xs , ys) (⊰-both {_} {x} {x} {xs} {ys}) zs (tail-⊑-tail x∷zs⊑x∷xs , zs⊑ys))
step (x ∷ xs , .x ∷ ys) step-H (z  ∷ zs) (there z∷zs⊑xs , there z∷zs⊑ys) | yes refl = ≤-step (step-H (xs , ys) (⊰-both {_} {x} {x} {xs} {ys}) (z ∷ zs) (z∷zs⊑xs , z∷zs⊑ys))
step (x ∷ xs , .x ∷ ys) step-H (.x ∷ zs) (here    zs⊑xs , here    zs⊑ys) | no x≢x = ⊥-elim (x≢x refl)
step (x ∷ xs ,  y ∷ ys) step-H (z  ∷ zs) (there z∷zs⊑xs , there z∷zs⊑ys) | no x≢y = lem3
  where
    lem1 : length (z ∷ zs) ≤ length (lcs (x ∷ xs) ys)
    lem1 = step-H (x ∷ xs , ys) (⊰-right {_} {y} {x ∷ xs} {ys}) (z ∷ zs) (there z∷zs⊑xs , z∷zs⊑ys)
    lem2 : length (z ∷ zs) ≤ length (lcs xs (y ∷ ys))
    lem2 = step-H (xs , y ∷ ys) (⊰-left {_} {x} {xs} {y ∷ ys}) (z ∷ zs) (z∷zs⊑xs , there z∷zs⊑ys)
    lem3 : length (z ∷ zs) ≤ length (longest (lcs (x ∷ xs) ys) (lcs xs (y ∷ ys)))
    lem3 = longest-either (\ws → length (z ∷ zs) ≤ length ws) {lcs (x ∷ xs) ys} {lcs xs (y ∷ ys)} lem1 lem2
step (x ∷ xs , y ∷ ys) step-H (.x ∷ zs) (here zs⊑xs , there x∷zs⊑ys) | no x≢y =
  begin
    length (x ∷ zs)
  ≤⟨ step-H (x ∷ xs , ys) (⊰-right {_} {y} {x ∷ xs} {ys}) (x ∷ zs) (here zs⊑xs , x∷zs⊑ys) ⟩
    length (lcs (x ∷ xs) ys)
  ≤⟨ longest-left (lcs (x ∷ xs) ys) (lcs xs (y ∷ ys)) ⟩
    length (longest (lcs (x ∷ xs) ys) (lcs xs (y ∷ ys)))
  ∎
step (x ∷ xs , y ∷ ys) step-H (.y ∷ zs) (there y∷zs⊑xs , here zs⊑ys) | no x≢y =
  begin
    length (x ∷ zs)
  ≤⟨ step-H (xs , y ∷ ys) (⊰-left {_} {x} {xs} {y ∷ ys}) (y ∷ zs) (y∷zs⊑xs , here zs⊑ys) ⟩
    length (lcs xs (y ∷ ys))
  ≤⟨ longest-right (lcs (x ∷ xs) ys) (lcs xs (y ∷ ys)) ⟩
    length (longest (lcs (x ∷ xs) ys) (lcs xs (y ∷ ys)))
  ∎

theorem-2 : ∀ p zs → zs is-CS-of p → length zs ≤ length (lcs (proj₁ p) (proj₂ p))
theorem-2 p = ⊰-rec step-P step p
