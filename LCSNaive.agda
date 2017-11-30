module LCSNaive where

open import Data.Empty
open import Data.List
open import Data.Nat
open import Data.Nat.Properties using (≤-step; ≰⇒>; n≤1+n)
open import Relation.Binary
import Relation.Binary.PartialOrderReasoning as PoR
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open DecTotalOrder decTotalOrder using () renaming (refl to ≤-refl)

infix 4 _⊑_

-- is-subsequence-of relation
data _⊑_ {a} {A : Set a} : List A → List A → Set a where
  empty : ∀ {xs} → [] ⊑ xs
  here  : ∀ {xs ys x} → xs ⊑ ys → (x ∷ xs) ⊑ (x ∷ ys)
  there : ∀ {xs ys y} → xs ⊑ ys → xs ⊑ (y ∷ ys)

longest : ∀ {a} {A : Set a} → List A → List A → List A
longest xs ys with length xs ≤? length ys
... | yes xs≤ys = ys
... | no  xs≰ys = xs
  where
    open IsDecTotalOrder

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
  where
    open IsDecTotalOrder

longest-left : ∀ {a} {A : Set a} (xs ys : List A) → length xs ≤ length (longest xs ys)
longest-left xs ys with length xs ≤? length ys
... | yes xs≤ys = xs≤ys
... | no _      = ≤-refl
  where
    open IsDecTotalOrder

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
  where
    open IsDecTotalOrder
    open ≤-Reasoning

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

length-lcs-cons-1 : ∀ {x} {xs} {ys} → length (lcs xs ys) ≤ length (lcs (x ∷ xs) ys)
length-lcs-cons-1 {x} {xs} {ys} = {!!}

length-lcs-cons-2 : ∀ {xs} {y} {ys} → length (lcs xs ys) ≤ length (lcs xs (y ∷ ys))
length-lcs-cons-2 {xs} {y} {ys} = {!!}

length-longest-lcs-cons : ∀ {xs} {ys} {x} {y} → length (lcs xs ys) ≤ length (longest (lcs (x ∷ xs) ys) (lcs xs (y ∷ ys)))
length-longest-lcs-cons {xs} {ys} {x} {y} = longest-either (\ws → length (lcs xs ys) ≤ length ws) {lcs (x ∷ xs) ys} {lcs xs (y ∷ ys)} lem1 lem2
  where
    lem1 : length (lcs xs ys) ≤ length (lcs (x ∷ xs) ys)
    lem1 = length-lcs-cons-1 {x} {xs} {ys}
    lem2 : length (lcs xs ys) ≤ length (lcs xs (y ∷ ys))
    lem2 = length-lcs-cons-2 {xs} {y} {ys}

theorem-2 : ∀ xs ys zs → zs ⊑ xs → zs ⊑ ys → length zs ≤ length (lcs xs ys)
theorem-2 []      ys .[] empty []⊑ys = ≤-refl
theorem-2 (_ ∷ _) [] .[] []⊑xs empty = ≤-refl
theorem-2 (x ∷ xs) (y   ∷ ys) [] _ _ = z≤n
theorem-2 (x ∷ xs) (y   ∷ ys) (z  ∷ zs) z∷zs⊑x∷xs z∷zs⊑y∷ys with x ≟ y
theorem-2 (x ∷ xs) (.x  ∷ ys) (.x ∷ zs) (here zs⊑xs) x∷zs⊑x∷ys | yes refl = s≤s (theorem-2 xs ys zs zs⊑xs (tail-⊑-tail x∷zs⊑x∷ys))
theorem-2 (x ∷ xs) (.x  ∷ ys) (.x ∷ zs) x∷zs⊑x∷xs (here zs⊑ys) | yes refl = s≤s (theorem-2 xs ys zs (tail-⊑-tail x∷zs⊑x∷xs) zs⊑ys)
theorem-2 (x ∷ xs) (.x  ∷ ys) (z  ∷ zs) (there z∷zs⊑xs) (there z∷zs⊑ys) | yes refl = ≤-step (theorem-2 xs ys (z ∷ zs) z∷zs⊑xs z∷zs⊑ys)
theorem-2 (x ∷ xs) (.x  ∷ ys) (.x ∷ zs) (here    zs⊑xs) (here    zs⊑ys) | no x≢x = ⊥-elim (x≢x refl)
theorem-2 (x ∷ xs) (y   ∷ ys) (z  ∷ zs) (there z∷zs⊑xs) (there z∷zs⊑ys) | no x≢y =
  begin
    suc (length zs)
  ≤⟨ theorem-2 xs ys (z ∷ zs) (z∷zs⊑xs) (z∷zs⊑ys) ⟩
    length (lcs xs ys)
  ≤⟨ length-longest-lcs-cons {xs} {ys} {x} {y} ⟩
    length (longest (lcs (x ∷ xs) ys) (lcs xs (y ∷ ys)))
  ∎
  where open ≤-Reasoning
theorem-2 (x ∷ xs) (y ∷ ys) (.x ∷ zs) (here zs⊑xs) (there x∷zs⊑ys) | no x≢y =
  begin
    length (x ∷ zs)
  ≤⟨ ≤-refl ⟩
    suc (length zs)
  ≤⟨ theorem-2 (x ∷ xs) ys (x ∷ zs) (here zs⊑xs) x∷zs⊑ys ⟩
    length (lcs (x ∷ xs) ys)
  ≤⟨ longest-left (lcs (x ∷ xs) ys) (lcs xs (y ∷ ys)) ⟩
    length (longest (lcs (x ∷ xs) ys) (lcs xs (y ∷ ys)))
  ∎
  where
    open ≤-Reasoning
theorem-2 (x ∷ xs) (y ∷ ys) (.y ∷ zs) (there y∷zs⊑xs) (here zs⊑ys) | no x≢y =
  begin
    length (x ∷ zs)
  ≤⟨ ≤-refl ⟩
    suc (length zs)
  ≤⟨ theorem-2 xs (y ∷ ys) (y ∷ zs) y∷zs⊑xs (here zs⊑ys) ⟩
    length (lcs xs (y ∷ ys))
  ≤⟨ longest-right (lcs (x ∷ xs) ys) (lcs xs (y ∷ ys)) ⟩
    length (longest (lcs (x ∷ xs) ys) (lcs xs (y ∷ ys)))
  ∎
  where
    open ≤-Reasoning
