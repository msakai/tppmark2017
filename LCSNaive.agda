module LCSNaive where

open import Data.List
open import Data.Nat
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

infix 4 _⊑_

-- is-subsequence-of relation
data _⊑_ {a} {A : Set a} : List A → List A → Set a where
  empty : ∀ {xs} → [] ⊑ xs
  here  : ∀ {xs ys x} → xs ⊑ ys → (x ∷ xs) ⊑ (x ∷ ys)
  there : ∀ {xs ys y} → xs ⊑ ys → xs ⊑ (y ∷ ys)

longest : ∀ {a} {A : Set a} → List A → List A → List A
longest xs ys with length xs ≤? length ys
... | yes xs≤ys = ys
... | no ¬xs≤ys = xs
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
