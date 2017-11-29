module LCSNaive where

open import Data.Bool hiding (_≟_)
open import Data.List
open import Data.Nat
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

-- is-subsequence-of relation
data _⊑_ {a} {A : Set a} : List A → List A → Set a where
  empty : ∀ {xs} → [] ⊑ xs
  here  : ∀ {xs ys x} → xs ⊑ ys → (x ∷ xs) ⊑ (x ∷ ys)
  there : ∀ {xs ys y} → xs ⊑ ys → xs ⊑ (y ∷ ys)

longest : List ℕ → List ℕ → List ℕ
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

longest-lemma : ∀ {xs} {ys} {zs} → xs ⊑ zs → ys ⊑ zs → longest xs ys ⊑ zs
longest-lemma {xs} {ys} {zs} xs⊑zs ys⊑zs with length xs ≤? length ys
... | yes xs≤ys = ys⊑zs
... | no ¬xs≤ys = xs⊑zs
  where
    open IsDecTotalOrder
  
lcs-lemma-1 : ∀ {xs} ys → lcs xs ys ⊑ xs
lcs-lemma-1 {[]} _     = empty
lcs-lemma-1 {_ ∷ _} [] = empty
lcs-lemma-1 {x ∷ xs} (y ∷ ys) with x ≟ y
... | yes x≡y = here (lcs-lemma-1 ys)
... | no  x≢y = longest-lemma (lcs-lemma-1 ys) (there (lcs-lemma-1 (y ∷ ys)))
  where open IsDecTotalOrder

lcs-lemma-2 : ∀ xs {ys} → lcs xs ys ⊑ ys
lcs-lemma-2 [] {_}       = empty
lcs-lemma-2 (_ ∷ _) {[]} = empty
lcs-lemma-2 (x ∷ xs) {y ∷ ys} with x ≟ y
lcs-lemma-2 (x ∷ xs) {.x ∷ ys} | yes refl = here (lcs-lemma-2 xs)
lcs-lemma-2 (x ∷ xs) {y ∷ ys}  | no  x≢y = longest-lemma (there (lcs-lemma-2 (x ∷ xs))) (lcs-lemma-2 xs)
  where open IsDecTotalOrder
