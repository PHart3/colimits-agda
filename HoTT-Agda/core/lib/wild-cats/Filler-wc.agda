{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.wild-cats.WildCat

-- fillers of commuting squares in a wild category

module lib.wild-cats.Filler-wc where

module _ {i j} {C : WildCat {i} {j}} where

  -- the type of fillers
  record Fill-wc {a b c d : ob C} {l : hom C a b} {r : hom C c d}
    (f : hom C a c) (g : hom C b d) (S : ⟦ C ⟧ g ◻ l == ⟦ C ⟧ r ◻ f) : Type (lmax i j) where
    constructor fillwc
    field
      diag : hom C b c
      tri-top : ⟦ C ⟧ diag ◻ l == f
      tri-bottom : ⟦ C ⟧ r ◻ diag == g
      tri-coh : α C r diag l ∙ ap (λ m → ⟦ C ⟧ r ◻ m) tri-top == ap (λ m → ⟦ C ⟧ m ◻ l) tri-bottom ∙ S

  -- left lifting property against a class of morphisms
  llp-wc : ∀ {k} (H : ∀ {a b} → hom C a b → -1 -Type k) {a b : ob C} (l : hom C a b) → Type (lmax (lmax i j) k)
  llp-wc H {a} {b} l = ∀ {c d} {r : hom C c d} (r-H : fst (H r))
    (f : hom C a c) (g : hom C b d) (S : ⟦ C ⟧ g ◻ l == ⟦ C ⟧ r ◻ f) → is-contr (Fill-wc f g S)
