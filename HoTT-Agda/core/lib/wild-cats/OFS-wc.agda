{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Sigma
open import lib.wild-cats.WildCat

-- orthogonal factorization systems on wild categories

module lib.wild-cats.OFS-wc where

module _ {i j} {C : WildCat {i} {j}} where

  -- the type of factorizations of a morphism
  record fact-mor-wc {a b : ob C} (f : hom C a b) : Type (lmax i j) where
    constructor factmor
    field
      im : ob C
      mor-l : hom C a im
      mor-r : hom C im b
      fact : ⟦ C ⟧ mor-r ◻ mor-l == f
  open fact-mor-wc

  record ofs-wc {k₁ k₂ : ULevel} : Type (lmax (lmax i j) (lmax (lsucc k₁) (lsucc k₂))) where
    constructor ofs
    field
      lclass : {a b : ob C} → hom C a b → -1 -Type k₁
      rclass : {a b : ob C} → hom C a b → -1 -Type k₂
      id₁-lc : {a : ob C} → fst (lclass (id₁ C a))
      id₁-rc : {a : ob C} → fst (rclass (id₁ C a))
      ∘-lc : {a b c : ob C} {f : hom C a b} {g : hom C b c} (lf : fst (lclass f)) (lg : fst (lclass g)) →
        fst (lclass (⟦ C ⟧ g ◻ f))
      ∘-rc : {a b c : ob C} {f : hom C a b} {g : hom C b c} (rf : fst (rclass f)) (rg : fst (rclass g)) →
        fst (rclass (⟦ C ⟧ g ◻ f))
      fact-contr : {a b : ob C} (f : hom C a b) → is-contr $
        Σ (fact-mor-wc f) (λ fct →
          fst (lclass (mor-l fct)) × fst (rclass (mor-r fct)))
  open ofs-wc public
