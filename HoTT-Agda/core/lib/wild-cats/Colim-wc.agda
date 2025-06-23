{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.Equivalence2
open import lib.types.Graph
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc
open import lib.wild-cats.Diag-coher-wc

-- colimiting cocones in a wild cat

module lib.wild-cats.Colim-wc where

module _ {i j} {C : WildCat {i} {j}} {ℓv ℓe} {G : Graph ℓv ℓe} {D : Diagram G C} where

  is-colim : {a : ob C} (K : Cocone-wc D a) → Type (lmax (lmax i j) (lmax ℓv ℓe))
  is-colim K = (b : ob C) → is-equiv (post-cmp-coc K b)

  is-colim-≃ : {a : ob C} (K : Cocone-wc D a) (cl : is-colim K) (b : ob C)
    → hom C a b ≃ Cocone-wc D b
  fst (is-colim-≃ K _ b) = post-cmp-coc K b
  snd (is-colim-≃ _ cl b) = cl b

  module _ {a₁ a₂ : ob C} {K₁ : Cocone-wc D a₁} {K₂ : Cocone-wc D a₂} (φ@(f , σ) : Coc-wc-mor K₁ K₂)
    (pent : pentagon-wc C) where

    coc-wc-tri : {b : ob C} (g : hom C a₂ b) → post-cmp-coc K₁ _ (⟦ C ⟧ g ◻ f) == post-cmp-coc K₂ _ g
    coc-wc-tri {b} g = pst-cmp-∘ pent g f K₁ ∙ ap (λ K → post-cmp-coc K b g) σ

    colim-wc-unq : is-colim K₁ → is-colim K₂ → equiv-wc C f
    fst (colim-wc-unq cl1 cl2) = {!!}
    snd (colim-wc-unq cl1 cl2) = {!!}
