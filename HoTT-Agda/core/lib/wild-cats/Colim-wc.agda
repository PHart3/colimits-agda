{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc

module lib.wild-cats.Colim-wc where

module _ {i j} {C : WildCat {i} {j}} {a b : ob C} (f : hom C a b) where

  post-comp-coc : ∀ {ℓv ℓe} {G : Graph ℓv ℓe} (D : Diagram G C)
    → Cocone D a → Cocone D b
  comp (post-comp-coc D K) x = ⟦ C ⟧ f ◻ comp K x
  tri (post-comp-coc D K) {x} {y} γ = α C f (comp K y) (D₁ D γ) ∙ ap (λ m → ⟦ C ⟧ f ◻ m) (tri K γ)
