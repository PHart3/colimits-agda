{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc

module lib.wild-cats.Colim-wc where

module _ {i j} {C : WildCat {i} {j}} {ℓv ℓe} {G : Graph ℓv ℓe} {D : Diagram G C}
  {a : ob C} (K : Cocone D a) where

  post-cmp-coc : (b : ob C) → hom C a b → Cocone D b
  leg (post-cmp-coc _ f) x = ⟦ C ⟧ f ◻ leg K x
  tri (post-cmp-coc _ f) {x} {y} γ = α C f (leg K y) (D₁ D γ) ∙ ap (λ m → ⟦ C ⟧ f ◻ m) (tri K γ)

  is-colim : Type (lmax (lmax i j) (lmax ℓv ℓe))
  is-colim = (b : ob C) → is-equiv (post-cmp-coc b)

  is-colim-≃ : (cl : is-colim) (b : ob C) → hom C a b ≃ Cocone D b
  fst (is-colim-≃ _ b) = post-cmp-coc b
  snd (is-colim-≃ cl b) = cl b
