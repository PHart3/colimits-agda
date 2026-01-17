{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.wild-cats.WildCat
open import lib.wild-cats.Adjoint

-- the hexagon coherence condition for a wild adjunction

module lib.wild-cats.Adj-hexagon where

module _ {i₁ i₂ j₁ j₂} {C : WildCat {i₁} {j₁}} {D : WildCat {i₂} {j₂}}
  {L : Functor-wc C D} {R : Functor-wc D C} (adj : Adjunction L R) where

  adj-wc-hexagon : Type (lmax (lmax (lmax i₁ i₂) j₁) j₂)
  adj-wc-hexagon = {a b : ob C} {x y : ob D} (f : hom C a b) (g : hom D x y) (d : hom D (obj L b) x) →
    ap (λ m → ⟦ C ⟧ m ◻ f) (nat-cod adj g d) ∙
    nat-dom adj f (⟦ D ⟧ g ◻ d) ∙
    ap (–> (iso adj)) (α D g d (arr L f))
      ==
    α C (arr R g) (–> (iso adj) d) f ∙
    ap (λ m → ⟦ C ⟧ arr R g ◻ m) (nat-dom adj f d) ∙
    nat-cod adj g (⟦ D ⟧ d ◻ arr L f)

  module _ (hex : adj-wc-hexagon) {a b : ob C} {x y : ob D} {f : hom C a b} {g : hom D x y} {d : hom D (obj L b) x} where

    abstract

      adj-wc-hexagon◃ :
        ap (λ m → ⟦ C ⟧ m ◻ f) (nat-cod adj g d) ◃∙
        nat-dom adj f (⟦ D ⟧ g ◻ d) ◃∙
        ap (–> (iso adj)) (α D g d (arr L f)) ◃∎
          =ₛ
        α C (arr R g) (–> (iso adj) d) f ◃∙
        ap (λ m → ⟦ C ⟧ arr R g ◻ m) (nat-dom adj f d) ◃∙
        nat-cod adj g (⟦ D ⟧ d ◻ arr L f) ◃∎
      adj-wc-hexagon◃ = =ₛ-in (hex f g d)
