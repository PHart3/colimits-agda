{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.Equivalence2
open import lib.SIP
open import lib.types.Sigma
open import lib.types.Paths
open import lib.wild-cats.WildCat
open import lib.wild-cats.Adjoint
open import lib.wild-cats.OFS-filler-wc

{- Under a reasonable hexagon identity, a left adjoint preserves the left class
   of an OFS as soon as its right adjoint preserves the right class. -}

module lib.wild-cats.Adj-OFS-wc where

module _ {i₁ i₂ j₁ j₂} {C : WildCat {i₁} {j₁}} {D : WildCat {i₂} {j₂}} {L : Functor-wc C D} {R : Functor-wc D C} (adj : Adjunction L R)
  {a b : ob C} {x y : ob D} {f : hom C a b} {g : hom D x y} (u : hom D (obj L a) x) (v : hom D (obj L b) y)
  (S : ⟦ D ⟧ v ◻ arr L f == ⟦ D ⟧ g ◻ u) where

  open import lib.wild-cats.Adj-hexagon public

  fill-adj-transf :
    Fill-wc {C = D} u v S
      ≃
    Fill-wc {C = C} (–> (iso adj) u) (–> (iso adj) v) (nat-dom adj f v ∙ ap (–> (iso adj)) S ∙ ! (nat-cod adj g u))
  fill-adj-transf = {!!}
