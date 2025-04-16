{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.wild-cats.WildCat

module lib.wild-cats.Ptd-wc (i : ULevel) where

  Ptd-wc : WildCat
  ob Ptd-wc = Ptd i
  hom Ptd-wc X Y = X ⊙→ Y
  id₁ Ptd-wc X = ⊙idf X
  _◻_ Ptd-wc g f = g ⊙∘ f
  ρ Ptd-wc f = {!!} -- ⊙-comp-to-== (⊙∘-runit f)
  lamb Ptd-wc f = {!!} -- ⊙-comp-to-== (⊙∘-lunit f)
  α Ptd-wc h g f = {!!} -- ⊙-comp-to-== (⊙∘-α-comp h g f)
