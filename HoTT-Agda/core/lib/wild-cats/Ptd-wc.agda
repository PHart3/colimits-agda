{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.wild-cats.WildCat

module lib.wild-cats.Ptd-wc where

  Ptd-wc : (i : ULevel) → WildCat
  ob (Ptd-wc i) = Ptd i
  hom (Ptd-wc _) X Y = X ⊙→ Y
  id₁ (Ptd-wc _) X = ⊙idf X
  _◻_ (Ptd-wc _) g f = g ⊙∘ f
  ρ (Ptd-wc _) f = ⊙-crd∼-to-== (⊙∘-runit f) 
  lamb (Ptd-wc _) f = ⊙-crd∼-to-== (⊙∘-lunit f)
  α (Ptd-wc _) h g f = ⊙-crd∼-to-== (⊙∘-assoc-crd h g f)

  PtdFunctor : (i j : ULevel) → Type (lsucc (lmax i j))
  PtdFunctor i j = Functor-wc (Ptd-wc i) (Ptd-wc j)
