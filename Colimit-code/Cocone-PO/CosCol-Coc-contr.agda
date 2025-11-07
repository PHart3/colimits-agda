{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Cofiber
open import lib.types.Colim
open import lib.types.Unit
open import lib.wild-cats.WildCats
open import Coslice
open import Diagram-Cos
open import Cocone-po
open import Cos-wc

module CosCol-Coc-contr where

module _ {ℓv ℓe ℓd} {Γ : Graph ℓv ℓe} (F : Diagram Γ (Coslice-wc Unit ℓd)) where

  private Δ = Diag-to-grhom F

  open Id.Maps Γ Unit Δ

  -- if each vertex of the diagram is contractible, then the cofiber is contractible 
  diag-contr-po-contr : (∀ i → is-contr (ty (Δ # i))) → is-contr P
  diag-contr-po-contr as = cofib-eqv-contr (ColMap-deqv λ i → Unit-to-contr (as i))
