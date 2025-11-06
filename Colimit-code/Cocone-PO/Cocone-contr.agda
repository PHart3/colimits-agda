{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Cofiber
open import lib.types.Colim
open import lib.types.Unit
open import Coslice
open import Diagram-Cos
open import Cocone-po

module Cocone-contr where

module _ {ℓv ℓe ℓd} {Γ : Graph ℓv ℓe} (F : CosDiag ℓd _ Unit Γ) where

  open Id.Maps Γ Unit F

  -- if each vertex of the diagram is contractible, then the cofiber is contractible 
  diag-contr-po-contr : (∀ i → is-contr (ty (F # i))) → is-contr P
  diag-contr-po-contr as = cofib-eqv-contr (ColMap-deqv λ i → Unit-to-contr (as i))
