{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Sigma
open import lib.types.Graph
open import lib.types.Diagram
open import lib.types.Colim
open import lib.types.Pushout
open import Cocone-po

module Tr-coc-eqv where

module _ {ℓv ℓe ℓ} {Γ : Graph ℓv ℓe} (A : Type ℓ) (tr : is-tree Γ) where

  open Id Γ A
