{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Diagram
open import lib.types.Colim
open import lib.types.Suspension
open import lib.types.Acyclic
open import lib.wild-cats.WildCats
open import homotopy.Susp-colim
open import Diagram-Cos
open import Id-col
open import CosColim-Iso
open import Cocone-po
open import Cos-wc
open import CosCol-Coc-contr

-- acyclic types are closed under all (graph-indexed) pointed colimits

module homotopy.Acyc-colim where

module _ {ℓv ℓe ℓd} {Γ : Graph ℓv ℓe} (F : Diagram Γ (Coslice-wc Unit ℓd)) where

  private Δ = Diag-to-grhom F

  open Id.Maps Γ Unit Δ
{-
  abstract
    ptdcolim-acyc : (Π (Obj Γ) (λ i → is-acyclic (ty (Δ # i)))) → is-acyclic P
    ptdcolim-acyc acycs = equiv-preserves-level {!!} {{diag-contr-po-contr (F-diag SuspFunctor-Cos F) {!acycs!}}}
-}
