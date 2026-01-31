{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Graph
open import lib.types.Suspension
open import lib.types.Acyclic
open import lib.wild-cats.WildCats
open import homotopy.Susp-colim
open import CosCol-Coc-contr

-- Pointed acyclic types are closed under (graph-indexed) pointed colimits.

module homotopy.Acyc-colim where

module _ {ℓv ℓe ℓd} {Γ : Graph ℓv ℓe} (F : Diagram Γ (Ptd-wc ℓd)) {X : Ptd ℓd} {K : Cocone-wc F X} (cK : is-colim K) where

  open PtdColContr (F-diag SuspFunctor F) (Susp-prsrv-colim cK)

  abstract
    ptdcolim-acyc : (∀ i → is-acyclic⊙ (D₀ F i)) → is-acyclic⊙ X
    ptdcolim-acyc acycs = ptdcolim-contr acycs
