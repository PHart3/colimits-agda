{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Graph
open import lib.types.Suspension
open import homotopy.SuspAdjointLoop
open import homotopy.Susp-2coher
open import lib.wild-cats.WildCats

{- Suspension preserves colimits. -}

module homotopy.Susp-colim where

Susp-prsrv-colim : ∀ {i ℓv ℓe} {G : Graph ℓv ℓe} {Δ : Diagram G (Ptd-wc i)}
  {X : Ptd i} {K : Cocone Δ X}→ (cl : is-colim K) → is-colim (F-coc SuspFunctor K)
Susp-prsrv-colim = Ladj-prsrv-clim {adj = SuspLoopAdj-exp} Susp-is-2-coher
