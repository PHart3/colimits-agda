{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Graph
open import lib.types.Suspension
open import homotopy.SuspAdjointLoop
open import homotopy.Susp-2coher
open import lib.wild-cats.WildCats
open import lib.wild-cats.Iso-wc
open import lib.wild-cats.Ladj-colim
open import Cos-wc

-- Suspension preserves colimits over graphs.

module homotopy.Susp-colim {i ℓv ℓe} {G : Graph ℓv ℓe} where

Susp-prsrv-colim : {Δ : Diagram G (Ptd-wc i)} {X : Ptd i} {K : Cocone-wc Δ X}
  → is-colim K → is-colim (F-coc SuspFunctor K)
Susp-prsrv-colim = Ladj-prsrv-clim {adj = SuspLoopAdj-exp} Susp-is-2-coher

-- equivalent version for the coslice under Unit

Susp-prsrv-colim-Cos-exp : (Δ : Diagram G (Coslice-wc Unit i)) (X : Coslice i _ Unit) (K : Cocone-wc Δ X)
  → is-colim K → is-colim (F-coc SuspFunctor-Cos K)
Susp-prsrv-colim-Cos-exp = wc-iso-ef-same (λ {D} F → (Δ : Diagram G D) (X : ob D) (K : Cocone-wc Δ X) → is-colim K → is-colim (F-coc F K)) (λ _ _ _ → Susp-prsrv-colim)

abstract
  Susp-prsrv-colim-Cos : {Δ : Diagram G (Coslice-wc Unit i)} {X : Coslice i _ Unit} {K : Cocone-wc Δ X}
    → is-colim K → is-colim (F-coc SuspFunctor-Cos K)
  Susp-prsrv-colim-Cos {Δ} {X} {K} = Susp-prsrv-colim-Cos-exp Δ X K
