{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Colim
open import lib.wild-cats.WildCats

{- the wild adjunction between the Type-valued colimit functor and the constant diagram functor
   along with a proof of the hexagon coherence condition -}

module homotopy.ColimAdjointConst where

