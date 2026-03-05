{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics

-- construction of coslice pullbacks
  
module Cos-pullback where

open import Coslice public

module _ {j} (A : Type j) where

  open MapsCos A
