{-# OPTIONS --without-K --rewriting #-}

open import lib.Base

module lib.types.Graph where

record Graph (ℓv ℓe : ULevel) : Type (lsucc (lmax ℓv ℓe)) where
  field
    Obj : Type ℓv
    Hom : Obj → Obj → Type ℓe
open Graph public
