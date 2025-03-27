{-# OPTIONS --without-K --rewriting  #-}

module CosColim-main where

{-
  This module shows that our pushout construction satisfies the universal property of an A-colimit,
  namely that it's left adjoint to the constant diagram functor. We construct such an adjunction
  by presenting the expected natural isomorphism. This amounts to combining two files.  
-}

open import CosColim-Iso  -- shows that the canonical post-comp map is an equivalence
open import CosColim-Adjunction  -- shows that post-comp fits into the two naturality squares
