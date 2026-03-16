{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Cospan
open import lib.types.Pullback

-- construction of coslice pullbacks
  
module Cos-pullback {j} {A : Type j} where

open import Coslice public
open import Cos-cospan

open MapsCos A

module _ {i k l} {X : Coslice i j A} {Y : Coslice k j A} {Z : Coslice l j A} (f : X *→ Z) (g : Y *→ Z) where

  open CosCone-csp

  cspan : CosCospan
  CosCospan.X cspan = X
  CosCospan.Y cspan = Y
  CosCospan.Z cspan = Z
  CosCospan.f cspan = f
  CosCospan.g cspan = g

  cospan-forg : Cospan
  Cospan.A cospan-forg = ty X
  Cospan.B cospan-forg = ty Y
  Cospan.C cospan-forg = ty Z
  Cospan.f cospan-forg = fst f
  Cospan.g cospan-forg = fst g

  pb-forg-ty : Type (lmax (lmax i k) l)
  pb-forg-ty = Pullback cospan-forg

  pb-forg-pt : A → pb-forg-ty
  Pullback.a (pb-forg-pt a) = str X a
  Pullback.b (pb-forg-pt a) = str Y a
  Pullback.h (pb-forg-pt a) = snd f a ∙ ! (snd g a)

  pb-forg : Coslice (lmax (lmax i k) l) j A
  pb-forg = *[ pb-forg-ty , pb-forg-pt ]

  pb-cos-cone : CosCone-csp cspan pb-forg
  left pb-cos-cone = Pullback.a , (λ _ → idp)
  right pb-cos-cone = Pullback.b , (λ _ → idp)
  fst (sq pb-cos-cone) = Pullback.h
  snd (sq pb-cos-cone) a = !-inv-l-∙-!-! (snd f a) (snd g a)

  open Cone-pb-id
