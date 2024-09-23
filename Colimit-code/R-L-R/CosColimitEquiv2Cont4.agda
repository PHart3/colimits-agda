{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import lib.PathSeq
open import Coslice
open import Diagram
open import Colim
open import FTID-Cos
open import CosColimitEquiv2
open import CosColimitEquiv2Cont3

module CosColimitEquiv2Cont4 where

module _ {ℓv ℓe ℓ ℓd ℓc} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓd ℓ A Γ} {T : Coslice ℓc ℓ A} (K : CosCocone A F T) where

  open ConstrE2 F T K

  open ConstrE2Cont3.Equiv2d F T K

  LRfun-∼ : CosCocEq F T LRfun K
  W LRfun-∼ i x = idp
  u LRfun-∼ i a = ↯ (CompEq i a)
  fst (Λ LRfun-∼ g) x = ↯ (FunHomEq g x)
  snd (Λ LRfun-∼ {i} {j} g) a = =ₛ-in (=ₛ-out (Λ-eq i j g a))

  LRfunEq : LRfun == K
  LRfunEq = CosCocEq-ind F T LRfun LRfun-∼ 
