{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import Coslice
open import Diagram-Cos
open import lib.types.Colim
open import SIP-CosCoc
open import CC-Equiv-RLR-3

module CC-Equiv-RLR-4 where

module _ {ℓv ℓe ℓ ℓd ℓc} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓd ℓ A Γ} {T : Coslice ℓc ℓ A} (K : CosCocone A F T) where

  open import CC-Equiv-RLR-0 F T K

  open ConstrE2Cont3.Equiv2d F T K

  LRfun-∼ : CosCocEq LRfun K
  W LRfun-∼ i x = idp
  u LRfun-∼ i a = ↯ (CompEq i a)
  fst (Λ LRfun-∼ g) x = ↯ (FunHomEq g x)
  snd (Λ LRfun-∼ {i} {j} g) a = =ₛ-in (=ₛ-out (Λ-eq i j g a))

  LRfunEq : LRfun == K
  LRfunEq = CosCocEq-to-== LRfun-∼ 
