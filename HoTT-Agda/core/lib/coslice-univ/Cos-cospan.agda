{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import Coslice

-- cospans and cones over them in coslices of Type

module Cos-cospan {j} {A : Type j} where

open MapsCos A

record CosCospan {i k l} : Type (lmax (lsucc i) (lmax (lsucc k) (lmax (lsucc l) j))) where
  constructor cos-cospan
  field
    X : Coslice i j A
    Y : Coslice k j A
    Z : Coslice l j A
    f : X *→ Z
    g : Y *→ Z

module _ {i k l} (D : CosCospan {i} {k} {l}) where

  open CosCospan D

  record CosCone-csp {ℓ} (T : Coslice ℓ j A) : Type (lmax i (lmax k (lmax l (lmax ℓ j)))) where
    constructor cone-csp
    field
      left : T *→ X
      right : T *→ Y
      sq : < T > f ∘* left ∼ g ∘* right

  open CosCone-csp

  -- pre-composition map
  coscoc-precmp : ∀ {ℓ₁ ℓ₂} {T : Coslice ℓ₁ j A} {V : Coslice ℓ₂ j A} → CosCone-csp T → (V *→ T) → CosCone-csp V
  left (coscoc-precmp κ h) = left κ ∘* h
  right (coscoc-precmp κ h) = right κ ∘* h
  sq (coscoc-precmp κ h) = *→-assoc-rev f (left κ) h ∼∘-cos pre-∘*-∼ h (sq κ) ∼∘-cos *→-assoc g (right κ) h
