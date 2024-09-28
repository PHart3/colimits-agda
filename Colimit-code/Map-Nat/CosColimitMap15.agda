{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import lib.PathSeq
open import Coslice
open import Diagram
open import Colim
open import CosColimitMap01
open import CosColimitMap09
open import CosColimitMap10
open import CosColimitMap11
open import CosColimitMap12
open import CosColimitMap13
open import CosColimitMap14

module CosColimitMap15 where

module _ {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  module _ (i j : Obj Γ) (g : Hom Γ i j) (a : A) where

    open ConstrMap10.MapCoher7 δ i j g a

    open ConstrMap11.MapCoher8 δ i j g a

    open ConstrMap12.MapCoher9 δ i j g a

    open ConstrMap13.MapCoher10 δ i j g a

    open ConstrMap14.MapCoher11 δ i j g a

    open ConstrMap15.MapCoher12 δ i j g a

--  𝕪-red : 𝕪 =ₛ ap-∘-!-!-rid (cin i) right (snd (nat δ i) a) (glue (cin i a)) ◃∎
    𝕪-red = 𝕪-red0 ∙ₛ (𝕪-red1 ∙ₛ (𝕪-red2 ∙ₛ (𝕪-red3 ∙ₛ (𝕪-red4 ∙ₛ 𝕪-red5))))

