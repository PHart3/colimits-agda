{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.wild-cats.WildCat
open import Coslice
open import SIP-Cos

-- coslice universe as wild category
  
module Cos-wc {j} (A : Type j) where

  open MapsCos A
  
  Coslice-wc : ∀ {i} → WildCat
  ob (Coslice-wc {i}) = Coslice i j A
  hom (Coslice-wc {i}) X Y = X *→ Y
  id₁ (Coslice-wc {i}) X = (idf (ty X)) , (λ _ → idp)
  _◻_ (Coslice-wc {i}) g f = g ∘* f
  ρ (Coslice-wc {i}) f = idp
  lamb (Coslice-wc {i}) f = UndFun∼-to-== ((λ _ → idp) , (λ a → ! (∙-unit-r (snd f a)) ∙ ap (λ p → p ∙ idp) (! (ap-idf (snd f a)))))
  α (Coslice-wc {i}) h g f = UndFun∼-to-== ((λ _ → idp) , (λ a → assoc-ap-∙ (fst h) (fst g) (fst f) (snd f a) (snd g a) (snd h a)))
