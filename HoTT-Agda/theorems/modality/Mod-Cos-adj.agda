{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Modality
open import lib.wild-cats.WildCats
open import lib.wild-cats.Ladj-2-coher
open import Coslice
open import Cos-wc
open import SIP-CosMap
open import modality.Mod-Cos

-- Every modality is a 2-coherent left adjoint.

module modality.Mod-Cos-adj where

module Mod-Adj {ℓ j} (μ : Modality ℓ) (A : Type j) where

  open Modality μ
  open MapsCos A

  Mod-cos-fctr : Functor-wc (Coslice-wc A ℓ) (Coslice-loc-wc μ A)
  obj Mod-cos-fctr X = (Mod-cos μ A X) , ◯-is-local
  arr Mod-cos-fctr = Mod-cos-fmap μ A
  id Mod-cos-fctr X = UndFun∼-to-== (Mod-cos-fmap-id μ A X)
  comp Mod-cos-fctr f g = UndFun∼-to-== (Mod-cos-fmap-∘ μ A g f)

  Loc-cos-forg-fctr : Functor-wc (Coslice-loc-wc μ A) (Coslice-wc A ℓ)
  obj Loc-cos-forg-fctr X = fst X
  arr Loc-cos-forg-fctr f = f
  id Loc-cos-forg-fctr _ = idp
  comp Loc-cos-forg-fctr _ _ = idp

  -- the adjunction in full
  Mod-cos-adj : Adjunction Mod-cos-fctr Loc-cos-forg-fctr
  fst (iso Mod-cos-adj) = Mod-cos-hom μ A
  snd (iso Mod-cos-adj {Z} {X}) = is-eq (Mod-cos-hom μ A) (Mod-cos-hom-inv μ A (snd X)) rtrip1 rtrip2
    where abstract
    
      rtrip1 : Mod-cos-hom μ A ∘ Mod-cos-hom-inv μ A {X = Z} {Y = fst X} (snd X) ∼ idf _
      rtrip1 f = UndFun∼-to-== ((λ x → ◯-rec-β (snd X) (fst f) x) , λ a → !-inv-l-assoc (◯-rec-β (snd X) (fst f) (str Z a)) (snd f a)) 
      
      rtrip2 : Mod-cos-hom-inv μ A {X = Z} {Y = fst X} (snd X) ∘ Mod-cos-hom μ A ∼ idf _
      rtrip2 f = UndFun∼-to-== ((◯-elim (λ x → =-preserves-local (snd X)) (λ x → ◯-rec-β (snd X) (fst f ∘ η) x)) , λ a →
        ap (λ p → ! p ∙ ◯-rec-β (snd X) (fst f ∘ η) (str Z a) ∙ snd f a)
          (◯-elim-β _ _ (str Z a)) ∙
        !-inv-l-assoc (◯-rec-β (snd X) (fst f ∘ η) (str Z a)) (snd f a))
      
  nat-cod Mod-cos-adj g h = UndFun∼-to-== (Mod-cos-cod μ A g h)
  nat-dom Mod-cos-adj f h = UndFun∼-to-== (Mod-cos-dom μ A f h)

  abstract
    Mod-cos-adj-2coh : ladj-is-2coher Mod-cos-adj
    Mod-cos-adj-2coh {y = y} h₁ h₂ h₃ = =ₛ-out (2coher-rot Mod-cos-adj {y = y} h₁ h₂ h₃ (Mod-cos-is-2-coher μ A h₂ h₃ h₁))
