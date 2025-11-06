{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.wild-cats.WildCat
open import lib.wild-cats.Iso-wc
open import Cos-wc
open import SIP-CosMap

module lib.wild-cats.Ptd-wc where

  Ptd-wc : (i : ULevel) → WildCat
  ob (Ptd-wc i) = Ptd i
  hom (Ptd-wc _) X Y = X ⊙→ Y
  id₁ (Ptd-wc _) X = ⊙idf X
  _◻_ (Ptd-wc _) g f = g ⊙∘ f
  ρ (Ptd-wc _) f = ⊙-crd∼-to-== (⊙∘-runit f) 
  lamb (Ptd-wc _) f = ⊙-crd∼-to-== (⊙∘-lunit f)
  α (Ptd-wc _) h g f = ⊙-crd∼-to-== (⊙∘-assoc-crd h g f)

  PtdFunctor : (i j : ULevel) → Type (lsucc (lmax i j))
  PtdFunctor i j = Functor-wc (Ptd-wc i) (Ptd-wc j)

  Ptd-Cos-iso : ∀ {i} → (Ptd-wc i) iso-wc (Coslice-wc Unit i)
  obj (fst (fst Ptd-Cos-iso)) = Ptd-to-Cos
  arr (fst (fst Ptd-Cos-iso)) = –> Ptd-Cos-hom≃
  id (fst (fst Ptd-Cos-iso)) _ = idp
  comp (fst (fst Ptd-Cos-iso)) _ _ = idp
  fst (snd (fst Ptd-Cos-iso)) _ =
    ap (λ p → p ∙ idp) (ap (ap (–> Ptd-Cos-hom≃)) (⊙-crd∼-to-==-β _)) 
  fst (snd (snd (fst Ptd-Cos-iso))) (_ , idp) =
    ap (λ p → p ∙ idp) (ap (ap (–> Ptd-Cos-hom≃)) (⊙-crd∼-to-==-β _)) ∙ ! UndFun∼-β
  snd (snd (snd (fst Ptd-Cos-iso))) (_ , idp) (_ , idp) (_ , idp) =
    UndFun∼-β ∙ ! (ap (λ p → p ∙ idp) (ap (ap (–> Ptd-Cos-hom≃)) (⊙-crd∼-to-==-β _)))
  fst (snd Ptd-Cos-iso) = snd Ptd-Cos-≃
  snd (snd Ptd-Cos-iso) X Y = snd Ptd-Cos-hom≃
