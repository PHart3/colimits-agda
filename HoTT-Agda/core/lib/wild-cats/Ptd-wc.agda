{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.Lift
open import lib.types.Unit
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

  Forg-funct-ptd : ∀ {i} → Functor-wc (Ptd-wc i) (Type-wc i)
  obj Forg-funct-ptd = de⊙
  arr Forg-funct-ptd = fst
  id Forg-funct-ptd = λ _ → idp
  comp Forg-funct-ptd = λ _ _ → idp

  Ptd-Cos-iso : ∀ {i} → (Ptd-wc i) iso-wc (Coslice-wc Unit i)
  obj (fst (fst Ptd-Cos-iso)) = Ptd-to-Cos
  arr (fst (fst Ptd-Cos-iso)) = –> Ptd-Cos-hom≃
  id (fst (fst Ptd-Cos-iso)) _ = idp
  comp (fst (fst Ptd-Cos-iso)) _ _ = idp
  fst (snd (fst Ptd-Cos-iso)) _ =
    ap (λ p → p ∙ idp) (ap (ap (–> Ptd-Cos-hom≃)) (⊙-crd∼-to-==-β _)) 
  fst (snd (snd (fst Ptd-Cos-iso))) (_ , idp) =
    ap (λ p → p ∙ idp) (ap (ap (–> Ptd-Cos-hom≃)) (⊙-crd∼-to-==-β _)) ∙ ! UndHom∼-β
  snd (snd (snd (fst Ptd-Cos-iso))) (_ , idp) (_ , idp) (_ , idp) =
    UndHom∼-β ∙ ! (ap (λ p → p ∙ idp) (ap (ap (–> Ptd-Cos-hom≃)) (⊙-crd∼-to-==-β _)))
  fst (snd Ptd-Cos-iso) = snd Ptd-Cos-≃
  snd (snd Ptd-Cos-iso) X Y = snd Ptd-Cos-hom≃

  ⊙Unit-term : ∀ {i} → is-term-wc (Ptd-wc i) (⊙Lift ⊙Unit)
  fst (has-level-apply (⊙Unit-term X)) = (λ _ → lift unit) , idp
  snd (has-level-apply (⊙Unit-term X)) _ = pair= idp (prop-has-all-paths {{=-preserves-level-instance}} _ _)

  Ptd-wc-term-contr : ∀ {i} {X : Ptd i} → is-term-wc (Ptd-wc i) X → is-contr (de⊙ X)
  Ptd-wc-term-contr {i} t = equiv-preserves-level (_ , eqv-wc-to-eqv-ty (F-equiv-wc Forg-funct-ptd (term-uniq-wc {C = Ptd-wc i} ⊙Unit-term t)))

  Ptd-wc-contr-term : ∀ {i} {X : ob (Ptd-wc i)} → is-contr (de⊙ X) → is-term-wc (Ptd-wc i) X
  fst (has-level-apply (Ptd-wc-contr-term c Y)) = (λ _ → contr-center c) , (contr-has-all-paths {{c}} _ _)
  snd (has-level-apply (Ptd-wc-contr-term c Y)) f = ⊙-crd∼-to-==
    ((λ _ → contr-has-all-paths {{c}} _ _) , (contr-has-all-paths {{=-preserves-contr c}} _ _))
