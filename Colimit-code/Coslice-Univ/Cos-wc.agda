{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.wild-cats.WildCats
open import SIP-Cos

-- coslice universe as wild category
  
module Cos-wc where

open import Coslice public

module _ {j} (A : Type j) where

  open MapsCos A
  
  Coslice-wc : ∀ i → WildCat
  ob (Coslice-wc i) = Coslice i j A
  hom (Coslice-wc i) X Y = X *→ Y
  id₁ (Coslice-wc i) X = (idf (ty X)) , (λ _ → idp)
  _◻_ (Coslice-wc i) g f = g ∘* f
  ρ (Coslice-wc i) f = idp
  lamb (Coslice-wc i) f = UndFun∼-to-== ((λ _ → idp) , (λ a → ! (∙-unit-r (snd f a)) ∙ ap (λ p → p ∙ idp) (! (ap-idf (snd f a)))))
  α (Coslice-wc i) h g f = UndFun∼-to-== (*→-assoc h g f)

  -- 2-coherence

  triangle-wc-Cos : ∀ {i} → triangle-wc (Coslice-wc i)
  triangle-wc-Cos = prove_later where postulate prove_later : _

  pentagon-wc-Cos : ∀ {i} → pentagon-wc (Coslice-wc i)
  pentagon-wc-Cos = prove_later where postulate prove_later : _

  -- forgetful functor

  Forg-funct-cos : ∀ {i} → Functor-wc (Coslice-wc (lmax i j)) (Type-wc (lmax i j))
  obj Forg-funct-cos = ty
  arr Forg-funct-cos f = fst f
  id Forg-funct-cos _ = idp
  comp Forg-funct-cos _ _ = idp

  Free-funct-cos : ∀ {i} → Functor-wc (Type-wc (lmax i j)) (Coslice-wc (lmax i j))
  obj Free-funct-cos X = *[ (Coprod X A) , inr ]
  fst (arr Free-funct-cos f) (inl x) = inl (f x)
  fst (arr Free-funct-cos f) (inr x) = inr x
  snd (arr Free-funct-cos f) _ = idp
  id Free-funct-cos X = UndFun∼-to-== ((λ { (inl _) → idp ; (inr _) → idp }) , (λ _ → idp))
  comp Free-funct-cos f g = UndFun∼-to-== ((λ { (inl _) → idp ; (inr _) → idp }) , (λ _ → idp))

  free-forg-adj-cos : ∀ {i} → Adjunction (Free-funct-cos {i = i}) (Forg-funct-cos {i = i})
  iso (free-forg-adj-cos {i}) {a = U} {x = V} = free-forg-cos A
  nat-cod free-forg-adj-cos _ _ = idp
  nat-dom free-forg-adj-cos _ _ = idp

