{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Lift
open import lib.wild-cats.WildCats
open import Coslice
open import SIP-Cos

-- coslice universe as wild category
  
module Cos-wc where

module _ {j} (A : Type j) where

  open MapsCos A
  
  Coslice-wc : ∀ i → WildCat
  ob (Coslice-wc i) = Coslice i j A
  hom (Coslice-wc i) X Y = X *→ Y
  id₁ (Coslice-wc i) X = (idf (ty X)) , (λ _ → idp)
  _◻_ (Coslice-wc i) g f = g ∘* f
  ρ (Coslice-wc i) f = idp
  lamb (Coslice-wc i) f = UndFun∼-to-== ((λ _ → idp) , (λ a → ! (∙-unit-r (snd f a)) ∙ ap (λ p → p ∙ idp) (! (ap-idf (snd f a)))))
  α (Coslice-wc i) h g f = UndFun∼-to-== ((λ _ → idp) , (λ a → assoc-ap-∙ (fst h) (fst g) (fst f) (snd f a) (snd g a) (snd h a)))

  Forg-funct-cos : ∀ {i} → Functor-wc (Coslice-wc (lmax i j)) (Type-wc (lmax i j))
  obj Forg-funct-cos = Lift {j = j} ∘ ty
  arr Forg-funct-cos f = Lift-fmap (fst f)
  id Forg-funct-cos _ = idp
  comp Forg-funct-cos _ _ = idp

  Free-funct-cos : ∀ {i} → Functor-wc (Type-wc (lmax i j)) (Coslice-wc (lmax i j))
  obj Free-funct-cos X = *[ (Coprod X A) , inr ]
  fst (arr Free-funct-cos f) (inl x) = inl (f x)
  fst (arr Free-funct-cos f) (inr x) = inr x
  snd (arr Free-funct-cos f) _ = idp
  id Free-funct-cos X = UndFun∼-to-== ((λ { (inl _) → idp ; (inr _) → idp }) , (λ _ → idp))
  comp Free-funct-cos f g = UndFun∼-to-== ((λ { (inl _) → idp ; (inr _) → idp }) , (λ _ → idp))
  
  free-forg-lift : ∀ {i} → {U : Type (lmax i j)} {V : Coslice (lmax i j) j A} (f : Coprod U A → ty V) → Coprod U A → Lift {j = j} (ty V)
  free-forg-lift f (inl u) = lift (f (inl u))
  free-forg-lift f (inr a) = lift (f (inr a))

  free-forg-lower : ∀ {i} → {U : Type (lmax i j)} {V : Coslice (lmax i j) j A} (f : Coprod U A → Lift {j = j} (ty V)) → Coprod U A → ty V
  free-forg-lower f (inl u) = lower (f (inl u))
  free-forg-lower f (inr a) = lower (f (inr a))

  free-forg-adj-cos : ∀ {i} → Adjunction (Free-funct-cos {i = i}) (Forg-funct-cos {i = i})
  iso (free-forg-adj-cos {i}) {a = U} {x = V} = free-forg-cos A ∘e eqv-aux
    where
      eqv-aux : (*[ Coprod U A , inr ] *→ V) ≃ (*[ Coprod U A , inr ] *→ *[ Lift (ty V) , lift ∘ fun V ])
      eqv-aux = equiv
        (λ (f , p) → free-forg-lift {i} {U = U} {V = V} f , λ a → ap lift (p a))
        (λ (f , p) → free-forg-lower {i} {U = U} {V = V} f , λ a → ap lower (p a))
        (λ (f , p) → UndFun∼-to-== ((λ { (inl u) → idp ; (inr a) → idp }) , λ _ → ∘-ap lift lower _ ∙ ap-idf _))
        λ (f , p) → UndFun∼-to-== ((λ { (inl u) → idp ; (inr a) → idp }) , λ a → ∘-ap lower lift _ ∙ ap-idf _)
  nat-cod free-forg-adj-cos _ _ = idp
  nat-dom free-forg-adj-cos _ _ = idp 
