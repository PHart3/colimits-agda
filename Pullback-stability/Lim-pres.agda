{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Graph
open import lib.wild-cats.WildCats
open import Cos-wc
open import SIP-Cos

-- forgetful functor from coslice preserves limits
  
module Lim-pres {j} (A : Type j) where

open MapsCos A

module _ {i} {ℓv ℓe} {G : Graph ℓv ℓe} {Δ : Diagram G (Coslice-wc A (lmax i j))} {X : Coslice (lmax i j) j A}
  {K : Cone Δ X} (lim : is-lim-wc K) where

  abstract
    Forg-cos-lim-pres : is-lim-wc (F-con (Forg-funct-cos A {i = i}) K)
    Forg-cos-lim-pres Z = ∼-preserves-equiv
      (λ f₁ → con-to-== ((λ _ → idp) , λ {t} f → 
        ap (ap (λ x₁ x₂ → fst x₁ (inl x₂)))
          (ap (λ p → ! (coe p idp) ∙ ap _ (Cone.tri K f))
            (ap (ap (λ (g , _) → (λ x →
               fst (D₁ Δ f) (fst (Cone.leg K t) (cos-map-promote A f₁ x))) ,
               (λ a → ap (fst (D₁ Δ f)) (snd (Cone.leg K t) a) ∙ snd (D₁ Δ f) a) == g))
            (!-inv-l (snd (has-level-apply UndFunHomContr)
              (((λ x → fst (D₁ Δ f) (fst (Cone.leg K t) (cos-map-promote A f₁ x))) ,
                (λ a → ap (fst (D₁ Δ f)) (snd (Cone.leg K t) a) ∙ snd (D₁ Δ f) a)) ,
               (λ _ → idp) , (λ _ → idp)))))) ∙ aux {g = f₁} {x = t} {f = f} (Cone.tri K f)))
      (snd (hom-to-lim-R lim (free-forg-adj-cos A {i})))
      where
        aux : {g : Z → ty X} {x y : Obj G} {f : Hom G x y} {c₁ c₂ : X *→ D₀ Δ y} (q : c₁ == c₂) →
          ap (λ x₁ x₂ → fst {B = λ k → (a : A) → k (inr a) == fun (D₀ Δ y) a} x₁ (inl {B = A} x₂))
            (ap (λ v →
                (λ x → fst v (cos-map-promote A {X = Z} {Y = X} g x)) ,
                (λ a → snd v a))
              q)
            ==
          ap (λ m z → m (g z)) (ap (λ k z → fst k z) q)
        aux idp = idp
