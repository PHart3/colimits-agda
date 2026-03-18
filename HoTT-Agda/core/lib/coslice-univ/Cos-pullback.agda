{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.Equivalence2
open import lib.types.Sigma
open import lib.types.Cospan
open import lib.types.Pullback

-- construction of coslice pullbacks (in extensional form) from standard pullbacks in Type
  
module Cos-pullback {j} {A : Type j} where

open import Coslice public
open import Cos-cospan

open MapsCos A

module _ {i k l} {X : Coslice i j A} {Y : Coslice k j A} {Z : Coslice l j A} (f : X *→ Z) (g : Y *→ Z) where

  open CosCone-csp

  cspan : CosCospan
  CosCospan.X cspan = X
  CosCospan.Y cspan = Y
  CosCospan.Z cspan = Z
  CosCospan.f cspan = f
  CosCospan.g cspan = g

  cspan-forg : Cospan
  cspan-forg = coscospan-forg cspan

  pb-forg-ty : Type (lmax (lmax i k) l)
  pb-forg-ty = Pullback cspan-forg

  pb-forg-pt : A → pb-forg-ty
  Pullback.a (pb-forg-pt a) = str X a
  Pullback.b (pb-forg-pt a) = str Y a
  Pullback.h (pb-forg-pt a) = snd f a ∙ ! (snd g a)

  pb-forg : Coslice (lmax (lmax i k) l) j A
  pb-forg = *[ pb-forg-ty , pb-forg-pt ]

  pb-cos-cone : CosCone-csp cspan pb-forg
  left pb-cos-cone = Pullback.a , (λ _ → idp)
  right pb-cos-cone = Pullback.b , (λ _ → idp)
  fst (sq pb-cos-cone) = Pullback.h
  snd (sq pb-cos-cone) a = !-inv-l-∙-!-! (snd f a) (snd g a)

  open CosCone-SIP

  module Pb-cos-contr {ℓ} {V : Coslice ℓ j A} (K : CosCone-csp cspan V) where

    private
      pb-forg-precmp-Σ =
        [ d ∈ (ty V → pb-forg-ty) ] ×
          [ h₁ ∈ (fst (left K)) ∼ Pullback.a ∘ d ] × [ h₂ ∈ (Pullback.b ∘ d ∼ fst (right K)) ] ×
            ((v : ty V) → ap (fst f) (h₁ v) ∙ Pullback.h (d v) ∙' ap (fst g) (h₂ v) == fst (sq K) v)

      pb-cos-precmp-fib =
        [ (d , h₁ , h₂ , τ) ∈ pb-forg-precmp-Σ ] ×
          ([ dₚ ∈ (d ∘ str V ∼ pb-forg-pt) ] ×
            ([ H₁ ∈ ((a : A) → ! (h₁ (str V a)) ∙ snd (left K) a == ap (Pullback.a) (dₚ a) ∙ idp) ] ×
              ([ H₂ ∈ ((a : A) → ! (h₂ (str V a)) ∙ ap (Pullback.b) (dₚ a) ∙ idp == snd (right K) a) ] ×
                ((a : A) →
                  ap (λ p → ! p ∙ snd (f ∘* left K) a) (! (τ (str V a))) ∙
                  snd (post-∘*-∼ f (h₁ , H₁) ∼∘-cos
                    (*→-assoc-rev f (left pb-cos-cone) (d , dₚ) ∼∘-cos
                    pre-∘*-∼ (d , dₚ) (sq pb-cos-cone) ∼∘'-cos
                    *→-assoc g (right pb-cos-cone) (d , dₚ)) ∼∘'-cos
                  post-∘*-∼ g (h₂ , H₂)) a
                    ==
                  snd (sq K) a))))
                  
    abstract
      pb-cos-precmp-fib-contr : is-contr (pb-cos-precmp-fib)
      pb-cos-precmp-fib-contr = equiv-preserves-level
        ((Σ-contr-red-any (limcsp-mor-alt-contr {K = coscone-forg pb-cos-cone} (stdpb-is-abspb cspan-forg) (coscone-forg K))
          ((λ v → pullback (fst (left K) v) (fst (right K) v) (fst (sq K) v)) , ((λ _ → idp) , ((λ _ → idp) , λ _ → idp))))⁻¹)
        {{equiv-preserves-level (
          Σ-emap-l (λ dₚ →
            [ H₁ ∈ ((a : A) → snd (left K) a == ap (Pullback.a) (dₚ a) ∙ idp) ] ×
              [ H₂ ∈ ((a : A) → ap (Pullback.b) (dₚ a) ∙ idp == snd (right K) a) ] ×
                ((a : A) →
                  snd (post-∘*-∼ f ((λ _ → idp) , H₁) ∼∘-cos
                    (*→-assoc-rev f (left pb-cos-cone) (_ , dₚ) ∼∘-cos
                    pre-∘*-∼ (_ , dₚ) (sq pb-cos-cone) ∼∘'-cos
                    *→-assoc g (right pb-cos-cone) (_ , dₚ)) ∼∘'-cos
                  post-∘*-∼ g ((λ _ → idp) , H₂)) a
                    ==
                  snd (sq K) a))
            ((map-to-stdpb-== cspan-forg _ pb-forg-pt)⁻¹) ∘e
            {!aux!})
          {{{!!}}}}}
          where abstract

            aux :
              {!!}
                ≃
              [ ((∼-a , ∼-b) , κ) ∈
                (Σ
                 ((Pullback.a ∘
                   (λ z →
                      pullback (fst (left K) (str V z)) (fst (right K) (str V z))
                      (fst (sq K) (str V z)))
                   ∼ Pullback.a ∘ pb-forg-pt)
                  ×
                  (Pullback.b ∘
                   (λ z →
                      pullback (fst (left K) (str V z)) (fst (right K) (str V z))
                      (fst (sq K) (str V z)))
                   ∼ Pullback.b ∘ pb-forg-pt))
                 (λ (∼-a , ∼-b) → (a : A) →
                    fst (sq K) (str V a) ∙ ap (Cospan.g cspan-forg) (∼-b a)
                      ==
                    ap (Cospan.f cspan-forg) (∼-a a) ∙ snd f a ∙ ! (snd g a))) ] ×
                [ H₁ ∈ ((a : A) → snd (left K) a == ∼-a a ∙ idp) ] ×
                  [ H₂ ∈ ((a : A) → ∼-b a ∙ idp == snd (right K) a) ] ×
                    ((a : A) →
                      _
                        ==
                      snd (sq K) a)
            aux = {!!}

    pb-cos-precmp-fib-≃ : pb-cos-precmp-fib ≃ hfiber (coscoc-precmp pb-cos-cone) K
    pb-cos-precmp-fib-≃ = Σ-emap-r (λ h → ConePb-∼-==-≃ ⁻¹) ∘e aux
      where abstract
        aux : pb-cos-precmp-fib ≃ Σ (V *→ pb-forg) (λ h → coscoc-precmp pb-cos-cone h ∼con-pb K)
        aux = equiv
          (λ ((d , h₁ , h₂ , τ) , dₚ , H₁ , H₂ , ν) → (d , dₚ) , (∼conpb (h₁ , H₁) (h₂ , H₂) (τ , ν)))
          (λ ((d , dₚ) , (∼conpb (h₁ , H₁) (h₂ , H₂) (τ , ν))) → ((d , h₁ , h₂ , τ) , dₚ , H₁ , H₂ , ν))
          (λ _ → idp)
          λ _ → idp

    abstract
      pb-cos-precmp-contr : is-contr (hfiber (coscoc-precmp pb-cos-cone) K)
      pb-cos-precmp-contr = equiv-preserves-level pb-cos-precmp-fib-≃ {{pb-cos-precmp-fib-contr}}

  abstract
    CosPb : ∀ {ℓ} → is-cospb-abs ℓ pb-cos-cone
    CosPb V = contr-map-is-equiv pb-cos-precmp-contr where open Pb-cos-contr
