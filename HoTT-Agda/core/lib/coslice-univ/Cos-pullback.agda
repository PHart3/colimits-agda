{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.SIP
open import lib.types.Sigma
open import lib.types.Cospan
open import lib.types.Pullback

-- construction of coslice pullbacks
  
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

  cospan-forg : Cospan
  Cospan.A cospan-forg = ty X
  Cospan.B cospan-forg = ty Y
  Cospan.C cospan-forg = ty Z
  Cospan.f cospan-forg = fst f
  Cospan.g cospan-forg = fst g

  pb-forg-ty : Type (lmax (lmax i k) l)
  pb-forg-ty = Pullback cospan-forg

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

  -- equality of cones with tip pb-forg
  module Cone-pb-id {K₁ : CosCone-csp cspan pb-forg} where

  {-
    ConePbContr-aux :
      is-contr
        (Σ (Σ (ty X → ty Y) (λ K₂ → fst f ∼ g))
          (λ (h , K) → Σ ((a : A) → h (str X a) == str Y a) (λ p → ((a : A) → ! (K (str X a)) ∙ (snd f a) == p a))))
    ConePbContr-aux =
      equiv-preserves-level
        ((Σ-contr-red
          {P = λ (h , K) → Σ ((a : A) → h (str X a) == str Y a) (λ p → ((a : A) → ! (K (str X a)) ∙ (snd f a) == p a))}
          (funhom-contr {f = fst f}))⁻¹)
        {{equiv-preserves-level ((Σ-emap-r (λ _ → app=-equiv))) {{pathfrom-is-contr (snd f)}}}}

    ConePbContr : is-contr (Σ (CosCone-csp cspan pb-forg) (λ K₂ → K₁ ∼-con-pb K₂))
    ConePbContr = equiv-preserves-level lemma {{ConePbContr-aux}}
      where
        lemma :
          ?
            ≃
          Σ (CosCone-csp cspan pb-forg) (λ K₂ → K₁∼-con-pb K₂)
        lemma =
          equiv
            ?
            ?
            ?
            ?

    abstract
      ConePbContr-abs : is-contr (Σ (CosCone-csp cspan pb-forg) (λ K₂ → K₁∼-con-pb K₂))
      ConePbContr-abs = ConePbContr

    ConePb-ind : ∀ {ℓ} (P : (K₂: CosCone-csp cspan pb-forg) → (K₁∼-con-pb K₂→ Type ℓ))
      → P K₁ ∼-cpb-id → {K₂: CosCone-csp cspan pb-forg} (p : K₁∼-con-pb K₂) → P K₂p
    ConePb-ind P = ID-ind-map {b = ∼-cpb-id} P ConePbContr-abs

    ConePb∼-from-== : {K₂: CosCone-csp cspan pb-forg} → K₁ == K₂→ K₁∼-con-pb K₂
    ConePb∼-from-== idp = ∼-cpb-id

    ConePb∼-to-== : {K₂: CosCone-csp cspan pb-forg} → (K₁∼-con-pb K₂) → K₁ == K₂
    ConePb∼-to-== {K₂} = ConePb-ind (λ K₂ _ → K₁ == K₂) idp

    ConePb∼-β : ConePb∼-to-== ∼-cpb-id == idp
    ConePb∼-β = ID-ind-map-β (λ K₂ _ → K₁ == K₂) ConePbContr-abs idp

    ConePb-∼-==-≃ : {K₂: CosCone-csp cspan pb-forg} → (K₁ == K₂) ≃ (K₁∼-con-pb K₂)
    ConePb-∼-==-≃ = equiv ConePb∼-from-== ConePb∼-to-==
      (ConePb-ind (λ K₂ H → ConePb∼-from-== (ConePb∼-to-== H) == H) (ap ConePb∼-from-== ConePb∼-β)) aux
      where
        aux : ∀ {K₂} (e : K₁ == K₂) → ConePb∼-to-== (ConePb∼-from-== e) == e
        aux idp = ConePb∼-β
  -}
