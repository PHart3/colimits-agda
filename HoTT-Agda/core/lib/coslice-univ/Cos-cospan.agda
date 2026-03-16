{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.SIP
open import lib.types.Sigma
open import Coslice

-- cospans and cones over them in coslices of Type

module Cos-cospan {j} {A : Type j} where

open MapsCos A

record CosCospan {i k l} : Type (lmax (lsucc i) (lmax (lsucc k) (lmax (lsucc l) j))) where
  constructor cos-cospan
  field
    X : Coslice i j A
    Y : Coslice k j A
    Z : Coslice l j A
    f : X *→ Z
    g : Y *→ Z

module _ {i k l} (D : CosCospan {i} {k} {l}) where

  open CosCospan D

  record CosCone-csp {ℓ} (T : Coslice ℓ j A) : Type (lmax i (lmax k (lmax l (lmax ℓ j)))) where
    constructor cos-cone
    field
      left : T *→ X
      right : T *→ Y
      sq : < T > f ∘* left ∼ g ∘* right

  open CosCone-csp

  -- pre-composition map
  coscoc-precmp : ∀ {ℓ₁ ℓ₂} {T : Coslice ℓ₁ j A} {V : Coslice ℓ₂ j A} → CosCone-csp T → (V *→ T) → CosCone-csp V
  left (coscoc-precmp κ h) = left κ ∘* h
  right (coscoc-precmp κ h) = right κ ∘* h
  sq (coscoc-precmp κ h) = *→-assoc-rev f (left κ) h ∼∘-cos pre-∘*-∼ h (sq κ) ∼∘-cos *→-assoc g (right κ) h

-- SIP for cones over coslice cospans
module Cone-pb-id {i k l ℓ} {D : CosCospan {i} {k} {l}} {T : Coslice ℓ j A} where

  open CosCone-csp

  infixr 80 _∼con-pb_
  record _∼con-pb_ (K₁ : CosCone-csp D T) (K₂ : CosCone-csp D T) : Type (lmax i (lmax k (lmax l (lmax ℓ j)))) where
    constructor ∼conpb
    field
      ∼left : < T > left K₂ ∼ left K₁
      ∼right : < T > right K₁ ∼ right K₂
      ∼sq : < T > post-∘*-∼ (CosCospan.f D) ∼left ∼∘-cos sq K₁ ∼∘'-cos post-∘*-∼ (CosCospan.g D) ∼right ∼∼ sq K₂

  open _∼con-pb_

  ∼cpb-id-coh : ∀{u} {X : Type u} {x y z : X} {t : z == y} (r₁ : x == y) (r₂ : z == x) (r₃ : r₂ ∙ r₁ == t) →
    (ap (λ p → p ∙ r₁) (! (∙-unit-r r₂)) ∙ ∙-assoc r₂ idp r₁) ∙ ap (λ q → q) r₃ ∙ idp
      ==
    r₃
  ∼cpb-id-coh _ idp r₃ = ap-idf-idp r₃

  ∼cpb-id : {K : CosCone-csp D T} → K ∼con-pb K
  ∼left (∼cpb-id {K}) = cos∼id (left K)
  ∼right (∼cpb-id {K}) = cos∼id (right K)
  fst (∼sq (∼cpb-id {K})) = λ _ → idp
  snd (∼sq (∼cpb-id {K})) a = ∼cpb-id-coh
    (ap (fst (CosCospan.f D)) (snd (left K) a) ∙ snd (CosCospan.f D) a) (! (fst (sq K) (str T a))) (snd (sq K) a)

  module _ {K₁ : CosCone-csp D T} where

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

    ConePbContr : is-contr (Σ (CosCone-csp D T) (λ K₂ → K₁ ∼con-pb K₂))
    ConePbContr = equiv-preserves-level lemma {{ConePbContr-aux}}
      where
        lemma :
          ?
            ≃
          Σ (CosCone-csp D T) (λ K₂ → K₁ ∼con-pb K₂)
        lemma =
          equiv
            ?
            ?
            ?
            ?

    abstract
      ConePbContr-abs : is-contr (Σ (CosCone-csp D T) (λ K₂ → K₁ ∼con-pb K₂))
      ConePbContr-abs = ConePbContr

    ConePb-ind : ∀ {ℓ} (P : (K₂: CosCone-csp D T) → (K₁ ∼con-pb K₂→ Type ℓ))
      → P K₁ ∼cpb-id → {K₂: CosCone-csp D T} (p : K₁ ∼con-pb K₂) → P K₂p
    ConePb-ind P = ID-ind-map {b = ∼cpb-id} P ConePbContr-abs

    ConePb∼-from-== : {K₂: CosCone-csp D T} → K₁ == K₂→ K₁ ∼con-pb K₂
    ConePb∼-from-== idp = ∼cpb-id

    ConePb∼-to-== : {K₂: CosCone-csp D T} → (K₁ ∼con-pb K₂) → K₁ == K₂
    ConePb∼-to-== {K₂} = ConePb-ind (λ K₂ _ → K₁ == K₂) idp

    ConePb∼-β : ConePb∼-to-== ∼cpb-id == idp
    ConePb∼-β = ID-ind-map-β (λ K₂ _ → K₁ == K₂) ConePbContr-abs idp

    ConePb-∼-==-≃ : {K₂: CosCone-csp D T} → (K₁ == K₂) ≃ (K₁ ∼con-pb K₂)
    ConePb-∼-==-≃ = equiv ConePb∼-from-== ConePb∼-to-==
      (ConePb-ind (λ K₂ H → ConePb∼-from-== (ConePb∼-to-== H) == H) (ap ConePb∼-from-== ConePb∼-β)) aux
      where
        aux : ∀ {K₂} (e : K₁ == K₂) → ConePb∼-to-== (ConePb∼-from-== e) == e
        aux idp = ConePb∼-β
  -}
