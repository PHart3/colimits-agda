{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pi
open import lib.types.Graph
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc

module lib.types.Cospan where

record Cospan {i j k : ULevel} : Type (lsucc (lmax (lmax i j) k)) where
  constructor cospan
  field
    A : Type i
    B : Type j
    C : Type k
    f : A → C
    g : B → C

record ⊙Cospan {i j k : ULevel} : Type (lsucc (lmax (lmax i j) k)) where
  constructor ⊙cospan
  field
    X : Ptd i
    Y : Ptd j
    Z : Ptd k
    f : X ⊙→ Z
    g : Y ⊙→ Z

⊙cospan-out : ∀ {i j k} → ⊙Cospan {i} {j} {k} → Cospan {i} {j} {k}
⊙cospan-out (⊙cospan X Y Z f g) =
  cospan (de⊙ X) (de⊙ Y) (de⊙ Z) (fst f) (fst g)

module _ {i j k} (D : Cospan {i} {j} {k}) where

  open Cospan D

  record Cone-csp {ℓ} (T : Type ℓ) : Type (lmax (lmax i j) (lmax k ℓ)) where
    constructor cone-csp
    field
      left : T → A
      right : T → B
      sq : f ∘ left ∼ g ∘ right
  open Cone-csp

  record Cone-csp-mor-str {ℓ₁ ℓ₂} {T₁ : Type ℓ₁} {T₂ : Type ℓ₂} (K₁ : Cone-csp T₁) (K₂ : Cone-csp T₂)
    (m : T₁ → T₂) : Type (lmax (lmax ℓ₁ ℓ₂) (lmax (lmax i j) k)) where
    constructor conecspmor
    field
      map-left : left K₂ ∘ m ∼ left K₁
      map-right : right K₂ ∘ m ∼ right K₁
      map-sq : (x : T₁) → ap f (! (map-left x)) ∙ sq K₂ (m x) ∙' ap g (map-right x) == sq K₁ x

open Cone-csp

-- SIP for cospan cones

module _ {i j k l} {D : Cospan {i} {j} {k}} {T : Type l} where

  open Cospan D

  record ConCspEq (K₁ K₂ : Cone-csp D T) : Type (lmax (lmax i j) (lmax k l)) where
    constructor concspeq
    field
      left-== : left K₂ ∼ left K₁
      right-== : right K₂ ∼ right K₁
      sq-== : (x : T) → ap f (! (left-== x)) ∙ sq K₂ x ∙' ap g (right-== x) == sq K₁ x
  open ConCspEq public

  concsp-idp : {K : Cone-csp D T} → ConCspEq K K
  left-== concsp-idp _ = idp
  right-== concsp-idp _ = idp
  sq-== concsp-idp _ = idp

  ==-to-CocEq : {K₁ K₂ : Cone-csp D T} → K₁ == K₂ → ConCspEq K₁ K₂
  ==-to-CocEq idp = concsp-idp

-- translating between diagrams over graphs and cospans

module _ {ℓ} (Δ : Diag-cspan (Type-wc ℓ)) where

  diag-to-csp : Cospan
  diag-to-csp = cospan (D₀ Δ lft) (D₀ Δ rght) (D₀ Δ mid) (D₁ Δ unit) (D₁ Δ unit)

  open Cone

  module _ {T : Type ℓ} where

    con-to-csp : Cone Δ T → Cone-csp diag-to-csp T
    left (con-to-csp K) = leg K lft
    right (con-to-csp K) = leg K rght
    sq (con-to-csp K) = app= (tri K {lft} unit ∙ ! (tri K {rght} unit))
    
    csp-to-con : Cone-csp diag-to-csp T → Cone Δ T
    leg (csp-to-con K) lft = left K 
    leg (csp-to-con K) mid = D₁ Δ unit ∘ left K
    leg (csp-to-con K) rght = right K
    tri (csp-to-con K) {lft} {mid} f = idp
    tri (csp-to-con K) {rght} {mid} unit = ! (λ= (sq K))
    tri (csp-to-con x) {lft} {lft} ()
    tri (csp-to-con x) {rght} {lft} ()
    tri (csp-to-con x) {lft} {rght} ()
    tri (csp-to-con x) {rght} {rght} ()
