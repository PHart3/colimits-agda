{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import Coslice
open import Diagram-Cos
open import lib.types.Colim
open import Cocone

module CC-Equiv-LRL-0 where

module Constr {ℓv ℓe ℓ ℓd ℓc} {Γ : Graph ℓv ℓe} {A : Type ℓ} (F : CosDiag ℓd ℓ A Γ) (T : Coslice ℓc ℓ A) where

  open Id Γ A public

  open Maps F public

  open Recc T public

  RLfun : (< A > Cos P left *→ T) →  (< A > Cos P left *→ T)
  RLfun f* = recCosCoc (PostComp-cos ColCoC f*) 

  RfunEq : (f* : < A > Cos P left *→ T) → fst f* ∘ right ∼ fst (RLfun f*) ∘ right
  RfunEq (f , fₚ) =
    colimE
      (λ i x → idp)
      (λ i → λ j → λ g → λ x → from-transp-g (λ z → (f ∘ right) z == (fst (RLfun (f , fₚ)) ∘ right) z) (cglue g x) (↯ (V i j g x)))
    module _ where
      V : (i j : Obj Γ) (g : Hom Γ i j) (x : ty (F # i)) →
        transport (λ z → (f ∘ right) z == (fst (RLfun (f , fₚ)) ∘ right) z) (cglue g x) idp =-= idp
      V i j g x =
        transport (λ z → (f ∘ right) z == (fst (RLfun (f , fₚ)) ∘ right) z) (cglue g x) idp
          =⟪ transp-pth {f = f ∘ right} {g = fst (RLfun (f , fₚ)) ∘ right} (cglue g x)  idp ⟫
        ! (ap (f ∘ right) (cglue g x)) ∙ ap (reccForg (PostComp-cos ColCoC (f , fₚ))) (cglue g x)
          =⟪ ap (λ p → ! (ap (f ∘ right) (cglue g x)) ∙ p) (recc-βr (PostComp-cos ColCoC (f , fₚ)) g x) ⟫
        ! (ap (f ∘ right) (cglue g x)) ∙ (ap f (ap right (cglue g x)))
          =⟪ cmp-inv-l (cglue g x) ⟫ 
        idp ∎∎
