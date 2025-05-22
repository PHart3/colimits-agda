{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import Coslice
open import Diagram
open import FTID-Cos
open import lib.types.Colim
open import CC-Equiv-LRL-0
open import CC-Equiv-LRL-5
open import CC-Equiv-LRL-6

module CC-Equiv-LRL-7 where

module _ {ℓv ℓe ℓ ℓd ℓc} {Γ : Graph ℓv ℓe} {A : Type ℓ} (F : CosDiag ℓd ℓ A Γ) (T : Coslice ℓc ℓ A) where

  open Constr F T

  module _ (f : P → ty T) (fₚ : (a : A) → f (left a) == fun T a) where

    RLfunEqFun : f ∼ fst (RLfun (f , fₚ))
    RLfunEqFun =
      PushoutMapEq f (fst (RLfun (f , fₚ))) fₚ (RfunEq (f , fₚ))
      (colimE (λ i a → ↯ (Constr6.𝕣 F T (f , fₚ) i a))
        (λ i j g a →
          from-transp-g (λ z → (! (ap f (glue z)) ∙ fₚ ([id] z)) ∙ ap (fst (RLfun (f , fₚ))) (glue z)
            ==
          RfunEq (f , fₚ) (ψ z)) (cglue g a) (=ₛ-out (Constr7.DiagCoher7.RLfunHtpy F T i j f fₚ g a))))

    RLfunEqBP : (a : A) → ! (RLfunEqFun (left a)) ∙ fₚ a == idp
    RLfunEqBP a = !-inv-l (fₚ a)

    RLfun-∼ : [ A , Cos P left ] (f , fₚ) ∼ RLfun (f , fₚ)
    fst RLfun-∼ = RLfunEqFun
    snd RLfun-∼ = RLfunEqBP

    RLfunEq : (f , fₚ) == RLfun (f , fₚ)
    RLfunEq = PtFunEq (f , fₚ) RLfun-∼

    
