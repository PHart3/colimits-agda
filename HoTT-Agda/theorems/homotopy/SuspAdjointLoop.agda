{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.Pushout
open import lib.types.Suspension
open import lib.types.LoopSpace
open import homotopy.PtdAdjoint

module homotopy.SuspAdjointLoop where

module _ {i} where

  SuspFunctor : PtdFunctor i i
  SuspFunctor = record {
    obj = ⊙Susp;
    arr = ⊙Susp-fmap;
    id = ⊙Susp-fmap-idf;
    comp = ⊙Susp-fmap-∘}

  LoopFunctor : PtdFunctor i i
  LoopFunctor = record {
    obj = ⊙Ω;
    arr = ⊙Ω-fmap;
    id = λ _ → ⊙Ω-fmap-idf;
    comp = ⊙Ω-fmap-∘}

-- counit

  module _ (X : Ptd i) where

    η : de⊙ X → Ω (⊙Susp X)
    η x = σloop X x

    ⊙η : X ⊙→ ⊙Ω (⊙Susp X)
    ⊙η = (η , σloop-pt)

-- induced map of homs

module _ {i j} (X : Ptd i) (U : Ptd j) where

  into : ⊙Susp X ⊙→ U → X ⊙→ ⊙Ω U
  into r = ⊙Ω-fmap r ⊙∘ ⊙η X

module _ {i j} {X Y : Ptd i} where 

  nat-dom : (U : Ptd j) (r : ⊙Susp Y ⊙→ U) (h : X ⊙→ Y)
    → (into Y U) r ⊙∘ h ⊙-comp (into X U) (r ⊙∘ ⊙Susp-fmap h)
  fst (nat-dom U (r₀ , idp) (h₀ , idp)) x = ↯ (
    ap-∙ r₀ (glue (h₀ x)) (! (glue (pt Y))) ◃∙
    ! (ap (λ p → ap r₀ (glue (h₀ x)) ∙ p) (ap (λ p → ap r₀ (! p)) (SuspFmap.merid-β h₀ (pt X)))) ◃∙
    ! (ap (λ p → ap r₀ (glue (h₀ x)) ∙ p) (ap-∘ r₀ (Susp-fmap h₀) (! (glue (pt X))) ∙
      ap (ap r₀) (ap-! (Susp-fmap h₀) (glue (pt X))))) ◃∙
    ! (ap (λ p → ap r₀ p ∙ ap (r₀ ∘ Susp-fmap h₀) (! (glue (pt X)))) (SuspFmap.merid-β h₀ x)) ◃∙
    ! ((ap (λ p → p ∙ ap (r₀ ∘ Susp-fmap h₀) (! (glue (pt X)))) (ap-∘ r₀ (Susp-fmap h₀) (glue x)))) ◃∙
    ! (ap-∙ (r₀ ∘ Susp-fmap h₀) (glue x) (! (glue (pt X)))) ◃∎
    )
  snd (nat-dom U (r₀ , idp) (h₀ , idp)) = {!!}

{-
!
(ap-∙ r₀ (glue (h₀ (pt X))) (! (glue (h₀ (pt X)))) ∙
 !
 (ap (_∙_ (ap r₀ (glue (h₀ (pt X)))))
  (ap (λ p → ap r₀ (! p))
   (PushoutRec.glue-β (λ _ → north) (λ _ → south) (merid ∘ h₀)
    (pt X))))
 ∙
 !
 (ap (_∙_ (ap r₀ (glue (h₀ (pt X)))))
  (ap-∘ r₀ (Susp-fmap h₀) (! (glue (pt X))) ∙
   ap (ap r₀) (ap-! (Susp-fmap h₀) (glue (pt X)))))
 ∙
 !
 (ap (λ p → ap r₀ p ∙ ap (r₀ ∘ Susp-fmap h₀) (! (glue (pt X))))
  (PushoutRec.glue-β (λ _ → north) (λ _ → south) (merid ∘ h₀)
   (pt X)))
 ∙
 !
 (ap (λ p → p ∙ ap (r₀ ∘ Susp-fmap h₀) (! (glue (pt X))))
  (ap-∘ r₀ (Susp-fmap h₀) (glue (pt X))))
 ∙ ! (ap-∙ (r₀ ∘ Susp-fmap h₀) (glue (pt X)) (! (glue (pt X)))))
 ∙ ap (ap r₀) (!-inv-r (glue (h₀ (pt X)))) ∙ idp
=-=
ap
 (ap
  (Susp-fmap h₀))
 (!-inv-r (glue (pt X)))
 ∙ idp
-}

{- the nat-dom proof makes Susp a 2-coherent left adjoint to Loop -} 

-- module 2_coher_Susp (h₁ : ) (h₂ : ) (h₃ : ) where 

-- ap into () ⊙-comp ?

