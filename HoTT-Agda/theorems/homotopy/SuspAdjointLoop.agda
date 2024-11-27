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

-- induced map of hom types

module _ {i j} (X : Ptd i) (U : Ptd j) where

  into : ⊙Susp X ⊙→ U → X ⊙→ ⊙Ω U
  into r = ⊙Ω-fmap r ⊙∘ ⊙η X

  ap-comp-into-coher-aux : {f g : Susp (de⊙ X) → de⊙ U} (H₀ : f ∼ g)
    {x : Susp (de⊙ X)} (v : x == right unit)
    → ! (
        (hmpty-nat-∙'-r H₀ (v ∙ ! v) ∙
          ap (λ p → p ∙ ap g (v ∙ ! v) ∙' ! (H₀ x))
            (! (!-! (H₀ x)) ∙ ! (!-∙ (! (H₀ x)) idp)) ∙
          ap (λ p → ! (! (H₀ x) ∙ idp) ∙ ap g (v ∙ ! v) ∙' p)
            (! (∙-unit-r (! (H₀ x)))) ∙ idp) ∙
        ! (Ω-fmap-β (g , ! (H₀ x) ∙ idp)  (v ∙ ! v))) ∙
      ap (ap f) (!-inv-r v) ∙ idp
      =-=
      ap (fst (⊙Ω-fmap (g , ! (H₀ x) ∙ idp))) (!-inv-r v) ∙
      snd (⊙Ω-fmap (g , ! (H₀ x) ∙ idp))
  ap-comp-into-coher-aux {g = g} H₀ idp = lemma (H₀ (right unit))
    where
      lemma : {x : de⊙ U} (u : x == g (right unit))
        → ! (
          ((! (!-inv-r u) ∙
          ap (_∙_ u) (! (∙'-unit-l (! u)))) ∙
          ap (λ p → p ∙ idp ∙' ! u)
            (! (!-! u) ∙ ! (!-∙ (! u) idp)) ∙
          ap (λ p → ! (! u ∙ idp) ∙ idp ∙' p)
            (! (∙-unit-r (! u))) ∙ idp) ∙
          ! (Ω-fmap-β (g , ! u ∙ idp) idp)) ∙ idp
          =-=
          snd (⊙Ω-fmap (g , ! u ∙ idp))
      lemma idp = idp ◃∎

  ap-comp-into-coher : {f g : Susp (de⊙ X) → de⊙ U} (H₀ : f ∼ g)
    {gₚ : g (left unit) == f (left unit)} (H₁ : ! (H₀ (left unit)) ∙ idp == gₚ)
    → ! (
        (hmpty-nat-∙'-r H₀ (glue (pt X) ∙ ! (glue (pt X))) ∙
        ap (λ p → p ∙ ap g (glue (pt X) ∙ ! (glue (pt X))) ∙' ! (H₀ (left unit)))
          (! (!-! (H₀ (left unit))) ∙ ! (!-∙ (! (H₀ (left unit))) idp)) ∙
        ap (λ p → ! (! (H₀ (left unit)) ∙ idp) ∙ ap g (glue (pt X) ∙ ! (glue (pt X))) ∙' p)
          (! (∙-unit-r (! (H₀ (left unit))))) ∙
        ∙-∙'-= (ap g (glue (pt X) ∙ ! (glue (pt X)))) H₁) ∙
        ! (Ω-fmap-β (g , gₚ) (glue (pt X) ∙ ! (glue (pt X))))) ∙
      ap (ap f) (!-inv-r (glue (pt X))) ∙ idp
      =-=
      ap (Ω-fmap (g , gₚ)) (!-inv-r (glue (pt X))) ∙ snd (⊙Ω-fmap (g , gₚ))
  ap-comp-into-coher H₀ idp = ap-comp-into-coher-aux H₀ (glue (pt X))

  ap-comp-into : {f₁ f₂ : ⊙Susp X ⊙→ U} (H : f₁ ⊙-comp f₂) → into f₁ ⊙-comp into f₂
  fst (ap-comp-into {f₁ = (f , idp)} {f₂} H) x =
    (hmpty-nat-∙'-r (fst H) (glue x ∙ ! (glue (pt X))) ∙
      ap (λ p → p ∙ ap (λ z → fst f₂ z) (glue x ∙ ! (glue (pt X))) ∙' ! (fst H (left unit)))
        (! (!-! (fst H (left unit))) ∙ ! (!-∙ (! (fst H (left unit))) idp)) ∙
      ap (λ p → (! (! (fst H (left unit)) ∙ idp)) ∙ ap (fst f₂) (glue x ∙ ! (glue (pt X))) ∙' p)
        (! (∙-unit-r (! (fst H (left unit))))) ∙
      ∙-∙'-= (ap (fst f₂) (glue x ∙ ! (glue (pt X)))) (↯ (snd H))) ∙
    ! (Ω-fmap-β f₂ (glue x ∙ ! (glue (pt X)))) 
  snd (ap-comp-into {f₁ = (f , idp)} {f₂} H) = ap-comp-into-coher (fst H) (↯ (snd H))

{-
  an explicit component-based homotopy witnessing the
  naturality of into in its first argument
-}

module _ {i j} {X Y : Ptd i} {U : Ptd j} where 

  module _ (r₀ : Susp (de⊙ Y) → de⊙ U) (h₀ : de⊙ X → de⊙ Y) where

    nat-dom-aux-r : {v : Susp (de⊙ Y)} (τ : left unit == v)
      →
      ! (ap-∙ r₀ τ (! τ) ∙
        (ap-!-inv r₀ τ ∙ ! (cmp-inv-r (glue (pt X)))) ∙
        ! (ap (λ p → p ∙ ap (r₀ ∘ Susp-fmap h₀) (! (glue (pt X))))
        (ap-∘ r₀ (Susp-fmap h₀) (glue (pt X)))) ∙
        ! (ap-∙ (r₀ ∘ Susp-fmap h₀) (glue (pt X)) (! (glue (pt X))))) ∙
      ap (ap r₀) (!-inv-r τ) ∙ idp
      ==
      ap (ap (r₀ ∘ Susp-fmap h₀)) (!-inv-r (glue (pt X))) ∙ idp
    nat-dom-aux-r idp = ap-!-∘-∙-rid-coher r₀ (Susp-fmap h₀) (glue (pt X))

    nat-dom-aux-l2 : {v : Susp-fmap h₀ (left unit) == Susp-fmap h₀ (right unit)}
      (τ : ap (Susp-fmap h₀) (glue (pt X)) == v)
      →
      ! (ap (_∙_ (ap r₀ v)) (ap (λ p → ap r₀ (! p)) τ)) ∙
      ! (ap (_∙_ (ap r₀ v)) (ap-∘ r₀ (Susp-fmap h₀) (! (glue (pt X))) ∙
        ap (ap r₀) (ap-! (Susp-fmap h₀) (glue (pt X))))) ∙
      ! (ap (λ p → ap r₀ p ∙ ap (r₀ ∘ Susp-fmap h₀) (! (glue (pt X)))) τ)
      ==
      ap-!-inv r₀ v ∙ ! (cmp-inv-r (glue (pt X)))
    nat-dom-aux-l2 idp = ap-!-∘-rid-coher r₀ (Susp-fmap h₀) (glue (pt X))
    
    nat-dom-aux-l : 
      ! (ap (_∙_ (ap r₀ (glue (h₀ (pt X)))))
        (ap (λ p → ap r₀ (! p))
        (SuspFmap.merid-β h₀ (pt X)))) ∙
      ! (ap (_∙_ (ap r₀ (glue (h₀ (pt X)))))
        (ap-∘ r₀ (Susp-fmap h₀) (! (glue (pt X))) ∙
        ap (ap r₀) (ap-! (Susp-fmap h₀) (glue (pt X))))) ∙
      ! (ap (λ p → ap r₀ p ∙ ap (r₀ ∘ Susp-fmap h₀) (! (glue (pt X))))
        (SuspFmap.merid-β h₀ (pt X)))
      ==
      ap-!-inv r₀ ((merid ∘ h₀) (pt X)) ∙ ! (cmp-inv-r {f = Susp-fmap h₀} {g = r₀} (glue (pt X))) 
    nat-dom-aux-l = nat-dom-aux-l2 (SuspFmap.merid-β h₀ (pt X)) 

  nat-dom : (h : X ⊙→ Y) (r : ⊙Susp Y ⊙→ U)
    → (into Y U) r ⊙∘ h ⊙-comp (into X U) (r ⊙∘ ⊙Susp-fmap h)
  fst (nat-dom (h₀ , idp) (r₀ , idp)) x = ↯ (
    ap-∙ r₀ (glue (h₀ x)) (! (glue (pt Y))) ◃∙
    ! (ap (λ p → ap r₀ (glue (h₀ x)) ∙ p) (ap (λ p → ap r₀ (! p)) (SuspFmap.merid-β h₀ (pt X)))) ◃∙
    ! (ap (λ p → ap r₀ (glue (h₀ x)) ∙ p) (ap-∘ r₀ (Susp-fmap h₀) (! (glue (pt X))) ∙
      ap (ap r₀) (ap-! (Susp-fmap h₀) (glue (pt X))))) ◃∙
    ! (ap (λ p → ap r₀ p ∙ ap (r₀ ∘ Susp-fmap h₀) (! (glue (pt X)))) (SuspFmap.merid-β h₀ x)) ◃∙
    ! ((ap (λ p → p ∙ ap (r₀ ∘ Susp-fmap h₀) (! (glue (pt X)))) (ap-∘ r₀ (Susp-fmap h₀) (glue x)))) ◃∙
    ! (ap-∙ (r₀ ∘ Susp-fmap h₀) (glue x) (! (glue (pt X)))) ◃∎
    )
  snd (nat-dom (h₀ , idp) (r₀ , idp)) =
    ap (λ p → ! (ap-∙ r₀ (glue (h₀ (pt X))) (! (glue (h₀ (pt X)))) ∙ p) ∙
      ap (ap r₀) (!-inv-r (glue (h₀ (pt X)))) ∙ idp)
      (assoc-4-∙
        (! (ap (_∙_ (ap r₀ (glue (h₀ (pt X))))) (ap (λ p → ap r₀ (! p)) (SuspFmap.merid-β h₀ (pt X)))))
        (! (ap (_∙_ (ap r₀ (glue (h₀ (pt X))))) (ap-∘ r₀ (Susp-fmap h₀) (! (glue (pt X))) ∙
          ap (ap r₀) (ap-! (Susp-fmap h₀) (glue (pt X))))))
        (! (ap (λ p → ap r₀ p ∙ ap (r₀ ∘ Susp-fmap h₀) (! (glue (pt X)))) (SuspFmap.merid-β h₀ (pt X))))
        (! (ap (λ p → p ∙ ap (r₀ ∘ Susp-fmap h₀) (! (glue (pt X)))) (ap-∘ r₀ (Susp-fmap h₀) (glue (pt X)))))
        (! (ap-∙ (r₀ ∘ Susp-fmap h₀) (glue (pt X)) (! (glue (pt X)))))) ◃∙
    ap (λ p → ! (ap-∙ r₀ (glue (h₀ (pt X))) (! (glue (h₀ (pt X)))) ∙ p ∙
      ! (ap (λ p → p ∙ ap (r₀ ∘ Susp-fmap h₀) (! (glue (pt X)))) (ap-∘ r₀ (Susp-fmap h₀) (glue (pt X)))) ∙
      ! (ap-∙ (r₀ ∘ Susp-fmap h₀) (glue (pt X)) (! (glue (pt X))))) ∙
        ap (ap r₀) (!-inv-r (glue (h₀ (pt X)))) ∙ idp) (nat-dom-aux-l r₀ h₀) ◃∙
    nat-dom-aux-r r₀ h₀ ((glue (h₀ (pt X)))) ◃∎

{- the nat-dom proof makes Susp a 2-coherent left adjoint to Loop -} 

module _ {i} {X : Ptd i} {Y : Ptd i} {Z : Ptd i} {W : Ptd i} where 


  -- unfolded version of naturality square for Susp-fmap-∘

  module _ (f₂ : de⊙ Z → de⊙ X) (f₃ : de⊙ W → de⊙ Z) (f₁ : Susp (de⊙ X) → de⊙ Y)
    (x : de⊙ W) where 

    Susp-fmap-∘-sq-unf : 
      ap (λ z → f₁ (Susp-fmap f₂ (Susp-fmap f₃ z))) (glue x ∙ ! (glue (pt W)))
        =-=
      ap (λ z → f₁ (Susp-fmap (f₂ ∘ f₃) z)) (glue x ∙ ! (glue (pt W)))
    Susp-fmap-∘-sq-unf = 
      ap (λ z → f₁ (Susp-fmap f₂ (Susp-fmap f₃ z))) (glue x ∙ ! (glue (pt W)))
        =⟪ ap-∙ (λ z → f₁ (Susp-fmap f₂ (Susp-fmap f₃ z))) (glue x) (! (glue (pt W))) ⟫
      ap (λ z → f₁ (Susp-fmap f₂ (Susp-fmap f₃ z))) (glue x) ∙
      ap (λ z → f₁ (Susp-fmap f₂ (Susp-fmap f₃ z))) (! (glue (pt W)))
        =⟪ ap (λ p → ap (λ z → f₁ (Susp-fmap f₂ (Susp-fmap f₃ z))) (glue x) ∙ p)
             (ap-! (λ z → f₁ (Susp-fmap f₂ (Susp-fmap f₃ z))) (glue (pt W))) ⟫
      ap (λ z → f₁ (Susp-fmap f₂ (Susp-fmap f₃ z))) (glue x) ∙
      ! (ap (λ z → f₁ (Susp-fmap f₂ (Susp-fmap f₃ z))) (glue (pt W)))
        =⟪ ap (λ p → ap (λ z → f₁ (Susp-fmap f₂ (Susp-fmap f₃ z))) (glue x) ∙ ! p)
             (ap-∘-∘ f₁ (Susp-fmap f₂) (Susp-fmap f₃) (glue (pt W))) ⟫
      ap (λ z → f₁ (Susp-fmap f₂ (Susp-fmap f₃ z))) (glue x) ∙
      ! (ap f₁ (ap (Susp-fmap f₂) (ap (Susp-fmap f₃) (glue (pt W)))))
        =⟪ ap (λ p → p ∙ ! (ap f₁ (ap (Susp-fmap f₂) (ap (Susp-fmap f₃) (glue (pt W))))))
            (ap-∘-∘ f₁ (Susp-fmap f₂) (Susp-fmap f₃) (glue x)) ⟫
      ap f₁ (ap (Susp-fmap f₂) (ap (Susp-fmap f₃) (glue x))) ∙
      ! (ap f₁ (ap (Susp-fmap f₂) (ap (Susp-fmap f₃) (glue (pt W)))))
        =⟪ ap (λ p → p ∙ ! (ap f₁ (ap (Susp-fmap f₂) (ap (Susp-fmap f₃) (glue (pt W)))))) (
             ap (ap f₁) (ap (ap (Susp-fmap f₂)) (SuspFmap.merid-β f₃ x))) ⟫
      ap f₁ (ap (Susp-fmap f₂) ((merid ∘ f₃) x)) ∙
      ! (ap f₁ (ap (Susp-fmap f₂) (ap (Susp-fmap f₃) (glue (pt W)))))
        =⟪ ap (λ p → ap f₁ (ap (Susp-fmap f₂) ((merid ∘ f₃) x)) ∙ ! p) (
             ap (ap f₁) (ap (ap (Susp-fmap f₂)) (SuspFmap.merid-β f₃ (pt W)))) ⟫
      ap f₁ (ap (Susp-fmap f₂) ((merid ∘ f₃) x)) ∙
      ! (ap f₁ (ap (Susp-fmap f₂) ((merid ∘ f₃) (pt W))))
        =⟪ ap (λ p → p ∙ ! (ap f₁ (ap (Susp-fmap f₂) ((merid ∘ f₃) (pt W))))) (
             ap (ap f₁) (SuspFmap.merid-β f₂ (f₃ x))) ⟫
      ap f₁ ((merid ∘ f₂) (f₃ x)) ∙
      ! (ap f₁ (ap (Susp-fmap f₂) ((merid ∘ f₃) (pt W))))
        =⟪ ap (λ p → ap f₁ ((merid ∘ f₂) (f₃ x)) ∙ ! p) (
             ap (ap f₁) (SuspFmap.merid-β f₂ (f₃ (pt W)))) ⟫
      ap f₁ ((merid ∘ f₂) (f₃ x)) ∙ ! (ap f₁ ((merid ∘ f₂) (f₃ (pt W))))
        =⟪ ap (λ p → ap f₁ ((merid ∘ f₂) (f₃ x)) ∙ ! p) (ap (ap f₁) (! (
             SuspFmap.merid-β (f₂ ∘ f₃) (pt W)))) ⟫
      ap f₁ ((merid ∘ f₂) (f₃ x)) ∙ ! (ap f₁ (ap (Susp-fmap (f₂ ∘ f₃)) (glue (pt W))))
        =⟪ ! (ap (λ p → ap f₁ ((merid ∘ f₂) (f₃ x)) ∙ ! p) (
             ap-∘ f₁ (Susp-fmap (f₂ ∘ f₃)) (glue (pt W)))) ⟫
      ap f₁ ((merid ∘ f₂ ∘ f₃) x) ∙
      ! (ap (λ z → f₁ (Susp-fmap (f₂ ∘ f₃) z)) (glue (pt W)))
        =⟪ ! (ap (λ p → p ∙ ! (ap (λ z → f₁ (Susp-fmap (f₂ ∘ f₃) z)) (glue (pt W)))) (
             ap (ap f₁) (SuspFmap.merid-β (f₂ ∘ f₃) x))) ⟫
      ap f₁ (ap (Susp-fmap (f₂ ∘ f₃)) (glue x)) ∙
      ! (ap (λ z → f₁ (Susp-fmap (f₂ ∘ f₃) z)) (glue (pt W)))
        =⟪ ! (ap (λ p → p ∙ ! (ap (λ z → f₁ (Susp-fmap (f₂ ∘ f₃) z)) (glue (pt W))))
             (ap-∘ f₁ (Susp-fmap (f₂ ∘ f₃)) (glue x))) ⟫
      ap (λ z → f₁ (Susp-fmap (f₂ ∘ f₃) z)) (glue x) ∙
      ! (ap (λ z → f₁ (Susp-fmap (f₂ ∘ f₃) z)) (glue (pt W)))
        =⟪ ! (ap (λ p → ap (λ z → f₁ (Susp-fmap (f₂ ∘ f₃) z)) (glue x) ∙ p) (
             ap-! (λ z → f₁ (Susp-fmap (f₂ ∘ f₃) z)) (glue (pt W)))) ⟫
      ap (λ z → f₁ (Susp-fmap (f₂ ∘ f₃) z)) (glue x) ∙
      ap (λ z → f₁ (Susp-fmap (f₂ ∘ f₃) z)) (! (glue (pt W)))
        =⟪ ! (ap-∙ (λ z → f₁ (Susp-fmap (f₂ ∘ f₃) z)) (glue x) (! (glue (pt W)))) ⟫
      ap (λ z → f₁ (Susp-fmap (f₂ ∘ f₃) z)) (glue x ∙ ! (glue (pt W))) ∎∎

    Susp-fmap-∘-sq-rw : 
      (hmpty-nat-∙'-r (λ x₁ → ap f₁ (! (Susp-fmap-∘ f₂ f₃ x₁)))
        (glue x ∙ ! (glue (pt W))) ∙ idp) ∙ idp
        ==
      ↯ (Susp-fmap-∘-sq-unf)
    Susp-fmap-∘-sq-rw = {!!}

{-
  -- proof of 2-coherence
  two_coher_Susp : (h₁ : ⊙Susp X ⊙→ Y) (h₂ : Z ⊙→ X) (h₃ : W ⊙→ Z) →
    !-⊙∼ (⊙∘-assoc-comp (into X Y h₁) h₂ h₃) ∙⊙∼
    ⊙∘-pre h₃ (nat-dom h₂ h₁) ∙⊙∼
    nat-dom h₃ (h₁ ⊙∘ ⊙Susp-fmap h₂) ∙⊙∼
    ap-comp-into W Y (⊙∘-assoc-comp h₁ (⊙Susp-fmap h₂) (⊙Susp-fmap h₃) ∙⊙∼
      ⊙∘-post h₁ (!-⊙∼ ((Susp-fmap-∘ (fst h₂) (fst h₃)) , idp ◃∎))) ∙⊙∼
    !-⊙∼ (nat-dom (h₂ ⊙∘ h₃) h₁)
      ⊙→∼
    ⊙∼-id ((into X Y h₁) ⊙∘ h₂ ⊙∘ h₃)
  fst (two_coher_Susp (f₁ , idp) (f₂ , idp) (f₃ , idp)) x = {!!}
  snd (two_coher_Susp (f₁ , idp) (f₂ , idp) (f₃ , idp)) = {!!}
-}

{-

(ap-∙ f₁ (glue (f₂ (f₃ x))) (! (glue (f₂ (f₃ (pt W))))) ∙
! (ap (_∙_ (ap f₁ (glue (f₂ (f₃ x))))) (ap (λ p → ap f₁ (! p))
  (SuspFmap.merid-β f₂ (f₃ (pt W))))) ∙
! (ap (_∙_ (ap f₁ (glue (f₂ (f₃ x)))))
  (ap-∘ f₁ (Susp-fmap f₂) (! (glue (f₃ (pt W)))) ∙
  ap (ap f₁) (ap-! (Susp-fmap f₂) (glue (f₃ (pt W)))))) ∙
! (ap (λ p → ap f₁ p ∙ ap (f₁ ∘ Susp-fmap f₂) (! (glue (f₃ (pt W)))))
  (SuspFmap.merid-β f₂ (f₃ x))) ∙
! (ap (λ p → p ∙ ap (f₁ ∘ Susp-fmap f₂) (! (glue (f₃ (pt W)))))
  (ap-∘ f₁ (Susp-fmap f₂) (glue (f₃ x)))) ∙
! (ap-∙ (f₁ ∘ Susp-fmap f₂) (glue (f₃ x)) (! (glue (f₃ (pt W)))))) ∙
(ap-∙ (f₁ ∘ (Susp-fmap f₂)) (glue (f₃ x)) (! (glue (f₃ (pt W)))) ∙
! (ap (_∙_ (ap (f₁ ∘ (Susp-fmap f₂)) (glue (f₃ x))))
  (ap (λ p → ap (f₁ ∘ (Susp-fmap f₂)) (! p))
  (SuspFmap.merid-β f₃ (pt W)))) ∙
! (ap (_∙_ (ap (f₁ ∘ (Susp-fmap f₂)) (glue (f₃ x))))
  (ap-∘ (f₁ ∘ (Susp-fmap f₂)) (Susp-fmap f₃) (! (glue (pt W))) ∙
  ap (ap (f₁ ∘ (Susp-fmap f₂))) (ap-! (Susp-fmap f₃) (glue (pt W))))) ∙
! (ap (λ p → ap (f₁ ∘ (Susp-fmap f₂)) p ∙
  ap (f₁ ∘ (Susp-fmap f₂) ∘ Susp-fmap f₃) (! (glue (pt W))))
  (SuspFmap.merid-β f₃ x)) ∙
! (ap (λ p → p ∙ ap (f₁ ∘ (Susp-fmap f₂) ∘ Susp-fmap f₃)
  (! (glue (pt W)))) (ap-∘ (f₁ ∘ (Susp-fmap f₂)) (Susp-fmap f₃)
  (glue x))) ∙
! (ap-∙ (f₁ ∘ (Susp-fmap f₂) ∘ Susp-fmap f₃)
  (glue x) (! (glue (pt W))))) ∙
((hmpty-nat-∙'-r (λ x₁ → ap f₁ (! (Susp-fmap-∘ f₂ f₃ x₁)))
  (glue x ∙ ! (glue (pt W))) ∙ idp) ∙ idp) ∙
! (ap-∙ f₁ (glue (f₂ ∘ f₃ x)) (! (glue (f₂ ∘ f₃ (pt W)))) ∙
! (ap (_∙_ (ap f₁ (glue (f₂ ∘ f₃ x)))) (ap (λ p → ap f₁ (! p))
  (SuspFmap.merid-β (f₂ ∘ f₃) (pt W)))) ∙
! (ap (_∙_ (ap f₁ (glue (f₂ ∘ f₃ x)))) (ap-∘ f₁ (Susp-fmap (f₂ ∘ f₃))
  (! (glue (pt W))) ∙ ap (ap f₁)
  (ap-! (Susp-fmap (f₂ ∘ f₃)) (glue (pt W))))) ∙
! (ap (λ p → ap f₁ p ∙ ap (f₁ ∘ Susp-fmap (f₂ ∘ f₃))
  (! (glue (pt W)))) (SuspFmap.merid-β (f₂ ∘ f₃) x)) ∙
! (ap (λ p → p ∙ ap (f₁ ∘ Susp-fmap (f₂ ∘ f₃)) (! (glue (pt W))))
  (ap-∘ f₁ (Susp-fmap (f₂ ∘ f₃)) (glue x))) ∙
! (ap-∙ (f₁ ∘ Susp-fmap (f₂ ∘ f₃)) (glue x) (! (glue (pt W)))))
=₂
idp ◃∎

-}

