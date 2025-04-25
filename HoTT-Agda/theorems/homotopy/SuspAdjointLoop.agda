{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.Pushout
open import lib.types.Suspension
open import lib.types.LoopSpace
open import lib.types.Homogeneous
open import lib.wild-cats.WildCat
open import lib.wild-cats.Ptd-wc
open import lib.wild-cats.Adjoint

module homotopy.SuspAdjointLoop where

module _ {i} where

  SuspFunctor : PtdFunctor i i
  obj SuspFunctor = ⊙Susp
  arr SuspFunctor = ⊙Susp-fmap
  id SuspFunctor = ⊙Susp-fmap-idf
  comp SuspFunctor f g = ⊙Susp-fmap-∘ g f
  
  LoopFunctor : PtdFunctor i i
  obj LoopFunctor = ⊙Ω
  arr LoopFunctor = ⊙Ω-fmap
  id LoopFunctor _ = ⊙Ω-fmap-idf
  comp LoopFunctor f g = ⊙Ω-fmap-∘ g f

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

  ap-cmp-into-coher-aux : {f g : Susp (de⊙ X) → de⊙ U} (H₀ : f ∼ g)
    {x : Susp (de⊙ X)} (v : x == right unit)
    → ! (
        (hmtpy-nat-∙'-r H₀ (v ∙ ! v) ∙
          ap (λ p → p ∙ ap g (v ∙ ! v) ∙' ! (H₀ x))
            (! (!-! (H₀ x)) ∙ ! (!-∙ (! (H₀ x)) idp)) ∙
          ap (λ p → ! (! (H₀ x) ∙ idp) ∙ ap g (v ∙ ! v) ∙' p)
            (! (∙-unit-r (! (H₀ x)))) ∙ idp) ∙
        ! (Ω-fmap-β (g , ! (H₀ x) ∙ idp)  (v ∙ ! v))) ∙
      ap (ap f) (!-inv-r v) ∙ idp
        ==
      ap (fst (⊙Ω-fmap (g , ! (H₀ x) ∙ idp))) (!-inv-r v) ∙
      snd (⊙Ω-fmap (g , ! (H₀ x) ∙ idp))
  ap-cmp-into-coher-aux {g = g} H₀ idp = lemma (H₀ (right unit))
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
            ==
          snd (⊙Ω-fmap (g , ! u ∙ idp))
      lemma idp = idp

  ap-cmp-into-coher : {f g : Susp (de⊙ X) → de⊙ U} (H₀ : f ∼ g)
    {gₚ : g (left unit) == f (left unit)} (H₁ : ! (H₀ (left unit)) ∙ idp == gₚ)
    → ! (
        (hmtpy-nat-∙'-r H₀ (glue (pt X) ∙ ! (glue (pt X))) ∙
        ap (λ p → p ∙ ap g (glue (pt X) ∙ ! (glue (pt X))) ∙' ! (H₀ (left unit)))
          (! (!-! (H₀ (left unit))) ∙ ! (!-∙ (! (H₀ (left unit))) idp)) ∙
        ap (λ p → ! (! (H₀ (left unit)) ∙ idp) ∙ ap g (glue (pt X) ∙ ! (glue (pt X))) ∙' p)
          (! (∙-unit-r (! (H₀ (left unit))))) ∙
        ∙-∙'-= (ap g (glue (pt X) ∙ ! (glue (pt X)))) H₁) ∙
        ! (Ω-fmap-β (g , gₚ) (glue (pt X) ∙ ! (glue (pt X))))) ∙
      ap (ap f) (!-inv-r (glue (pt X))) ∙ idp
        ==
      ap (Ω-fmap (g , gₚ)) (!-inv-r (glue (pt X))) ∙ snd (⊙Ω-fmap (g , gₚ))
  ap-cmp-into-coher H₀ idp = ap-cmp-into-coher-aux H₀ (glue (pt X))

  ap-cmp-into : {f₁ f₂ : ⊙Susp X ⊙→ U} (H : f₁ ⊙-comp f₂) → into f₁ ⊙-comp into f₂
  fst (ap-cmp-into {f₁ = (f , idp)} {f₂} H) x =
    (hmtpy-nat-∙'-r (fst H) (glue x ∙ ! (glue (pt X))) ∙
      ap (λ p → p ∙ ap (λ z → fst f₂ z) (glue x ∙ ! (glue (pt X))) ∙' ! (fst H (left unit)))
        (! (!-! (fst H (left unit))) ∙ ! (!-∙ (! (fst H (left unit))) idp)) ∙
      ap (λ p → (! (! (fst H (left unit)) ∙ idp)) ∙ ap (fst f₂) (glue x ∙ ! (glue (pt X))) ∙' p)
        (! (∙-unit-r (! (fst H (left unit))))) ∙
      ∙-∙'-= (ap (fst f₂) (glue x ∙ ! (glue (pt X)))) (snd H)) ∙
    ! (Ω-fmap-β f₂ (glue x ∙ ! (glue (pt X)))) 
  snd (ap-cmp-into {f₁ = (f , idp)} {f₂} H) = ap-cmp-into-coher (fst H) (snd H)

  {-
     This definition of ap agrees with the standard ap on the id homotopy,
     hence on all homotopies by the SIP.
  -}

  ap-cmp-into-id : (f* : ⊙Susp X ⊙→ U) → ap-cmp-into (⊙∼-id f*) ⊙→∼ ⊙∼-id (into f*)
  fst (ap-cmp-into-id (f , idp)) x = 
    ∙-unit-r (hmtpy-nat-∙'-r (λ x₁ → idp) (glue x ∙ ! (glue (pt X))) ∙ idp) ∙
    ∙-unit-r (hmtpy-nat-∙'-r (λ x₁ → idp) (glue x ∙ ! (glue (pt X)))) ∙
    hmtpy-nat-∙'-r-idp (glue x ∙ ! (glue (pt X)))
  snd (ap-cmp-into-id (f , idp)) = lemma (glue (pt X))
    where
      lemma : {x : Susp (de⊙ X)} (v : x == right unit) →
        ap (λ p → ! p ∙ ap (ap f) (!-inv-r v) ∙ idp)
        (∙-unit-r (hmtpy-nat-∙'-r (λ x₁ → idp) (v ∙ ! v) ∙ idp) ∙
        ∙-unit-r (hmtpy-nat-∙'-r (λ x₁ → idp) (v ∙ ! v)) ∙
        hmtpy-nat-∙'-r-idp (v ∙ ! v)) ∙ idp
          ==
        ap-cmp-into-coher-aux (λ x → idp) v
      lemma idp = idp

  ap-cmp-into-agree : {f* g* : ⊙Susp X ⊙→ U} (H : f* ⊙-comp g*)
    → ap into (⊙-comp-to-== H) == ⊙-comp-to-== (ap-cmp-into H)
  ap-cmp-into-agree {f*} = ⊙hom-ind f*
    (λ g* H → ap into (⊙-comp-to-== H) == ⊙-comp-to-== (ap-cmp-into H))
    (ap (ap into) (⊙-comp-to-==-β f*) ∙
    ! (ap ⊙-comp-to-== (⊙→∼-to-== (ap-cmp-into-id f*)) ∙ ⊙-comp-to-==-β (into f*)))

{-
  an explicit component-based homotopy witnessing the
  naturality of into in its first argument
-}

module _ {i i' j} {X : Ptd i} {Y : Ptd i'} {U : Ptd j} where 

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

  nat-dom-cmp : (h : X ⊙→ Y) (r : ⊙Susp Y ⊙→ U)
    → (into Y U) r ⊙∘ h ⊙-comp (into X U) (r ⊙∘ ⊙Susp-fmap h)
  fst (nat-dom-cmp (h₀ , idp) (r₀ , idp)) x = ↯ $
    ap-∙ r₀ (glue (h₀ x)) (! (glue (pt Y))) ◃∙
    ! (ap (λ p → ap r₀ (glue (h₀ x)) ∙ p) (ap (λ p → ap r₀ (! p)) (SuspFmap.merid-β h₀ (pt X)))) ◃∙
    ! (ap (λ p → ap r₀ (glue (h₀ x)) ∙ p) (ap-∘ r₀ (Susp-fmap h₀) (! (glue (pt X))) ∙
      ap (ap r₀) (ap-! (Susp-fmap h₀) (glue (pt X))))) ◃∙
    ! (ap (λ p → ap r₀ p ∙ ap (r₀ ∘ Susp-fmap h₀) (! (glue (pt X)))) (SuspFmap.merid-β h₀ x)) ◃∙
    ! ((ap (λ p → p ∙ ap (r₀ ∘ Susp-fmap h₀) (! (glue (pt X)))) (ap-∘ r₀ (Susp-fmap h₀) (glue x)))) ◃∙
    ! (ap-∙ (r₀ ∘ Susp-fmap h₀) (glue x) (! (glue (pt X)))) ◃∎
  snd (nat-dom-cmp (h₀ , idp) (r₀ , idp)) =
    ap (λ p → ! (ap-∙ r₀ (glue (h₀ (pt X))) (! (glue (h₀ (pt X)))) ∙ p) ∙
      ap (ap r₀) (!-inv-r (glue (h₀ (pt X)))) ∙ idp)
      (assoc-4-∙
        (! (ap (_∙_ (ap r₀ (glue (h₀ (pt X))))) (ap (λ p → ap r₀ (! p)) (SuspFmap.merid-β h₀ (pt X)))))
        (! (ap (_∙_ (ap r₀ (glue (h₀ (pt X))))) (ap-∘ r₀ (Susp-fmap h₀) (! (glue (pt X))) ∙
          ap (ap r₀) (ap-! (Susp-fmap h₀) (glue (pt X))))))
        (! (ap (λ p → ap r₀ p ∙ ap (r₀ ∘ Susp-fmap h₀) (! (glue (pt X)))) (SuspFmap.merid-β h₀ (pt X))))
        (! (ap (λ p → p ∙ ap (r₀ ∘ Susp-fmap h₀) (! (glue (pt X)))) (ap-∘ r₀ (Susp-fmap h₀) (glue (pt X)))))
        (! (ap-∙ (r₀ ∘ Susp-fmap h₀) (glue (pt X)) (! (glue (pt X)))))) ∙
    ap (λ p → ! (ap-∙ r₀ (glue (h₀ (pt X))) (! (glue (h₀ (pt X)))) ∙ p ∙
      ! (ap (λ p → p ∙ ap (r₀ ∘ Susp-fmap h₀) (! (glue (pt X)))) (ap-∘ r₀ (Susp-fmap h₀) (glue (pt X)))) ∙
      ! (ap-∙ (r₀ ∘ Susp-fmap h₀) (glue (pt X)) (! (glue (pt X))))) ∙
        ap (ap r₀) (!-inv-r (glue (h₀ (pt X)))) ∙ idp) (nat-dom-aux-l r₀ h₀) ∙
    nat-dom-aux-r r₀ h₀ ((glue (h₀ (pt X))))
