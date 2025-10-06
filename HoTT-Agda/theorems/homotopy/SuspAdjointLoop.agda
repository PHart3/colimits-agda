{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.cubical.Square
open import lib.types.Pointed
open import lib.types.Pushout
open import lib.types.Suspension
open import lib.types.LoopSpace
open import lib.types.Homogeneous
open import lib.wild-cats.WildCats

module homotopy.SuspAdjointLoop where

SuspFunctor : ∀ {i} → PtdFunctor i i
obj SuspFunctor = ⊙Susp
arr SuspFunctor = ⊙Susp-fmap
id SuspFunctor = ⊙Susp-fmap-idf
comp SuspFunctor f g = ⊙Susp-fmap-∘ g f

LoopFunctor : ∀ {i} → PtdFunctor i i
obj LoopFunctor = ⊙Ω
arr LoopFunctor = ⊙Ω-fmap
id LoopFunctor _ = ⊙Ω-fmap-idf
comp LoopFunctor f g = ⊙Ω-fmap-∘ g f

module _ {i} (X : Ptd i) where

  η : de⊙ X → Ω (⊙Susp X)
  η x = σloop X x

  module E = SuspRec (pt X) (pt X) (idf _)

  ε : de⊙ (⊙Susp (⊙Ω X)) → de⊙ X
  ε = E.f

  ⊙η : X ⊙→ ⊙Ω (⊙Susp X)
  ⊙η = (η , σloop-pt)

  ⊙ε : ⊙Susp (⊙Ω X) ⊙→ X
  ⊙ε = (ε , idp)

module _ {i} where

  η-natural : {X Y : Ptd i} (f : X ⊙→ Y)
    → ⊙η Y ⊙∘ f == ⊙Ω-fmap (⊙Susp-fmap f) ⊙∘ ⊙η X
  η-natural {X = X} (f , idp) = ⊙λ='
    (λ x → ! $
      ap-∙ (Susp-fmap f) (merid x) (! (merid (pt X)))
      ∙ SuspFmap.merid-β f x
        ∙2 (ap-! (Susp-fmap f) (merid (pt X))
            ∙ ap ! (SuspFmap.merid-β f (pt X))))
    (pt-lemma (Susp-fmap f) (merid (pt X)) (SuspFmap.merid-β f (pt X)))
    where
    pt-lemma : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
      {x y : A} (p : x == y) {q : f x == f y} (α : ap f p == q)
      → !-inv-r q == ap (ap f) (!-inv-r p) ∙ idp
        [ _== idp ↓ ! (ap-∙ f p (! p) ∙ α ∙2 (ap-! f p ∙ ap ! α)) ]
    pt-lemma f idp idp = idp

  ε-natural : {X Y : Ptd i} (f : X ⊙→ Y)
    → ⊙ε Y ⊙∘ ⊙Susp-fmap (⊙Ω-fmap f) == f ⊙∘ ⊙ε X
  ε-natural (f , idp) = ⊙λ='
    (SuspElim.f idp idp
      (λ p → ↓-='-from-square $ vert-degen-square $
        ap-∘ (ε _) (Susp-fmap (ap f)) (merid p)
        ∙ ap (ap (ε _)) (SuspFmap.merid-β (ap f) p)
        ∙ E.merid-β _ (ap f p)
        ∙ ap (ap f) (! (E.merid-β _ p))
        ∙ ∘-ap f (ε _) (merid p)))
    idp

  εΣ-Ση : (X : Ptd i) → ⊙ε (⊙Susp X) ⊙∘ ⊙Susp-fmap (⊙η X) == ⊙idf _
  εΣ-Ση X = ⊙λ='
    (SuspElim.f
      idp
      (merid (pt X))
      (λ x → ↓-='-from-square $
        (ap-∘ (ε (⊙Susp X)) (Susp-fmap (η X)) (merid x)
         ∙ ap (ap (ε (⊙Susp X))) (SuspFmap.merid-β (η X) x)
         ∙ E.merid-β _ (merid x ∙ ! (merid (pt X))))
        ∙v⊡ square-lemma (merid x) (merid (pt X))
        ⊡v∙ ! (ap-idf (merid x))))
    idp
    where
    square-lemma : ∀ {i} {A : Type i} {x y z : A}
      (p : x == y) (q : z == y)
      → Square idp (p ∙ ! q) p q
    square-lemma idp idp = ids

  Ωε-ηΩ : (X : Ptd i) → ⊙Ω-fmap (⊙ε X) ⊙∘ ⊙η (⊙Ω X) == ⊙idf _
  Ωε-ηΩ X = ⊙λ='
    (λ p → ap-∙ (ε X) (merid p) (! (merid idp))
         ∙ (E.merid-β X p ∙2 (ap-! (ε X) (merid idp) ∙ ap ! (E.merid-β X idp)))
         ∙ ∙-unit-r _)
    (pt-lemma (ε X) (merid idp) (E.merid-β X idp))
    where
    pt-lemma : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
      {x y : A} (p : x == y) {q : f x == f y} (α : ap f p == q)
      → ap (ap f) (!-inv-r p) ∙ idp == idp
        [ _== idp ↓ ap-∙ f p (! p) ∙ (α ∙2 (ap-! f p ∙ ap ! α)) ∙ !-inv-r q ]
    pt-lemma f idp idp = idp

  SuspLoopAdj-unit : CounitUnitAdjoint SuspFunctor LoopFunctor
  SuspLoopAdj-unit = counitunitadjoint ⊙η ⊙ε η-natural ε-natural εΣ-Ση Ωε-ηΩ

  SuspLoopAdj : Adjunction SuspFunctor LoopFunctor
  SuspLoopAdj = counit-unit-to-hom SuspLoopAdj-unit

module _ {i j} (X : Ptd i) (U : Ptd j) where

  -- component morphism of adjunction
  into : ⊙Susp X ⊙→ U → X ⊙→ ⊙Ω U
  into r = ⊙Ω-fmap r ⊙∘ ⊙η X

  ap-cmp-into-coher-aux : {f g : Susp (de⊙ X) → de⊙ U} (H₀ : f ∼ g)
    {x : Susp (de⊙ X)} (v : x == right unit)
    → ! (
        (hmtpy-nat-∙' H₀ (v ∙ ! v) ∙
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
        (hmtpy-nat-∙' H₀ (glue (pt X) ∙ ! (glue (pt X))) ∙
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

  ap-cmp-into : {f₁ f₂ : ⊙Susp X ⊙→ U} (H : f₁ ⊙-crd∼ f₂) → into f₁ ⊙-crd∼ into f₂
  fst (ap-cmp-into {f₁ = (f , idp)} {f₂} H) x =
    (hmtpy-nat-∙' (fst H) (glue x ∙ ! (glue (pt X))) ∙
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
    ∙-unit-r (hmtpy-nat-∙' (λ x₁ → idp) (glue x ∙ ! (glue (pt X))) ∙ idp) ∙
    ∙-unit-r (hmtpy-nat-∙' (λ x₁ → idp) (glue x ∙ ! (glue (pt X)))) ∙
    hmtpy-nat-∙'-idp (glue x ∙ ! (glue (pt X)))
  snd (ap-cmp-into-id (f , idp)) = lemma (glue (pt X))
    where
      lemma : {x : Susp (de⊙ X)} (v : x == right unit) →
        ap (λ p → ! p ∙ ap (ap f) (!-inv-r v) ∙ idp)
        (∙-unit-r (hmtpy-nat-∙' (λ x₁ → idp) (v ∙ ! v) ∙ idp) ∙
        ∙-unit-r (hmtpy-nat-∙' (λ x₁ → idp) (v ∙ ! v)) ∙
        hmtpy-nat-∙'-idp (v ∙ ! v)) ∙ idp
          ==
        ap-cmp-into-coher-aux (λ x → idp) v
      lemma idp = idp

  ap-cmp-into-agree : {f* g* : ⊙Susp X ⊙→ U} (H : f* ⊙-crd∼ g*)
    → ap into (⊙-crd∼-to-== H) == ⊙-crd∼-to-== (ap-cmp-into H)
  ap-cmp-into-agree {f*} = ⊙hom-ind f*
    (λ g* H → ap into (⊙-crd∼-to-== H) == ⊙-crd∼-to-== (ap-cmp-into H))
    (ap (ap into) (⊙-crd∼-to-==-β f*) ∙
    ! (ap ⊙-crd∼-to-== (⊙→∼-to-== (ap-cmp-into-id f*)) ∙ ⊙-crd∼-to-==-β (into f*)))

{-
  an explicit component-based homotopy witnessing the
  naturality of into in its first argument
-}

module _ {i i' j} {X : Ptd i} {Y : Ptd i'} {U : Ptd j} where

  module _ (r₀ : Susp (de⊙ Y) → de⊙ U) (h₀ : de⊙ X → de⊙ Y) where

    nat-dom-aux-r : {v : Susp (de⊙ Y)} (τ : left unit == v) →
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
      (τ : ap (Susp-fmap h₀) (glue (pt X)) == v) →
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
    → (into Y U) r ⊙∘ h ⊙-crd∼ (into X U) (r ⊙∘ ⊙Susp-fmap h)
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
    ap (λ p →
      ! (ap-∙ r₀ (glue (h₀ (pt X))) (! (glue (h₀ (pt X)))) ∙ p ∙
        ! (ap (λ p → p ∙ ap (r₀ ∘ Susp-fmap h₀) (! (glue (pt X)))) (ap-∘ r₀ (Susp-fmap h₀) (glue (pt X)))) ∙
        ! (ap-∙ (r₀ ∘ Susp-fmap h₀) (glue (pt X)) (! (glue (pt X))))) ∙
        ap (ap r₀) (!-inv-r (glue (h₀ (pt X)))) ∙ idp)
      (nat-dom-aux-l r₀ h₀) ∙
    nat-dom-aux-r r₀ h₀ ((glue (h₀ (pt X))))

-- adjunction with nat-dom replaced by explicit version
SuspLoopAdj-exp : ∀ {i} → Adjunction (SuspFunctor {i}) (LoopFunctor {i})
iso SuspLoopAdj-exp = iso SuspLoopAdj
nat-cod SuspLoopAdj-exp = nat-cod SuspLoopAdj
nat-dom SuspLoopAdj-exp h r = ⊙-crd∼-to-== (nat-dom-cmp h r)
