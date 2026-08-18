{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.PtdMap-conv
open import lib.types.Join
open import lib.types.LoopSpace
open import lib.types.Homogeneous
open import lib.wild-cats.WildCats

-- wild adjunction between the unary pointed join (X ⊙* -) and (X ⊙–→ ⊙Ω(-))  

module homotopy.Join.JoinAdjointLoopCod where

module JoinAdjLoop-units {i} (X : Ptd i) {j} (Y : Ptd j) where

  ⊙η : Y ⊙→ X ⊙–→ ⊙Ω (X ⊙* Y)
  fst (fst ⊙η y) x = jglue (pt X) (pt Y) ∙ ! (jglue x (pt Y)) ∙ jglue x y ∙ ! (jglue (pt X) y) 
  snd (fst ⊙η y) = !-inv-r-twice (jglue (pt X) (pt Y)) (jglue (pt X) y)
  snd ⊙η = ⊙-crd∼-to-== $
    (λ x → !-inv-r-twice-mid (jglue (pt X) (pt Y)) (jglue x (pt Y))) ,
    ap (λ p → ! (!-inv-r-twice-mid (jglue (pt X) (pt Y)) (jglue (pt X) (pt Y))) ∙ p)
      (!-inv-r-twice-coh (jglue (pt X) (pt Y))) ∙
    !-inv-l (!-inv-r-twice-mid (jglue (pt X) (pt Y)) (jglue (pt X) (pt Y)))

  ⊙ε : X ⊙* (X ⊙–→ ⊙Ω Y) ⊙→ Y
  fst ⊙ε = Join-rec (λ _ → pt Y) (λ _ → pt Y) (λ x (f , _) → f x)
  snd ⊙ε = idp

module JoinAdjLoop-units-coh {i} (X : Ptd i) where

  open JoinAdjLoop-units X public

  η-natural : ∀ {j k} {Z : Ptd j} {Y : Ptd k} (f : Z ⊙→ Y)
    → ⊙η Y ⊙∘ f == ⊙hom-cod-fmap (⊙Ω-fmap (jmap⊙-un X f)) ⊙∘ ⊙η Z
  η-natural {Z = Z} (f , idp) = ⊙-crd∼-to-== $
    ⊙→homog∼ ((λ _ → idp) , idp) (⊙→-homog-cod loop-homog)
    (λ z → ⊙-crd∼-to-== $
      ⊙→homog∼ idp loop-homog
        (λ x → !
          (ap-∙!∙∙! _ (jglue (pt X) (pt Z)) (jglue x (pt Z)) (jglue x z) (jglue (pt X) z) ∙
          ap4 (λ p₁ p₂ p₃ p₄ → p₁ ∙ ! p₂ ∙ p₃ ∙ ! p₄)
            (glue-β _ _ _ (pt X) (pt Z))
            (glue-β _ _ _ x (pt Z))
            (glue-β _ _ _ x z)
            (glue-β _ _ _ (pt X) z))))
    where open JoinRec

  abstract
    Ωcodε-ηΩcod : ∀ {j} (Y : Ptd j) → ⊙hom-cod-fmap (⊙Ω-fmap (⊙ε Y)) ⊙∘ ⊙η (X ⊙–→ ⊙Ω Y) == ⊙idf _
    Ωcodε-ηΩcod Y = ⊙-crd∼-to-== $
      ⊙→homog∼ ((λ _ → idp) , idp) (⊙→-homog-cod loop-homog)
      (λ (p , q) → ⊙-crd∼-to-== $
        ⊙→homog∼ idp loop-homog
          (λ x →
            ap-∙!∙∙! _ (jglue _ _) (jglue _ _) (jglue _ _) (jglue _ _) ∙
            ap4 (λ p₁ p₂ p₃ p₄ → p₁ ∙ ! p₂ ∙ p₃ ∙ ! p₄)
              (glue-β _ _ _ _ _)
              (glue-β _ _ _ _ _)
              (glue-β _ _ _ _ _)
              (glue-β _ _ _ _ _) ∙
            ap (λ r → p x ∙ ! r) q ∙ ∙-unit-r (p x)))
      where open JoinRec

  open JoinElim

  abstract
  
    ε-natural : ∀ {j k} {Z : Ptd j} {Y : Ptd k} (f : Z ⊙→ Y)
      → ⊙ε Y ⊙∘ jmap⊙-un X (⊙hom-cod-fmap (⊙Ω-fmap f)) == f ⊙∘ ⊙ε Z
    ε-natural {Z = Z} (f , idp) = ⊙-crd∼-to-== $
      JoinMapEq (λ _ → idp) (λ _ → idp) (λ x (p , q) →
        ap2 _∙_
          (ap ! (ap-∘ (fst (⊙ε _)) (fst (jmap⊙-un X (⊙hom-cod-fmap (ap f , idp)))) (jglue x (p , q)) ∙
          ap (ap _) (JoinRec.glue-β _ _ _ x (p , q)) ∙ JoinRec.glue-β _ _ _ x _))
        (ap-∘ f (fst (⊙ε Z)) (jglue x (p , q)) ∙ ap (ap f) (JoinRec.glue-β _ _ _ x (p , q))) ∙
        !-inv-l (ap f (p x))) ,
      idp

    εJoin-Joinη : ∀ {j} (Y : Ptd j) → ⊙ε (X ⊙* Y) ⊙∘ jmap⊙-un X (⊙η Y) == ⊙idf _
    εJoin-Joinη Y = ⊙-crd∼-to-== $
      JoinMapEq (λ x → jglue (pt X) (pt Y) ∙ ! (jglue x (pt Y))) (λ y → jglue (pt X) y) (λ x y →
        ap (λ r → ! r ∙ (jglue (pt X) (pt Y) ∙ ! (jglue x (pt Y))) ∙ ap (λ z → z) (jglue x y))
          (ap-∘ (fst (⊙ε (X ⊙* Y))) (fst (jmap⊙-un X (⊙η Y))) (jglue x y) ∙
          ap (ap _) (JoinRec.glue-β _ _ _ x y) ∙ JoinRec.glue-β _ _ _ x (fst (⊙η Y) y)) ∙
        aux-coher (jglue (pt X) (pt Y)) (jglue x (pt Y)) (jglue x y) (jglue (pt X) y)) ,
        ap (λ r → ! r ∙ idp) (!-inv-r (jglue (pt X) (pt Y)))
      where abstract
        aux-coher : {x y z w v : de⊙ X * de⊙ Y} (p₁ : x == y) (p₂ : z == y) (p₃ : z == w) (p₄ : v == w) →
          ! (p₁ ∙ ! p₂ ∙ p₃ ∙ ! p₄) ∙ (p₁ ∙ ! p₂) ∙ ap (λ z → z) p₃ == p₄
        aux-coher idp idp idp idp = idp

-- component morphism of adjunction
JLA-into : ∀ {i j k} {X : Ptd i} (Y : Ptd j) (U : Ptd k) → X ⊙* Y ⊙→ U → (Y ⊙→ X ⊙–→ ⊙Ω U)
JLA-into {X = X} Y _ r = ⊙hom-cod-fmap (⊙Ω-fmap r) ⊙∘ ⊙η Y where open JoinAdjLoop-units-coh X

-- extensional variant of JLA-into's action on paths
module JLA-into-ap {i j k} {X : Ptd i} {Y : Ptd j} {U : Ptd k} where

  private
    JLA-into-imp = JLA-into {X = X} Y U

  abstract

    ap-crd-into-coher2-aux : {f g : de⊙ X * de⊙ Y → de⊙ U} (H₀ : f ∼ g)
      {x y z : de⊙ X * de⊙ Y} (v : x == y) (u : z == y) →
      ! (hmtpy-nat-∙' H₀ (v ∙ ! u ∙ u ∙ ! v) ∙
      ap (λ p → p ∙ ap g (v ∙ ! u ∙ u ∙ ! v) ∙' ! (H₀ x))
        (! (!-! (H₀ x)) ∙ ! (!-∙ (! (H₀ x)) idp)) ∙
      ap (λ p → ! (! (H₀ x) ∙ idp) ∙ ap g (v ∙ ! u ∙ u ∙ ! v) ∙' p)
        (! (∙-unit-r (! (H₀ x)))) ∙
      ! (Ω-fmap-β (g , ! (H₀ x) ∙ idp) (v ∙ ! u ∙ u ∙ ! v))) ∙
      ap (ap f) (!-inv-r-twice-mid v u)
        ==
      ap (fst (⊙Ω-fmap (g , ! (H₀ x) ∙ idp)))
        (!-inv-r-twice-mid v u) ∙
      snd (⊙Ω-fmap (g , ! (H₀ x) ∙ idp))
    ap-crd-into-coher2-aux {g = g} H₀ {x = x} idp idp = lemma (H₀ x)
      where
        lemma : ∀ {x} {y} (u : x == g y) →
          ! ((! (!-inv-r u) ∙ ap (λ p → u ∙ p) (! (∙'-unit-l (! u)))) ∙
          ap (λ p → p ∙ idp ∙' ! u) (! (!-! u) ∙ ! (!-∙ (! u) idp)) ∙
          ap (λ p → ! (! u ∙ idp) ∙ idp ∙' p) (! (∙-unit-r (! u))) ∙
          ! (Ω-fmap-β (g , ! u ∙ idp) idp)) ∙ idp
            ==
          snd (⊙Ω-fmap (g , ! u ∙ idp))
        lemma idp = idp

    ap-crd-into-coher2 : {x : de⊙ X} {f g : de⊙ X * de⊙ Y → de⊙ U} (H₀ : f ∼ g)
      {gₚ : g (jleft (pt X)) == f (jleft (pt X))} (H₁ : ! (H₀ (jleft (pt X))) ∙ idp == gₚ) →
      ! (hmtpy-nat-∙' H₀ (jglue (pt X) (pt Y) ∙ ! (jglue x (pt Y)) ∙ jglue x (pt Y) ∙ ! (jglue (pt X) (pt Y))) ∙
      ap (λ p → p ∙ ap g (jglue (pt X) (pt Y) ∙ ! (jglue x (pt Y)) ∙ jglue x (pt Y) ∙ ! (jglue (pt X) (pt Y))) ∙' ! (H₀ (jleft (pt X))))
        (! (!-! (H₀ (jleft (pt X)))) ∙ ! (!-∙ (! (H₀ (jleft (pt X)))) idp)) ∙
      ap (λ p → ! (! (H₀ (jleft (pt X))) ∙ idp) ∙ ap g (jglue (pt X) (pt Y) ∙ ! (jglue x (pt Y)) ∙ jglue x (pt Y) ∙ ! (jglue (pt X) (pt Y))) ∙' p)
        (! (∙-unit-r (! (H₀ (jleft (pt X)))))) ∙
      ∙-∙'-= (ap g (jglue (pt X) (pt Y) ∙ ! (jglue x (pt Y)) ∙ jglue x (pt Y) ∙ ! (jglue (pt X) (pt Y)))) H₁ ∙
      ! (Ω-fmap-β (g , gₚ) (jglue (pt X) (pt Y) ∙ ! (jglue x (pt Y)) ∙ jglue x (pt Y) ∙ ! (jglue (pt X) (pt Y))))) ∙
      ap (ap f) (!-inv-r-twice-mid (jglue (pt X) (pt Y)) (jglue x (pt Y)))
        ==
      ap (fst (⊙Ω-fmap (g , gₚ))) (!-inv-r-twice-mid (jglue (pt X) (pt Y)) (jglue x (pt Y))) ∙ snd (⊙Ω-fmap (g , gₚ))
    ap-crd-into-coher2 {x} H₀ idp = ap-crd-into-coher2-aux H₀ (jglue (pt X) (pt Y)) (jglue x (pt Y))

    ap-crd-into-coher1-aux : {f g : de⊙ X * de⊙ Y → de⊙ U} (H₀ : f ∼ g)
      {x y z : de⊙ X * de⊙ Y} (v : x == y) (u : x == z) →
      ! (hmtpy-nat-∙' H₀ (v ∙ ! v ∙ u ∙ ! u) ∙
         ap (λ p → p ∙ ap g (v ∙ ! v ∙ u ∙ ! u) ∙' ! (H₀ x))
           (! (!-! (H₀ x)) ∙ ! (!-∙ (! (H₀ x)) idp)) ∙
         ap (λ p → ! (! (H₀ x) ∙ idp) ∙ ap g (v ∙ ! v ∙ u ∙ ! u) ∙' p)
           (! (∙-unit-r (! (H₀ x)))) ∙ idp ∙
         ! (Ω-fmap-β (g , ! (H₀ x) ∙ idp)  (v ∙ ! v ∙ u ∙ ! u))) ∙
      ap (ap f) (!-inv-r-twice v u) ∙ idp
        ==
      ap (fst (⊙Ω-fmap (g , ! (H₀ x) ∙ idp))) (!-inv-r-twice v u) ∙
      snd (⊙Ω-fmap (g , ! (H₀ x) ∙ idp))
    ap-crd-into-coher1-aux {g = g} H₀ {x} idp idp = lemma (H₀ x)
      where
        lemma : ∀ {x} {y} (u : x == g y) →
          ! ((! (!-inv-r u) ∙ ap (λ p → u ∙ p) (! (∙'-unit-l (! u)))) ∙
            ap (λ p → p ∙ idp ∙' ! u) (! (!-! u) ∙ ! (!-∙ (! u) idp)) ∙
            ap (λ p → ! (! u ∙ idp) ∙ idp ∙' p) (! (∙-unit-r (! u))) ∙
            ! (Ω-fmap-β (g , ! u ∙ idp) idp)) ∙ idp
            ==
          snd (⊙Ω-fmap (g , ! u ∙ idp))
        lemma idp = idp 

    ap-crd-into-coh1 : {y : de⊙ Y} {f g : de⊙ X * de⊙ Y → de⊙ U} (H₀ : f ∼ g)
      {gₚ : g (jleft (pt X)) == f (jleft (pt X))} (H₁ : ! (H₀ (jleft (pt X))) ∙ idp == gₚ) →
      ! (hmtpy-nat-∙' H₀ (jglue (pt X) (pt Y) ∙  ! (jglue (pt X) (pt Y)) ∙ jglue (pt X) y ∙ ! (jglue (pt X) y)) ∙
        ap (λ p →  p ∙ ap g (jglue (pt X) (pt Y) ∙ ! (jglue (pt X) (pt Y)) ∙ jglue (pt X) y ∙ ! (jglue (pt X) y)) ∙' ! (H₀ (jleft (pt X))))
          (! (!-! (H₀ (jleft (pt X)))) ∙ ! (!-∙ (! (H₀ (jleft (pt X)))) idp)) ∙
        ap (λ p → ! (! (H₀ (jleft (pt X))) ∙ idp) ∙ ap g (jglue (pt X) (pt Y) ∙ ! (jglue (pt X) (pt Y)) ∙ jglue (pt X) y ∙ ! (jglue (pt X) y)) ∙' p)
          (! (∙-unit-r (! (H₀ (jleft (pt X)))))) ∙
        ∙-∙'-= (ap g (jglue (pt X) (pt Y) ∙ ! (jglue (pt X) (pt Y)) ∙ jglue (pt X) y ∙ ! (jglue (pt X) y))) H₁ ∙
        ! (Ω-fmap-β (g , gₚ) (jglue (pt X) (pt Y) ∙ ! (jglue (pt X) (pt Y)) ∙ jglue (pt X) y ∙ ! (jglue (pt X) y)))) ∙
      ap (ap f) (!-inv-r-twice (jglue (pt X) (pt Y)) (jglue (pt X) y)) ∙ idp
        ==
      ap (Ω-fmap (g , gₚ)) (!-inv-r-twice (jglue (pt X) (pt Y)) (jglue (pt X) y)) ∙ snd (⊙Ω-fmap (g , gₚ))
    ap-crd-into-coh1 {y} H₀ idp = ap-crd-into-coher1-aux H₀ (jglue (pt X) (pt Y)) (jglue (pt X) y)

  ap-crd-into : {f₁ f₂ : X ⊙* Y ⊙→ U} (H : f₁ ⊙-crd∼ f₂) → JLA-into-imp f₁ ⊙-crd∼ JLA-into-imp f₂
  fst (ap-crd-into {f₁ = (f , idp)} {f₂} H) y =
    ⊙-crd∼-to-== $
      (λ x → 
        (hmtpy-nat-∙' (fst H) (jglue (pt X) (pt Y) ∙ ! (jglue x (pt Y)) ∙ jglue x y ∙ ! (jglue (pt X) y)) ∙
        ap (λ p → p ∙ ap (λ z → fst f₂ z) (jglue (pt X) (pt Y) ∙ ! (jglue x (pt Y)) ∙ jglue x y ∙ ! (jglue (pt X) y)) ∙' ! (fst H (jleft (pt X))))
          (! (!-! (fst H (jleft (pt X)))) ∙ ! (!-∙ (! (fst H (jleft (pt X)))) idp)) ∙
        ap (λ p → (! (! (fst H (jleft (pt X))) ∙ idp)) ∙ ap (fst f₂) (jglue (pt X) (pt Y) ∙ ! (jglue x (pt Y)) ∙ jglue x y ∙ ! (jglue (pt X) y)) ∙' p)
          (! (∙-unit-r (! (fst H (jleft (pt X)))))) ∙
        ∙-∙'-= (ap (fst f₂) (jglue (pt X) (pt Y) ∙ ! (jglue x (pt Y)) ∙ jglue x y ∙ ! (jglue (pt X) y))) (snd H) ∙
        ! (Ω-fmap-β f₂ (jglue (pt X) (pt Y) ∙ ! (jglue x (pt Y)) ∙ jglue x y ∙ ! (jglue (pt X) y))))) ,
      ap-crd-into-coh1 (fst H) (snd H) 
  snd (ap-crd-into {f₁ = (f , idp)} {f₂} H) = let comp-fst = fst (ap-crd-into H) (pt Y) in
    ap (λ p → ! comp-fst ∙ p) (∙-unit-r _ ∙ ! (whisk⊙-conv-l {f₁ = (ap f , idp)} _)) ∙
    !-⊙∘-conv _ _ ∙
    ap ⊙-crd∼-to-== (⊙→∼-to-== (∼⊙Ωhomog∼ (λ x →
      ap-crd-into-coher2 (fst H) (snd H)))) ∙
    =ₛ-out (⊙∘-conv _ _) ∙
    ap2 _∙_ (⊙hom-cod-fmap-fstβ _) (⊙hom-cod-fmap-sndβ {f = ⊙Ω-fmap f₂})

  {-
     This definition of ap agrees with the standard ap on the id homotopy,
     hence on all homotopies by the SIP.
  -}

  abstract
    ap-crd-into-id : (f* : X ⊙* Y ⊙→ U) → ap-crd-into (⊙∼-id f*) ⊙→∼ ⊙∼-id (JLA-into-imp f*)
    ap-crd-into-id (f , idp) = ∼⊙homog∼ ⊙→-homog-str-⊙Ωcod _ $
      λ y → ap ⊙-crd∼-to-== (⊙→∼-to-== (∼⊙Ωhomog∼ (λ x →
        ∙-unit-r _ ∙ hmtpy-nat-∙'-idp (jglue (pt X) (pt Y) ∙ ! (jglue x (pt Y)) ∙ jglue x y ∙ ! (jglue (pt X) y)) ))) ∙
      ⊙-crd∼-to-==-β _

  abstract
    ap-crd-into-agree : {f* g* : X ⊙* Y ⊙→ U} (H : f* ⊙-crd∼ g*)
      → ap JLA-into-imp (⊙-crd∼-to-== H) == ⊙-crd∼-to-== (ap-crd-into H)
    ap-crd-into-agree {f*} = ⊙hom-ind f*
      (λ g* H → ap JLA-into-imp (⊙-crd∼-to-== H) == ⊙-crd∼-to-== (ap-crd-into H))
      (ap (ap JLA-into-imp) (⊙-crd∼-to-==-β f*) ∙
      ! (ap ⊙-crd∼-to-== (⊙→∼-to-== (ap-crd-into-id f*)) ∙ ⊙-crd∼-to-==-β (JLA-into-imp f*)))

-- explicit naturality proof designed to be amenable to checking 2-coherence
JLA-nat-dom-⊙∼ : ∀ {i l j k} {X : Ptd i} {Z : Ptd l} {Y : Ptd j} {U : Ptd k} (h : Z ⊙→ Y) (r : X ⊙* Y ⊙→ U)
  → (JLA-into Y U) r ⊙∘ h ⊙-crd∼ (JLA-into Z U) (r ⊙∘ jmap⊙-un X h)
fst (JLA-nat-dom-⊙∼ {X = X} {Z} {⊙[ Y , _ ]} (h , idp) (r , idp)) z = ⊙-crd∼-to-==
  ((λ x →
    ! (ap (ap r)
      (ap4 (λ p₁ p₂ p₃ p₄ → p₁ ∙ ! p₂ ∙ p₃ ∙ ! p₄)
        (glue-β _ _ _ (pt X) (pt Z))
        (glue-β _ _ _ x (pt Z))
        (glue-β _ _ _ x z)
        (glue-β _ _ _ (pt X) z))) ∙
    ∘-ap-∙!∙∙! r _ (jglue (pt X) (pt Z)) (jglue x (pt Z)) (jglue x z) (jglue (pt X) z)) ,
  ap (λ p →
      ! (! (ap (ap r) p) ∙
      ∘-ap-∙!∙∙! r (λ w → jmap (λ x → x) h w) (jglue (pt X) (pt Z)) (jglue (pt X) (pt Z)) (jglue (pt X) z) (jglue (pt X) z)) ∙
      ap (ap r) (!-inv-r-twice (jglue (pt X) (h (pt Z))) (jglue (pt X) (h z))) ∙ idp)
    (ap4-∙!-∙!-canc
      (glue-β jleft (jright ∘ h) (λ a b → jglue a (h b)) (pt X) (pt Z))
      (glue-β jleft (jright ∘ h) (λ a b → jglue a (h b)) (pt X) z)) ∙
  ptd-coh1 {Join-rec jleft (jright ∘ h) (λ a b → jglue a (h b))}
    (jglue (pt X) (pt Z)) (jglue (pt X) z) (jglue (pt X) (h z)) (jglue (pt X) (h (pt Z))))
  where abstract
    open JoinRec
    ptd-coh1 : {m : de⊙ X * de⊙ Z → de⊙ X * Y} {x y z : de⊙ X * de⊙ Z} {u v : de⊙ X * Y} (p₁ : x == y) (p₂ : x == z) (p₃ : m x == u) (p₄ : m x == v) →
      ! (! (ap (ap r) (!-inv-r-twice (ap m p₁) (ap m p₂) ∙ ! (!-inv-r-twice p₄ p₃))) ∙
      ∘-ap-∙!∙∙! r m p₁ p₁ p₂ p₂) ∙
      ap (ap r) (!-inv-r-twice p₄ p₃) ∙ idp
        ==
      ap (ap (r ∘ m)) (!-inv-r-twice p₁ p₂) ∙ idp
    ptd-coh1 idp idp p₃ p₄ = !-!-ap-!-unit-r-∙ (ap r) (!-inv-r-twice p₄ p₃)
snd (JLA-nat-dom-⊙∼ {X = X} {Z} {⊙[ Y , _ ]} (h , idp) (r , idp)) = let comp-fst = fst (JLA-nat-dom-⊙∼ (h , idp) (r , idp)) (pt Z) in
  ap (λ p → ! comp-fst ∙ p) (∙-unit-r _ ∙ ! (whisk⊙-conv-l {f₁ = (ap r , idp)} _)) ∙
  !-⊙∘-conv _ _ ∙
  ap ⊙-crd∼-to-== (⊙→∼-to-== (∼⊙Ωhomog∼ (λ x →
    ap (λ p →
        ! (! (ap (ap r) p) ∙
        ∘-ap-∙!∙∙! r (Join-rec jleft (jright ∘ h) (λ a b → jglue a (h b)))
          (jglue (pt X) (pt Z)) (jglue x (pt Z)) (jglue x (pt Z)) (jglue (pt X) (pt Z))) ∙
        ap (ap r) (!-inv-r-twice-mid (jglue (pt X) (h (pt Z))) (jglue x (h (pt Z)))))
      (ap4-∙!-∙!-canc-mid
        (glue-β jleft (jright ∘ h) (λ a b → jglue a (h b)) (pt X) (pt Z))
        (glue-β jleft (jright ∘ h) (λ a b → jglue a (h b)) x (pt Z))) ∙
    ptd-coh2 {Join-rec jleft (jright ∘ h) (λ a b → jglue a (h b))}
      (jglue (pt X) (pt Z)) (jglue x (pt Z)) (jglue (pt X) (h (pt Z))) (jglue x (h (pt Z)))))) ∙
  whisk⊙-conv-l {f₁ = (ap (r ∘ Join-rec jleft (jright ∘ h) (λ a b → jglue a (h b))) , idp)} _ ∙
  ! (∙-unit-r _)
  where abstract
    open JoinRec
    ptd-coh2 : {m : de⊙ X * de⊙ Z → de⊙ X * Y} {x y z : de⊙ X * de⊙ Z} {u v : de⊙ X * Y} (p₁ : x == y) (p₂ : z == y) (p₃ : m x == v) (p₄ : u == v) →
      ! (! (ap (ap r) (!-inv-r-twice-mid (ap m p₁) (ap m p₂) ∙ ! (!-inv-r-twice-mid p₃ p₄))) ∙
      ∘-ap-∙!∙∙! r m p₁ p₂ p₂ p₁) ∙
      ap (ap r) (!-inv-r-twice-mid p₃ p₄)
        ==
      ap (ap (r ∘ m)) (!-inv-r-twice-mid p₁ p₂)
    ptd-coh2 idp idp idp idp = idp

JLA-nat-dom : ∀ {i l j k} {X : Ptd i} {Z : Ptd l} {Y : Ptd j} {U : Ptd k} (h : Z ⊙→ Y) (r : X ⊙* Y ⊙→ U)
  → (JLA-into Y U) r ⊙∘ h == (JLA-into Z U) (r ⊙∘ jmap⊙-un X h)
JLA-nat-dom h r = ⊙-crd∼-to-== (JLA-nat-dom-⊙∼ h r)

module _ {i j} (X : Ptd i) where

  open JoinAdjLoop-units-coh X

  JoinLoopCodAdj-unit : CounitUnitAdjoint (JoinFunctor {j = lmax i j} X) (⊙hom-codF X ∘WC LoopFunctor {lmax i j})
  JoinLoopCodAdj-unit = counitunitadjoint ⊙η ⊙ε η-natural ε-natural εJoin-Joinη Ωcodε-ηΩcod

  -- final form of adjunction
  JoinLoopCodAdj : Adjunction (JoinFunctor {j = lmax i j} X) (⊙hom-codF X ∘WC LoopFunctor {lmax i j})
  JoinLoopCodAdj = let hom-adj = counit-unit-to-hom JoinLoopCodAdj-unit in
    adjunction (iso hom-adj) (nat-cod hom-adj) JLA-nat-dom
