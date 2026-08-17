{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.Join
open import lib.types.LoopSpace
open import lib.types.Homogeneous
open import lib.wild-cats.WildCats

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

-- explicit naturality proof designed to be amenable to checking 2-coherence
open import lib.types.Pushout
JLA-nat-dom-⊙∼ : ∀ {i l j k} {X : Ptd i} {Z : Ptd l} {Y : Ptd j} {U : Ptd k} (h : Z ⊙→ Y) (r : X ⊙* Y ⊙→ U)
  → (JLA-into Y U) r ⊙∘ h ⊙-crd∼ (JLA-into Z U) (r ⊙∘ jmap⊙-un X h)
fst (JLA-nat-dom-⊙∼ {X = X} {Z} (h , idp) (r , idp)) z = ⊙-crd∼-to-==
  ((λ x →
    ! (ap (ap r) (ap4 (λ p₁ p₂ p₃ p₄ → p₁ ∙ ! p₂ ∙ p₃ ∙ ! p₄)
      (glue-β _ _ _ (pt X) (pt Z))
      (glue-β _ _ _ x (pt Z))
      (glue-β _ _ _ x z)
      (glue-β _ _ _ (pt X) z))) ∙
    ∘-ap-∙!∙∙! r _ (jglue (pt X) (pt Z)) (jglue x (pt Z)) (jglue x z) (jglue (pt X) z)) ,
  ap (λ p →
      ! (! (ap (ap r) p) ∙
      ∘-ap-∙!∙∙! r (λ w → jmap (λ x → x) h w) (jglue (pt X) (pt Z)) (jglue (pt X) (pt Z)) (jglue (pt X) z) (jglue (pt X) z)) ∙
      ap (ap r) (!-inv-r-twice (glue (pt X , h (pt Z))) (jglue (pt X) (h z))) ∙ idp)
    (ap4-∙!-∙!-refl
      (glue-β jleft (jright ∘ h) (λ a b → jglue a (h b)) (pt X) (pt Z))
      (glue-β jleft (jright ∘ h) (λ a b → jglue a (h b)) (pt X) z)) ∙
  aux {Join-rec jleft (jright ∘ h) (λ a b → jglue a (h b))}
    (jglue (pt X) (pt Z)) (jglue (pt X) z) (jglue (pt X) (h z)) (jglue (pt X) (h (pt Z))))
  module ptd-coh1 where
    open JoinRec
    aux : ∀ {m} {x y z} {u v} (p₁ : x == y) (p₂ : x == z) (p₃ : m x == u) (p₄ : m x == v) →
      ! (! (ap (ap r) (!-inv-r-twice (ap m p₁) (ap m p₂) ∙ ! (!-inv-r-twice p₄ p₃))) ∙
      ∘-ap-∙!∙∙! r m p₁ p₁ p₂ p₂) ∙
      ap (ap r) (!-inv-r-twice p₄ p₃) ∙ idp
        ==
      ap (ap (r ∘ m)) (!-inv-r-twice p₁ p₂) ∙ idp
    aux idp idp p₃ p₄ = !-!-ap-!-unit-r-∙ (ap r) (!-inv-r-twice p₄ p₃)
snd (JLA-nat-dom-⊙∼ (h , idp) (r , idp)) = {!!}

JLA-nat-dom : ∀ {i l j k} {X : Ptd i} {Z : Ptd l} {Y : Ptd j} {U : Ptd k} (h : Z ⊙→ Y) (r : X ⊙* Y ⊙→ U)
  → (JLA-into Y U) r ⊙∘ h == (JLA-into Z U) (r ⊙∘ jmap⊙-un X h)
JLA-nat-dom h r = ⊙-crd∼-to-== (JLA-nat-dom-⊙∼ h r)
{-
module _ {i j} (X : Ptd i) where

  open JoinAdjLoop-units-coh X

  JoinLoopCodAdj-unit : CounitUnitAdjoint (JoinFunctor {j = lmax i j} X) (⊙hom-codF X ∘WC LoopFunctor {lmax i j})
  JoinLoopCodAdj-unit = counitunitadjoint ⊙η ⊙ε η-natural ε-natural εJoin-Joinη Ωcodε-ηΩcod

  -- final form of adjunction
  JoinLoopCodAdj : Adjunction (JoinFunctor {j = lmax i j} X) (⊙hom-codF X ∘WC LoopFunctor {lmax i j})
  JoinLoopCodAdj = let hom-adj = counit-unit-to-hom JoinLoopCodAdj-unit in
    adjunction (iso hom-adj) (nat-cod hom-adj) JLA-nat-dom
-}
