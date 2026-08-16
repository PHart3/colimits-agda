{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.Pushout
open import lib.types.Join
open import lib.types.LoopSpace
open import lib.types.Homogeneous
open import lib.wild-cats.WildCats

module homotopy.Join.JoinAdjointLoopCod where

module JoinAdjLoop-units {i} (X : Ptd i) {j} (Y : Ptd j) where

  ⊙η : Y ⊙→ X ⊙–→ ⊙Ω (X ⊙* Y)
  fst (fst ⊙η y) x = jglue (pt X) (pt Y) ∙ ! (jglue x (pt Y)) ∙ jglue x y ∙ ! (jglue (pt X) y) 
  snd (fst ⊙η y) = !-inv-r-twice (jglue (pt X) (pt Y)) (jglue (pt X) y)
  snd ⊙η = ⊙-crd∼-to-== ((λ x → !-inv-r-twice-mid (jglue (pt X) (pt Y)) (jglue x (pt Y))) ,
    ap (λ p → ! (!-inv-r-twice-mid (jglue (pt X) (pt Y)) (jglue (pt X) (pt Y))) ∙ p)
      (!-inv-r-twice-coh (jglue (pt X) (pt Y))) ∙
    !-inv-l (!-inv-r-twice-mid (jglue (pt X) (pt Y)) (jglue (pt X) (pt Y))))

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
          (ap-∙!∙∙! _ (glue (pt X , pt Z)) (glue (x , pt Z)) (glue (x , z)) (glue (pt X , z)) ∙
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
            ap-∙!∙∙! _ (glue _) (glue _) (glue _) (glue _) ∙
            ap4 (λ p₁ p₂ p₃ p₄ → p₁ ∙ ! p₂ ∙ p₃ ∙ ! p₄)
              (glue-β _ _ _ _ _)
              (glue-β _ _ _ _ _)
              (glue-β _ _ _ _ _)
              (glue-β _ _ _ _ _) ∙
            ap (λ r → p x ∙ ! r) q ∙ ∙-unit-r (p x)))
      where open JoinRec

  open JoinElim

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

  abstract
    εJoin-Joinη : ∀ {j} (Y : Ptd j) → ⊙ε (X ⊙* Y) ⊙∘ jmap⊙-un X (⊙η Y) == ⊙idf _
    εJoin-Joinη Y = ⊙-crd∼-to-== $
      JoinMapEq (λ x → jglue (pt X) (pt Y) ∙ ! (jglue x (pt Y))) (λ y → jglue (pt X) y) (λ x y →
        ap (λ r → ! r ∙ (glue (pt X , pt Y) ∙ ! (glue (x , pt Y))) ∙ ap (λ z → z) (glue (x , y)))
          (ap-∘ (fst (⊙ε (X ⊙* Y))) (fst (jmap⊙-un X (⊙η Y))) (jglue x y) ∙
          ap (ap _) (JoinRec.glue-β _ _ _ x y) ∙ JoinRec.glue-β _ _ _ x (fst (⊙η Y) y)) ∙
        aux-coher (glue (pt X , pt Y)) (glue (x , pt Y)) (glue (x , y)) (glue (pt X , y))) ,
        ap (λ r → ! r ∙ idp) (!-inv-r (glue (pt X , pt Y)))
      where abstract
        aux-coher : {x y z w v : de⊙ X * de⊙ Y} (p₁ : x == y) (p₂ : z == y) (p₃ : z == w) (p₄ : v == w) →
          ! (p₁ ∙ ! p₂ ∙ p₃ ∙ ! p₄) ∙ (p₁ ∙ ! p₂) ∙ ap (λ z → z) p₃ == p₄
        aux-coher idp idp idp idp = idp
      
-- desired adjunction

module _ {i j} (X : Ptd i) where

  open JoinAdjLoop-units-coh X

  JoinLoopCodAdj-unit : CounitUnitAdjoint (JoinFunctor {j = lmax i j} X) (⊙hom-codF X ∘WC LoopFunctor {lmax i j})
  JoinLoopCodAdj-unit = counitunitadjoint ⊙η ⊙ε η-natural ε-natural εJoin-Joinη Ωcodε-ηΩcod

  JoinLoopCodAdj : Adjunction (JoinFunctor {j = lmax i j} X) (⊙hom-codF X ∘WC LoopFunctor {lmax i j})
  JoinLoopCodAdj = counit-unit-to-hom JoinLoopCodAdj-unit
