{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.Pushout
open import lib.types.Join
open import lib.types.LoopSpace
open import lib.types.Homogeneous
open import lib.wild-cats.WildCats

module homotopy.Join.JoinAdjointLoopCod where

module JoinAdjLoop-units {i j} (X : Ptd i) (Y : Ptd j) where

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
{-
-- desired adjunction
JoinLoopCodAdj : ∀ {i j} (X : Ptd i) → Adjunction (JoinFunctor {j = lmax i j} X) (⊙hom-codF X ∘WC LoopFunctor {lmax i j})
JoinLoopCodAdj X = ?
-}
