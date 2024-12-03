{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.LoopSpace
open import lib.types.Paths
open import lib.types.Sigma

module lib.types.Homogenous where

module _ {i} {X : Type i} where

  module _ (x : X) where

    record homogenous : Type i where
      constructor homog
      field
        auto : (y : X) → ⊙[ X , x ] ⊙≃ ⊙[ X , y ]
        pt-idf : auto x == (⊙idf ⊙[ X , x ] , idf-is-equiv X) -- can weaken this a bit
    open homogenous public

    homog-idf : (η : homogenous) →  fst (auto η x) == ⊙idf ⊙[ X , x ]
    homog-idf (homog auto pt-idf) = ap fst pt-idf

    homog-⊙Ω≃ : (y : X) → homogenous → ⊙Ω ⊙[ X , x ] ⊙≃ ⊙Ω ⊙[ X , y ]
    homog-⊙Ω≃ y (homog auto _) = ⊙Ω-emap (auto y)

    homog-Ω≃ : (y : X) → homogenous → (x == x) ≃ (y == y)
    homog-Ω≃ y η = ⊙≃-to-≃ (homog-⊙Ω≃ y η)

  module _ {j} {Z : Type j} {z : Z} {f : Z → X} where

    ⊙∼-eval : ⊙[ f ∼ f , (λ z → idp) ] ⊙→ ⊙[ f z == f z , idp ]
    fst ⊙∼-eval = λ H → H z
    snd ⊙∼-eval = idp

    ⊙∼-eval-sect : homogenous (f z) → has-sect⊙ ⊙∼-eval
    fst (has-sect⊙.r-inv (⊙∼-eval-sect η)) p = λ x₁ → –>(homog-Ω≃ (f z) (f x₁) η) p
    snd (has-sect⊙.r-inv (⊙∼-eval-sect (homog auto _))) =
      λ= λ x → Ω-fmap-β∙ (fst (auto (f x))) idp ∙
        !-inv-l (snd (fst (auto (f x))))
    has-sect⊙.sect⊙-eq (⊙∼-eval-sect η) =
      ⊙λ= (comp-to-⊙
        ((λ x → app= (ap (fst ∘ ⊙Ω-fmap) (homog-idf (f z) η) ∙ ap fst ⊙Ω-fmap-idf) x) ,
        pathseq))
      where
        pathseq :
          ! (ap (λ u → u idp)
            (ap (fst ∘ ⊙Ω-fmap) (homog-idf (f z) η) ∙
            ap fst (pair= (λ= ap-idf)
              (↓-app=cst-in (ap (_∙ idp) (! (app=-β ap-idf idp))))))) ∙
          ap (λ H → H z) (λ= (λ x → Ω-fmap-β∙ (fst (auto η (f x))) idp ∙
            !-inv-l (snd (fst (auto η (f x)))))) ∙ idp
          =-=
          idp
        pathseq = 
          ! (ap (λ u → u idp)
            (ap (fst ∘ ⊙Ω-fmap) (homog-idf (f z) η) ∙
            ap fst (pair= (λ= ap-idf) _))) ∙
          ap (λ H → H z) (λ= (λ x → Ω-fmap-β∙ (fst (auto η (f x))) idp ∙
            !-inv-l (snd (fst (auto η (f x)))))) ∙ idp
            =⟪ ap (λ p → ! p ∙ ap (λ H → H z)
                   (λ= (λ x → Ω-fmap-β∙ (fst (auto η (f x))) idp ∙
                   !-inv-l (snd (fst (auto η (f x)))))) ∙ idp) (
                 ap-∙ (λ u → u idp) (ap (fst ∘ ⊙Ω-fmap) (homog-idf (f z) η))
                   (ap fst (pair= (λ= ap-idf) _))) ⟫
          ! (ap (λ u → u idp) (ap (fst ∘ ⊙Ω-fmap) (homog-idf (f z) η)) ∙
            ap (λ u → u idp) (ap (λ r → fst r) (pair= (λ= ap-idf) _))) ∙
          ap (λ H → H z) (λ= (λ x → Ω-fmap-β∙ (fst (auto η (f x))) idp ∙
            !-inv-l (snd (fst (auto η (f x)))))) ∙ idp
            =⟪ ap (λ p → ! (ap (λ u → u idp) (ap (fst ∘ ⊙Ω-fmap)
                    (homog-idf (f z) η)) ∙ p) ∙ ap (λ H → H z)
                    (λ= (λ x → Ω-fmap-β∙ (fst (auto η (f x))) idp ∙
                    !-inv-l (snd (fst (auto η (f x)))))) ∙ idp)
                  (ap (ap (λ u → u idp)) (fst=-β (λ= ap-idf)
                    (↓-app=cst-in (ap (_∙ idp) (! (app=-β ap-idf idp))))) ∙ λ=-ap-idf) ⟫
          ! (ap (λ u → u idp) (ap ((λ r → fst r) ∘ ⊙Ω-fmap)
            (homog-idf (f z) η)) ∙ idp) ∙
          ap (λ H → H z) (λ= (λ x → Ω-fmap-β∙ (fst (auto η (f x))) idp ∙
            !-inv-l (snd (fst (auto η (f x)))))) ∙ idp
          =⟪ {!!} ⟫
          {!!}
          

    ⊙∼-evalΩ-sect : homogenous (f z) → has-sect⊙ (⊙Ω-fmap ⊙∼-eval)
    ⊙∼-evalΩ-sect η = ⊙Ω-sect (⊙∼-eval) (⊙∼-eval-sect η)

    module _ (η : homogenous (f z)) where

      open has-sect⊙

      ∼⊙homog= : (x : X) {g : Z → X}
        {fₚ : f z == x} {gₚ : g z == x}
        {H₁ H₂ : f == g}
        {H₁ₚ : ! (app= H₁ z) ∙ fₚ =-= gₚ}
        {H₂ₚ : ! (app= H₂ z) ∙ fₚ =-= gₚ}
        →  H₁ == H₂ → (app= H₁ , H₁ₚ) ⊙→∼ (app= H₂ , H₂ₚ)
      fst (∼⊙homog= x {fₚ = idp} {H₁ = idp} {H₁ₚ = H₁ₚ} {H₂ₚ} idp) =
        λ x₁ → app= (fst (r-inv (⊙∼-evalΩ-sect η))
          (ap-post∙idp∘!-inv (↯ (H₁ₚ) ∙ ! (↯ (H₂ₚ))))) x₁
      snd (∼⊙homog= x {fₚ = idp} {H₁ = idp} {H₁ₚ = H₁ₚ} {H₂ₚ} idp) =
        post↯-rotate-in (=ₛ-in (ap (ap (λ p → ! p ∙ idp))
        (app= (ap fst (sect⊙-eq (⊙∼-evalΩ-sect η)))
          (ap-post∙idp∘!-inv (↯ (H₁ₚ) ∙ ! (↯ (H₂ₚ))))) ∙
        <–-inv-r (ap-equiv (post∙idp∘!-is-equiv) idp idp)
          (↯ (H₁ₚ) ∙ ! (↯ (H₂ₚ)))))
