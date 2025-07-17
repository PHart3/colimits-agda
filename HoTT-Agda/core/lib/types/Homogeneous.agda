{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.LoopSpace
open import lib.types.Paths
open import lib.types.Sigma

-- strongly homogeneous types

module lib.types.Homogeneous where

module _ {i} {X : Type i} where

  module _ (x : X) where

    record homogeneous : Type i where
      constructor homog
      field
        auto : (y : X) → ⊙[ X , x ] ⊙≃ ⊙[ X , y ]

    record str-homog : Type i where
      constructor sthomog
      field
        auto : (y : X) → ⊙[ X , x ] ⊙≃ ⊙[ X , y ]
        homog-idf : fst (auto x) == ⊙idf ⊙[ X , x ]
    open str-homog

    -- every homogeneous structure can be promoted to a strongly homogeneous one
    homog-to-strhomog : homogeneous → str-homog
    auto (homog-to-strhomog (homog self)) y = self y ⊙∘e (self x) ⊙⁻¹
    homog-idf (homog-to-strhomog (homog self)) = ⊙λ= (⊙<–-inv-r (self x)) 

    homog-⊙Ω≃ : (y : X) → str-homog → ⊙Ω ⊙[ X , x ] ⊙≃ ⊙Ω ⊙[ X , y ]
    homog-⊙Ω≃ y (sthomog auto _) = ⊙Ω-emap (auto y)

    homog-Ω≃ : (y : X) → str-homog → (x == x) ≃ (y == y)
    homog-Ω≃ y η = ⊙≃-to-≃ (homog-⊙Ω≃ y η)

  {-
    Two pointed homotopies of pointed maps valued in a strongly homogeneous
    type are equal as soon as their underlying homotopies are equal.
  -}
  
  module _ {j} {Z : Type j} {z : Z} {f : Z → X} where

    ⊙∼-eval : ⊙[ f ∼ f , (λ z → idp) ] ⊙→ ⊙[ f z == f z , idp ]
    fst ⊙∼-eval = λ H → H z
    snd ⊙∼-eval = idp

    ⊙∼-eval-sect : str-homog (f z) → has-sect⊙ ⊙∼-eval
    fst (has-sect⊙.r-inv (⊙∼-eval-sect η)) p = λ x₁ → –>(homog-Ω≃ (f z) (f x₁) η) p
    snd (has-sect⊙.r-inv (⊙∼-eval-sect (sthomog auto _))) =
      λ= λ x → Ω-fmap-β∙ (fst (auto (f x))) idp ∙
        !-inv-l (snd (fst (auto (f x))))
    has-sect⊙.sect⊙-eq (⊙∼-eval-sect (sthomog auto homog-idf)) =
      ⊙λ= (comp-to-⊙
        ((λ x → app= (ap (fst ∘ ⊙Ω-fmap) homog-idf ∙ ap fst ⊙Ω-fmap-idf) x) ,
        ↯ pathseq))
      where
        lemma : {m : ⊙[ X , f z ] ⊙→ ⊙[ X , f z ]} (τ : m == ⊙idf ⊙[ X , f z ]) 
          → ! (ap (λ u → u idp) (ap (fst ∘ ⊙Ω-fmap) τ) ∙ idp) ∙
            transport (λ v → Ω-fmap v idp == idp) (! τ) idp ∙ idp
            == idp
        lemma idp = idp

        pathseq :
          ! (ap (λ u → u idp)
            (ap (fst ∘ ⊙Ω-fmap) homog-idf ∙
            ap fst (pair= (λ= ap-idf)
              (↓-app=cst-in (ap (_∙ idp) (! (app=-β ap-idf idp))))))) ∙
          ap (λ H → H z) (λ= (λ x → Ω-fmap-β∙ (fst (auto (f x))) idp ∙
            !-inv-l (snd (fst (auto (f x)))))) ∙ idp
          =-=
          idp
        pathseq = 
          ! (ap (λ u → u idp)
            (ap (fst ∘ ⊙Ω-fmap) homog-idf ∙
            ap fst (pair= (λ= ap-idf) _))) ∙
          ap (λ H → H z) (λ= (λ x → Ω-fmap-β∙ (fst (auto (f x))) idp ∙
            !-inv-l (snd (fst (auto (f x)))))) ∙ idp
            =⟪ ap (λ p → ! p ∙ ap (λ H → H z)
                   (λ= (λ x → Ω-fmap-β∙ (fst (auto (f x))) idp ∙
                   !-inv-l (snd (fst (auto (f x)))))) ∙ idp)
                 (ap-∙ (λ u → u idp)
                   (ap (fst ∘ ⊙Ω-fmap) homog-idf) (ap fst (pair= (λ= ap-idf) _))) ⟫
          ! (ap (λ u → u idp) (ap (fst ∘ ⊙Ω-fmap) homog-idf) ∙
            ap (λ u → u idp) (ap fst (pair= (λ= ap-idf) _))) ∙
          ap (λ H → H z)
            (λ= (λ x → Ω-fmap-β∙ (fst (auto (f x))) idp ∙
              !-inv-l (snd (fst (auto (f x)))))) ∙ idp
            =⟪ ap (λ p → ! (ap (λ u → u idp) (ap (fst ∘ ⊙Ω-fmap)
                    homog-idf) ∙ p) ∙ ap (λ H → H z)
                    (λ= (λ x → Ω-fmap-β∙ (fst (auto (f x))) idp ∙
                    !-inv-l (snd (fst (auto (f x)))))) ∙ idp)
                  (ap (ap (λ u → u idp)) (fst=-β (λ= ap-idf)
                    (↓-app=cst-in (ap (_∙ idp) (! (app=-β ap-idf idp))))) ∙ λ=-ap-idf) ⟫
          ! (ap (λ u → u idp) (ap (fst ∘ ⊙Ω-fmap)
            homog-idf) ∙ idp) ∙
          ap (λ H → H z) (λ= (λ x → Ω-fmap-β∙ (fst (auto (f x))) idp ∙
            !-inv-l (snd (fst (auto (f x)))))) ∙ idp
          =⟪ ap (λ p → ! (ap (λ u → u idp) (ap (fst ∘ ⊙Ω-fmap)
                 homog-idf) ∙ idp) ∙ p ∙ idp) (
               funext-nat-∼  z (λ x → Ω-fmap-β∙ (fst (auto (f x))) idp ∙
               !-inv-l (snd (fst (auto (f x)))))) ⟫
          ! (ap (λ u → u idp) (ap (fst ∘ ⊙Ω-fmap) homog-idf) ∙ idp) ∙
          (Ω-fmap-β∙ (fst (auto (f z))) idp ∙
          !-inv-l (snd (fst (auto (f z))))) ∙ idp
            =⟪ ap (λ p → ! (ap (λ u → u idp)
                 (ap (fst ∘ ⊙Ω-fmap) homog-idf) ∙ idp) ∙ p ∙ idp)
               (! (apd-tr (λ F → Ω-fmap-β∙ F idp ∙ !-inv-l (snd F)) (! homog-idf))) ⟫
          ! (ap (λ u → u idp) (ap (fst ∘ ⊙Ω-fmap) homog-idf) ∙ idp) ∙
          transport (λ v → Ω-fmap v idp == idp) (! homog-idf) idp ∙ idp
            =⟪ lemma homog-idf ⟫
          idp ∎∎

    ⊙∼-evalΩ-sect : str-homog (f z) → has-sect⊙ (⊙Ω-fmap ⊙∼-eval)
    ⊙∼-evalΩ-sect η = ⊙Ω-sect (⊙∼-eval) (⊙∼-eval-sect η)

    module _ (η : str-homog (f z)) where

      open has-sect⊙

      ∼⊙homog= : (x : X) {g : Z → X}
        {fₚ : f z == x} {gₚ : g z == x}
        {H₁ H₂ : f == g}
        {H₁ₚ : ! (app= H₁ z) ∙ fₚ == gₚ}
        {H₂ₚ : ! (app= H₂ z) ∙ fₚ == gₚ}
        →  H₁ == H₂ → (app= H₁ , H₁ₚ) ⊙→∼◃ (app= H₂ , H₂ₚ)
      fst (∼⊙homog= x {fₚ = idp} {H₁ = idp} {H₁ₚ = H₁ₚ} {H₂ₚ} idp) =
        app= (fst (r-inv (⊙∼-evalΩ-sect η)) (ap-post∙idp∘!-inv (H₁ₚ ∙ ! (H₂ₚ))))
      snd (∼⊙homog= x {fₚ = idp} {H₁ = idp} {H₁ₚ = H₁ₚ} {H₂ₚ} idp) = post↯-rotate-in $ =ₛ-in $
        ap (ap (λ p → ! p ∙ idp))
          (app= (ap fst (sect⊙-eq (⊙∼-evalΩ-sect η))) (ap-post∙idp∘!-inv (H₁ₚ ∙ ! (H₂ₚ)))) ∙
        <–-inv-r (ap-equiv (post∙idp∘!-is-equiv) idp idp) (H₁ₚ ∙ ! (H₂ₚ))

      ∼⊙homog∼ : (x : X) {g : Z → X}
        {fₚ : f z == x} {gₚ : g z == x}
        {H₁ H₂ : f ∼ g}
        {H₁ₚ : ! (H₁ z) ∙ fₚ == gₚ}
        {H₂ₚ : ! (H₂ z) ∙ fₚ == gₚ}
        →  H₁ ∼ H₂ → (H₁ , H₁ₚ) ⊙→∼ (H₂ , H₂ₚ)
      fst (∼⊙homog∼ x {fₚ = idp} {gₚ} {H₁} {H₂} {H₁ₚ} {H₂ₚ} K) t =
        ! (app=-β H₁ t) ∙
        fst (∼⊙homog= x {fₚ = idp} {gₚ = gₚ} {H₁ = λ= H₁} {H₂ = λ= H₂}
          {H₁ₚ = (ap (λ p → ! p ∙ idp) (app=-β H₁ z) ∙ H₁ₚ)}
          {H₂ₚ = (ap (λ p → ! p ∙ idp) (app=-β H₂ z) ∙ H₂ₚ)}
          (ap λ= (λ= K))) t ∙
        app=-β H₂ t
      snd (∼⊙homog∼ x {fₚ = idp} {gₚ} {H₁} {H₂} {H₁ₚ} {H₂ₚ} K) = =ₛ-out $
        ap (λ p → ! p ∙ idp) (! (app=-β H₁ z) ∙
          fst (∼⊙homog= (f z) {fₚ = idp} {gₚ = gₚ} {H₁ = λ= H₁} {H₂ = λ= H₂}
            {H₁ₚ = (ap (λ p → ! p ∙ idp) (app=-β H₁ z) ∙ H₁ₚ)}
            {H₂ₚ = (ap (λ p → ! p ∙ idp) (app=-β H₂ z) ∙ H₂ₚ)}
            (ap λ= (λ= K))) z ∙ app=-β H₂ z) ◃∙
        H₂ₚ ◃∎
          =ₛ₁⟨ 0 & 1 & ap-!∙∙ (λ p → ! p ∙ idp) (app=-β H₁ z)
               (fst (∼⊙homog= (f z) {fₚ = idp} {gₚ = gₚ} {H₁ = λ= H₁} {H₂ = λ= H₂}
                 {H₁ₚ = (ap (λ p → ! p ∙ idp) (app=-β H₁ z) ∙ H₁ₚ)}
                 {H₂ₚ = (ap (λ p → ! p ∙ idp) (app=-β H₂ z) ∙ H₂ₚ)}
                 (ap λ= (λ= K))) z) (app=-β H₂ z) ⟩
        ↯ (! (ap (λ p → ! p ∙ idp) (app=-β H₁ z)) ◃∙
         ap (λ p → ! p ∙ idp) (fst (∼⊙homog= (f z) {fₚ = idp} {gₚ = gₚ}
              {H₁ = λ= H₁} {H₂ = λ= H₂}
              {H₁ₚ = (ap (λ p → ! p ∙ idp) (app=-β H₁ z) ∙ H₁ₚ)}
              {H₂ₚ = (ap (λ p → ! p ∙ idp) (app=-β H₂ z) ∙ H₂ₚ)}
              (ap λ= (λ= K))) z) ◃∙
         ap (λ p → ! p ∙ idp) (app=-β H₂ z) ◃∎) ◃∙ H₂ₚ ◃∎
           =ₛ⟨ pre-rotate-in-↯-assoc
                 (snd (∼⊙homog= x
                 {fₚ = idp} {gₚ = gₚ} {H₁ = λ= H₁} {H₂ = λ= H₂}
                 {H₁ₚ = (ap (λ p → ! p ∙ idp) (app=-β H₁ z) ∙ H₁ₚ)}
                 {H₂ₚ = (ap (λ p → ! p ∙ idp) (app=-β H₂ z) ∙ H₂ₚ)}
                 (ap λ= (λ= K)))) ⟩
         H₁ₚ ◃∎ ∎ₛ

-- All loop spaces are strongly homogeneous.

module _ {i} {X : Type i} {x : X} where

  module _ {p : x == x} where

    open homogeneous
    
    loop-homog : homogeneous p
    fst (fst (auto loop-homog q)) ℓ = ℓ ∙ ! p ∙ q
    snd (fst (auto loop-homog q)) = ! (∙-assoc p (! p) q) ∙ ap (λ c → c ∙ q) (!-inv-r p)
    snd (auto loop-homog q) = post∙-is-equiv (! p ∙ q)

    loop-homog-str : str-homog p
    loop-homog-str = homog-to-strhomog p loop-homog

  ∼⊙Ωhomog∼ : ∀ {j} {Z : Ptd j} {p : x == x}
    {f g : Z ⊙→ ⊙[ x == x , p ]}
    {H₁ H₂ : fst f ∼ fst g}
    {H₁ₚ : ! (H₁ (pt Z)) ∙ snd f == snd g}
    {H₂ₚ : ! (H₂ (pt Z)) ∙ snd f == snd g}
    → H₁ ∼ H₂ → (H₁ , H₁ₚ) ⊙→∼ (H₂ , H₂ₚ)
  ∼⊙Ωhomog∼ {Z = Z} {p} {f} K = ∼⊙homog∼ (loop-homog-str {p = fst f (pt Z)}) p K

open str-homog public
