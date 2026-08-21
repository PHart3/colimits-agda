{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Join
open import lib.types.Pushout

-- auxiliary lemmas for the Join 2-coherence proof

module homotopy.Join.Join-2coher-aux where

-- helper path algebra lemma
!-ap4-ap-ap-idf-∙!∙!∙ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ ℓ₇ ℓ₈ ℓ₉ ℓ₁₀ ℓ₁₁ ℓ₁₂ ℓ₁₃} {A₁ : Type ℓ₁} {A₂ : Type ℓ₂} {A₃ : Type ℓ₃} {A₄ : Type ℓ₄} {B : Type ℓ₅}
  {C₁ : Type ℓ₆} {C₂ : Type ℓ₇} {C₃ : Type ℓ₈} {C₄ : Type ℓ₉} {D₁ : Type ℓ₁₀} {D₂ : Type ℓ₁₁} {D₃ : Type ℓ₁₂} {D₄ : Type ℓ₁₃}
  (f : A₁ → A₂ → A₃ → A₄ → B) (g₁ : C₁ → A₁) (g₂ : C₂ → A₂) (g₃ : C₃ → A₃) (g₄ : C₄ → A₄) (k₁ : D₁ → C₁) (k₂ : D₂ → C₂) (k₃ : D₃ → C₃) (k₄ : D₄ → C₄)
  {c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂} {d₁ d₂ : D₁} {d₃ d₄ : D₂} {d₅ d₆ : D₃} {d₇ d₈ : D₄}
  (p₁ : c₁ == c₂) (q₁ : c₃ == c₄) (r₁ : c₅ == c₆) (s₁ : c₇ == c₈) (p₂ : k₁ d₂ == c₂) (q₂ : k₂ d₄ == c₄) (r₂ : k₃ d₆ == c₆) (s₂ : k₄ d₈ == c₈)
  (p₃ : d₁ == d₂) (q₃ : d₃ == d₄) (r₃ : d₅ == d₆) (s₃ : d₇ == d₈) (p₄ : k₁ d₁ == c₉) (q₄ : k₂ d₃ == c₁₀) (r₄ : k₃ d₅ == c₁₁) (s₄ : k₄ d₇ == c₁₂) →
  ! (ap4 f
      (ap g₁ (ap (λ z → z) (p₁ ∙ ! p₂ ∙ ! (ap k₁ p₃) ∙ p₄)))
      (ap g₂ (ap (λ z → z) (q₁ ∙ ! q₂ ∙ ! (ap k₂ q₃) ∙ q₄)))
      (ap g₃ (ap (λ z → z) (r₁ ∙ ! r₂ ∙ ! (ap k₃ r₃) ∙ r₄)))
      (ap g₄ (ap (λ z → z) (s₁ ∙ ! s₂ ∙ ! (ap k₄ s₃) ∙ s₄))))
    ==
  ! (ap4 (λ x₁ x₂ x₃ x₄ → f (g₁ x₁) (g₂ x₂) (g₃ x₃) (g₄ x₄)) p₄ q₄ r₄ s₄) ∙
  ap4 (λ x₁ x₂ x₃ x₄ → f (g₁ (k₁ x₁)) (g₂ (k₂ x₂)) (g₃ (k₃ x₃)) (g₄ (k₄ x₄))) p₃ q₃ r₃ s₃ ∙
  ap4 (λ x₁ x₂ x₃ x₄ → f (g₁ x₁) (g₂ x₂) (g₃ x₃) (g₄ x₄)) p₂ q₂ r₂ s₂ ∙
  ! (ap4 (λ x₁ x₂ x₃ x₄ → f (g₁ x₁) (g₂ x₂) (g₃ x₃) (g₄ x₄)) p₁ q₁ r₁ s₁)
!-ap4-ap-ap-idf-∙!∙!∙ {C₁ = C₁} {C₂} {C₃} {C₄} f g₁ g₂ g₃ g₄  _ _ _ _ idp idp idp idp p₂ q₂ r₂ s₂ idp idp idp idp idp idp idp idp = lemma p₂ q₂ r₂ s₂
  where abstract
    lemma : ∀ {c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈} (p₁ : c₁ == c₂) (p₂ : c₃ == c₄) (p₃ : c₅ == c₆) (p₄ : c₇ == c₈) →
      ! (ap4 f
          (ap g₁ (ap (λ z → z) (! p₁ ∙ idp)))
          (ap g₂ (ap (λ z → z) (! p₂ ∙ idp)))
          (ap g₃ (ap (λ z → z) (! p₃ ∙ idp)))
          (ap g₄ (ap (λ z → z) (! p₄ ∙ idp))))
        ==
      ap4 (λ x₁ x₂ x₃ x₄ → f (g₁ x₁) (g₂ x₂) (g₃ x₃) (g₄ x₄)) p₁ p₂ p₃ p₄ ∙ idp
    lemma idp idp idp idp = idp

module _ {i₀} (A : Ptd i₀) {i₁ i₂ i₃ i₄} {X : Ptd i₁} {Y : Ptd i₂} {Z : Ptd i₃} {W : Ptd i₄} where

  open JoinRec

  abstract

    jmap-∘-sq-rw : ∀ {a w} (f₁ : de⊙ A * de⊙ X → de⊙ Y) (f₂ : de⊙ Z → de⊙ X) (f₃ : de⊙ W → de⊙ Z) → 
      hmtpy-nat-∙' (λ x → ap f₁ (! (fst (jmap⊙-un-∘ {X = A} {Y₁ = W} (f₂ , idp) (f₃ , idp)) x)))
        (jglue (pt A) (pt W) ∙ ! (jglue a (pt W)) ∙ jglue a w ∙ ! (jglue (pt A) w))
        ==
      ! (ap-∘-∙!∙! f₁
          (jmap-un (de⊙ A) f₂ ∘ jmap-un (de⊙ A) f₃)
          (jglue (pt A) (pt W)) (jglue a (pt W)) (jglue a w)
          (jglue (pt A) w)) ∙
      (! (ap4
            (λ x₁ x₂ x₃ x₄ → ap f₁ x₁ ∙ ! (ap f₁ x₂) ∙ ap f₁ x₃ ∙ ! (ap f₁ x₄))
            (∘-ap (jmap-un (de⊙ A) f₂) (jmap-un (de⊙ A) f₃) (glue (pt A , pt W)))
            (∘-ap (jmap-un (de⊙ A) f₂) (jmap-un (de⊙ A) f₃) (jglue a (pt W)))
            (∘-ap (jmap-un (de⊙ A) f₂) (jmap-un (de⊙ A) f₃) (jglue a w))
            (∘-ap (jmap-un (de⊙ A) f₂) (jmap-un (de⊙ A) f₃) (jglue (pt A) w))) ∙
      ap4
        (λ x₁ x₂ x₃ x₄ →
           ap f₁ (ap (jmap-un (de⊙ A) f₂) x₁) ∙
           ! (ap f₁ (ap (jmap-un (de⊙ A) f₂) x₂)) ∙
           ap f₁ (ap (jmap-un (de⊙ A) f₂) x₃) ∙
           ! (ap f₁ (ap (jmap-un (de⊙ A) f₂) x₄)))
        (glue-β jleft (jright ∘ f₃) (λ c b → jglue c (f₃ b)) (pt A) (pt W))
        (glue-β jleft (jright ∘ f₃) (λ c b → jglue c (f₃ b)) a (pt W))
        (glue-β jleft (jright ∘ f₃) (λ c b → jglue c (f₃ b)) a w)
        (glue-β jleft (jright ∘ f₃) (λ c b → jglue c (f₃ b)) (pt A) w) ∙
      ap4 (λ x₁ x₂ x₃ x₄ → ap f₁ x₁ ∙ ! (ap f₁ x₂) ∙ ap f₁ x₃ ∙ ! (ap f₁ x₄))
        (glue-β jleft (jright ∘ f₂) (λ c b → jglue c (f₂ b)) (pt A) (f₃ (pt W)))
        (glue-β jleft (jright ∘ f₂) (λ c b → jglue c (f₂ b)) a (f₃ (pt W)))
        (glue-β jleft (jright ∘ f₂) (λ c b → jglue c (f₂ b)) a (f₃ w))
        (glue-β jleft (jright ∘ f₂) (λ c b → jglue c (f₂ b)) (pt A) (f₃ w)) ∙
      ! (ap4 (λ x₁ x₂ x₃ x₄ → ap f₁ x₁ ∙ ! (ap f₁ x₂) ∙ ap f₁ x₃ ∙ ! (ap f₁ x₄))
           (glue-β jleft (jright ∘ f₂ ∘ f₃) (λ c b → jglue c (f₂ (f₃ b))) (pt A) (pt W))
           (glue-β jleft (jright ∘ f₂ ∘ f₃) (λ c b → jglue c (f₂ (f₃ b))) a (pt W))
           (glue-β jleft (jright ∘ f₂ ∘ f₃) (λ c b → jglue c (f₂ (f₃ b))) a w)
           (glue-β jleft (jright ∘ f₂ ∘ f₃) (λ c b → jglue c (f₂ (f₃ b))) (pt A) w))) ∙
      hmtpy-nat-∙'-ap∙!∙!-aux f₁
        (jmap-un (de⊙ A) (f₂ ∘ f₃))
        (jglue (pt A) (pt W)) (jglue a (pt W)) (jglue a w)
        (jglue (pt A) w)
        idp idp idp idp idp
    jmap-∘-sq-rw {a} {w} f₁ f₂ f₃ =
      JoinMapEq-β-ap∙!∙! (λ _ → idp) (λ _ → idp) _ f₁ ∙
      ap (λ p →
          ! (ap-∘-∙!∙! f₁ (jmap-un (de⊙ A) f₂ ∘ jmap-un (de⊙ A) f₃) (jglue (pt A) (pt W)) (jglue a (pt W)) (jglue a w) (jglue (pt A) w)) ∙
          p ∙
          hmtpy-nat-∙'-ap∙!∙!-aux f₁
            (jmap-un (de⊙ A) (f₂ ∘ f₃))
            (jglue (pt A) (pt W)) (jglue a (pt W)) (jglue a w)
            (jglue (pt A) w)
            idp idp idp idp idp) (
          !-ap4-ap-ap-idf-∙!∙!∙ (λ q₁ q₂ q₃ q₄ → q₁ ∙ ! q₂ ∙ q₃ ∙ ! q₄)
            (ap f₁) (ap f₁) (ap f₁) (ap f₁)
            (ap (jmap-un (de⊙ A) f₂)) (ap (jmap-un (de⊙ A) f₂)) (ap (jmap-un (de⊙ A) f₂)) (ap (jmap-un (de⊙ A) f₂))
            (glue-β jleft (jright ∘ f₂ ∘ f₃) (λ c b → jglue c (f₂ (f₃ b))) (pt A) (pt W))
            (glue-β jleft (jright ∘ f₂ ∘ f₃) (λ c b → jglue c (f₂ (f₃ b))) a (pt W))
            (glue-β jleft (jright ∘ f₂ ∘ f₃) (λ c b → jglue c (f₂ (f₃ b))) a w)
            (glue-β jleft (jright ∘ f₂ ∘ f₃) (λ c b → jglue c (f₂ (f₃ b))) (pt A) w)
            (glue-β jleft (jright ∘ f₂) (λ c b → jglue c (f₂ b)) (pt A) (f₃ (pt W)))
            (glue-β jleft (jright ∘ f₂) (λ c b → jglue c (f₂ b)) a (f₃ (pt W)))
            (glue-β jleft (jright ∘ f₂) (λ c b → jglue c (f₂ b)) a (f₃ w))
            (glue-β jleft (jright ∘ f₂) (λ c b → jglue c (f₂ b)) (pt A) (f₃ w))
            (glue-β jleft (jright ∘ f₃) (λ c b → jglue c (f₃ b)) (pt A) (pt W))
            (glue-β jleft (jright ∘ f₃) (λ c b → jglue c (f₃ b)) a (pt W))
            (glue-β jleft (jright ∘ f₃) (λ c b → jglue c (f₃ b)) a w)
            (glue-β jleft (jright ∘ f₃) (λ c b → jglue c (f₃ b)) (pt A) w)
            (∘-ap (jmap-un (de⊙ A) f₂) (jmap-un (de⊙ A) f₃) (jglue (pt A) (pt W)))
            (∘-ap (jmap-un (de⊙ A) f₂) (jmap-un (de⊙ A) f₃) (jglue a (pt W)))
            (∘-ap (jmap-un (de⊙ A) f₂) (jmap-un (de⊙ A) f₃) (jglue a w))
            (∘-ap (jmap-un (de⊙ A) f₂) (jmap-un (de⊙ A) f₃) (jglue (pt A) w)))
