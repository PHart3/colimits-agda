{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.PtdMap-conv
open import lib.types.Join
open import lib.types.LoopSpace
open import lib.types.Homogeneous
open import homotopy.Join.JoinAdjointLoopCod
open import lib.wild-cats.Ladj-2-coher
open import lib.types.Pushout

-- The unary pointed join is a 2-coherent left adjoint to the covariant Loop hom functor.

module homotopy.Join.Join-2coher where

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

-- proof of 2-coherence
module JLA-2-coher-cmp {i₀} (A : Ptd i₀) {i₁ i₂ i₃ i₄} {X : Ptd i₁} {Y : Ptd i₂} {Z : Ptd i₃} {W : Ptd i₄} where

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
        (glue-β jleft (jright ∘ f₃) (λ a b → jglue a (f₃ b)) (pt A) (pt W))
        (glue-β jleft (jright ∘ f₃) (λ a b → jglue a (f₃ b)) a (pt W))
        (glue-β jleft (jright ∘ f₃) (λ a b → jglue a (f₃ b)) a w)
        (glue-β jleft (jright ∘ f₃) (λ a b → jglue a (f₃ b)) (pt A) w) ∙
      ap4 (λ x₁ x₂ x₃ x₄ → ap f₁ x₁ ∙ ! (ap f₁ x₂) ∙ ap f₁ x₃ ∙ ! (ap f₁ x₄))
        (glue-β jleft (jright ∘ f₂) (λ a b → jglue a (f₂ b)) (pt A) (f₃ (pt W)))
        (glue-β jleft (jright ∘ f₂) (λ a b → jglue a (f₂ b)) a (f₃ (pt W)))
        (glue-β jleft (jright ∘ f₂) (λ a b → jglue a (f₂ b)) a (f₃ w))
        (glue-β jleft (jright ∘ f₂) (λ a b → jglue a (f₂ b)) (pt A) (f₃ w)) ∙
      ! (ap4 (λ x₁ x₂ x₃ x₄ → ap f₁ x₁ ∙ ! (ap f₁ x₂) ∙ ap f₁ x₃ ∙ ! (ap f₁ x₄))
           (glue-β jleft (jright ∘ f₂ ∘ f₃) (λ a b → jglue a (f₂ (f₃ b))) (pt A) (pt W))
           (glue-β jleft (jright ∘ f₂ ∘ f₃) (λ a b → jglue a (f₂ (f₃ b))) a (pt W))
           (glue-β jleft (jright ∘ f₂ ∘ f₃) (λ a b → jglue a (f₂ (f₃ b))) a w)
           (glue-β jleft (jright ∘ f₂ ∘ f₃) (λ a b → jglue a (f₂ (f₃ b))) (pt A) w))) ∙
      hmtpy-nat-∙'-ap∙!∙!-aux f₁
        (jmap-un (de⊙ A) (f₂ ∘ f₃))
        (jglue (pt A) (pt W)) (jglue a (pt W)) (jglue a w)
        (jglue (pt A) w)
        idp idp idp idp idp
    jmap-∘-sq-rw {a} {w} f₁ f₂ f₃ =
      JoinMapEq-β-ap∙!∙! _ _ _ f₁ ∙
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
            (glue-β jleft (jright ∘ f₂ ∘ f₃) (λ a b → jglue a (f₂ (f₃ b))) (pt A) (pt W))
            (glue-β jleft (jright ∘ f₂ ∘ f₃) (λ a b → jglue a (f₂ (f₃ b))) a (pt W))
            (glue-β jleft (jright ∘ f₂ ∘ f₃) (λ a b → jglue a (f₂ (f₃ b))) a w)
            (glue-β jleft (jright ∘ f₂ ∘ f₃) (λ a b → jglue a (f₂ (f₃ b))) (pt A) w)
            (glue-β jleft (jright ∘ f₂) (λ a b → jglue a (f₂ b)) (pt A) (f₃ (pt W)))
            (glue-β jleft (jright ∘ f₂) (λ a b → jglue a (f₂ b)) a (f₃ (pt W)))
            (glue-β jleft (jright ∘ f₂) (λ a b → jglue a (f₂ b)) a (f₃ w))
            (glue-β jleft (jright ∘ f₂) (λ a b → jglue a (f₂ b)) (pt A) (f₃ w))
            (glue-β jleft (jright ∘ f₃) (λ a b → jglue a (f₃ b)) (pt A) (pt W))
            (glue-β jleft (jright ∘ f₃) (λ a b → jglue a (f₃ b)) a (pt W))
            (glue-β jleft (jright ∘ f₃) (λ a b → jglue a (f₃ b)) a w)
            (glue-β jleft (jright ∘ f₃) (λ a b → jglue a (f₃ b)) (pt A) w)
            (∘-ap (jmap-un (de⊙ A) f₂) (jmap-un (de⊙ A) f₃) (jglue (pt A) (pt W)))
            (∘-ap (jmap-un (de⊙ A) f₂) (jmap-un (de⊙ A) f₃) (jglue a (pt W)))
            (∘-ap (jmap-un (de⊙ A) f₂) (jmap-un (de⊙ A) f₃) (jglue a w))
            (∘-ap (jmap-un (de⊙ A) f₂) (jmap-un (de⊙ A) f₃) (jglue (pt A) w)))

  open JLA-into-ap

  {-
    It suffices to prove that the underlying homotopies are equal
    because loop spaces are strongly homogeneous and the pointed
    covariant hom preserves homogeneous types.
  -}
{-
  abstract
    2-coher-Join-cmp : (h₁ : A ⊙* X ⊙→ Y) (h₂ : Z ⊙→ X) (h₃ : W ⊙→ Z) →
      !-⊙∼ (⊙∘-assoc-crd (JLA-into X Y h₁) h₂ h₃) ∙⊙∼
      ⊙∘-pre h₃ (JLA-nat-dom-⊙∼ h₂ h₁) ∙⊙∼
      JLA-nat-dom-⊙∼ h₃ (h₁ ⊙∘ jmap⊙-un A h₂) ∙⊙∼
      ap-crd-into (⊙∘-assoc-crd h₁ (jmap⊙-un A h₂) (jmap⊙-un A h₃) ∙⊙∼
        ⊙∘-post h₁ (!-⊙∼ (jmap⊙-un-∘ h₂ h₃))) ∙⊙∼
      !-⊙∼ (JLA-nat-dom-⊙∼ (h₂ ⊙∘ h₃) h₁)
        ⊙→∼
      ⊙∼-id ((JLA-into X Y h₁) ⊙∘ h₂ ⊙∘ h₃)
    2-coher-Join-cmp (f₁ , idp) (f₂ , idp) (f₃ , idp) = ∼⊙homog∼ ⊙→-homog-str-⊙Ωcod _ (λ w →
      ⊙∘-conv-tri-∙! _ _ _ _ ∙
      ap ⊙-crd∼-to-== (⊙→∼-to-== (∼⊙Ωhomog∼ λ a →
        {!-- GOAL:
        ((! (ap (ap f₁)
          (ap4 (λ p₁ p₂ p₃ p₄ → p₁ ∙ ! p₂ ∙ p₃ ∙ ! p₄)
            (glue-β jleft (jright ∘ f₂) (λ c b → jglue c (f₂ b)) (pt A) (f₃ (pt W)))
            (glue-β jleft (jright ∘ f₂) (λ c b → jglue c (f₂ b)) a (f₃ (pt W)))
            (glue-β jleft (jright ∘ f₂) (λ c b → jglue c (f₂ b)) a (f₃ w))
            (glue-β jleft (jright ∘ f₂) (λ c b → jglue c (f₂ b)) (pt A) (f₃ w)))) ∙
          ∘-ap-∙!∙∙! f₁
            (jmap (λ x → x) f₂)
            (jglue (pt A) (f₃ (pt W))) (jglue a (f₃ (pt W))) (jglue a (f₃ w)) (jglue (pt A) (f₃ w))) ∙
         (! (ap (ap (f₁ ∘ jmap (λ x → x) f₂))
           (ap4 (λ p₁ p₂ p₃ p₄ → p₁ ∙ ! p₂ ∙ p₃ ∙ ! p₄)
             (glue-β jleft (jright ∘ f₃) (λ c b → jglue c (f₃ b)) (pt A) (pt W))
             (glue-β jleft (jright ∘ f₃) (λ c b → jglue c (f₃ b)) a (pt W))
             (glue-β jleft (jright ∘ f₃) (λ c b → jglue c (f₃ b)) a w)
             (glue-β jleft (jright ∘ f₃) (λ c b → jglue c (f₃ b)) (pt A) w))) ∙
         ∘-ap-∙!∙∙! (f₁ ∘ jmap (λ x → x) f₂)
           (jmap (λ x → x) f₃)
           (jglue (pt A) (pt W)) (jglue a (pt W)) (jglue a w) (jglue (pt A) w)) ∙
         hmtpy-nat-∙' (λ x → ap f₁ (! (fst (jmap⊙-un-∘ (f₂ , idp) (f₃ , idp)) x)))
           (jglue (pt A) (pt W) ∙ ! (jglue a (pt W)) ∙ jglue a w ∙ ! (jglue (pt A) w)) ∙ idp) ∙
        ! (! (ap (ap f₁)
          (ap4 (λ p₁ p₂ p₃ p₄ → p₁ ∙ ! p₂ ∙ p₃ ∙ ! p₄)
            (glue-β jleft (jright ∘ f₂ ∘ f₃) (λ c b → jglue c (f₂ (f₃ b))) (pt A) (pt W))
            (glue-β jleft (jright ∘ f₂ ∘ f₃) (λ c b → jglue c (f₂ (f₃ b))) a (pt W))
            (glue-β jleft (jright ∘ f₂ ∘ f₃) (λ c b → jglue c (f₂ (f₃ b))) a w)
            (glue-β jleft (jright ∘ f₂ ∘ f₃) (λ c b → jglue c (f₂ (f₃ b))) (pt A) w))) ∙
          ∘-ap-∙!∙∙! f₁
            (jmap (λ x → x) (f₂ ∘ f₃))
            (jglue (pt A) (pt W)) (jglue a (pt W)) (jglue a w) (jglue (pt A) w))
          ==
        idp!})) ∙
      ⊙-crd∼-to-==-β _)
      -}
{-
module _ {i₀} (A : Ptd i₀) {i₁ i₂ i₃ i₄} {X : Ptd i₁} {Y : Ptd i₂} {Z : Ptd i₃} {W : Ptd i₄} where

  open JLA-into-ap
  open JLA-2-coher-cmp A

  -- converting 2-coherence property via the SIP
  abstract
    2-coher-Join : (h₁ : A ⊙* X ⊙→ Y) (h₂ : Z ⊙→ X) (h₃ : W ⊙→ Z) →
      ! (⊙-crd∼-to-== (⊙∘-assoc-crd (JLA-into X Y h₁) h₂ h₃)) ∙
      ap (λ m → m ⊙∘ h₃) (⊙-crd∼-to-== (JLA-nat-dom-⊙∼ h₂ h₁)) ∙
      ⊙-crd∼-to-== (JLA-nat-dom-⊙∼ h₃ (h₁ ⊙∘ jmap⊙-un A h₂)) ∙
      ap (JLA-into W Y)
        (⊙-crd∼-to-== (⊙∘-assoc-crd h₁ (jmap⊙-un A h₂) (jmap⊙-un A h₃)) ∙
        ap (λ m →  h₁ ⊙∘ m) (! (jmap⊙-un-∘-== h₂ h₃))) ∙
      ! (⊙-crd∼-to-== (JLA-nat-dom-⊙∼ (h₂ ⊙∘ h₃) h₁))
        ==
      idp
    2-coher-Join h₁ h₂ h₃ = =ₛ-out $
      ! (⊙-crd∼-to-== (⊙∘-assoc-crd (JLA-into X Y h₁) h₂ h₃)) ◃∙
      ap (λ m → m ⊙∘ h₃) (⊙-crd∼-to-== (JLA-nat-dom-⊙∼ h₂ h₁)) ◃∙
      ⊙-crd∼-to-== (JLA-nat-dom-⊙∼ h₃ (h₁ ⊙∘ jmap⊙-un A h₂)) ◃∙
      ap (JLA-into W Y)
        (⊙-crd∼-to-== (⊙∘-assoc-crd h₁ (jmap⊙-un A h₂) (jmap⊙-un A h₃)) ∙
        ap (λ m →  h₁ ⊙∘ m) (! (jmap⊙-un-∘-== h₂ h₃))) ◃∙
      ! (⊙-crd∼-to-== (JLA-nat-dom-⊙∼ (h₂ ⊙∘ h₃) h₁)) ◃∎
        =ₛ₁⟨ 0 & 1 & ! (!⊙-conv (⊙∘-assoc-crd (JLA-into X Y h₁) h₂ h₃)) ⟩
      ⊙-crd∼-to-== (!-⊙∼ (⊙∘-assoc-crd (JLA-into X Y h₁) h₂ h₃)) ◃∙
      ap (λ m → m ⊙∘ h₃) (⊙-crd∼-to-== (JLA-nat-dom-⊙∼ h₂ h₁)) ◃∙
      ⊙-crd∼-to-== (JLA-nat-dom-⊙∼ h₃ (h₁ ⊙∘ jmap⊙-un A h₂)) ◃∙
      ap (JLA-into W Y)
        (⊙-crd∼-to-== (⊙∘-assoc-crd h₁ (jmap⊙-un A h₂) (jmap⊙-un A h₃)) ∙
        ap (λ m →  h₁ ⊙∘ m) (! (jmap⊙-un-∘-== h₂ h₃))) ◃∙
      ! (⊙-crd∼-to-== (JLA-nat-dom-⊙∼ (h₂ ⊙∘ h₃) h₁)) ◃∎
        =ₛ₁⟨ 1 & 1 & ! (whisk⊙-conv-r (JLA-nat-dom-⊙∼ h₂ h₁)) ⟩
      ⊙-crd∼-to-== (!-⊙∼ (⊙∘-assoc-crd (JLA-into X Y h₁) h₂ h₃)) ◃∙
      ⊙-crd∼-to-== (⊙∘-pre h₃ (JLA-nat-dom-⊙∼ h₂ h₁)) ◃∙
      ⊙-crd∼-to-== (JLA-nat-dom-⊙∼ h₃ (h₁ ⊙∘ jmap⊙-un A h₂)) ◃∙
      ap (JLA-into W Y)
        (⊙-crd∼-to-== (⊙∘-assoc-crd h₁ (jmap⊙-un A h₂) (jmap⊙-un A h₃)) ∙
        ap (λ m →  h₁ ⊙∘ m) (! (jmap⊙-un-∘-== h₂ h₃))) ◃∙
      ! (⊙-crd∼-to-== (JLA-nat-dom-⊙∼ (h₂ ⊙∘ h₃) h₁)) ◃∎
        =ₛ₁⟨ 4 & 1 & ! (!⊙-conv (JLA-nat-dom-⊙∼ (h₂ ⊙∘ h₃) h₁)) ⟩
      ⊙-crd∼-to-== (!-⊙∼ (⊙∘-assoc-crd (JLA-into X Y h₁) h₂ h₃)) ◃∙
      ⊙-crd∼-to-== (⊙∘-pre h₃ (JLA-nat-dom-⊙∼ h₂ h₁)) ◃∙
      ⊙-crd∼-to-== (JLA-nat-dom-⊙∼ h₃ (h₁ ⊙∘ jmap⊙-un A h₂)) ◃∙
      ap (JLA-into W Y)
        (⊙-crd∼-to-== (⊙∘-assoc-crd h₁ (jmap⊙-un A h₂) (jmap⊙-un A h₃)) ∙
        ap (λ m →  h₁ ⊙∘ m) (! (jmap⊙-un-∘-== h₂ h₃))) ◃∙
      ⊙-crd∼-to-== (!-⊙∼ (JLA-nat-dom-⊙∼ (h₂ ⊙∘ h₃) h₁)) ◃∎
        =ₛ₁⟨ 3 & 1 & ap (ap (JLA-into W Y)) (
          ap (λ p → ⊙-crd∼-to-== (⊙∘-assoc-crd h₁ (jmap⊙-un A h₂) (jmap⊙-un A h₃)) ∙ p)
            (ap (ap (_⊙∘_ h₁)) (! (!⊙-conv (jmap⊙-un-∘ h₂ h₃))) ∙
            ! (whisk⊙-conv-l (!-⊙∼ (jmap⊙-un-∘ h₂ h₃)))) ∙
          ! (=ₛ-out (⊙∘-conv
            (⊙∘-assoc-crd h₁ (jmap⊙-un A h₂) (jmap⊙-un A h₃))
            (⊙∘-post h₁ (!-⊙∼ (jmap⊙-un-∘ h₂ h₃)))))) ⟩
      ⊙-crd∼-to-== (!-⊙∼ (⊙∘-assoc-crd (JLA-into X Y h₁) h₂ h₃)) ◃∙
      ⊙-crd∼-to-== (⊙∘-pre h₃ (JLA-nat-dom-⊙∼ h₂ h₁)) ◃∙
      ⊙-crd∼-to-== (JLA-nat-dom-⊙∼ h₃ (h₁ ⊙∘ jmap⊙-un A h₂)) ◃∙
      ap (JLA-into W Y) (⊙-crd∼-to-==
        (⊙∘-assoc-crd h₁ (jmap⊙-un A h₂) (jmap⊙-un A h₃) ∙⊙∼
        ⊙∘-post h₁ (!-⊙∼ (jmap⊙-un-∘ h₂ h₃)))) ◃∙
      ⊙-crd∼-to-== (!-⊙∼ (JLA-nat-dom-⊙∼ (h₂ ⊙∘ h₃) h₁)) ◃∎
        =ₛ₁⟨ 3 & 1 & ap-crd-into-agree
          (⊙∘-assoc-crd h₁ (jmap⊙-un A h₂) (jmap⊙-un A h₃) ∙⊙∼
          ⊙∘-post h₁ (!-⊙∼ (jmap⊙-un-∘ h₂ h₃))) ⟩
      ⊙-crd∼-to-== (!-⊙∼ (⊙∘-assoc-crd (JLA-into X Y h₁) h₂ h₃)) ◃∙
      ⊙-crd∼-to-== (⊙∘-pre h₃ (JLA-nat-dom-⊙∼ h₂ h₁)) ◃∙
      ⊙-crd∼-to-== (JLA-nat-dom-⊙∼ h₃ (h₁ ⊙∘ jmap⊙-un A h₂)) ◃∙
      ⊙-crd∼-to-== (ap-crd-into
        (⊙∘-assoc-crd h₁ (jmap⊙-un A h₂) (jmap⊙-un A h₃) ∙⊙∼
        ⊙∘-post h₁ (!-⊙∼ (jmap⊙-un-∘ h₂ h₃)))) ◃∙
      ⊙-crd∼-to-== (!-⊙∼ (JLA-nat-dom-⊙∼ (h₂ ⊙∘ h₃) h₁)) ◃∎
        =ₛ⟨ ⊙∘-conv-quint
              (!-⊙∼ (⊙∘-assoc-crd (JLA-into X Y h₁) h₂ h₃))
              (⊙∘-pre h₃ (JLA-nat-dom-⊙∼ h₂ h₁))
              (JLA-nat-dom-⊙∼ h₃ (h₁ ⊙∘ jmap⊙-un A h₂))
              (ap-crd-into
                (⊙∘-assoc-crd h₁ (jmap⊙-un A h₂) (jmap⊙-un A h₃) ∙⊙∼
                ⊙∘-post h₁ (!-⊙∼ (jmap⊙-un-∘ h₂ h₃))))
              (!-⊙∼ (JLA-nat-dom-⊙∼ (h₂ ⊙∘ h₃) h₁)) ⟩
      ⊙-crd∼-to-==
        (!-⊙∼ (⊙∘-assoc-crd (JLA-into X Y h₁) h₂ h₃) ∙⊙∼
        ⊙∘-pre h₃ (JLA-nat-dom-⊙∼ h₂ h₁) ∙⊙∼
        JLA-nat-dom-⊙∼ h₃ (h₁ ⊙∘ jmap⊙-un A h₂) ∙⊙∼
        ap-crd-into
          (⊙∘-assoc-crd h₁ (jmap⊙-un A h₂) (jmap⊙-un A h₃) ∙⊙∼
          ⊙∘-post h₁ (!-⊙∼ (jmap⊙-un-∘ h₂ h₃))) ∙⊙∼
        !-⊙∼ (JLA-nat-dom-⊙∼ (h₂ ⊙∘ h₃) h₁)) ◃∎
        =ₛ₁⟨ ap ⊙-crd∼-to-== (⊙→∼-to-== (2-coher-Join-cmp h₁ h₂ h₃)) ⟩
      ⊙-crd∼-to-== (⊙∼-id ((JLA-into X Y h₁) ⊙∘ h₂ ⊙∘ h₃)) ◃∎
        =ₛ₁⟨ ⊙-crd∼-to-==-β (JLA-into X Y h₁ ⊙∘ h₂ ⊙∘ h₃) ⟩
      idp ◃∎ ∎ₛ

abstract
  Join-is-2-coher : ∀ {i j} (X : Ptd i) → ladj-is-2coher (JoinLoopCodAdj {j = j} X)
  Join-is-2-coher X = 2-coher-Join X
-}
