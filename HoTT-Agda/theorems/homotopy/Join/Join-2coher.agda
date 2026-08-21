{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.PtdMap-conv
open import lib.types.Join
open import lib.types.LoopSpace
open import lib.types.Homogeneous
open import lib.wild-cats.Ladj-2-coher
open import homotopy.Join.JoinAdjointLoopCod
open import homotopy.Join.Join-2coher-aux

-- The unary pointed join is a 2-coherent left adjoint to the covariant Loop hom functor.

module homotopy.Join.Join-2coher where

-- proof of 2-coherence
module JLA-2-coher-cmp {i₀} (A : Ptd i₀) {i₁ i₂ i₃ i₄} {X : Ptd i₁} {Y : Ptd i₂} {Z : Ptd i₃} {W : Ptd i₄} where

  open JoinRec
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
