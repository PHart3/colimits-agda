{-# OPTIONS --without-K --rewriting --lossy-unification #-}

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

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {X₁ : Type ℓ₁} {X₂ : Type ℓ₂} {X₃ : Type ℓ₃} {X₄ : Type ℓ₄} (f₁ : X₁ → X₂) (f₂ : X₃ → X₁) (f₃ : X₄ → X₃) (f₄ : X₄ → X₁) where

  -- generalized form of 2-coherence proof amenable to path induction
  2-coher-Join-cmp-gen : {x₁ x₂ x₃ x₄ x₅ : X₄} 
    {t₁ : f₃ x₁ == f₃ x₂} {t₂ : f₃ x₃ == f₃ x₂} {t₃ : f₃ x₃ == f₃ x₄} {t₄ : f₃ x₅ == f₃ x₄}
    (t₅ : x₁ == x₂) (t₆ : x₃ == x₂) (t₇ : x₃ == x₄) (t₈ : x₅ == x₄) →
    ∀ {v₁ v₂ v₃ v₄} (q₁ : ap f₂ t₁ == v₁) (q₂ : ap f₂ t₂ == v₂) (q₃ : ap f₂ t₃ == v₃) (q₄ : ap f₂ t₄ == v₄)
    (r₁ : ap f₃ t₅ == t₁) (r₂ : ap f₃ t₆ == t₂) (r₃ : ap f₃ t₇ == t₃) (r₄ : ap f₃ t₈ == t₄)
    (u₁ : f₂ (f₃ x₁) == f₄ x₁) (u₂ : f₄ x₂ == f₂ (f₃ x₂)) (u₃ : f₂ (f₃ x₃) == f₄ x₃) (u₄ : f₄ x₄ == f₂ (f₃ x₄)) (u₅ : f₂ (f₃ x₅) == f₄ x₅)
    (s₁ : u₁ ∙ ap f₄ t₅ ∙' u₂ == v₁) (s₂ : u₃ ∙ ap f₄ t₆ ∙' u₂ == v₂) (s₃ : u₃ ∙ ap f₄ t₇ ∙' u₄ == v₃) (s₄ : u₅ ∙ ap f₄ t₈ ∙' u₄ == v₄)
    {Δ : ap (f₁ ∘ f₂ ∘ f₃) (t₅ ∙ ! t₆ ∙ t₇ ∙ ! t₈) == ap f₁ u₁ ∙ ap (f₁ ∘ f₄) (t₅ ∙ ! t₆ ∙ t₇ ∙ ! t₈) ∙' ap f₁ (! u₅)}
    (ρ : Δ ==
      ! (ap-∘-∙!∙! f₁ (f₂ ∘ f₃) t₅ t₆ t₇ t₈) ∙
      (! (ap4 (λ p₁ p₂ p₃ p₄ → ap f₁ p₁ ∙ ! (ap f₁ p₂) ∙ ap f₁ p₃ ∙ ! (ap f₁ p₄))
            (∘-ap f₂ f₃ t₅) (∘-ap f₂ f₃ t₆) (∘-ap f₂ f₃ t₇) (∘-ap f₂ f₃ t₈)) ∙
       ap4 (λ p₁ p₂ p₃ p₄ → ap f₁ (ap f₂ p₁) ∙ ! (ap f₁ (ap f₂ p₂)) ∙ ap f₁ (ap f₂ p₃) ∙ ! (ap f₁ (ap f₂ p₄))) r₁ r₂ r₃ r₄ ∙
       ap4 (λ p₁ p₂ p₃ p₄ → ap f₁ p₁ ∙ ! (ap f₁ p₂) ∙ ap f₁ p₃ ∙ ! (ap f₁ p₄)) q₁ q₂ q₃ q₄ ∙
       ! (ap4 (λ p₁ p₂ p₃ p₄ → ap f₁ p₁ ∙ ! (ap f₁ p₂) ∙ ap f₁ p₃ ∙ ! (ap f₁ p₄)) s₁ s₂ s₃ s₄)) ∙
       {!hmtpy-nat-∙'-ap∙!∙!-aux f₁ f₄ t₅ t₆ t₇ t₈ idp idp idp idp idp!}) →
    ((! (ap (ap f₁) (ap4 (λ p₁ p₂ p₃ p₄ → p₁ ∙ ! p₂ ∙ p₃ ∙ ! p₄) q₁ q₂ q₃ q₄)) ∙
      ∘-ap-∙!∙∙! f₁ f₂ t₁ t₂ t₃ t₄) ∙
     (! (ap (ap (f₁ ∘ f₂)) (ap4 (λ p₁ p₂ p₃ p₄ → p₁ ∙ ! p₂ ∙ p₃ ∙ ! p₄) r₁ r₂ r₃ r₄)) ∙
     ∘-ap-∙!∙∙! (f₁ ∘ f₂) f₃ t₅ t₆ t₇ t₈) ∙ Δ ∙ idp) ∙
    ! (! (ap (ap f₁) (ap4 (λ p₁ p₂ p₃ p₄ → p₁ ∙ ! p₂ ∙ p₃ ∙ ! p₄) s₁ s₂ s₃ s₄)) ∙
      {!∘-ap-∙!∙∙! f₁ f₄ t₅ t₆ t₇ t₈!})
      ==
    idp
  2-coher-Join-cmp-gen = {!!} -- lemma s₁ s₂ s₃ s₄
    where abstract
      lemma : {x : X₁} {v₁ v₂ v₃ v₄ : x == x} (s₁ : idp == v₁) (s₂ : idp == v₂) (s₃ : idp == v₃) (s₄ : idp == v₄) → 
        ((! (ap4 (λ p₁ p₂ p₃ p₄ → ap f₁ p₁ ∙ ! (ap f₁ p₂) ∙ ap f₁ p₃ ∙ ! (ap f₁ p₄)) s₁ s₂ s₃ s₄) ∙ idp) ∙ idp) ∙
        ! (! (ap (ap f₁) (ap4 (λ p₁ p₂ p₃ p₄ → p₁ ∙ ! p₂ ∙ p₃ ∙ ! p₄) s₁ s₂ s₃ s₄)) ∙ idp)
          ==
        ! (ap-∙!∙∙! f₁ v₁ v₂ v₃ v₄)
      lemma idp idp idp idp = idp
-- 
-- 
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
        (2-coher-Join-cmp-gen f₁ (jmap (λ x → x) f₂) (jmap (λ x → x) f₃) (jmap (λ x → x) (f₂ ∘ f₃))
          (jglue (pt A) (pt W)) (jglue a (pt W)) (jglue a w) (jglue (pt A) w)
          (glue-β jleft (jright ∘ f₂) (λ c b → jglue c (f₂ b)) (pt A) (f₃ (pt W)))
          (glue-β jleft (jright ∘ f₂) (λ c b → jglue c (f₂ b)) a (f₃ (pt W)))
          (glue-β jleft (jright ∘ f₂) (λ c b → jglue c (f₂ b)) a (f₃ w))
          (glue-β jleft (jright ∘ f₂) (λ c b → jglue c (f₂ b)) (pt A) (f₃ w))
          (glue-β jleft (jright ∘ f₃) (λ c b → jglue c (f₃ b)) (pt A) (pt W))
          (glue-β jleft (jright ∘ f₃) (λ c b → jglue c (f₃ b)) a (pt W))
          (glue-β jleft (jright ∘ f₃) (λ c b → jglue c (f₃ b)) a w)
          (glue-β jleft (jright ∘ f₃) (λ c b → jglue c (f₃ b)) (pt A) w)
          (glue-β jleft (jright ∘ f₂ ∘ f₃) (λ c b → jglue c (f₂ (f₃ b))) (pt A) (pt W))
          (glue-β jleft (jright ∘ f₂ ∘ f₃) (λ c b → jglue c (f₂ (f₃ b))) a (pt W))
          (glue-β jleft (jright ∘ f₂ ∘ f₃) (λ c b → jglue c (f₂ (f₃ b))) a w)
          (glue-β jleft (jright ∘ f₂ ∘ f₃) (λ c b → jglue c (f₂ (f₃ b))) (pt A) w)
          (jmap-∘-sq-rw A f₁ f₂ f₃)))) ∙
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
