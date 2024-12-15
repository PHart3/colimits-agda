{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.types.Truncation
open import Coslice

module TruncAdj where

module _ {j} (A : Type j) where

  open MapsCos A

  module _ (n : ℕ₋₂) where

    -- truncation functor on coslices

    Trunc-cos : ∀ {i}  → (Coslice i j A) → (Coslice i j A)
    ty (Trunc-cos *[ ty , fun ]) = Trunc n ty
    Coslice.fun (Trunc-cos *[ ty , fun ]) a = [ fun a ]

    Trunc-cos-fmap : ∀ {i k} {X : Coslice i j A} {Y : Coslice k j A}
      → ((X *→ Y) → (Trunc-cos X *→ Trunc-cos Y))
    Trunc-cos-fmap F = Trunc-fmap (fst F) , λ a → ap [_] (snd F a)

    Trunc-cos-fmap-∘ : ∀ {i k ℓ} {X : Coslice i j A} {Y : Coslice k j A} {Z : Coslice ℓ j A}
      → (g : Y *→ Z) (f : X *→ Y)
      → < Trunc-cos X > Trunc-cos-fmap (g ∘* f) ∼ Trunc-cos-fmap g ∘* Trunc-cos-fmap f
    fst (Trunc-cos-fmap-∘ g f) = Trunc-elim (λ _ → idp)
    snd (Trunc-cos-fmap-∘ g f) a =
      ap-∘-∙ [_] (fst g) (snd f a) (snd g a) ∙
      ap (λ p → p ∙ ap [_] (snd g a)) (ap-∘ (Trunc-elim (λ x → [ fst g x ])) [_] (snd f a))

    -- hom map of the adjunction
    Trunc-cos-hom : ∀ {i k} {X : Coslice i j A} {Y : Coslice k j A}
      {{p : has-level n (ty Y)}} → (Trunc-cos X *→ Y) → (X *→ Y)
    fst (Trunc-cos-hom f) = fst f ∘ [_]
    snd (Trunc-cos-hom f) a = snd f a

    -- naturality of hom map
    Trunc-cos-∘-nat : ∀ {i k ℓ} {X : Coslice i j A} {Y : Coslice k j A} {Z : Coslice ℓ j A}
      {{p : has-level n (ty Y)}} (f : Z *→ X) (h : Trunc-cos X *→ Y)
      → < Z > Trunc-cos-hom h ∘* f ∼ Trunc-cos-hom (h ∘* Trunc-cos-fmap f) 
    fst (Trunc-cos-∘-nat f h) x = idp
    snd (Trunc-cos-∘-nat f h) a = ap (λ p → p ∙ snd h a) (ap-∘ (fst h) [_] (snd f a))

    ap-Trunc-cos-hom : ∀ {i k} {X : Coslice i j A} {Y : Coslice k j A} {{p : has-level n (ty Y)}}
      {h₁ h₂ : Trunc-cos X *→ Y} → < Trunc-cos X > h₁ ∼ h₂ → < X > Trunc-cos-hom h₁ ∼ Trunc-cos-hom h₂
    fst (ap-Trunc-cos-hom H) x = fst H [ x ]
    snd (ap-Trunc-cos-hom H) a = snd H a

    -- Our custom ap function behaves as expected
    ap-Trunc-cos-hom-id : ∀ {i k} {X : Coslice i j A} {Y : Coslice k j A} {{p : has-level n (ty Y)}}
      (f : Trunc-cos X *→ Y) → < X > ap-Trunc-cos-hom (cos∼id f) ∼∼ cos∼id (Trunc-cos-hom f)
    fst (ap-Trunc-cos-hom-id f) x = idp
    snd (ap-Trunc-cos-hom-id f) a = idp

    -- Truncation on coslices is a 2-coherent left adjoint

    module _ {i₁ i₂ i₃ i₄}
      {X : Coslice i₁ j A} {Y : Coslice i₂ j A} {Z : Coslice i₃ j A} {W : Coslice i₄ j A}
      {{p : has-level n (ty Y)}}
      (f₂ : Z *→ X) (f₃ : W *→ Z) (f₁ : Trunc-cos X *→ Y) where

      two-coher-Trunc-cos :
        < W >
          (pre-∘*-∼ f₃ (Trunc-cos-∘-nat f₂ f₁)) ∼∘-cos
          Trunc-cos-∘-nat f₃ (f₁ ∘* Trunc-cos-fmap f₂) ∼∘-cos
          ap-Trunc-cos-hom (*→-assoc f₁ (Trunc-cos-fmap f₂) (Trunc-cos-fmap f₃))
        ∼∼
          *→-assoc (Trunc-cos-hom f₁) f₂ f₃ ∼∘-cos
          Trunc-cos-∘-nat (f₂ ∘* f₃) f₁ ∼∘-cos
          ap-Trunc-cos-hom (post-∘*-∼ f₁ (Trunc-cos-fmap-∘ f₂ f₃))
      fst two-coher-Trunc-cos x = idp
      snd two-coher-Trunc-cos a = lemma a (snd f₃ a)
        where
          lemma : (a : A) {w : ty Z} (τ : w == fun Z a) → 
            ap (λ q → q) ((ap (λ p₁ → p₁ ∙ ap (λ x → fst f₁ [ x ])
              (snd f₂ a) ∙ snd f₁ a)
              (hmtpy-nat-!-sq (λ x → idp) τ) ∙
              ∙-assoc (ap (λ z → fst f₁ [ fst f₂ z ]) τ) idp
              (ap (λ x → fst f₁ [ x ]) (snd f₂ a) ∙ snd f₁ a)) ∙
              ap (_∙_ (ap (λ z → fst f₁ [ fst f₂ z ]) τ))
              (ap (λ p₁ → p₁ ∙ snd f₁ a) (ap-∘ (fst f₁) [_] (snd f₂ a)))) ∙
            ap (λ q → q) (ap (λ p₁ → p₁ ∙ ap (fst f₁)
              (ap [_] (snd f₂ a)) ∙ snd f₁ a)
              (ap-∘ (λ x → fst f₁ (Trunc-elim (λ x₁ → [ fst f₂ x₁ ]) x))
              [_] τ)) ∙
            ap (λ p₁ → p₁ ∙ ap (fst f₁) (ap [_] (snd f₂ a)) ∙ snd f₁ a)
              (ap-∘ (fst f₁) (Trunc-elim (λ x → [ fst f₂ x ]))
              (ap [_] τ)) ∙
            ! (ap2-∙-∙ (fst f₁) (Trunc-elim (λ x → [ fst f₂ x ]))
              (ap [_] τ) (ap [_] (snd f₂ a)) (snd f₁ a))
            ==
            ap (λ q → q) (ap (λ p₁ → p₁ ∙ ap (λ x → fst f₁ [ x ])
              (snd f₂ a) ∙ snd f₁ a)
              (ap-∘ (λ x → fst f₁ [ x ]) (fst f₂) τ) ∙
              ! (ap2-∙-∙ (λ x → fst f₁ [ x ]) (fst f₂) τ
              (snd f₂ a) (snd f₁ a))) ∙
            ap (λ q → q) (ap (λ p₁ → p₁ ∙ snd f₁ a)
              (ap-∘ (fst f₁) [_] (ap (fst f₂) τ ∙ snd f₂ a))) ∙
            ap (λ p₁ → ap (fst f₁) p₁ ∙ snd f₁ a)
              (ap-∘-∙ [_] (fst f₂) τ (snd f₂ a) ∙
              ap (λ p₁ → p₁ ∙ ap [_] (snd f₂ a))
              (ap-∘ (Trunc-elim (λ x → [ fst f₂ x ])) [_] τ))
          lemma a idp =
            ap (λ p → p ∙ idp) (ap-idf (ap (λ q → q)
              (ap (λ p₁ → p₁ ∙ snd f₁ a) (ap-∘ (fst f₁) [_] (snd f₂ a)))))
