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
      {{p : has-level n (ty Y)}} → (X *→ Y) → (Trunc-cos X *→ Y)
    fst (Trunc-cos-hom f) = Trunc-rec (fst f)
    snd (Trunc-cos-hom f) a = snd f a

    -- naturality of hom map
    Trunc-cos-∘-nat : ∀ {i k ℓ} {X : Coslice i j A} {Y : Coslice k j A} {Z : Coslice ℓ j A}
      {{p : has-level n (ty Y)}} (f : Z *→ X) (h : X *→ Y)
      → < Trunc-cos Z > Trunc-cos-hom h ∘* Trunc-cos-fmap f ∼ Trunc-cos-hom (h ∘* f) 
    fst (Trunc-cos-∘-nat f h) = Trunc-elim (λ _ → idp)
    snd (Trunc-cos-∘-nat f h) a = ap (λ p → p ∙ snd h a) (∘-ap (Trunc-elim (fst h)) [_] (snd f a))

    ap-Trunc-cos-hom : ∀ {i k} {X : Coslice i j A} {Y : Coslice k j A} {{p : has-level n (ty Y)}}
      {h₁ h₂ : X *→ Y} → < X > h₁ ∼ h₂ → < Trunc-cos X > Trunc-cos-hom h₁ ∼ Trunc-cos-hom h₂
    fst (ap-Trunc-cos-hom H) = Trunc-elim (λ x → fst H x)
    snd (ap-Trunc-cos-hom H) a = snd H a

    -- Our custom ap function behaves as expected
    ap-Trunc-cos-hom-id : ∀ {i k} {X : Coslice i j A} {Y : Coslice k j A} {{p : has-level n (ty Y)}}
      (f : X *→ Y) → < Trunc-cos X > ap-Trunc-cos-hom (cos∼id f) ∼∼ cos∼id (Trunc-cos-hom f)
    fst (ap-Trunc-cos-hom-id f) = Trunc-elim (λ _ → idp)
    snd (ap-Trunc-cos-hom-id f) a = idp
