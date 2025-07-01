{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Modality
open import lib.wild-cats.WildCats
open import Coslice
open import Cos-wc

module modality.Mod-Cos where

module _ {ℓ j} (μ : Modality ℓ) (A : Type j) where

  open Modality μ
  open MapsCos A
  

  Mod-cos : Coslice ℓ j A → Coslice ℓ j A
  ty (Mod-cos *[ ty , str ]) = ◯ ty
  Coslice.str (Mod-cos *[ ty , str ]) a = η (str a)

  Mod-cos-fmap : {X : Coslice ℓ j A} {Y : Coslice ℓ j A}
    → (X *→ Y) → (Mod-cos X *→ Mod-cos Y)
  Mod-cos-fmap {X} F = ◯-fmap (fst F) , λ a → ◯-fmap-β (fst F) (str X a) ∙ ap η (snd F a)
{-
  Mod-cos-fmap-∘ : {X : Coslice ℓ j A} {Y : Coslice ℓ j A} {Z : Coslice ℓ j A}
    → (g : Y *→ Z) (f : X *→ Y)
    → < Mod-cos X > Mod-cos-fmap (g ∘* f) ∼ Mod-cos-fmap g ∘* Mod-cos-fmap f
  fst (Mod-cos-fmap-∘ g f) = Mod-elim (λ _ → idp)
  snd (Mod-cos-fmap-∘ g f) a =
    ap-∘-∙ [_] (fst g) (snd f a) (snd g a) ∙
    ap (λ p → p ∙ ap [_] (snd g a)) (ap-∘ (Mod-elim (λ x → [ fst g x ])) [_] (snd f a))

  -- hom map of the adjunction
  Mod-cos-hom : {X : Coslice ℓ j A} {Y : Coslice ℓ j A}
    {{p : has-level n (ty Y)}} → (Mod-cos X *→ Y) → (X *→ Y)
  fst (Mod-cos-hom f) = fst f ∘ [_]
  snd (Mod-cos-hom f) a = snd f a

  -- naturality of hom map
  Mod-cos-∘-nat : {X : Coslice ℓ j A} {Y : Coslice ℓ j A} {Z : Coslice ℓ j A}
    {{p : has-level n (ty Y)}} (f : Z *→ X) (h : Mod-cos X *→ Y)
    → < Z > Mod-cos-hom h ∘* f ∼ Mod-cos-hom (h ∘* Mod-cos-fmap f) 
  fst (Mod-cos-∘-nat f h) x = idp
  snd (Mod-cos-∘-nat f h) a = ap (λ p → p ∙ snd h a) (ap-∘ (fst h) [_] (snd f a))
-}
