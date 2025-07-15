{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.SIP
open import lib.wild-cats.WildCat
open import lib.types.Sigma
open import lib.types.Modality
open import Coslice
open import Cos-wc
open import CosMap-conv
open import Cos-univ

module modality.Mod-Cos where

module _ {ℓ j} (μ : Modality ℓ) (A : Type j) where

  open Modality μ
  open MapsCos A

  -- full subcategory of μ-local types under A
  Coslice-loc-wc : WildCat
  ob Coslice-loc-wc = Σ (Coslice ℓ j A) (λ X → is-local (ty X))
  hom Coslice-loc-wc X Y = fst X *→ fst Y
  id₁ Coslice-loc-wc X = id-cos {X = fst X}
  _◻_ Coslice-loc-wc g f = g ∘* f
  ρ Coslice-loc-wc f = idp
  lamb Coslice-loc-wc f = UndFun∼-to-== (lunit-∘* f)
  α Coslice-loc-wc h g f = UndFun∼-to-== (*→-assoc h g f)

  module _ (X : ob Coslice-loc-wc) where

    contr-iso-cos-loc-aux : is-contr $
      Σ (Σ (Coslice ℓ j A) (λ Y₀ → Σ (fst X *→ Y₀) (iso-cos A))) (λ (Y₀ , _) → is-local (ty Y₀))
    contr-iso-cos-loc-aux = 
      equiv-preserves-level
        ((Σ-contr-red {A = Σ (Coslice ℓ j A) (λ Y₀ → Σ (fst X *→ Y₀) (iso-cos A))}
          (contr-iso-cos (fst X)))⁻¹)
        {{inhab-prop-is-contr (snd X) {{is-local-is-prop}}}}

    abstract
      contr-iso-cos-loc : is-contr (Σ (ob Coslice-loc-wc) (λ Y → Σ (fst X *→ fst Y) (iso-cos A)))
      contr-iso-cos-loc = equiv-preserves-level lemma {{contr-iso-cos-loc-aux}}
        where
          lemma :
            Σ (Σ (Coslice ℓ j A) (λ Y₀ → Σ (fst X *→ Y₀) (iso-cos A))) (λ (Y₀ , _) → is-local (ty Y₀))
              ≃
            Σ (ob Coslice-loc-wc) (λ Y → Σ (fst X *→ fst Y) (iso-cos A))
          lemma =
            equiv
              (λ ((Y₀ , eqv) , loc) → (Y₀ , loc) , eqv)
              (λ ((Y₀ , loc) , eqv) → (Y₀ , eqv) , loc)
              (λ _ → idp)
              λ _ → idp

    id-sys-iso-cos-loc : ID-sys _ (λ Y → Σ (fst X *→ fst Y) (iso-cos A)) X (id-cos , iso-cos-id A (fst X))
    id-sys-iso-cos-loc = tot-cent-idsys contr-iso-cos-loc

  -- functor on coslices induced by arbitrary modality

  Mod-cos : Coslice ℓ j A → Coslice ℓ j A
  ty (Mod-cos *[ ty , str ]) = ◯ ty
  Coslice.str (Mod-cos *[ ty , str ]) a = η (str a)

  Mod-cos-fmap : {X : Coslice ℓ j A} {Y : Coslice ℓ j A}
    → (X *→ Y) → (Mod-cos X *→ Mod-cos Y)
  Mod-cos-fmap {X} F = ◯-fmap (fst F) , λ a → ◯-fmap-β (fst F) (str X a) ∙ ap η (snd F a)

  Mod-cos-fmap-id : (X : Coslice ℓ j A) → < Mod-cos X > Mod-cos-fmap id-cos ∼ id-cos
  fst (Mod-cos-fmap-id X) = ◯-elim (λ x → ◯-=-is-local (◯-elim (λ _ → ◯-is-local) η x) x) λ x → ◯-fmap-β (λ z → z) x
  snd (Mod-cos-fmap-id X) a =
    ap (λ p → ! p ∙ snd (Mod-cos-fmap {X} id-cos) a)
      (◯-elim-β (λ x → ◯-=-is-local (◯-elim (λ _ → ◯-is-local) η x) x) (◯-fmap-β (λ z → z)) (str X a)) ∙
    ap (λ p → ! (◯-elim-β (λ _ → ◯-is-local) η (str X a)) ∙ p) (∙-unit-r (◯-elim-β (λ _ → ◯-is-local) η (str X a))) ∙
    !-inv-l (◯-elim-β (λ _ → ◯-is-local) η (str X a)) 

  Mod-cos-fmap-∘ : {X : Coslice ℓ j A} {Y : Coslice ℓ j A} {Z : Coslice ℓ j A}
    → (g : Y *→ Z) (f : X *→ Y)
    → < Mod-cos X > Mod-cos-fmap (g ∘* f) ∼ Mod-cos-fmap g ∘* Mod-cos-fmap f
  fst (Mod-cos-fmap-∘ g f) = ◯-elim
    (λ x → ◯-=-is-local (fst (Mod-cos-fmap (g ∘* f)) x) (fst (Mod-cos-fmap g ∘* Mod-cos-fmap f) x))
    λ x →
      ◯-fmap-β (fst g ∘ fst f) x ∙ ! (ap (fst (Mod-cos-fmap g)) (◯-fmap-β (fst f) x) ∙ ◯-fmap-β (fst g) (fst f x))
  snd (Mod-cos-fmap-∘ {X} {Y} {Z} g f) a =
    ap (λ p → ! p ∙ snd (Mod-cos-fmap (g ∘* f)) a)
      (◯-elim-β (λ x → ◯-=-is-local (fst (Mod-cos-fmap (g ∘* f)) x) (fst (Mod-cos-fmap g ∘* Mod-cos-fmap f) x))
      (λ x →
        ◯-fmap-β (fst g ∘ fst f) x ∙
        ! (ap (fst (Mod-cos-fmap g)) (◯-fmap-β (fst f) x) ∙ ◯-fmap-β (fst g) (fst f x)))
      (str X a)) ∙
    ap (λ p →
        ! (◯-fmap-β (fst g ∘ fst f) (str X a) ∙
        ! (ap (fst (Mod-cos-fmap g)) (◯-fmap-β (fst f) (str X a)) ∙ p)) ∙
        snd (Mod-cos-fmap (g ∘* f)) a)
      (apCommSq2' (◯-fmap-β (fst g)) (snd f a)) ∙
    (equal
      (◯-elim-β (λ _ → ◯-is-local) (λ x → η (fst g (fst f x))) (str X a))
      (◯-elim-β (λ _ → ◯-is-local) (λ x → η (fst f x)) (str X a))
      (◯-elim-β (λ _ → ◯-is-local) (λ x → η (fst g x)) (str Y a))
      (snd f a) (snd g a))
    module Mod-cos-∘ where
      equal : {z₁ : ◯ (ty Z)} {y₁ : ◯ (ty Y)} {z : ty Z} {y y' : ty Y}
        (p₁ : z₁ == η (fst g y)) (p₂ : y₁ == η y) (p₃ : ◯-elim (λ _ → ◯-is-local) (λ x → η (fst g x)) (η y') == η (fst g y'))
        (q₁ : y == y') (q₂ : fst g y' == z) →
        ! (p₁ ∙
        ! (ap (◯-elim (λ _ → ◯-is-local) (λ x → η (fst g x))) p₂ ∙
        ap (λ z → ◯-elim (λ _ → ◯-is-local) (λ x → η (fst g x)) (η z)) q₁ ∙
        p₃ ∙'
        ! (ap (λ z → η (fst g z)) q₁))) ∙
        p₁ ∙
        ap η (ap (fst g) q₁ ∙ q₂)
          ==
        ap (◯-elim (λ _ → ◯-is-local) (λ x → η (fst g x))) (p₂ ∙ ap η q₁) ∙
        p₃ ∙
        ap η q₂
      equal idp idp p₃ idp idp = ap (λ p → p ∙ idp) (!-! p₃)

  -- adjunction associated to modality

  -- hom map of the adjunction
  Mod-cos-hom : {X : Coslice ℓ j A} {Y : Coslice ℓ j A}
    → (Mod-cos X *→ Y) → (X *→ Y)
  fst (Mod-cos-hom f) = fst f ∘ η
  snd (Mod-cos-hom f) a = snd f a

  -- inverse of hom map
  Mod-cos-hom-inv : {X : Coslice ℓ j A} {Y : Coslice ℓ j A}
    → is-local (ty Y) → (X *→ Y) → (Mod-cos X *→ Y)
  fst (Mod-cos-hom-inv p f) = ◯-rec p (fst f)
  snd (Mod-cos-hom-inv {X} p f) a = ◯-rec-β p (fst f) (str X a) ∙ snd f a

  -- extensional form of `ap Mod-cos-hom`
  ap-Mod-cos-hom : {X : Coslice ℓ j A} {Y : Coslice ℓ j A} {h₁ h₂ : Mod-cos X *→ Y}
    → < Mod-cos X > h₁ ∼ h₂ → < X > Mod-cos-hom h₁ ∼ Mod-cos-hom h₂
  fst (ap-Mod-cos-hom H) x = fst H (η x) 
  snd (ap-Mod-cos-hom H) a = snd H a

  ap-Mod-cos-hom-id : {X : Coslice ℓ j A} {Y : Coslice ℓ j A} {f : Mod-cos X *→ Y}
    → < X > ap-Mod-cos-hom (cos∼id f) ∼∼ cos∼id (Mod-cos-hom f)
  fst ap-Mod-cos-hom-id _ = idp
  snd ap-Mod-cos-hom-id _ = idp

  abstract
    ap-Mod-cos-coh : {X : Coslice ℓ j A} {Y : Coslice ℓ j A} {h₁ h₂ : Mod-cos X *→ Y} (H : < Mod-cos X > h₁ ∼ h₂)
      → ap Mod-cos-hom (UndFun∼-to-== H) == UndFun∼-to-== (ap-Mod-cos-hom H)
    ap-Mod-cos-coh {h₁ = h₁} = 
      UndFun-ind {f = h₁} (λ h₂ H → ap Mod-cos-hom (UndFun∼-to-== H) == UndFun∼-to-== (ap-Mod-cos-hom H))
        (ap (ap Mod-cos-hom) UndFun∼-β ∙
        ! (ap UndFun∼-to-== (∼∼-cos∼-to-== (ap-Mod-cos-hom-id {f = h₁})) ∙ UndFun∼-β))

  -- naturality of hom map in the codomain
  Mod-cos-cod : {X : Coslice ℓ j A} {Y : Coslice ℓ j A} {Z : Coslice ℓ j A}
    (g : Y *→ Z) (h : Mod-cos X *→ Y)
    → < X > g ∘* Mod-cos-hom h ∼ Mod-cos-hom (g ∘* h)
  fst (Mod-cos-cod g h) _ = idp
  snd (Mod-cos-cod g h) _ = idp

  -- naturality of hom map in the domain
  Mod-cos-dom : {X : Coslice ℓ j A} {Y : Coslice ℓ j A} {Z : Coslice ℓ j A}
    (f : Z *→ X) (h : Mod-cos X *→ Y)
    → < Z > Mod-cos-hom h ∘* f ∼ Mod-cos-hom (h ∘* Mod-cos-fmap f) 
  fst (Mod-cos-dom f h) x = ap (fst h) (! (◯-fmap-β (fst f) x))
  snd (Mod-cos-dom {X} {Y} {Z} f h) a = equal (◯-elim-β (λ _ → ◯-is-local) (λ x → η (fst f x)) (str Z a)) (snd f a) (snd h a)
    module Mod-cos-nat where
      equal : {x₁ : ty (Mod-cos X)} {x₂ x₃ : ty X} {y : ty Y}
        (p : x₁ == η x₂) (q : x₂ == x₃) (s : fst h (η x₃) == y) → 
        ! (ap (fst h) (! p)) ∙
        ap (λ x → fst h (η x)) q ∙ s
          ==
        ap (fst h) (p ∙ ap η q) ∙ s
      equal idp idp s = idp

  -- 2-coherence
  
  module Mod-2coher
    {X : Coslice ℓ j A} {Y : Coslice ℓ j A} {Z : Coslice ℓ j A} {W : Coslice ℓ j A}
    (f₂ : Z *→ X) (f₃ : W *→ Z) (f₁ : Mod-cos X *→ Y) where

    abstract
      two-coher-Mod-cos :
        < W >
          pre-∘*-∼ f₃ (Mod-cos-dom f₂ f₁) ∼∘-cos
          Mod-cos-dom f₃ (f₁ ∘* Mod-cos-fmap f₂) ∼∘-cos
          ap-Mod-cos-hom (*→-assoc f₁ (Mod-cos-fmap f₂) (Mod-cos-fmap f₃))
        ∼∼
          *→-assoc (Mod-cos-hom f₁) f₂ f₃ ∼∘-cos
          Mod-cos-dom (f₂ ∘* f₃) f₁ ∼∘-cos
          ap-Mod-cos-hom (post-∘*-∼ f₁ (Mod-cos-fmap-∘ f₂ f₃))
      two-coher-Mod-cos =
        (λ x → ! (ap (λ p →
          ap (fst f₁) (! (◯-fmap-β (fst f₂ ∘ fst f₃) x)) ∙ ap (fst f₁) p) (◯-elim-β _ _ x) ∙
        aux-fun (◯-fmap-β (fst f₂ ∘ fst f₃ ) x) (◯-fmap-β (fst f₃) x) (◯-fmap-β (fst f₂) (fst f₃ x)))) ,
        λ a → aux-str a
            (snd f₃ a) (snd f₂ a) (snd f₁ a)
            (◯-elim-β (λ _ → ◯-is-local) (λ x → η (fst f₂ (fst f₃ x))) (str W a))
            (◯-elim-β (λ _ → ◯-is-local) (λ x → η (fst f₃ x)) (str W a))
            (◯-elim-β (λ _ → ◯-is-local) (λ z → η (fst f₂ z)))
            (◯-elim-β
              (λ x →
                ◯-=-is-local
                  (◯-elim (λ _ → ◯-is-local) (λ z → η (fst f₂ (fst f₃ z))) x)
                  (◯-elim (λ _ → ◯-is-local) (λ z → η (fst f₂ z)) (◯-elim (λ _ → ◯-is-local) (λ z → η (fst f₃ z)) x)))
              (λ x →
                ◯-elim-β (λ _ → ◯-is-local) (λ z → η (fst f₂ (fst f₃ z))) x ∙
                ! (ap (◯-elim (λ _ → ◯-is-local) (λ z → η (fst f₂ z)))
                    (◯-elim-β (λ _ → ◯-is-local) (λ z → η (fst f₃ z)) x) ∙
                ◯-elim-β (λ _ → ◯-is-local) (λ z → η (fst f₂ z)) (fst f₃ x))) (str W a))

        where
        
          aux-fun : {x₁ x₂ : ty (Mod-cos X)} {z₁ z₂ : ty (Mod-cos Z)}
            (p₁ : x₁ == x₂) (p₂ : z₁ == z₂) (p₃ : fst (Mod-cos-fmap f₂) z₂ == x₂) → 
            ap (fst f₁) (! p₁) ∙
            ap (fst f₁) (p₁ ∙ ! (ap (fst (Mod-cos-fmap f₂)) p₂ ∙ p₃))
              ==
            ap (fst f₁) (! p₃) ∙
            ap (λ z → fst f₁ (◯-fmap (fst f₂) z)) (! p₂) ∙ idp
          aux-fun idp idp p₃ = ! (∙-unit-r (ap (fst f₁) (! p₃)))
          
          abstract
            aux-str : (a : A)
              {x' : ◯ (ty X)} {x : ty X} {z' : ◯ (ty Z)} {z : ty Z} {y : ty Y}
              {s : x' == ◯-elim (λ _ → ◯-is-local) (λ x → η (fst f₂ x)) z'}
              (q₁ : fst f₃ (str W a) == z) (q₂ : fst f₂ z == x) (q₃ : fst f₁ (η x) == y)
              (p₁ : x' == η (fst f₂ (fst f₃ (str W a)))) (p₂ : z' == η (fst f₃ (str W a)))
              (H : ◯-elim (λ _ → ◯-is-local) (λ x → η (fst f₂ x)) ∘ η ∼ η ∘ fst f₂)
              (r : s == p₁ ∙ ! (ap (fst (Mod-cos-fmap f₂)) p₂ ∙ H (fst f₃ (str W a)))) → 
              ap (λ p →
                  ! p ∙ ap (λ z → fst f₁ (η (fst f₂ z))) q₁ ∙
                  ap (λ x → fst f₁ (η x)) q₂ ∙ q₃)
                (! (! (ap (λ p → ap (fst f₁) (! p₁) ∙ ap (fst f₁) p) r ∙
                    aux-fun p₁ p₂ (H (fst f₃ (str W a)))))) ∙
              (ap (λ p →  p ∙
                  ap (λ z → fst f₁ (η (fst f₂ z))) q₁ ∙ ap (λ x → fst f₁ (η x)) q₂ ∙ q₃)
                (!-∙ (ap (fst f₁) (! (H (fst f₃ (str W a)))))
                  (ap (λ x → fst f₁ (◯-elim (λ _ → ◯-is-local) (λ z → η (fst f₂ z)) x)) (! p₂) ∙ idp)) ∙
              ∙-assoc
                (! (ap (λ x → fst f₁ (◯-elim (λ _ → ◯-is-local) (λ z → η (fst f₂ z)) x)) (! p₂) ∙ idp))
                (! (ap (fst f₁) (! (H (fst f₃ (str W a))))))
                (ap (λ z → fst f₁ (η (fst f₂ z))) q₁ ∙ ap (λ x → fst f₁ (η x)) q₂ ∙ q₃)) ∙
              ap (_∙_ (! (ap (λ x → fst f₁ (◯-elim (λ _ → ◯-is-local) (λ z → η (fst f₂ z)) x)) (! p₂) ∙ idp)))
                ((! (∙-assoc
                    (! (ap (fst f₁) (! (H (fst f₃ (str W a))))))
                    (ap (λ z → fst f₁ (η (fst f₂ z))) q₁)
                    (ap (λ x → fst f₁ (η x)) q₂ ∙ q₃)) ∙
                  ap (λ p → p ∙ ap (λ x → fst f₁ (η x)) q₂ ∙ q₃)
                    (hmtpy-nat-!-sq (λ x → ap (fst f₁) (! (H x))) q₁) ∙
                  ∙-assoc
                    (ap (λ z → fst f₁ (◯-elim (λ _ → ◯-is-local) (λ x → η (fst f₂ x)) (η z))) q₁)
                    (! (ap (fst f₁) (! (H z))))
                    (ap (λ x → fst f₁ (η x)) q₂ ∙ q₃)) ∙
                ap (_∙_ (ap (λ z → fst f₁ (◯-elim (λ _ → ◯-is-local) (λ x → η (fst f₂ x)) (η z))) q₁))
                  (Mod-cos-nat.equal f₂ f₁ a (H z) q₂ q₃)) ∙
                (ap (λ p → p ∙
                    ap (λ x → fst f₁ (◯-elim (λ _ → ◯-is-local) (λ z → η (fst f₂ z)) (η x))) q₁ ∙
                    ap (fst f₁) ((H z) ∙ ap η q₂) ∙ q₃)
                  (!-∙ (ap (λ x → fst f₁ (◯-elim (λ _ → ◯-is-local) (λ z → η (fst f₂ z)) x)) (! p₂)) idp) ∙ idp) ∙
                ap (λ q → q)
                  (Mod-cos-nat.equal f₃
                    ((λ x → fst f₁ (◯-elim (λ _ → ◯-is-local) (λ z → η (fst f₂ z)) x)) ,
                     (λ w → ap (fst f₁) (H (str Z w) ∙ ap η (snd f₂ w)) ∙ snd f₁ w))
                   a p₂ q₁ (ap (fst f₁) ((H z) ∙ ap η q₂) ∙ q₃)) ∙
                ap (λ p → p ∙  ap (fst f₁) ((H z) ∙ ap η q₂) ∙ q₃)
                  (ap-∘ (fst f₁) (◯-elim (λ _ → ◯-is-local) (λ x → η (fst f₂ x))) (p₂ ∙ ap η q₁)) ∙
                ! (ap-ap-∙-∙ (fst f₁) (◯-elim (λ _ → ◯-is-local) (λ x → η (fst f₂ x))) (p₂ ∙ ap η q₁)
                  ((H z) ∙ ap η q₂) q₃)
                ==
              (ap (λ p → p ∙ ap (λ x → fst f₁ (η (fst f₂ x))) q₁ ∙ ap (λ x → fst f₁ (η x)) q₂ ∙ q₃)
                (!-∙ idp (ap (fst f₁) (! p₁) ∙ ap (fst f₁) s)) ∙
              ∙-assoc
                (! (ap (fst f₁) (! p₁) ∙ ap (fst f₁) s))
                idp
                (ap (λ x → fst f₁ (η (fst f₂ x))) q₁ ∙ ap (λ x → fst f₁ (η x)) q₂ ∙ q₃)) ∙
              ap (_∙_ (! (ap (fst f₁) (! p₁) ∙ ap (fst f₁) s)))
                (ap (λ p → p ∙ ap (λ x → fst f₁ (η x)) q₂ ∙ q₃)
                  (ap-∘ (λ x → fst f₁ (η x)) (fst f₂) q₁) ∙
                ! (ap-ap-∙-∙ (λ x → fst f₁ (η x)) (fst f₂) q₁ q₂ q₃)) ∙
              (ap (λ p → p ∙ ap (λ x → fst f₁ (η x)) (ap (fst f₂) q₁ ∙ q₂) ∙ q₃)
                (!-∙ (ap (fst f₁) (! p₁)) (ap (fst f₁) s)) ∙
              ∙-assoc
                (! (ap (fst f₁) s))
                (! (ap (fst f₁) (! p₁)))
                (ap (λ x → fst f₁ (η x)) (ap (fst f₂) q₁ ∙ q₂) ∙ q₃)) ∙
              ap (_∙_ (! (ap (fst f₁) s)))
                (Mod-cos-nat.equal ((λ x → fst f₂ (fst f₃ x)) , (λ w → ap (fst f₂) (snd f₃ w) ∙ snd f₂ w))
                  f₁ a p₁ (ap (fst f₂) q₁ ∙ q₂) q₃) ∙
              ap (λ p → p ∙ ap (fst f₁) (p₁ ∙ ap η (ap (fst f₂) q₁ ∙ q₂)) ∙ q₃) (!-ap (fst f₁) s) ∙
              ! (∙-assoc (ap (fst f₁) (! s)) (ap (fst f₁) (p₁ ∙ ap η (ap (fst f₂) q₁ ∙ q₂))) q₃) ∙
              ap (λ p → p ∙ q₃) (∙-ap (fst f₁) (! s) (p₁ ∙ ap η (ap (fst f₂) q₁ ∙ q₂))) ∙
              ap (λ p → ap (fst f₁) p ∙ q₃)
                (ap (λ p → ! p ∙ p₁ ∙ ap η (ap (fst f₂) q₁ ∙ q₂)) r ∙
                ap (λ p →
                    ! (p₁ ∙ ! (ap (◯-elim (λ _ → ◯-is-local) (λ x → η (fst f₂ x))) p₂ ∙ p)) ∙  p₁ ∙ ap η (ap (fst f₂) q₁ ∙ q₂))
                  (apCommSq2' H q₁) ∙
                Mod-cos-∘.equal f₂ f₃ a p₁ p₂ (H z) q₁ q₂)
            aux-str a idp idp idp idp idp H idp = aux-str-aux (H (fst f₃ (str W a)))
              where abstract
                aux-str-aux : {v : ◯ (ty X)} (Q : v == η (fst f₂ (fst f₃ (str W a)))) →
                  ap (λ p → ! p ∙ idp) (! (! (! (∙-unit-r (ap (fst f₁) (! Q)))))) ∙
                  (ap (λ p → p ∙ idp) (!-∙ (ap (fst f₁) (! Q)) idp) ∙ idp) ∙
                  ap (λ q → q)
                    ((! (∙-assoc (! (ap (fst f₁) (! Q))) idp idp) ∙
                    ap (λ p → p ∙ idp) (∙-unit-r (! (ap (fst f₁) (! Q)))) ∙ idp) ∙
                    ap (λ q → q) (Mod-cos-nat.equal f₂ f₁ a Q idp idp)) ∙ idp
                    ==
                  (ap (λ p → p ∙ idp) (!-∙ idp (ap (fst f₁) (! Q))) ∙
                  ∙-assoc (! (ap (fst f₁) (! Q))) idp idp) ∙
                  (ap (λ p → p ∙ idp) (!-∙ idp (ap (fst f₁) (! Q))) ∙
                  ∙-assoc (! (ap (fst f₁) (! Q))) idp idp) ∙
                  ap (λ p → p ∙ idp) (!-ap (fst f₁) (! Q)) ∙
                  ! (∙-assoc (ap (fst f₁) (! (! Q))) idp idp) ∙
                  ap (λ p → p ∙ idp) (∙-ap (fst f₁) (! (! Q)) idp) ∙
                  ap (λ p → ap (fst f₁) p ∙ idp) (ap (λ p → p ∙ idp) (!-! Q))
                aux-str-aux idp = idp

  module _
    {X : Coslice ℓ j A} {Y : Coslice ℓ j A} {Z : Coslice ℓ j A} {W : Coslice ℓ j A}
    (f₂ : Z *→ X) (f₃ : W *→ Z) (f₁ : Mod-cos X *→ Y) where

    open Mod-2coher f₂ f₃ f₁

    abstract
      Mod-cos-is-2-coher :
        ap (λ m → m ∘* f₃) (UndFun∼-to-== (Mod-cos-dom f₂ f₁)) ◃∙
        UndFun∼-to-== (Mod-cos-dom f₃ (f₁ ∘* Mod-cos-fmap f₂)) ◃∙
        ap Mod-cos-hom (UndFun∼-to-== (*→-assoc f₁ (Mod-cos-fmap f₂) (Mod-cos-fmap f₃))) ◃∎
          =ₛ
        UndFun∼-to-== (*→-assoc (Mod-cos-hom f₁) f₂ f₃) ◃∙
        UndFun∼-to-== (Mod-cos-dom (f₂ ∘* f₃) f₁) ◃∙
        ap Mod-cos-hom (ap (λ m → f₁ ∘* m) (UndFun∼-to-== (Mod-cos-fmap-∘ f₂ f₃))) ◃∎
      Mod-cos-is-2-coher = 
        ap (λ m → m ∘* f₃) (UndFun∼-to-== (Mod-cos-dom f₂ f₁)) ◃∙
        UndFun∼-to-== (Mod-cos-dom f₃ (f₁ ∘* Mod-cos-fmap f₂)) ◃∙
        ap Mod-cos-hom (UndFun∼-to-== (*→-assoc f₁ (Mod-cos-fmap f₂) (Mod-cos-fmap f₃))) ◃∎
          =ₛ₁⟨ 2 & 1 & ap-Mod-cos-coh (*→-assoc f₁ (Mod-cos-fmap f₂) (Mod-cos-fmap f₃)) ⟩
        ap (λ m → m ∘* f₃) (UndFun∼-to-== (Mod-cos-dom f₂ f₁)) ◃∙
        UndFun∼-to-== (Mod-cos-dom f₃ (f₁ ∘* Mod-cos-fmap f₂)) ◃∙
        UndFun∼-to-== (ap-Mod-cos-hom (*→-assoc f₁ (Mod-cos-fmap f₂) (Mod-cos-fmap f₃))) ◃∎
          =ₛ₁⟨ 0 & 1 & whisk-cos-conv-r (Mod-cos-dom f₂ f₁) ⟩
        UndFun∼-to-== (pre-∘*-∼ f₃ (Mod-cos-dom f₂ f₁)) ◃∙
        UndFun∼-to-== (Mod-cos-dom f₃ (f₁ ∘* Mod-cos-fmap f₂)) ◃∙
        UndFun∼-to-== (ap-Mod-cos-hom (*→-assoc f₁ (Mod-cos-fmap f₂) (Mod-cos-fmap f₃))) ◃∎
          =ₛ⟨ cos∘-conv-tri ⟩
        UndFun∼-to-==
          (pre-∘*-∼ f₃ (Mod-cos-dom f₂ f₁) ∼∘-cos
          Mod-cos-dom f₃ (f₁ ∘* Mod-cos-fmap f₂) ∼∘-cos
          ap-Mod-cos-hom (*→-assoc f₁ (Mod-cos-fmap f₂) (Mod-cos-fmap f₃))) ◃∎
          =ₛ₁⟨ ap UndFun∼-to-== (∼∼-cos∼-to-== two-coher-Mod-cos) ⟩
        UndFun∼-to-==
          (*→-assoc (Mod-cos-hom f₁) f₂ f₃ ∼∘-cos
          Mod-cos-dom (f₂ ∘* f₃) f₁ ∼∘-cos
          ap-Mod-cos-hom (post-∘*-∼ f₁ (Mod-cos-fmap-∘ f₂ f₃))) ◃∎
          =ₛ⟨ !ₛ cos∘-conv-tri ⟩
        UndFun∼-to-== (*→-assoc (Mod-cos-hom f₁) f₂ f₃) ◃∙
        UndFun∼-to-== (Mod-cos-dom (f₂ ∘* f₃) f₁) ◃∙
        UndFun∼-to-== (ap-Mod-cos-hom (post-∘*-∼ f₁ (Mod-cos-fmap-∘ f₂ f₃))) ◃∎
          =ₛ₁⟨ 2 & 1 & ! (ap (ap Mod-cos-hom) (whisk-cos-conv-l (Mod-cos-fmap-∘ f₂ f₃)) ∙ ap-Mod-cos-coh _) ⟩
        UndFun∼-to-== (*→-assoc (Mod-cos-hom f₁) f₂ f₃) ◃∙
        UndFun∼-to-== (Mod-cos-dom (f₂ ∘* f₃) f₁) ◃∙
        ap Mod-cos-hom (ap (λ m → f₁ ∘* m) (UndFun∼-to-== (Mod-cos-fmap-∘ f₂ f₃))) ◃∎ ∎ₛ
