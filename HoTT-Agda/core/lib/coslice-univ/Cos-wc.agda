{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.types.Unit
open import lib.wild-cats.WildCat
open import lib.wild-cats.Cocone-wc-SIP
open import lib.wild-cats.Adjoint
open import SIP-CosMap
open import CosMap-conv

-- coslice universe as wild category
  
module Cos-wc where

open import Coslice public

module _ {j} (A : Type j) where

  open MapsCos A
  
  Coslice-wc : ∀ i → WildCat
  ob (Coslice-wc i) = Coslice i j A
  hom (Coslice-wc i) X Y = X *→ Y
  id₁ (Coslice-wc i) _ = id-cos
  _◻_ (Coslice-wc i) g f = g ∘* f
  ρ (Coslice-wc i) f = idp
  lamb (Coslice-wc i) f = UndHom∼-to-== (lunit-∘* f)
  α (Coslice-wc i) h g f = UndHom∼-to-== (*→-assoc h g f)

  iso-cos : ∀ {i} {X Y : ob (Coslice-wc i)} (f : hom (Coslice-wc i) X Y) → Type i
  iso-cos f = is-equiv (fst f)

  iso-cos-id : ∀ {i} (X : ob (Coslice-wc i)) → iso-cos (id-cos {X = X})
  iso-cos-id X = idf-is-equiv (ty X)

  -- isomorphism implies equivalence
  iso-to-eqv-cos : ∀ {i} {X Y : ob (Coslice-wc i)} {f : hom (Coslice-wc i) X Y} → iso-cos f → equiv-wc (Coslice-wc i) f
  fst (iso-to-eqv-cos {X = X} {f = f} iso) = (is-equiv.g iso) , λ a → ap (is-equiv.g iso) (! (snd f a)) ∙ is-equiv.g-f iso (str X a)
  fst (snd (iso-to-eqv-cos {X = X} {f = f} iso)) = UndHom∼-to-== ((λ x → ! (is-equiv.g-f iso x)) , λ a →
    ∙-unit-r (! (! (is-equiv.g-f iso (str X a)))) ∙
    !-! (is-equiv.g-f iso (str X a)) ∙
    ! (! (∙-assoc (ap (is-equiv.g iso) (snd f a)) (ap (is-equiv.g iso) (! (snd f a))) (is-equiv.g-f iso (str X a))) ∙
      ap (λ p → p ∙ is-equiv.g-f iso (str X a)) (ap-!-inv (is-equiv.g iso) (snd f a))))
  snd (snd (iso-to-eqv-cos {X = X} {Y} {f} iso)) = UndHom∼-to-== ((λ x → ! (is-equiv.f-g iso x)) , λ a →
    ! (ap (λ p → p ∙ snd f a)
        (ap-∙ (fst f) (ap (is-equiv.g iso) (! (snd f a))) (is-equiv.g-f iso (str X a)) ∙
        ap2 _∙_
          (∘-ap (fst f) (is-equiv.g iso) (! (snd f a)) ∙
          hmtpy-nat-∙' (is-equiv.f-g iso) (! (snd f a)))
          (is-equiv.adj iso (str X a))) ∙
      aux (is-equiv.f-g iso (str Y a)) (is-equiv.f-g iso (fst f (str X a))) (snd f a)))
      where abstract
        aux : ∀ {ℓ} {A : Type ℓ} {x y z w : A} (p₁ : x == y) (p₂ : z == w) (p₃ : w == y)
          → ((p₁ ∙ ap (λ z → z) (! p₃) ∙' ! p₂) ∙ p₂) ∙ p₃ == ! (! p₁) ∙ idp
        aux idp idp p₃ = ap (λ p → p ∙ p₃) (∙-unit-r _ ∙ ap-idf (! p₃)) ∙ !-inv-l p₃
        
  -- 2-coherence

  abstract

    triangle-wc-Cos : ∀ {i} → triangle-wc (Coslice-wc i)
    triangle-wc-Cos {b = Y} g f = ! (whisk-cos-conv-l (lunit-∘* f) ∙ ap UndHom∼-to-== (∼∼-cos∼-to-== ((λ _ → idp) , (λ a → aux (snd f a)))))
      where
        aux : {a : A} {x : ty Y} (q : x == str Y a) →
          ap (λ p → ap (λ v → fst g v) p ∙ snd g a)
            (! (∙-unit-r q) ∙
          ap (λ p → p ∙ idp) (! (ap-idf q)))
            ==
          ap (λ p → p ∙ snd g a) (ap-∘ (fst g) (λ z → z) q) ∙
          ! (ap-ap-∙-∙ (fst g) (λ x → x) q idp (snd g a))
        aux idp = idp

    pentagon-wc-Cos : ∀ {i} → pentagon-wc (Coslice-wc i)
    pentagon-wc-Cos {b = Y} {Z} {W} k g h f = =ₛ-out $
      ap (λ m → m ∘* f) (UndHom∼-to-== (*→-assoc k g h)) ◃∙
      UndHom∼-to-== (*→-assoc k (g ∘* h) f) ◃∙
      ap (λ m → k ∘* m) (UndHom∼-to-== (*→-assoc g h f)) ◃∎
        =ₛ₁⟨ 0 & 1 & whisk-cos-conv-r (*→-assoc k g h) ⟩
      UndHom∼-to-== (pre-∘*-∼ f (*→-assoc k g h)) ◃∙
      UndHom∼-to-== (*→-assoc k (g ∘* h) f) ◃∙
      ap (λ m → k ∘* m) (UndHom∼-to-== (*→-assoc g h f)) ◃∎
        =ₛ₁⟨ 2 & 1 & whisk-cos-conv-l (*→-assoc g h f) ⟩
      UndHom∼-to-== (pre-∘*-∼ f (*→-assoc k g h)) ◃∙
      UndHom∼-to-== (*→-assoc k (g ∘* h) f) ◃∙
      UndHom∼-to-== (post-∘*-∼ k (*→-assoc g h f)) ◃∎
        =ₛ⟨ cos∘-conv-tri ⟩
      UndHom∼-to-== (pre-∘*-∼ f (*→-assoc k g h) ∼∘-cos *→-assoc k (g ∘* h) f ∼∘-cos post-∘*-∼ k (*→-assoc g h f)) ◃∎
        =ₛ₁⟨ ap UndHom∼-to-== (∼∼-cos∼-to-== ((λ _ → idp) , (λ a → aux (snd f a) (snd h a) (snd g a)))) ⟩
      UndHom∼-to-== (*→-assoc (k ∘* g) h f ∼∘-cos *→-assoc k g (h ∘* f)) ◃∎
        =ₛ₁⟨ =ₛ-out (cos∘-conv (*→-assoc (k ∘* g) h f) (*→-assoc k g (h ∘* f))) ⟩
      (UndHom∼-to-== (*→-assoc (k ∘* g) h f) ∙
      UndHom∼-to-== (*→-assoc k g (h ∘* f))) ◃∎ ∎ₛ
      where
        aux : {a : A} {y₁ y₂ : ty Y} {z : ty Z}
          (p₁ : y₁ == y₂) (p₂ : fst h y₂ == z) (p₃ : fst g z == str W a) → 
          ap (λ q → q)
            ((ap (λ p →
                  p ∙ ap (λ x → fst k (fst g x)) p₂ ∙ ap (fst k) p₃ ∙ snd k a)
                (hmtpy-nat-!-sq (λ x → idp) p₁) ∙
              ∙-assoc (ap (λ z → fst k (fst g (fst h z))) p₁) idp
                (ap (λ x → fst k (fst g x)) p₂ ∙ ap (fst k) p₃ ∙ snd k a)) ∙
              ap (_∙_ (ap (λ z → fst k (fst g (fst h z))) p₁))
                (ap (λ p → p ∙ ap (fst k) p₃ ∙ snd k a) (ap-∘ (fst k) (fst g) p₂) ∙
                ! (ap-ap-∙-∙ (fst k) (fst g) p₂ p₃ (snd k a)))) ∙
          ap (λ q → q)
            (ap (λ p → p ∙ ap (fst k) (ap (fst g) p₂ ∙ p₃) ∙ snd k a)
              (ap-∘ (fst k) (λ x → fst g (fst h x)) p₁) ∙
            ! (ap-ap-∙-∙ (fst k) (λ x → fst g (fst h x)) p₁ (ap (fst g) p₂ ∙ p₃) (snd k a))) ∙
          ap (λ p → ap (fst k) p ∙ snd k a)
            (ap (λ p → p ∙ ap (fst g) p₂ ∙ p₃)
              (ap-∘ (fst g) (fst h) p₁) ∙
            ! (ap-ap-∙-∙ (fst g) (fst h) p₁ p₂ p₃))
            ==
          ap (λ q → q)
            (ap (λ p →  p ∙  ap (λ x → fst k (fst g x)) p₂ ∙ ap (fst k) p₃ ∙ snd k a)
              (ap-∘ (λ x → fst k (fst g x)) (fst h) p₁) ∙
            ! (ap-ap-∙-∙ (λ x → fst k (fst g x)) (fst h) p₁ p₂ (ap (fst k) p₃ ∙ snd k a))) ∙
          ap (λ p → p ∙ ap (fst k) p₃ ∙ snd k a)
            (ap-∘ (fst k) (fst g) (ap (fst h) p₁ ∙ p₂)) ∙
          ! (ap-ap-∙-∙ (fst k) (fst g) (ap (fst h) p₁ ∙ p₂) p₃ (snd k a))
        aux idp idp _ = idp

  -- forgetful functor

  Forg-funct-cos : ∀ {i} → Functor-wc (Coslice-wc (lmax i j)) (Type-wc (lmax i j))
  obj Forg-funct-cos = ty
  arr Forg-funct-cos = fst
  id Forg-funct-cos _ = idp
  comp Forg-funct-cos _ _ = idp

  abstract
    Forg-cos-α : ∀ {i} → F-α-wc (Forg-funct-cos {i})
    Forg-cos-α h g f = ap (λ p → p ∙ idp) (λ=-η idp ∙ fst=-UndHom∼ (*→-assoc h g f))

  Free-funct-cos : ∀ {i} → Functor-wc (Type-wc (lmax i j)) (Coslice-wc (lmax i j))
  obj Free-funct-cos X = *[ (Coprod X A) , inr ]
  fst (arr Free-funct-cos f) (inl x) = inl (f x)
  fst (arr Free-funct-cos f) (inr x) = inr x
  snd (arr Free-funct-cos f) _ = idp
  id Free-funct-cos X = UndHom∼-to-== ((λ { (inl _) → idp ; (inr _) → idp }) , (λ _ → idp))
  comp Free-funct-cos f g = UndHom∼-to-== ((λ { (inl _) → idp ; (inr _) → idp }) , (λ _ → idp))

  free-forg-adj-cos : ∀ {i} → Adjunction (Free-funct-cos {i = i}) (Forg-funct-cos {i = i})
  iso (free-forg-adj-cos {i}) {a = U} {x = V} = free-forg-cos A
  nat-cod free-forg-adj-cos _ _ = idp
  nat-dom free-forg-adj-cos _ _ = idp

CosUnit-contr-term : ∀ {i} {X : ob (Coslice-wc Unit i)} → is-contr (ty X) → is-term-wc (Coslice-wc Unit i) X
fst (has-level-apply (CosUnit-contr-term c Y)) = (λ _ → contr-center c) , (λ _ → contr-has-all-paths {{c}} _ _)
snd (has-level-apply (CosUnit-contr-term c Y)) f = UndHom∼-to-== ((λ _ → contr-has-all-paths {{c}} _ _) ,
  (λ unit → contr-has-all-paths {{=-preserves-contr c}} _ _))

CosUnit-Unit-term : ∀ {i} → is-term-wc (Coslice-wc Unit i) (*[ (Lift Unit) , (λ _ → lift unit) ])
fst (has-level-apply (CosUnit-Unit-term X)) = (λ _ → lift unit) , λ _ → idp 
snd (has-level-apply (CosUnit-Unit-term X)) _ = pair= idp (λ= (λ _ → prop-has-all-paths {{=-preserves-level-instance}} _ _)) 

CosUnit-term-contr : ∀ {i} {X : ob (Coslice-wc Unit i)} → is-term-wc (Coslice-wc Unit i) X → is-contr (ty X)
CosUnit-term-contr {i} t = equiv-preserves-level
  (_ , (eqv-wc-to-eqv-ty (F-equiv-wc (Forg-funct-cos Unit) (term-uniq-wc {C = Coslice-wc Unit i} CosUnit-Unit-term t))))

