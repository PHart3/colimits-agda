{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Diagram
open import lib.types.Colim
open import lib.types.Coc-conversion
open import lib.wild-cats.WildCats
open import lib.wild-cats.Diag-coher-wc
open import Diagram-Cos
open import SIP-Cos
open import CosMap-conv
open import Id-col
open import CosColim-Iso
open import Cocone-po
open import Cos-wc
open import CC-conversion

-- the forgetful functor preserves tree-indexed colimits

module Tree-preserve where

module _ {ℓv ℓe ℓ ℓd} {Γ : Graph ℓv ℓe} (tr : is-tree Γ) {A : Type ℓ} (F : CosDiag ℓd ℓ A Γ) where

  tr-coscol-col-≃ : Colim (DiagForg A Γ F) ≃ po-CosCol-ty F
  tr-coscol-col-≃ = po-of-equiv (tree-[id] A tr) ⁻¹

  open Id.Maps Γ A

  tr-coscol-col-ciso : cocone-iso (can-coc (DiagForg A Γ F)) (CocForg (ColCoC-cos F))
  fst (fst tr-coscol-col-ciso) = –> tr-coscol-col-≃
  comp-∼ (snd (fst tr-coscol-col-ciso)) i _ = idp
  comTri-∼ (snd (fst tr-coscol-col-ciso)) g _ = idp
  snd tr-coscol-col-ciso = snd tr-coscol-col-≃

module _ {ℓv ℓe ℓ} {Γ : Graph ℓv ℓe} (tr : is-tree Γ) {A : Type ℓ} where

  open MapsCos A
  open Id.Maps Γ A

  module _ {ℓd} (Δ : Diagram Γ (Coslice-wc A (lmax ℓ ℓd))) where

    private
      Δ-F = Diag-to-grhom Δ
      ceqv = tr-coscol-col-≃ tr Δ-F
      ciso = tr-coscol-col-ciso tr Δ-F

    tr-coscol-col-aux : Coc-wc-iso (Coc-to-wc (can-coc (DiagForg A Γ Δ-F))) (Coc-to-wc (CocForg (ColCoC-cos Δ-F)))
    fst tr-coscol-col-aux = coc-mor-to-wc (fst ciso) 
    fst (snd tr-coscol-col-aux) = <– ceqv 
    fst (snd (snd tr-coscol-col-aux)) = ! (λ= (<–-inv-l ceqv))
    snd (snd (snd tr-coscol-col-aux)) = ! (λ= (<–-inv-r ceqv))

    tr-coscol-col : Coc-wc-iso (Coc-to-wc (can-coc (DiagForg A Γ Δ-F))) (F-coc (Forg-funct-cos A {ℓd}) (CosCoc-to-wc (ColCoC-cos Δ-F)))
    tr-coscol-col = coe
      (ap (Coc-wc-iso (Coc-to-wc (can-coc (DiagForg A Γ Δ-F))))
        (ap (Coc-to-wc ∘ CocForg) (! (<–-inv-l CosCoc-wc-≃ _)) ∙ CocForg-coh {i = lmax ℓ ℓd} (CosCoc-to-wc (ColCoC-cos Δ-F))))
      tr-coscol-col-aux

    module FCol-iso {T : Coslice (lmax ℓ ℓd) ℓ A} (K : Cocone-wc Δ T) where

      private      
        -- colimiting cocone on pushout
        cl-po = ColCoc-is-colim {ℓd = lmax ℓ ℓd} Δ
        cg-PO = cogap-map-wc (ColCoc-is-colim {ℓd = lmax ℓ ℓd} Δ)

      cg-PO-eqv : is-colim K → equiv-wc (Coslice-wc A (lmax ℓ ℓd)) (cg-PO K)
      cg-PO-eqv cl = col-wc-unq {K₁ = CosCoc-to-wc {i = lmax ℓ ℓd} (ColCoC-cos Δ-F)} {K₂ = K} (pentagon-wc-Cos A {lmax ℓ ℓd})
        (λ g f →
          UndFun∼-to-== (*→-assoc id-cos g f) ◃∙
          ! (UndFun∼-to-== (lunit-∘* (g ∘* f))) ◃∎
            =ₛ₁⟨ 1 & 1 & !cos-conv (lunit-∘* (g ∘* f)) ⟩
          UndFun∼-to-== (*→-assoc id-cos g f) ◃∙
          UndFun∼-to-== (∼!-cos (lunit-∘* (g ∘* f))) ◃∎
            =ₛ⟨ !ₛ (cos∘-conv (*→-assoc id-cos g f) (∼!-cos (lunit-∘* (g ∘* f)))) ⟩
          UndFun∼-to-== (*→-assoc id-cos g f ∼∘-cos ∼!-cos (lunit-∘* (g ∘* f))) ◃∎
            =ₛ₁⟨ ap UndFun∼-to-== (∼∼-cos∼-to-== ((λ _ → idp) , (λ a → aux (fst g) (snd f a) (snd g a)))) ⟩
          UndFun∼-to-== (pre-∘*-∼ f (∼!-cos (lunit-∘* g))) ◃∎
            =ₛ₁⟨ ! (ap (ap (λ m → m ∘* f)) (!cos-conv (lunit-∘* g)) ∙ whisk-cos-conv-r (∼!-cos (lunit-∘* g))) ⟩
          ap (λ m → m ∘* f) (! (UndFun∼-to-== (lunit-∘* g))) ◃∎ ∎ₛ)
        cl-po cl
        where abstract
          aux : ∀ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} (k : X → Y)
            {x y : X} {z : Y} (p₁ : x == y) (p₂ : k y == z) → 
            ap (λ q → q)
              (ap (λ p → p ∙ ap (λ x → x) p₂ ∙ idp) (ap-∘ (λ x → x) k p₁) ∙
              ! (ap-ap-∙-∙ (λ x → x) k p₁ p₂ idp)) ∙
            ap (λ q → q) (!
              (! (∙-unit-r (ap k p₁ ∙ p₂)) ∙ ap (λ p → p ∙ idp) (! (ap-idf (ap k p₁ ∙ p₂))))) ∙ idp
              ==
            (ap (λ p → p ∙ ap (λ x → x) p₂ ∙ idp)
              (hmtpy-nat-!-sq (λ x → idp) p₁) ∙
            ∙-assoc (ap k p₁) idp (ap (λ x → x) p₂ ∙ idp)) ∙
            ap (_∙_ (ap k p₁))
              (ap (λ q → q) (! (! (∙-unit-r p₂) ∙ ap (λ p → p ∙ idp) (! (ap-idf p₂)))) ∙ idp)
          aux _ idp idp = idp

      tr-coscol-abs-mor : 
        Coc-wc-mor (F-coc (Forg-funct-cos A {ℓd}) (CosCoc-to-wc (ColCoC-cos Δ-F))) (F-coc (Forg-funct-cos A {ℓd}) K)
      tr-coscol-abs-mor = forg-coc-mor-cos {i = ℓd} {K₁ = CosCoc-to-wc {i = lmax ℓ ℓd} (ColCoC-cos Δ-F)} {K₂ = K}
        ((cg-PO K) , cogap-map-wc-β {K = CosCoc-to-wc {i = lmax ℓ ℓd} (ColCoC-cos Δ-F)} cl-po {V = K})

      tr-coscol-abs-iso : is-colim K → 
        Coc-wc-iso (F-coc (Forg-funct-cos A {ℓd}) (CosCoc-to-wc (ColCoC-cos Δ-F))) (F-coc (Forg-funct-cos A {ℓd}) K)
      fst (tr-coscol-abs-iso _) = tr-coscol-abs-mor
      snd (tr-coscol-abs-iso cl) = F-equiv-wc (Forg-funct-cos A {ℓd}) (cg-PO-eqv cl)

      abstract
        tr-forg-coscol-iso : is-colim K → Coc-wc-iso (Coc-to-wc (can-coc (DiagForg A Γ Δ-F))) (F-coc (Forg-funct-cos A {ℓd}) K)
        fst (tr-forg-coscol-iso cl) = coc-wc-mor-∘ pentagon-wc-ty (fst (tr-coscol-abs-iso cl)) (fst tr-coscol-col)
        snd (tr-forg-coscol-iso cl) = equiv-wc-∘ (Type-wc (lmax ℓ ℓd)) (snd (tr-coscol-abs-iso cl)) (snd tr-coscol-col)

    module _ {T : Coslice (lmax ℓ ℓd) ℓ A} (K : Cocone-wc Δ T) (cl : is-colim K) where

      open FCol-iso K

      abstract
        Forg-coscol-pres : is-colim {C = Type-wc (lmax ℓ ℓd)} (F-coc (Forg-funct-cos A {ℓd}) K)
        Forg-coscol-pres = fst (eqv-pres-colim pentagon-wc-ty (fst (tr-forg-coscol-iso cl)) (snd (tr-forg-coscol-iso cl)))
          lemma
          where abstract
            lemma : is-colim {C = Type-wc (lmax ℓ ℓd)} (Coc-to-wc (can-coc (DiagForg A Γ Δ-F)))
            lemma = can-coc-is-colim {Δ = Diag-from-grhom (DiagForg A Γ Δ-F)}
