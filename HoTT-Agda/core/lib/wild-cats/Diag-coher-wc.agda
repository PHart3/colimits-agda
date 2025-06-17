{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Graph
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc
open import lib.wild-cats.Cone-wc-SIP
open import lib.wild-cats.Colim-wc
open import lib.wild-cats.Cocone-wc-SIP

module lib.wild-cats.Diag-coher-wc where

open Cone-wc
open Cocone-wc
open Map-diag

module _ {ℓv ℓe ℓc₁ ℓc₂} {G : Graph ℓv ℓe} {C : WildCat {ℓc₁} {ℓc₂}} (pent : pentagon-wc C) where

  -- some useful coherence properties satisfied by a 2-coherent wild cat

  abstract
  
    pst-cmp-assoc : {a b c : ob C} (g : hom C b c) (f : hom C a b) {Δ : Diagram G C} (K : Cocone-wc Δ a)
      → post-cmp-coc K c (⟦ C ⟧ g ◻ f) == post-cmp-coc (post-cmp-coc K b f) c g
    pst-cmp-assoc g f {Δ} K = coc-to-==-◃ G ((λ x → α C g f (leg K x)) ,
      (λ {x} {y} γ →
        (α C (⟦ C ⟧ g ◻ f) (leg K y) (D₁ Δ γ) ∙
        ap (λ m → ⟦ C ⟧ (⟦ C ⟧ g ◻ f) ◻ m) (tri K γ)) ◃∙
        α C g f (leg K x) ◃∎
          =ₑ⟨ 0 & 1 & (α C (⟦ C ⟧ g ◻ f) (leg K y) (D₁ Δ γ) ◃∙ ap (λ m →  ⟦ C ⟧ (⟦ C ⟧ g ◻ f) ◻ m) (tri K γ) ◃∎)
            % =ₛ-in idp ⟩
        α C (⟦ C ⟧ g ◻ f) (leg K y) (D₁ Δ γ) ◃∙
        ap (λ m → ⟦ C ⟧ (⟦ C ⟧ g ◻ f) ◻ m) (tri K γ) ◃∙
        α C g f (leg K x) ◃∎
          =ₛ⟨ 1 & 1 & hmtpy-nat-∙◃ (λ m → α C g f m) (tri K γ) ⟩
        α C (⟦ C ⟧ g ◻ f) (leg K y) (D₁ Δ γ) ◃∙
        α C g f (⟦ C ⟧ leg K y ◻ D₁ Δ γ) ◃∙
        ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ f ◻ m) (tri K γ) ◃∙
        ! (α C g f (leg K x)) ◃∙
        α C g f (leg K x) ◃∎
          =ₛ₁⟨ 2 & 3 & 
            ap (λ p → ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ f ◻ m) (tri K γ) ∙ p) (!-inv-l (α C g f (leg K x))) ∙
            ∙-unit-r (ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ f ◻ m) (tri K γ)) ⟩
        α C (⟦ C ⟧ g ◻ f) (leg K y) (D₁ Δ γ) ◃∙
        α C g f (⟦ C ⟧ leg K y ◻ D₁ Δ γ) ◃∙
        ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ f ◻ m) (tri K γ) ◃∎
          =ₛ⟨ 0 & 2 & !ₛ (pentagon-wc◃ {C = C} pent g f (leg K y) (D₁ Δ γ)) ⟩
        ap (λ m → ⟦ C ⟧ m ◻ D₁ Δ γ) (α C g f (leg K y)) ◃∙
        α C g (⟦ C ⟧ f ◻ (leg K y)) (D₁ Δ γ) ◃∙
        ap (λ m → ⟦ C ⟧ g ◻ m) (α C f (leg K y) (D₁ Δ γ)) ◃∙
        ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ f ◻ m) (tri K γ) ◃∎
          =ₛ₁⟨ 2 & 2 &
            ! (ap-∙ (λ m → ⟦ C ⟧ g ◻ m) (α C f (leg K y) (D₁ Δ γ)) (ap (λ m → ⟦ C ⟧ f ◻ m) (tri K γ)) ∙
              ap (λ p → ap (λ m → ⟦ C ⟧ g ◻ m) (α C f (leg K y) (D₁ Δ γ)) ∙ p)
              (∘-ap (λ m → ⟦ C ⟧ g ◻ m) (λ m → ⟦ C ⟧ f ◻ m) (tri K γ))) ⟩
        ap (λ m → ⟦ C ⟧ m ◻ D₁ Δ γ) (α C g f (leg K y)) ◃∙
        α C g (⟦ C ⟧ f ◻ leg K y) (D₁ Δ γ) ◃∙
        ap (λ m → ⟦ C ⟧ g ◻ m) (α C f (leg K y) (D₁ Δ γ) ∙ ap (λ m → ⟦ C ⟧ f ◻ m) (tri K γ)) ◃∎
          =ₛ⟨ =ₛ-in idp ⟩
        ap (λ m → ⟦ C ⟧ m ◻ D₁ Δ γ) (α C g f (leg K y)) ◃∙
        (α C g (⟦ C ⟧ f ◻ leg K y) (D₁ Δ γ) ∙
        ap (λ m → ⟦ C ⟧ g ◻ m) (α C f (leg K y) (D₁ Δ γ) ∙ ap (λ m → ⟦ C ⟧ f ◻ m) (tri K γ))) ◃∎ ∎ₛ))

    pre-cmp-assoc : {a b c : ob C} (g : hom C b c) (f : hom C a b) {Δ : Diagram G C} (K : Cone-wc Δ c)
      → pre-cmp-con K a (⟦ C ⟧ g ◻ f) == pre-cmp-con (pre-cmp-con K b g) a f 
    pre-cmp-assoc g f {Δ} K = con-to-==-◃ ((λ x → ! (α C (leg K x) g f)) ,
      λ {x} {y} γ →
        (! (α C (D₁ Δ γ) (leg K x) (⟦ C ⟧ g ◻ f)) ∙ ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ g ◻ f) (tri K γ)) ◃∙
        ! (α C (leg K y) g f) ◃∎
          =ₑ⟨ 0 & 1 & (! (α C (D₁ Δ γ) (leg K x) (⟦ C ⟧ g ◻ f)) ◃∙ ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ g ◻ f) (tri K γ) ◃∎)
            % =ₛ-in idp ⟩
        ! (α C (D₁ Δ γ) (leg K x) (⟦ C ⟧ g ◻ f)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ g ◻ f) (tri K γ) ◃∙
        ! (α C (leg K y) g f) ◃∎
          =ₛ⟨ 1 & 1 & apCommSq◃ (λ m → α C m g f) (tri K γ) ⟩
        ! (α C (D₁ Δ γ) (leg K x) (⟦ C ⟧ g ◻ f)) ◃∙
        ! (α C (⟦ C ⟧ D₁ Δ γ ◻ leg K x) g f) ◃∙
        ap (λ m → ⟦ C ⟧ (⟦ C ⟧ m ◻ g) ◻ f) (tri K γ) ◃∙
        α C (leg K y) g f ◃∙
        ! (α C (leg K y) g f) ◃∎
          =ₛ₁⟨ 2 & 3 & ap (λ p → ap (λ m → ⟦ C ⟧ (⟦ C ⟧ m ◻ g) ◻ f) (tri K γ) ∙ p) (!-inv-r (α C (leg K y) g f)) ∙ ∙-unit-r _ ⟩
        ! (α C (D₁ Δ γ) (leg K x) (⟦ C ⟧ g ◻ f)) ◃∙
        ! (α C (⟦ C ⟧ D₁ Δ γ ◻ leg K x) g f) ◃∙
        ap (λ m → ⟦ C ⟧ (⟦ C ⟧ m ◻ g) ◻ f) (tri K γ) ◃∎
          =ₛ⟨ 0 & 2 & !ₛ (pentagon-wc-! {C = C} pent (D₁ Δ γ) (leg K x) g f) ⟩
        ! (ap (λ m → ⟦ C ⟧ D₁ Δ γ ◻ m) (α C (leg K x) g f)) ◃∙
        ! (α C (D₁ Δ γ) (⟦ C ⟧ leg K x ◻ g) f) ◃∙
        ! (ap (λ m → ⟦ C ⟧ m ◻ f) (α C (D₁ Δ γ) (leg K x) g)) ◃∙
        ap (λ m → ⟦ C ⟧ (⟦ C ⟧ m ◻ g) ◻ f) (tri K γ) ◃∎
          =ₛ₁⟨ 0 & 1 & !-ap (λ m → ⟦ C ⟧ D₁ Δ γ ◻ m) (α C (leg K x) g f) ⟩
        ap (λ m → ⟦ C ⟧ D₁ Δ γ ◻ m) (! (α C (leg K x) g f)) ◃∙
        ! (α C (D₁ Δ γ) (⟦ C ⟧ leg K x ◻ g) f) ◃∙
        ! (ap (λ m → ⟦ C ⟧ m ◻ f) (α C (D₁ Δ γ) (leg K x) g)) ◃∙
        ap (λ m → ⟦ C ⟧ (⟦ C ⟧ m ◻ g) ◻ f) (tri K γ) ◃∎
          =ₛ₁⟨ 2 & 2 &
            ! (ap-∙! (λ m → ⟦ C ⟧ m ◻ f) (α C (D₁ Δ γ) (leg K x) g) (ap (λ m → ⟦ C ⟧ m ◻ g) (tri K γ)) ∙
            ap (λ p → ! (ap (λ m → ⟦ C ⟧ m ◻ f) (α C (D₁ Δ γ) (leg K x) g)) ∙ p)
              (∘-ap (λ m → ⟦ C ⟧ m ◻ f) (λ m → ⟦ C ⟧ m ◻ g) (tri K γ))) ⟩
        ap (λ m → ⟦ C ⟧ D₁ Δ γ ◻ m) (! (α C (leg K x) g f)) ◃∙
        ! (α C (D₁ Δ γ) (⟦ C ⟧ leg K x ◻ g) f) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ f)
          (! (α C (D₁ Δ γ) (leg K x) g) ∙ ap (λ m → ⟦ C ⟧ m ◻ g) (tri K γ)) ◃∎
          =ₛ⟨ =ₛ-in idp ⟩
        ap (λ m → ⟦ C ⟧ D₁ Δ γ ◻ m) (! (α C (leg K x) g f)) ◃∙
        (! (α C (D₁ Δ γ) (⟦ C ⟧ leg K x ◻ g) f) ∙
        ap (λ m → ⟦ C ⟧ m ◻ f)
          (! (α C (D₁ Δ γ) (leg K x) g) ∙ ap (λ m → ⟦ C ⟧ m ◻ g) (tri K γ))) ◃∎ ∎ₛ)

    whisk-pre-cmp-coher : {Δ₁ Δ₂ : Diagram G C} (μ : Map-diag Δ₁ Δ₂) {a b : ob C}
      (f : hom C b a) (K : Cone-wc Δ₁ a)
      → pre-cmp-con (whisk-dmap-con μ K) b f == whisk-dmap-con μ (pre-cmp-con K b f)
    whisk-pre-cmp-coher {Δ₁} {Δ₂} μ f K = con-to-==-◃ ((λ x → α C (map-comp μ x) (leg K x) f) ,
      (λ {x} {y} g →
        (! (α C (D₁ Δ₂ g) (⟦ C ⟧ map-comp μ x ◻ leg K x) f) ∙
        ap (λ m → ⟦ C ⟧ m ◻ f)
          (! (α C (D₁ Δ₂ g) (map-comp μ x) (leg K x)) ∙
          ap (λ m → ⟦ C ⟧ m ◻ leg K x) (map-sq μ g) ∙
          α C (map-comp μ y) (D₁ Δ₁ g) (leg K x) ∙
          ap (λ m → ⟦ C ⟧ map-comp μ y ◻ m) (tri K g))) ◃∙
        α C (map-comp μ y) (leg K y) f ◃∎
          =ₑ⟨ 0 & 1 &
            (! (α C (D₁ Δ₂ g) (⟦ C ⟧ map-comp μ x ◻ leg K x) f) ◃∙
             ap (λ m → ⟦ C ⟧ m ◻ f)
               (! (α C (D₁ Δ₂ g) (map-comp μ x) (leg K x)) ∙
               ap (λ m → ⟦ C ⟧ m ◻ leg K x) (map-sq μ g) ∙
               α C (map-comp μ y) (D₁ Δ₁ g) (leg K x) ∙
               ap (λ m → ⟦ C ⟧ map-comp μ y ◻ m) (tri K g)) ◃∎)
             % =ₛ-in idp ⟩
        ! (α C (D₁ Δ₂ g) (⟦ C ⟧ map-comp μ x ◻ leg K x) f) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ f)
          (! (α C (D₁ Δ₂ g) (map-comp μ x) (leg K x)) ∙
          ap (λ m → ⟦ C ⟧ m ◻ leg K x) (map-sq μ g) ∙
          α C (map-comp μ y) (D₁ Δ₁ g) (leg K x) ∙
          ap (λ m → ⟦ C ⟧ map-comp μ y ◻ m) (tri K g)) ◃∙
        α C (map-comp μ y) (leg K y) f ◃∎
          =ₛ⟨ 1 & 1 & ap-seq-∙ (λ m → ⟦ C ⟧ m ◻ f)
                        (! (α C (D₁ Δ₂ g) (map-comp μ x) (leg K x)) ◃∙
                        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (map-sq μ g) ◃∙
                        α C (map-comp μ y) (D₁ Δ₁ g) (leg K x) ◃∙
                        ap (λ m → ⟦ C ⟧ map-comp μ y ◻ m) (tri K g) ◃∎) ⟩
        ! (α C (D₁ Δ₂ g) (⟦ C ⟧ map-comp μ x ◻ leg K x) f) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ f) (! (α C (D₁ Δ₂ g) (map-comp μ x) (leg K x))) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ f) (ap (λ m → ⟦ C ⟧ m ◻ leg K x) (map-sq μ g)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ f) (α C (map-comp μ y) (D₁ Δ₁ g) (leg K x)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ f) (ap (λ m → ⟦ C ⟧ map-comp μ y ◻ m) (tri K g)) ◃∙
        α C (map-comp μ y) (leg K y) f ◃∎
          =ₛ₁⟨ 4 & 1 & ∘-ap (λ m → ⟦ C ⟧ m ◻ f) (λ m → ⟦ C ⟧ map-comp μ y ◻ m) (tri K g) ⟩
        ! (α C (D₁ Δ₂ g) (⟦ C ⟧ map-comp μ x ◻ leg K x) f) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ f) (! (α C (D₁ Δ₂ g) (map-comp μ x) (leg K x))) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ f) (ap (λ m → ⟦ C ⟧ m ◻ leg K x) (map-sq μ g)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ f) (α C (map-comp μ y) (D₁ Δ₁ g) (leg K x)) ◃∙
        ap (λ m → ⟦ C ⟧ (⟦ C ⟧ map-comp μ y ◻ m) ◻ f) (tri K g) ◃∙
        α C (map-comp μ y) (leg K y) f ◃∎
          =ₛ⟨ 4 & 1 & hmtpy-nat-∙◃ (λ m → α C (map-comp μ y) m f) (tri K g) ⟩
        ! (α C (D₁ Δ₂ g) (⟦ C ⟧ map-comp μ x ◻ leg K x) f) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ f) (! (α C (D₁ Δ₂ g) (map-comp μ x) (leg K x))) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ f) (ap (λ m → ⟦ C ⟧ m ◻ leg K x) (map-sq μ g)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ f) (α C (map-comp μ y) (D₁ Δ₁ g) (leg K x)) ◃∙
        α C (map-comp μ y) (⟦ C ⟧ D₁ Δ₁ g ◻ leg K x) f ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ y ◻ ⟦ C ⟧ m ◻ f) (tri K g) ◃∙
        ! (α C (map-comp μ y) (leg K y) f) ◃∙
        α C (map-comp μ y) (leg K y) f ◃∎
          =ₛ₁⟨ 2 & 1 & ∘-ap (λ m → ⟦ C ⟧ m ◻ f) (λ m → ⟦ C ⟧ m ◻ leg K x) (map-sq μ g) ⟩
        ! (α C (D₁ Δ₂ g) (⟦ C ⟧ map-comp μ x ◻ leg K x) f) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ f) (! (α C (D₁ Δ₂ g) (map-comp μ x) (leg K x))) ◃∙
        ap (λ m → ⟦ C ⟧ (⟦ C ⟧ m ◻ leg K x) ◻ f) (map-sq μ g) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ f) (α C (map-comp μ y) (D₁ Δ₁ g) (leg K x)) ◃∙
        α C (map-comp μ y) (⟦ C ⟧ D₁ Δ₁ g ◻ leg K x) f ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ y ◻ ⟦ C ⟧ m ◻ f) (tri K g) ◃∙
        ! (α C (map-comp μ y) (leg K y) f) ◃∙
        α C (map-comp μ y) (leg K y) f ◃∎
          =ₛ⟨ 2 & 1 & hmtpy-nat-∙◃ (λ m → α C m (leg K x) f) (map-sq μ g) ⟩
        ! (α C (D₁ Δ₂ g) (⟦ C ⟧ map-comp μ x ◻ leg K x) f) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ f) (! (α C (D₁ Δ₂ g) (map-comp μ x) (leg K x))) ◃∙
        α C (⟦ C ⟧ D₁ Δ₂ g ◻ map-comp μ x) (leg K x) f ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ leg K x ◻ f) (map-sq μ g) ◃∙
        ! (α C (⟦ C ⟧ map-comp μ y ◻ D₁ Δ₁ g) (leg K x) f) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ f) (α C (map-comp μ y) (D₁ Δ₁ g) (leg K x)) ◃∙
        α C (map-comp μ y) (⟦ C ⟧ D₁ Δ₁ g ◻ leg K x) f ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ y ◻ ⟦ C ⟧ m ◻ f) (tri K g) ◃∙
        ! (α C (map-comp μ y) (leg K y) f) ◃∙
        α C (map-comp μ y) (leg K y) f ◃∎
          =ₛ₁⟨ 7 & 3 &
            ap (λ p → ap (λ m → ⟦ C ⟧ map-comp μ y ◻ ⟦ C ⟧ m ◻ f) (tri K g) ∙ p) (!-inv-l (α C (map-comp μ y) (leg K y) f)) ∙
            ∙-unit-r (ap (λ m → ⟦ C ⟧ map-comp μ y ◻ ⟦ C ⟧ m ◻ f) (tri K g)) ⟩
        ! (α C (D₁ Δ₂ g) (⟦ C ⟧ map-comp μ x ◻ leg K x) f) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ f) (! (α C (D₁ Δ₂ g) (map-comp μ x) (leg K x))) ◃∙
        α C (⟦ C ⟧ D₁ Δ₂ g ◻ map-comp μ x) (leg K x) f ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ leg K x ◻ f) (map-sq μ g) ◃∙
        ! (α C (⟦ C ⟧ map-comp μ y ◻ D₁ Δ₁ g) (leg K x) f) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ f) (α C (map-comp μ y) (D₁ Δ₁ g) (leg K x)) ◃∙
        α C (map-comp μ y) (⟦ C ⟧ D₁ Δ₁ g ◻ leg K x) f ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ y ◻ ⟦ C ⟧ m ◻ f) (tri K g) ◃∎
          =ₛ⟨ 0 & 3 & pentagon-wc-rot2 {C = C} pent (D₁ Δ₂ g) (map-comp μ x) (leg K x) f ⟩
        ap (λ m → ⟦ C ⟧ D₁ Δ₂ g ◻ m) (α C (map-comp μ x) (leg K x) f) ◃∙
        ! (α C (D₁ Δ₂ g) (map-comp μ x) (⟦ C ⟧ leg K x ◻ f)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ leg K x ◻ f) (map-sq μ g) ◃∙
        ! (α C (⟦ C ⟧ map-comp μ y ◻ D₁ Δ₁ g) (leg K x) f) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ f) (α C (map-comp μ y) (D₁ Δ₁ g) (leg K x)) ◃∙
        α C (map-comp μ y) (⟦ C ⟧ D₁ Δ₁ g ◻ leg K x) f ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ y ◻ ⟦ C ⟧ m ◻ f) (tri K g) ◃∎
          =ₛ⟨ 3 & 3 & pentagon-wc-rot1 {C = C} pent (map-comp μ y) (D₁ Δ₁ g) (leg K x) f ⟩
        ap (λ m → ⟦ C ⟧ D₁ Δ₂ g ◻ m) (α C (map-comp μ x) (leg K x) f) ◃∙
        ! (α C (D₁ Δ₂ g) (map-comp μ x) (⟦ C ⟧ leg K x ◻ f)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ leg K x ◻ f) (map-sq μ g) ◃∙
        α C (map-comp μ y) (D₁ Δ₁ g) (⟦ C ⟧ leg K x ◻ f) ◃∙
        ! (ap (λ m → ⟦ C ⟧ map-comp μ y ◻ m) (α C (D₁ Δ₁ g) (leg K x) f)) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ y ◻ ⟦ C ⟧ m ◻ f) (tri K g) ◃∎
          =ₛ₁⟨ 4 & 2 &
              ! (ap-∙! (λ m → ⟦ C ⟧ map-comp μ y ◻ m) (α C (D₁ Δ₁ g) (leg K x) f) (ap (λ m → ⟦ C ⟧ m ◻ f) (tri K g)) ∙
                ap (λ p → ! (ap (λ m → ⟦ C ⟧ map-comp μ y ◻ m) (α C (D₁ Δ₁ g) (leg K x) f)) ∙ p)
                  (∘-ap (λ m → ⟦ C ⟧ map-comp μ y ◻ m) (λ m → ⟦ C ⟧ m ◻ f) (tri K g))) ⟩
        ap (λ m → ⟦ C ⟧ D₁ Δ₂ g ◻ m) (α C (map-comp μ x) (leg K x) f) ◃∙
        ! (α C (D₁ Δ₂ g) (map-comp μ x) (⟦ C ⟧ leg K x ◻ f)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ leg K x ◻ f) (map-sq μ g) ◃∙
        α C (map-comp μ y) (D₁ Δ₁ g) (⟦ C ⟧ leg K x ◻ f) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ y ◻ m)
          (! (α C (D₁ Δ₁ g) (leg K x) f) ∙
          ap (λ m → ⟦ C ⟧ m ◻ f) (tri K g)) ◃∎
          =ₛ⟨ =ₛ-in idp ⟩
        ap (λ m → ⟦ C ⟧ D₁ Δ₂ g ◻ m) (α C (map-comp μ x) (leg K x) f) ◃∙
        (! (α C (D₁ Δ₂ g) (map-comp μ x) (⟦ C ⟧ leg K x ◻ f)) ∙
        ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ leg K x ◻ f) (map-sq μ g) ∙
        α C (map-comp μ y) (D₁ Δ₁ g) (⟦ C ⟧ leg K x ◻ f) ∙
        ap (λ m → ⟦ C ⟧ map-comp μ y ◻ m)
          (! (α C (D₁ Δ₁ g) (leg K x) f) ∙
          ap (λ m → ⟦ C ⟧ m ◻ f) (tri K g))) ◃∎ ∎ₛ ))

    whisk-diag-∘ : {Δ₁ Δ₂ Δ₃ : Diagram G C} (μ₁ : Map-diag Δ₁ Δ₂) (μ₂ : Map-diag Δ₂ Δ₃)
      {a : ob C} (K : Cone-wc Δ₁ a)
      → whisk-dmap-con (μ₂ diag-map-∘ μ₁) K == whisk-dmap-con μ₂ (whisk-dmap-con μ₁ K)
    whisk-diag-∘ {Δ₁} {Δ₂} {Δ₃} μ₁ μ₂ K = con-to-==-◃ ((λ x → α C (map-comp μ₂ x) (map-comp μ₁ x) (leg K x)) ,
      (λ {x} {y} f →
        (! (α C (D₁ Δ₃ f) (⟦ C ⟧ map-comp μ₂ x ◻ map-comp μ₁ x) (leg K x)) ∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x)
          (! (α C (D₁ Δ₃ f) (map-comp μ₂ x) (map-comp μ₁ x)) ∙
          ap (λ m → ⟦ C ⟧ m ◻ map-comp μ₁ x) (map-sq μ₂ f) ∙
          α C (map-comp μ₂ y) (D₁ Δ₂ f) (map-comp μ₁ x) ∙
          ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ m) (map-sq μ₁ f) ∙
          ! (α C (map-comp μ₂ y) (map-comp μ₁ y) (D₁ Δ₁ f))) ∙
        α C (⟦ C ⟧ map-comp μ₂ y ◻ map-comp μ₁ y) (D₁ Δ₁ f) (leg K x) ∙
        ap (λ m → ⟦ C ⟧ (⟦ C ⟧ map-comp μ₂ y ◻ map-comp μ₁ y) ◻ m) (tri K f)) ◃∙
        α C (map-comp μ₂ y) (map-comp μ₁ y) (leg K y) ◃∎
          =ₑ⟨ 0 & 1 &
            (! (α C (D₁ Δ₃ f) (⟦ C ⟧ map-comp μ₂ x ◻ map-comp μ₁ x) (leg K x)) ◃∙
            ap (λ m → ⟦ C ⟧ m ◻ leg K x)
              (! (α C (D₁ Δ₃ f) (map-comp μ₂ x) (map-comp μ₁ x)) ∙
              ap (λ m → ⟦ C ⟧ m ◻ map-comp μ₁ x) (map-sq μ₂ f) ∙
              α C (map-comp μ₂ y) (D₁ Δ₂ f) (map-comp μ₁ x) ∙
              ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ m) (map-sq μ₁ f) ∙
              ! (α C (map-comp μ₂ y) (map-comp μ₁ y) (D₁ Δ₁ f))) ◃∙
            α C (⟦ C ⟧ map-comp μ₂ y ◻ map-comp μ₁ y) (D₁ Δ₁ f) (leg K x) ◃∙
            ap (λ m → ⟦ C ⟧ (⟦ C ⟧ map-comp μ₂ y ◻ map-comp μ₁ y) ◻ m) (tri K f) ◃∎)
          % =ₛ-in idp ⟩
        ! (α C (D₁ Δ₃ f) (⟦ C ⟧ map-comp μ₂ x ◻ map-comp μ₁ x) (leg K x)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x)
          (! (α C (D₁ Δ₃ f) (map-comp μ₂ x) (map-comp μ₁ x)) ∙
          ap (λ m → ⟦ C ⟧ m ◻ map-comp μ₁ x) (map-sq μ₂ f) ∙
          α C (map-comp μ₂ y) (D₁ Δ₂ f) (map-comp μ₁ x) ∙
          ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ m) (map-sq μ₁ f) ∙
          ! (α C (map-comp μ₂ y) (map-comp μ₁ y) (D₁ Δ₁ f))) ◃∙
        α C (⟦ C ⟧ map-comp μ₂ y ◻ map-comp μ₁ y) (D₁ Δ₁ f) (leg K x) ◃∙
        ap (λ m → ⟦ C ⟧ (⟦ C ⟧ map-comp μ₂ y ◻ map-comp μ₁ y) ◻ m) (tri K f) ◃∙
        α C (map-comp μ₂ y) (map-comp μ₁ y) (leg K y) ◃∎
          =ₛ⟨ 1 & 1 & ap-seq-∙ (λ m → ⟦ C ⟧ m ◻ leg K x)
            (! (α C (D₁ Δ₃ f) (map-comp μ₂ x) (map-comp μ₁ x)) ◃∙
            ap (λ m → ⟦ C ⟧ m ◻ map-comp μ₁ x) (map-sq μ₂ f) ◃∙
            α C (map-comp μ₂ y) (D₁ Δ₂ f) (map-comp μ₁ x) ◃∙
            ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ m) (map-sq μ₁ f) ◃∙
            ! (α C (map-comp μ₂ y) (map-comp μ₁ y) (D₁ Δ₁ f)) ◃∎) ⟩
        ! (α C (D₁ Δ₃ f) (⟦ C ⟧ map-comp μ₂ x ◻ map-comp μ₁ x) (leg K x)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (! (α C (D₁ Δ₃ f) (map-comp μ₂ x) (map-comp μ₁ x))) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (ap (λ m → ⟦ C ⟧ m ◻ map-comp μ₁ x) (map-sq μ₂ f)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (α C (map-comp μ₂ y) (D₁ Δ₂ f) (map-comp μ₁ x)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ m) (map-sq μ₁ f)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (! (α C (map-comp μ₂ y) (map-comp μ₁ y) (D₁ Δ₁ f))) ◃∙
        α C (⟦ C ⟧ map-comp μ₂ y ◻ map-comp μ₁ y) (D₁ Δ₁ f) (leg K x) ◃∙
        ap (λ m → ⟦ C ⟧ (⟦ C ⟧ map-comp μ₂ y ◻ map-comp μ₁ y) ◻ m) (tri K f) ◃∙
        α C (map-comp μ₂ y) (map-comp μ₁ y) (leg K y) ◃∎
          =ₛ⟨ 7 & 1 & hmtpy-nat-∙◃ (λ m → α C (map-comp μ₂ y) (map-comp μ₁ y) m) (tri K f) ⟩
        ! (α C (D₁ Δ₃ f) (⟦ C ⟧ map-comp μ₂ x ◻ map-comp μ₁ x) (leg K x)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (! (α C (D₁ Δ₃ f) (map-comp μ₂ x) (map-comp μ₁ x))) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (ap (λ m → ⟦ C ⟧ m ◻ map-comp μ₁ x) (map-sq μ₂ f)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (α C (map-comp μ₂ y) (D₁ Δ₂ f) (map-comp μ₁ x)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ m) (map-sq μ₁ f)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (! (α C (map-comp μ₂ y) (map-comp μ₁ y) (D₁ Δ₁ f))) ◃∙
        α C (⟦ C ⟧ map-comp μ₂ y ◻ map-comp μ₁ y) (D₁ Δ₁ f) (leg K x) ◃∙
        α C (map-comp μ₂ y) (map-comp μ₁ y) (⟦ C ⟧ D₁ Δ₁ f ◻ leg K x) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ ⟦ C ⟧ map-comp μ₁ y ◻ m) (tri K f) ◃∙
        ! (α C (map-comp μ₂ y) (map-comp μ₁ y) (leg K y)) ◃∙
        α C (map-comp μ₂ y) (map-comp μ₁ y) (leg K y) ◃∎
          =ₛ₁⟨ 8 & 3 &
            ap (λ p → ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ ⟦ C ⟧ map-comp μ₁ y ◻ m) (tri K f) ∙ p)
              (!-inv-l (α C (map-comp μ₂ y) (map-comp μ₁ y) (leg K y))) ∙
            ∙-unit-r (ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ ⟦ C ⟧ map-comp μ₁ y ◻ m) (tri K f)) ⟩
        ! (α C (D₁ Δ₃ f) (⟦ C ⟧ map-comp μ₂ x ◻ map-comp μ₁ x) (leg K x)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (! (α C (D₁ Δ₃ f) (map-comp μ₂ x) (map-comp μ₁ x))) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (ap (λ m → ⟦ C ⟧ m ◻ map-comp μ₁ x) (map-sq μ₂ f)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (α C (map-comp μ₂ y) (D₁ Δ₂ f) (map-comp μ₁ x)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ m) (map-sq μ₁ f)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (! (α C (map-comp μ₂ y) (map-comp μ₁ y) (D₁ Δ₁ f))) ◃∙
        α C (⟦ C ⟧ map-comp μ₂ y ◻ map-comp μ₁ y) (D₁ Δ₁ f) (leg K x) ◃∙
        α C (map-comp μ₂ y) (map-comp μ₁ y) (⟦ C ⟧ D₁ Δ₁ f ◻ leg K x) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ ⟦ C ⟧ map-comp μ₁ y ◻ m) (tri K f) ◃∎
          =ₛ₁⟨ 4 & 1 & ∘-ap (λ m → ⟦ C ⟧ m ◻ leg K x) (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ m) (map-sq μ₁ f) ⟩
        ! (α C (D₁ Δ₃ f) (⟦ C ⟧ map-comp μ₂ x ◻ map-comp μ₁ x) (leg K x)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (! (α C (D₁ Δ₃ f) (map-comp μ₂ x) (map-comp μ₁ x))) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (ap (λ m → ⟦ C ⟧ m ◻ map-comp μ₁ x) (map-sq μ₂ f)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (α C (map-comp μ₂ y) (D₁ Δ₂ f) (map-comp μ₁ x)) ◃∙
        ap (λ m → ⟦ C ⟧ (⟦ C ⟧ map-comp μ₂ y ◻ m) ◻ leg K x) (map-sq μ₁ f) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (! (α C (map-comp μ₂ y) (map-comp μ₁ y) (D₁ Δ₁ f))) ◃∙
        α C (⟦ C ⟧ map-comp μ₂ y ◻ map-comp μ₁ y) (D₁ Δ₁ f) (leg K x) ◃∙
        α C (map-comp μ₂ y) (map-comp μ₁ y) (⟦ C ⟧ D₁ Δ₁ f ◻ leg K x) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ ⟦ C ⟧ map-comp μ₁ y ◻ m) (tri K f) ◃∎
          =ₛ⟨ 4 & 1 & hmtpy-nat-∙◃ (λ m → α C (map-comp μ₂ y) m (leg K x)) (map-sq μ₁ f) ⟩
        ! (α C (D₁ Δ₃ f) (⟦ C ⟧ map-comp μ₂ x ◻ map-comp μ₁ x) (leg K x)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (! (α C (D₁ Δ₃ f) (map-comp μ₂ x) (map-comp μ₁ x))) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (ap (λ m → ⟦ C ⟧ m ◻ map-comp μ₁ x) (map-sq μ₂ f)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (α C (map-comp μ₂ y) (D₁ Δ₂ f) (map-comp μ₁ x)) ◃∙
        α C (map-comp μ₂ y) (⟦ C ⟧ D₁ Δ₂ f ◻ map-comp μ₁ x) (leg K x) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ ⟦ C ⟧ m ◻ leg K x) (map-sq μ₁ f) ◃∙
        ! (α C (map-comp μ₂ y) (⟦ C ⟧ map-comp μ₁ y ◻ D₁ Δ₁ f) (leg K x)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (! (α C (map-comp μ₂ y) (map-comp μ₁ y) (D₁ Δ₁ f))) ◃∙
        α C (⟦ C ⟧ map-comp μ₂ y ◻ map-comp μ₁ y) (D₁ Δ₁ f) (leg K x) ◃∙
        α C (map-comp μ₂ y) (map-comp μ₁ y) (⟦ C ⟧ D₁ Δ₁ f ◻ leg K x) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ ⟦ C ⟧ map-comp μ₁ y ◻ m) (tri K f) ◃∎
          =ₛ₁⟨ 2 & 1 & ∘-ap (λ m → ⟦ C ⟧ m ◻ leg K x) (λ m → ⟦ C ⟧ m ◻ map-comp μ₁ x) (map-sq μ₂ f) ⟩
        ! (α C (D₁ Δ₃ f) (⟦ C ⟧ map-comp μ₂ x ◻ map-comp μ₁ x) (leg K x)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (! (α C (D₁ Δ₃ f) (map-comp μ₂ x) (map-comp μ₁ x))) ◃∙
        ap (λ m → ⟦ C ⟧ (⟦ C ⟧ m ◻ map-comp μ₁ x) ◻ leg K x) (map-sq μ₂ f) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (α C (map-comp μ₂ y) (D₁ Δ₂ f) (map-comp μ₁ x)) ◃∙
        α C (map-comp μ₂ y) (⟦ C ⟧ D₁ Δ₂ f ◻ map-comp μ₁ x) (leg K x) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ ⟦ C ⟧ m ◻ leg K x) (map-sq μ₁ f) ◃∙
        ! (α C (map-comp μ₂ y) (⟦ C ⟧ map-comp μ₁ y ◻ D₁ Δ₁ f) (leg K x)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (! (α C (map-comp μ₂ y) (map-comp μ₁ y) (D₁ Δ₁ f))) ◃∙
        α C (⟦ C ⟧ map-comp μ₂ y ◻ map-comp μ₁ y) (D₁ Δ₁ f) (leg K x) ◃∙
        α C (map-comp μ₂ y) (map-comp μ₁ y) (⟦ C ⟧ D₁ Δ₁ f ◻ leg K x) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ ⟦ C ⟧ map-comp μ₁ y ◻ m) (tri K f) ◃∎
          =ₛ⟨ 2 & 1 & hmtpy-nat-∙◃ (λ m → α C m (map-comp μ₁ x) (leg K x)) (map-sq μ₂ f) ⟩
        ! (α C (D₁ Δ₃ f) (⟦ C ⟧ map-comp μ₂ x ◻ map-comp μ₁ x) (leg K x)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (! (α C (D₁ Δ₃ f) (map-comp μ₂ x) (map-comp μ₁ x))) ◃∙
        α C (⟦ C ⟧ D₁ Δ₃ f ◻ map-comp μ₂ x) (map-comp μ₁ x) (leg K x) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ map-comp μ₁ x ◻ leg K x) (map-sq μ₂ f) ◃∙
        ! (α C (⟦ C ⟧ map-comp μ₂ y ◻ D₁ Δ₂ f) (map-comp μ₁ x) (leg K x)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (α C (map-comp μ₂ y) (D₁ Δ₂ f) (map-comp μ₁ x)) ◃∙
        α C (map-comp μ₂ y) (⟦ C ⟧ D₁ Δ₂ f ◻ map-comp μ₁ x) (leg K x) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ ⟦ C ⟧ m ◻ leg K x) (map-sq μ₁ f) ◃∙
        ! (α C (map-comp μ₂ y) (⟦ C ⟧ map-comp μ₁ y ◻ D₁ Δ₁ f) (leg K x)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (! (α C (map-comp μ₂ y) (map-comp μ₁ y) (D₁ Δ₁ f))) ◃∙
        α C (⟦ C ⟧ map-comp μ₂ y ◻ map-comp μ₁ y) (D₁ Δ₁ f) (leg K x) ◃∙
        α C (map-comp μ₂ y) (map-comp μ₁ y) (⟦ C ⟧ D₁ Δ₁ f ◻ leg K x) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ ⟦ C ⟧ map-comp μ₁ y ◻ m) (tri K f) ◃∎
          =ₛ⟨ 8 & 4 & !ₛ (pentagon-wc-rot3 {C = C} pent (map-comp μ₂ y) (map-comp μ₁ y) (D₁ Δ₁ f) (leg K x)) ⟩
        ! (α C (D₁ Δ₃ f) (⟦ C ⟧ map-comp μ₂ x ◻ map-comp μ₁ x) (leg K x)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (! (α C (D₁ Δ₃ f) (map-comp μ₂ x) (map-comp μ₁ x))) ◃∙
        α C (⟦ C ⟧ D₁ Δ₃ f ◻ map-comp μ₂ x) (map-comp μ₁ x) (leg K x) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ map-comp μ₁ x ◻ leg K x) (map-sq μ₂ f) ◃∙
        ! (α C (⟦ C ⟧ map-comp μ₂ y ◻ D₁ Δ₂ f) (map-comp μ₁ x) (leg K x)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (α C (map-comp μ₂ y) (D₁ Δ₂ f) (map-comp μ₁ x)) ◃∙
        α C (map-comp μ₂ y) (⟦ C ⟧ D₁ Δ₂ f ◻ map-comp μ₁ x) (leg K x) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ ⟦ C ⟧ m ◻ leg K x) (map-sq μ₁ f) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ m) (α C (map-comp μ₁ y) (D₁ Δ₁ f) (leg K x)) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ ⟦ C ⟧ map-comp μ₁ y ◻ m) (tri K f) ◃∎
          =ₛ⟨ 0 & 3 & pentagon-wc-rot2 {C = C} pent (D₁ Δ₃ f) (map-comp μ₂ x) (map-comp μ₁ x) (leg K x) ⟩
        ap (λ m → ⟦ C ⟧ D₁ Δ₃ f ◻ m) (α C (map-comp μ₂ x) (map-comp μ₁ x) (leg K x)) ◃∙
        ! (α C (D₁ Δ₃ f) (map-comp μ₂ x) (⟦ C ⟧ map-comp μ₁ x ◻ leg K x)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ map-comp μ₁ x ◻ leg K x) (map-sq μ₂ f) ◃∙
        ! (α C (⟦ C ⟧ map-comp μ₂ y ◻ D₁ Δ₂ f) (map-comp μ₁ x) (leg K x)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ leg K x) (α C (map-comp μ₂ y) (D₁ Δ₂ f) (map-comp μ₁ x)) ◃∙
        α C (map-comp μ₂ y) (⟦ C ⟧ D₁ Δ₂ f ◻ map-comp μ₁ x) (leg K x) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ ⟦ C ⟧ m ◻ leg K x) (map-sq μ₁ f) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ m) (α C (map-comp μ₁ y) (D₁ Δ₁ f) (leg K x)) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ ⟦ C ⟧ map-comp μ₁ y ◻ m) (tri K f) ◃∎
          =ₛ⟨ 3 & 3 & pentagon-wc-rot1 {C = C} pent (map-comp μ₂ y) (D₁ Δ₂ f) (map-comp μ₁ x) (leg K x) ⟩
        ap (λ m → ⟦ C ⟧ D₁ Δ₃ f ◻ m) (α C (map-comp μ₂ x) (map-comp μ₁ x) (leg K x)) ◃∙
        ! (α C (D₁ Δ₃ f) (map-comp μ₂ x) (⟦ C ⟧ map-comp μ₁ x ◻ leg K x)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ map-comp μ₁ x ◻ leg K x) (map-sq μ₂ f) ◃∙
        α C (map-comp μ₂ y) (D₁ Δ₂ f) (⟦ C ⟧ map-comp μ₁ x ◻ leg K x) ◃∙
        ! (ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ m) (α C (D₁ Δ₂ f) (map-comp μ₁ x) (leg K x))) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ ⟦ C ⟧ m ◻ leg K x) (map-sq μ₁ f) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ m) (α C (map-comp μ₁ y) (D₁ Δ₁ f) (leg K x)) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ ⟦ C ⟧ map-comp μ₁ y ◻ m) (tri K f) ◃∎
          =ₛ₁⟨ 4 & 1 & !-ap (λ m →  ⟦ C ⟧ map-comp μ₂ y ◻ m) (α C (D₁ Δ₂ f) (map-comp μ₁ x) (leg K x)) ⟩
        ap (λ m → ⟦ C ⟧ D₁ Δ₃ f ◻ m) (α C (map-comp μ₂ x) (map-comp μ₁ x) (leg K x)) ◃∙
        ! (α C (D₁ Δ₃ f) (map-comp μ₂ x) (⟦ C ⟧ map-comp μ₁ x ◻ leg K x)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ map-comp μ₁ x ◻ leg K x) (map-sq μ₂ f) ◃∙
        α C (map-comp μ₂ y) (D₁ Δ₂ f) (⟦ C ⟧ map-comp μ₁ x ◻ leg K x) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ m) (! (α C (D₁ Δ₂ f) (map-comp μ₁ x) (leg K x))) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ ⟦ C ⟧ m ◻ leg K x) (map-sq μ₁ f) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ m) (α C (map-comp μ₁ y) (D₁ Δ₁ f) (leg K x)) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ ⟦ C ⟧ map-comp μ₁ y ◻ m) (tri K f) ◃∎
          =ₛ₁⟨ 5 & 1 & ap-∘ (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ m) (λ m → ⟦ C ⟧ m ◻ leg K x) (map-sq μ₁ f) ⟩
        ap (λ m → ⟦ C ⟧ D₁ Δ₃ f ◻ m) (α C (map-comp μ₂ x) (map-comp μ₁ x) (leg K x)) ◃∙
        ! (α C (D₁ Δ₃ f) (map-comp μ₂ x) (⟦ C ⟧ map-comp μ₁ x ◻ leg K x)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ map-comp μ₁ x ◻ leg K x) (map-sq μ₂ f) ◃∙
        α C (map-comp μ₂ y) (D₁ Δ₂ f) (⟦ C ⟧ map-comp μ₁ x ◻ leg K x) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ m) (! (α C (D₁ Δ₂ f) (map-comp μ₁ x) (leg K x))) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ m) (ap (λ m → ⟦ C ⟧ m ◻ leg K x) (map-sq μ₁ f)) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ m) (α C (map-comp μ₁ y) (D₁ Δ₁ f) (leg K x)) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ ⟦ C ⟧ map-comp μ₁ y ◻ m) (tri K f) ◃∎
          =ₛ₁⟨ 7 & 1 & ap-∘ (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ m) (λ m → ⟦ C ⟧ map-comp μ₁ y ◻ m) (tri K f) ⟩
        ap (λ m → ⟦ C ⟧ D₁ Δ₃ f ◻ m) (α C (map-comp μ₂ x) (map-comp μ₁ x) (leg K x)) ◃∙
        ! (α C (D₁ Δ₃ f) (map-comp μ₂ x) (⟦ C ⟧ map-comp μ₁ x ◻ leg K x)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ map-comp μ₁ x ◻ leg K x) (map-sq μ₂ f) ◃∙
        α C (map-comp μ₂ y) (D₁ Δ₂ f) (⟦ C ⟧ map-comp μ₁ x ◻ leg K x) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ m) (! (α C (D₁ Δ₂ f) (map-comp μ₁ x) (leg K x))) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ m) (ap (λ m → ⟦ C ⟧ m ◻ leg K x) (map-sq μ₁ f)) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ m) (α C (map-comp μ₁ y) (D₁ Δ₁ f) (leg K x)) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ m) (ap (λ m → ⟦ C ⟧ map-comp μ₁ y ◻ m) (tri K f)) ◃∎
          =ₛ⟨ 4 & 4 & !ₛ (
            ap-seq-∙ (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ m)
              (! (α C (D₁ Δ₂ f) (map-comp μ₁ x) (leg K x)) ◃∙
              ap (λ m → ⟦ C ⟧ m ◻ leg K x) (map-sq μ₁ f) ◃∙
              α C (map-comp μ₁ y) (D₁ Δ₁ f) (leg K x) ◃∙
              ap (λ m → ⟦ C ⟧ map-comp μ₁ y ◻ m) (tri K f) ◃∎)) ⟩
        ap (λ m → ⟦ C ⟧ D₁ Δ₃ f ◻ m) (α C (map-comp μ₂ x) (map-comp μ₁ x) (leg K x)) ◃∙
        ! (α C (D₁ Δ₃ f) (map-comp μ₂ x) (⟦ C ⟧ map-comp μ₁ x ◻ leg K x)) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ map-comp μ₁ x ◻ leg K x) (map-sq μ₂ f) ◃∙
        α C (map-comp μ₂ y) (D₁ Δ₂ f) (⟦ C ⟧ map-comp μ₁ x ◻ leg K x) ◃∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ m)
          (! (α C (D₁ Δ₂ f) (map-comp μ₁ x) (leg K x)) ∙
          ap (λ m → ⟦ C ⟧ m ◻ leg K x) (map-sq μ₁ f) ∙
          α C (map-comp μ₁ y) (D₁ Δ₁ f) (leg K x) ∙
          ap (λ m → ⟦ C ⟧ map-comp μ₁ y ◻ m) (tri K f)) ◃∎
          =ₛ⟨ =ₛ-in idp ⟩
        ap (λ m → ⟦ C ⟧ D₁ Δ₃ f ◻ m) (α C (map-comp μ₂ x) (map-comp μ₁ x) (leg K x)) ◃∙
        (! (α C (D₁ Δ₃ f) (map-comp μ₂ x) (⟦ C ⟧ map-comp μ₁ x ◻ leg K x)) ∙
        ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ map-comp μ₁ x ◻ leg K x) (map-sq μ₂ f) ∙
        α C (map-comp μ₂ y) (D₁ Δ₂ f) (⟦ C ⟧ map-comp μ₁ x ◻ leg K x) ∙
        ap (λ m → ⟦ C ⟧ map-comp μ₂ y ◻ m)
          (! (α C (D₁ Δ₂ f) (map-comp μ₁ x) (leg K x)) ∙
          ap (λ m → ⟦ C ⟧ m ◻ leg K x) (map-sq μ₁ f) ∙
          α C (map-comp μ₁ y) (D₁ Δ₁ f) (leg K x) ∙
          ap (λ m → ⟦ C ⟧ map-comp μ₁ y ◻ m) (tri K f))) ◃∎ ∎ₛ))
