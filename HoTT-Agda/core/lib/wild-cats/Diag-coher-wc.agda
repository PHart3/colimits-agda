{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Graph
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc
open import lib.wild-cats.Cone-wc-SIP
open import lib.wild-cats.Cocone-wc-SIP

module lib.wild-cats.Diag-coher-wc where

open Cone-wc
open Cocone-wc
open Map-diag

-- some useful coherence properties satisfied by a 2-coherent wild cat

module _ {ℓv ℓe ℓc₁ ℓc₂} {G : Graph ℓv ℓe} {C : WildCat {ℓc₁} {ℓc₂}} where

  module _ (trig : triangle-wc C)
    -- we also assume a standard property of bicategories
    (trig-ρ : {a b c : ob C} (g : hom C b c) (f : hom C a b) →
      ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C f) ◃∙
      ! (α C g f (id₁ C a)) ◃∙
      ! (ρ C (⟦ C ⟧ g ◻ f)) ◃∎
        =ₛ
      []) where

    abstract
      act-dmap-coc-id : {a : ob C} {Δ : Diagram G C} (K : Cocone-wc Δ a)
        → ∀ {b} → post-cmp-coc K b ∼ post-cmp-coc (act-dmap-coc (diag-map-id Δ) K) b
      act-dmap-coc-id {Δ = Δ} K g = coc-to-==-◃ G ((λ x → ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (leg K x))) , λ f → !ₛ (aux f))
        where abstract
          aux : ∀ {x} {y} (f : Hom G x y) →
            ap (λ m → ⟦ C ⟧ m ◻ D₁ Δ f) (ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (leg K y))) ◃∙
            (α C g (⟦ C ⟧ leg K y ◻ id₁ C (D₀ Δ y)) (D₁ Δ f) ∙
            ap (λ m → ⟦ C ⟧ g ◻ m)
              (α C (leg K y) (id₁ C (D₀ Δ y)) (D₁ Δ f) ∙
              ap (λ m → ⟦ C ⟧ leg K y ◻ m) (! (! (ρ C (D₁ Δ f)) ∙ lamb C (D₁ Δ f))) ∙
              ! (α C (leg K y) (D₁ Δ f) (id₁ C (D₀ Δ x))) ∙
              ap (λ m → ⟦ C ⟧ m ◻ id₁ C (D₀ Δ x)) (tri K f))) ◃∎
              =ₛ
            (α C g (leg K y) (D₁ Δ f) ∙ ap (λ m → ⟦ C ⟧ g ◻ m) (tri K f)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (leg K x)) ◃∎
          aux {x} {y} f = 
            ap (λ m → ⟦ C ⟧ m ◻ D₁ Δ f) (ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (leg K y))) ◃∙
            (α C g (⟦ C ⟧ leg K y ◻ id₁ C (D₀ Δ y)) (D₁ Δ f) ∙
            ap (λ m → ⟦ C ⟧ g ◻ m)
              (α C (leg K y) (id₁ C (D₀ Δ y)) (D₁ Δ f) ∙
              ap (λ m → ⟦ C ⟧ leg K y ◻ m) (! (! (ρ C (D₁ Δ f)) ∙ lamb C (D₁ Δ f))) ∙
              ! (α C (leg K y) (D₁ Δ f) (id₁ C (D₀ Δ x))) ∙
              ap (λ m → ⟦ C ⟧ m ◻ id₁ C (D₀ Δ x)) (tri K f))) ◃∎
              =ₛ₁⟨ 0 & 1 & ∘-ap (λ m → ⟦ C ⟧ m ◻ D₁ Δ f) (λ m → ⟦ C ⟧ g ◻ m) (ρ C (leg K y)) ⟩
            ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ◻ m ◻ D₁ Δ f) (ρ C (leg K y)) ◃∙
            (α C g (⟦ C ⟧ leg K y ◻ id₁ C (D₀ Δ y)) (D₁ Δ f) ∙
            ap (λ m → ⟦ C ⟧ g ◻ m)
              (α C (leg K y) (id₁ C (D₀ Δ y)) (D₁ Δ f) ∙
              ap (λ m → ⟦ C ⟧ leg K y ◻ m) (! (! (ρ C (D₁ Δ f)) ∙ lamb C (D₁ Δ f))) ∙
              ! (α C (leg K y) (D₁ Δ f) (id₁ C (D₀ Δ x))) ∙
              ap (λ m → ⟦ C ⟧ m ◻ id₁ C (D₀ Δ x)) (tri K f))) ◃∎
              =ₑ⟨ 1 & 2 & (α C g (⟦ C ⟧ leg K y ◻ id₁ C (D₀ Δ y)) (D₁ Δ f) ◃∙
                          ap (λ m → ⟦ C ⟧ g ◻ m)
                            (α C (leg K y) (id₁ C (D₀ Δ y)) (D₁ Δ f) ∙
                            ap (λ m → ⟦ C ⟧ leg K y ◻ m) (! (! (ρ C (D₁ Δ f)) ∙ lamb C (D₁ Δ f))) ∙
                            ! (α C (leg K y) (D₁ Δ f) (id₁ C (D₀ Δ x))) ∙
                            ap (λ m → ⟦ C ⟧ m ◻ id₁ C (D₀ Δ x)) (tri K f)) ◃∎)
                % =ₛ-in idp ⟩
            ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ◻ m ◻ D₁ Δ f) (ρ C (leg K y)) ◃∙
            α C g (⟦ C ⟧ leg K y ◻ id₁ C (D₀ Δ y)) (D₁ Δ f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m)
              (α C (leg K y) (id₁ C (D₀ Δ y)) (D₁ Δ f) ∙
              ap (λ m → ⟦ C ⟧ leg K y ◻ m) (! (! (ρ C (D₁ Δ f)) ∙ lamb C (D₁ Δ f))) ∙
              ! (α C (leg K y) (D₁ Δ f) (id₁ C (D₀ Δ x))) ∙
              ap (λ m → ⟦ C ⟧ m ◻ id₁ C (D₀ Δ x)) (tri K f)) ◃∎
              =ₛ⟨ 2 & 1 & ap-seq-∙ (λ m → ⟦ C ⟧ g ◻ m)
                            (α C (leg K y) (id₁ C (D₀ Δ y)) (D₁ Δ f) ◃∙
                            ap (λ m → ⟦ C ⟧ leg K y ◻ m) (! (! (ρ C (D₁ Δ f)) ∙ lamb C (D₁ Δ f))) ◃∙
                            ! (α C (leg K y) (D₁ Δ f) (id₁ C (D₀ Δ x))) ◃∙
                            ap (λ m → ⟦ C ⟧ m ◻ id₁ C (D₀ Δ x)) (tri K f) ◃∎) ⟩
            ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ◻ m ◻ D₁ Δ f) (ρ C (leg K y)) ◃∙
            α C g (⟦ C ⟧ leg K y ◻ id₁ C (D₀ Δ y)) (D₁ Δ f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (α C (leg K y) (id₁ C (D₀ Δ y)) (D₁ Δ f)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m)
              (ap (λ m → ⟦ C ⟧ leg K y ◻ m) (! (! (ρ C (D₁ Δ f)) ∙ lamb C (D₁ Δ f)))) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (! (α C (leg K y) (D₁ Δ f) (id₁ C (D₀ Δ x)))) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (ap (λ m → ⟦ C ⟧ m ◻ id₁ C (D₀ Δ x)) (tri K f)) ◃∎
              =ₛ⟨ 1 & 1 & apCommSq2◃-rev (λ m → α C g m (D₁ Δ f)) (ρ C (leg K y)) ⟩
            ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ◻ m ◻ D₁ Δ f) (ρ C (leg K y)) ◃∙
            ! (ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ◻ m ◻ D₁ Δ f) (ρ C (leg K y))) ◃∙
            α C g (leg K y) (D₁ Δ f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ m ◻ D₁ Δ f) (ρ C (leg K y)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (α C (leg K y) (id₁ C (D₀ Δ y)) (D₁ Δ f)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m)
              (ap (λ m → ⟦ C ⟧ leg K y ◻ m) (! (! (ρ C (D₁ Δ f)) ∙ lamb C (D₁ Δ f)))) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (! (α C (leg K y) (D₁ Δ f) (id₁ C (D₀ Δ x)))) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (ap (λ m → ⟦ C ⟧ m ◻ id₁ C (D₀ Δ x)) (tri K f)) ◃∎
              =ₛ₁⟨ 0 & 2 & !-inv-r (ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ◻ m ◻ D₁ Δ f) (ρ C (leg K y))) ⟩
            idp ◃∙
            α C g (leg K y) (D₁ Δ f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ m ◻ D₁ Δ f) (ρ C (leg K y)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (α C (leg K y) (id₁ C (D₀ Δ y)) (D₁ Δ f)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m)
              (ap (λ m → ⟦ C ⟧ leg K y ◻ m) (! (! (ρ C (D₁ Δ f)) ∙ lamb C (D₁ Δ f)))) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (! (α C (leg K y) (D₁ Δ f) (id₁ C (D₀ Δ x)))) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (ap (λ m → ⟦ C ⟧ m ◻ id₁ C (D₀ Δ x)) (tri K f)) ◃∎
              =ₛ₁⟨ 6 & 1 & ∘-ap (λ m → ⟦ C ⟧ g ◻ m) (λ m → ⟦ C ⟧ m ◻ id₁ C (D₀ Δ x)) (tri K f) ⟩
            idp ◃∙
            α C g (leg K y) (D₁ Δ f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ m ◻ D₁ Δ f) (ρ C (leg K y)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (α C (leg K y) (id₁ C (D₀ Δ y)) (D₁ Δ f)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m)
              (ap (λ m → ⟦ C ⟧ leg K y ◻ m) (! (! (ρ C (D₁ Δ f)) ∙ lamb C (D₁ Δ f)))) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (! (α C (leg K y) (D₁ Δ f) (id₁ C (D₀ Δ x)))) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ m ◻ id₁ C (D₀ Δ x)) (tri K f) ◃∎
              =ₛ⟨ 6 & 1 & apCommSq◃ (λ m → ap (λ n → ⟦ C ⟧ g ◻ n) (ρ C m)) (tri K f) ⟩
            idp ◃∙
            α C g (leg K y) (D₁ Δ f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ m ◻ D₁ Δ f) (ρ C (leg K y)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (α C (leg K y) (id₁ C (D₀ Δ y)) (D₁ Δ f)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m)
              (ap (λ m → ⟦ C ⟧ leg K y ◻ m) (! (! (ρ C (D₁ Δ f)) ∙ lamb C (D₁ Δ f)))) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (! (α C (leg K y) (D₁ Δ f) (id₁ C (D₀ Δ x)))) ◃∙
            ! (ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (⟦ C ⟧ leg K y ◻ D₁ Δ f))) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (tri K f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (leg K x)) ◃∎
              =ₛ₁⟨ 4 & 1 & ∘-ap (λ m → ⟦ C ⟧ g ◻ m) (λ m → ⟦ C ⟧ leg K y ◻ m) (! (! (ρ C (D₁ Δ f)) ∙ lamb C (D₁ Δ f))) ⟩
            idp ◃∙
            α C g (leg K y) (D₁ Δ f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ m ◻ D₁ Δ f) (ρ C (leg K y)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (α C (leg K y) (id₁ C (D₀ Δ y)) (D₁ Δ f)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ leg K y ◻ m) (! (! (ρ C (D₁ Δ f)) ∙ lamb C (D₁ Δ f))) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (! (α C (leg K y) (D₁ Δ f) (id₁ C (D₀ Δ x)))) ◃∙
            ! (ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (⟦ C ⟧ leg K y ◻ D₁ Δ f))) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (tri K f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (leg K x)) ◃∎
              =ₛ⟨ 4 & 1 & apCommSq◃ (λ m → α C g (leg K y) m) (! (! (ρ C (D₁ Δ f)) ∙ lamb C (D₁ Δ f))) ⟩
            idp ◃∙
            α C g (leg K y) (D₁ Δ f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ m ◻ D₁ Δ f) (ρ C (leg K y)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (α C (leg K y) (id₁ C (D₀ Δ y)) (D₁ Δ f)) ◃∙
            ! (α C g (leg K y) (⟦ C ⟧ id₁ C (D₀ Δ y) ◻ D₁ Δ f)) ◃∙
            ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ◻ leg K y ◻ m) (! (! (ρ C (D₁ Δ f)) ∙ lamb C (D₁ Δ f))) ◃∙
            α C g (leg K y) (⟦ C ⟧ D₁ Δ f ◻ id₁ C (D₀ Δ x)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (! (α C (leg K y) (D₁ Δ f) (id₁ C (D₀ Δ x)))) ◃∙
            ! (ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (⟦ C ⟧ leg K y ◻ D₁ Δ f))) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (tri K f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (leg K x)) ◃∎
              =ₛ⟨ 6 & 1 & apCommSq2◃-rev (λ m → α C g (leg K y) m) (ρ C (D₁ Δ f)) ⟩
            idp ◃∙
            α C g (leg K y) (D₁ Δ f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ m ◻ D₁ Δ f) (ρ C (leg K y)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (α C (leg K y) (id₁ C (D₀ Δ y)) (D₁ Δ f)) ◃∙
            ! (α C g (leg K y) (⟦ C ⟧ id₁ C (D₀ Δ y) ◻ D₁ Δ f)) ◃∙
            ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ◻ leg K y ◻ m) (! (! (ρ C (D₁ Δ f)) ∙ lamb C (D₁ Δ f))) ◃∙
            ! (ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ◻ leg K y ◻ m) (ρ C (D₁ Δ f))) ◃∙
            α C g (leg K y) (D₁ Δ f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ leg K y ◻ m) (ρ C (D₁ Δ f)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (! (α C (leg K y) (D₁ Δ f) (id₁ C (D₀ Δ x)))) ◃∙
            ! (ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (⟦ C ⟧ leg K y ◻ D₁ Δ f))) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (tri K f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (leg K x)) ◃∎
              =ₛ⟨ 4 & 1 & hnat-sq-!◃ (λ m → α C g (leg K y) m) (lamb C (D₁ Δ f)) ⟩
            idp ◃∙
            α C g (leg K y) (D₁ Δ f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ m ◻ D₁ Δ f) (ρ C (leg K y)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (α C (leg K y) (id₁ C (D₀ Δ y)) (D₁ Δ f)) ◃∙
            ! (ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ leg K y ◻ m) (lamb C (D₁ Δ f))) ◃∙
            ! (α C g (leg K y) (D₁ Δ f)) ◃∙
            ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ◻ leg K y ◻ m) (lamb C (D₁ Δ f)) ◃∙
            ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ◻ leg K y ◻ m) (! (! (ρ C (D₁ Δ f)) ∙ lamb C (D₁ Δ f))) ◃∙
            ! (ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ◻ leg K y ◻ m) (ρ C (D₁ Δ f))) ◃∙
            α C g (leg K y) (D₁ Δ f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ leg K y ◻ m) (ρ C (D₁ Δ f)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (! (α C (leg K y) (D₁ Δ f) (id₁ C (D₀ Δ x)))) ◃∙
            ! (ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (⟦ C ⟧ leg K y ◻ D₁ Δ f))) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (tri K f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (leg K x)) ◃∎
              =ₛ⟨ 7 & 1 & ap-!-!-∙◃ (λ m → ⟦ C ⟧ ⟦ C ⟧ g ◻ leg K y ◻ m) (ρ C (D₁ Δ f)) (lamb C (D₁ Δ f)) ⟩
            idp ◃∙
            α C g (leg K y) (D₁ Δ f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ m ◻ D₁ Δ f) (ρ C (leg K y)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (α C (leg K y) (id₁ C (D₀ Δ y)) (D₁ Δ f)) ◃∙
            ! (ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ leg K y ◻ m) (lamb C (D₁ Δ f))) ◃∙
            ! (α C g (leg K y) (D₁ Δ f)) ◃∙
            ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ◻ leg K y ◻ m) (lamb C (D₁ Δ f)) ◃∙
            ! (ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ◻ leg K y ◻ m) (lamb C (D₁ Δ f))) ◃∙
            ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ◻ leg K y ◻ m) (ρ C (D₁ Δ f)) ◃∙
            ! (ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ◻ leg K y ◻ m) (ρ C (D₁ Δ f))) ◃∙
            α C g (leg K y) (D₁ Δ f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ leg K y ◻ m) (ρ C (D₁ Δ f)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (! (α C (leg K y) (D₁ Δ f) (id₁ C (D₀ Δ x)))) ◃∙
            ! (ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (⟦ C ⟧ leg K y ◻ D₁ Δ f))) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (tri K f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (leg K x)) ◃∎
              =ₛ₁⟨ 6 & 2 & !-inv-r (ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ◻ leg K y ◻ m) (lamb C (D₁ Δ f))) ⟩
            idp ◃∙
            α C g (leg K y) (D₁ Δ f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ m ◻ D₁ Δ f) (ρ C (leg K y)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (α C (leg K y) (id₁ C (D₀ Δ y)) (D₁ Δ f)) ◃∙
            ! (ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ leg K y ◻ m) (lamb C (D₁ Δ f))) ◃∙
            ! (α C g (leg K y) (D₁ Δ f)) ◃∙
            idp ◃∙
            ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ◻ leg K y ◻ m) (ρ C (D₁ Δ f)) ◃∙
            ! (ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ◻ leg K y ◻ m) (ρ C (D₁ Δ f))) ◃∙
            α C g (leg K y) (D₁ Δ f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ leg K y ◻ m) (ρ C (D₁ Δ f)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (! (α C (leg K y) (D₁ Δ f) (id₁ C (D₀ Δ x)))) ◃∙
            ! (ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (⟦ C ⟧ leg K y ◻ D₁ Δ f))) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (tri K f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (leg K x)) ◃∎
              =ₛ₁⟨ 6 & 3 & !-inv-r (ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ◻ leg K y ◻ m) (ρ C (D₁ Δ f))) ⟩
            idp ◃∙
            α C g (leg K y) (D₁ Δ f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ m ◻ D₁ Δ f) (ρ C (leg K y)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (α C (leg K y) (id₁ C (D₀ Δ y)) (D₁ Δ f)) ◃∙
            ! (ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ leg K y ◻ m) (lamb C (D₁ Δ f))) ◃∙
            ! (α C g (leg K y) (D₁ Δ f)) ◃∙
            idp ◃∙
            α C g (leg K y) (D₁ Δ f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ leg K y ◻ m) (ρ C (D₁ Δ f)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (! (α C (leg K y) (D₁ Δ f) (id₁ C (D₀ Δ x)))) ◃∙
            ! (ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (⟦ C ⟧ leg K y ◻ D₁ Δ f))) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (tri K f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (leg K x)) ◃∎
              =ₛ₁⟨ 5 & 3 & !-inv-l (α C g (leg K y) (D₁ Δ f)) ⟩
            idp ◃∙
            α C g (leg K y) (D₁ Δ f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ m ◻ D₁ Δ f) (ρ C (leg K y)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (α C (leg K y) (id₁ C (D₀ Δ y)) (D₁ Δ f)) ◃∙
            ! (ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ leg K y ◻ m) (lamb C (D₁ Δ f))) ◃∙
            idp ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ leg K y ◻ m) (ρ C (D₁ Δ f)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (! (α C (leg K y) (D₁ Δ f) (id₁ C (D₀ Δ x)))) ◃∙
            ! (ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (⟦ C ⟧ leg K y ◻ D₁ Δ f))) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (tri K f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (leg K x)) ◃∎
              =ₛ₁⟨ 4 & 1 & ! (∘-ap-! (λ m → ⟦ C ⟧ g ◻ m) (λ m → ⟦ C ⟧ leg K y ◻ m) (lamb C (D₁ Δ f))) ⟩
            idp ◃∙
            α C g (leg K y) (D₁ Δ f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ m ◻ D₁ Δ f) (ρ C (leg K y)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (α C (leg K y) (id₁ C (D₀ Δ y)) (D₁ Δ f)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (! (ap (λ m → ⟦ C ⟧ leg K y ◻ m) (lamb C (D₁ Δ f)))) ◃∙
            idp ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ leg K y ◻ m) (ρ C (D₁ Δ f)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (! (α C (leg K y) (D₁ Δ f) (id₁ C (D₀ Δ x)))) ◃∙
            ! (ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (⟦ C ⟧ leg K y ◻ D₁ Δ f))) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (tri K f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (leg K x)) ◃∎
              =ₛ₁⟨ 2 & 1 & ap-∘ (λ m → ⟦ C ⟧ g ◻ m) (λ m → ⟦ C ⟧ m ◻ D₁ Δ f) (ρ C (leg K y)) ⟩
            idp ◃∙
            α C g (leg K y) (D₁ Δ f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (ap (λ m → ⟦ C ⟧ m ◻ D₁ Δ f) (ρ C (leg K y))) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (α C (leg K y) (id₁ C (D₀ Δ y)) (D₁ Δ f)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (! (ap (λ m → ⟦ C ⟧ leg K y ◻ m) (lamb C (D₁ Δ f)))) ◃∙
            idp ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ leg K y ◻ m) (ρ C (D₁ Δ f)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (! (α C (leg K y) (D₁ Δ f) (id₁ C (D₀ Δ x)))) ◃∙
            ! (ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (⟦ C ⟧ leg K y ◻ D₁ Δ f))) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (tri K f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (leg K x)) ◃∎
              =ₛ⟨ 2 & 3 & ap-seq-=ₛ (λ m → ⟦ C ⟧ g ◻ m) (triangle-wc-rot1 {C = C} trig (leg K y) (D₁ Δ f)) ⟩
            idp ◃∙
            α C g (leg K y) (D₁ Δ f) ◃∙
            idp ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ ⟦ C ⟧ leg K y ◻ m) (ρ C (D₁ Δ f)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (! (α C (leg K y) (D₁ Δ f) (id₁ C (D₀ Δ x)))) ◃∙
            ! (ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (⟦ C ⟧ leg K y ◻ D₁ Δ f))) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (tri K f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (leg K x)) ◃∎
              =ₛ₁⟨ 2 & 2 & ap-∘ (λ m → ⟦ C ⟧ g ◻ m) (λ m → ⟦ C ⟧ leg K y ◻ m) (ρ C (D₁ Δ f)) ⟩
            idp ◃∙
            α C g (leg K y) (D₁ Δ f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (ap (λ m → ⟦ C ⟧ leg K y ◻ m) (ρ C (D₁ Δ f))) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (! (α C (leg K y) (D₁ Δ f) (id₁ C (D₀ Δ x)))) ◃∙
            ! (ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (⟦ C ⟧ leg K y ◻ D₁ Δ f))) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (tri K f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (leg K x)) ◃∎
              =ₛ₁⟨ 4 & 1 & !-ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (⟦ C ⟧ leg K y ◻ D₁ Δ f)) ⟩
            idp ◃∙
            α C g (leg K y) (D₁ Δ f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (ap (λ m → ⟦ C ⟧ leg K y ◻ m) (ρ C (D₁ Δ f))) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (! (α C (leg K y) (D₁ Δ f) (id₁ C (D₀ Δ x)))) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (! (ρ C (⟦ C ⟧ leg K y ◻ D₁ Δ f))) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (tri K f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (leg K x)) ◃∎
              =ₛ⟨ 2 & 3 & ap-seq-=ₛ (λ m → ⟦ C ⟧ g ◻ m) (trig-ρ (leg K y) (D₁ Δ f)) ⟩
            idp ◃∙
            α C g (leg K y) (D₁ Δ f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (tri K f) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (leg K x)) ◃∎
              =ₛ₁⟨ 0 & 3 & idp ⟩
            (α C g (leg K y) (D₁ Δ f) ∙ ap (λ m → ⟦ C ⟧ g ◻ m) (tri K f)) ◃∙
            ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C (leg K x)) ◃∎ ∎ₛ

  -- we assume a standard property of bicategories
  module _ (trig : {a b c : ob C} (g : hom C b c) (f : hom C a b) →
      α C (id₁ C c) g f ◃∙ 
      ! (lamb C (⟦ C ⟧ g ◻ f)) ◃∎
        =ₛ
      ap (λ m → ⟦ C ⟧ m ◻ f) (! (lamb C g)) ◃∎)
    where

    abstract

      pst-cmp-id : {a : ob C} {Δ : Diagram G C} (K : Cocone-wc Δ a) → post-cmp-coc K a (id₁ C a) == K
      pst-cmp-id {a} {Δ} K = coc-to-==-◃ G ((λ x → ! (lamb C (leg K x))) ,
        (λ {x} {y} f →
          (α C (id₁ C a) (leg K y) (D₁ Δ f) ∙
          ap (λ m → ⟦ C ⟧ id₁ C a ◻ m) (tri K f)) ◃∙
          ! (lamb C (leg K x)) ◃∎
            =ₑ⟨ 0 & 1 & (α C (id₁ C a) (leg K y) (D₁ Δ f) ◃∙ ap (λ m → ⟦ C ⟧ id₁ C a ◻ m) (tri K f) ◃∎)
              % =ₛ-in idp ⟩
          α C (id₁ C a) (leg K y) (D₁ Δ f) ◃∙
          ap (λ m → ⟦ C ⟧ id₁ C a ◻ m) (tri K f) ◃∙
          ! (lamb C (leg K x)) ◃∎
            =ₛ⟨ 1 & 1 & apCommSq◃ (λ m → lamb C m) (tri K f) ⟩
          α C (id₁ C a) (leg K y) (D₁ Δ f) ◃∙
          ! (lamb C (⟦ C ⟧ leg K y ◻ D₁ Δ f)) ◃∙
          ap (λ z → z) (tri K f) ◃∙
          lamb C (leg K x) ◃∙
          ! (lamb C (leg K x)) ◃∎
            =ₛ₁⟨ 2 & 3 & ap2 _∙_ (ap-idf (tri K f)) (!-inv-r (lamb C (leg K x))) ∙ ∙-unit-r (tri K f) ⟩
          α C (id₁ C a) (leg K y) (D₁ Δ f) ◃∙
          ! (lamb C (⟦ C ⟧ leg K y ◻ D₁ Δ f)) ◃∙
          tri K f ◃∎
            =ₛ⟨ 0 & 2 & trig (leg K y) (D₁ Δ f) ⟩
          ap (λ m → ⟦ C ⟧ m ◻ D₁ Δ f) (! (lamb C (leg K y))) ◃∙
          tri K f ◃∎ ∎ₛ))

  -- we assume the pentagon identity of a bicat
  module _ (pent : pentagon-wc C) where

    abstract

      pst-cmp-∘ : {a b c : ob C} (g : hom C b c) (f : hom C a b) {Δ : Diagram G C} (K : Cocone-wc Δ a)
        → post-cmp-coc K c (⟦ C ⟧ g ◻ f) == post-cmp-coc (post-cmp-coc K b f) c g
      pst-cmp-∘ g f {Δ} K = coc-to-==-◃ G ((λ x → α C g f (leg K x)) ,
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

    coc-wc-mor-∘ : {Δ : Diagram G C} {T₁ T₂ T₃ : ob C}
      {K₁ : Cocone-wc Δ T₁} {K₂ : Cocone-wc Δ T₂} {K₃ : Cocone-wc Δ T₃}
      → Coc-wc-mor K₂ K₃ → Coc-wc-mor K₁ K₂ → Coc-wc-mor K₁ K₃
    fst (coc-wc-mor-∘ μ₂ μ₁) = ⟦ C ⟧ fst μ₂ ◻ fst μ₁
    snd (coc-wc-mor-∘ {T₃ = T₃} {K₁} μ₂ μ₁) =
      pst-cmp-∘ (fst μ₂) (fst μ₁) K₁ ∙
      ap (λ K → post-cmp-coc K T₃ (fst μ₂)) (snd μ₁) ∙
      snd μ₂

    abstract
    
      pre-cmp-∘ : {a b c : ob C} (g : hom C b c) (f : hom C a b) {Δ : Diagram G C} (K : Cone-wc Δ c)
        → pre-cmp-con K a (⟦ C ⟧ g ◻ f) == pre-cmp-con (pre-cmp-con K b g) a f 
      pre-cmp-∘ g f {Δ} K = con-to-==-◃ ((λ x → ! (α C (leg K x) g f)) ,
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
        → pre-cmp-con (act-dmap-con μ K) b f == act-dmap-con μ (pre-cmp-con K b f)
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
        → act-dmap-con (μ₂ diag-map-∘ μ₁) K == act-dmap-con μ₂ (act-dmap-con μ₁ K)
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
