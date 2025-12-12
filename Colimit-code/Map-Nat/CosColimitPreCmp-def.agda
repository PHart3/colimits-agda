{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import Coslice
open import Diagram-Cos
open import Map-helpers

-- action of CosCocone (i.e., Limit) on morphisms of A-diagrams

module CosColimitPreCmp-def where

module _ {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ}
  (δ : CosDiagMor A F G) where

  Diag-to-Lim-map : ∀ {ℓc} {T : Coslice ℓc ℓ A} → CosCocone A G T → CosCocone A F T
  Diag-to-Lim-map (comp₁ & comTri₁) =
    (λ i → < A > comp₁ i ∘ nat δ i) &
    λ {j} {i} g → (λ x → ! (ap (fst (comp₁ j)) (comSq δ g x)) ∙ fst (comTri₁ g) (fst (nat δ i) x)) , λ a → ↯ (V g a)
      where
        V : {j i : Obj Γ} (g : Hom Γ i j) (a : A) →
          ! (! (ap (fst (comp₁ j)) (comSq δ g (str (F # i) a))) ∙ fst (comTri₁ g) (fst (nat δ i) (str (F # i) a))) ∙
          snd (< A > < A > comp₁ j ∘ nat δ j ∘ F <#> g) a
            =-=
          snd (< A > comp₁ i ∘ nat δ i) a
        V {j} {i} g a =
          ! (! (ap (fst (comp₁ j)) (comSq δ g (str (F # i) a))) ∙ fst (comTri₁ g) (fst (nat δ i) (str (F # i) a))) ∙
          snd (< A > < A > comp₁ j ∘ nat δ j ∘ F <#> g) a
            =⟪ !-!-∙-pth (ap (fst (comp₁ j)) (comSq δ g (str (F # i) a)))
                 (fst (comTri₁ g) (fst (nat δ i) (str (F # i) a))) ⟫
          ! (fst (comTri₁ g) (fst (nat δ i) (str (F # i) a))) ∙
          ap (fst (comp₁ j)) (comSq δ g (str (F # i) a)) ∙
          snd (< A > < A > comp₁ j ∘ nat δ j ∘ F <#> g) a
            =⟪ ap (λ p →
                    ! (fst (comTri₁ g) (fst (nat δ i) (str (F # i) a))) ∙
                    ap (fst (comp₁ j)) p ∙
                    snd (< A > < A > comp₁ j ∘ nat δ j ∘ F <#> g) a)
                 (comSq-coher δ g a) ⟫
          ! (fst (comTri₁ g) (fst (nat δ i) (str (F # i) a))) ∙
          ap (fst (comp₁ j))
            (ap (fst (G <#> g)) (snd (nat δ i) a) ∙
            snd (G <#> g) a ∙
            ! (snd (nat δ j) a) ∙
            ! (ap (fst (nat δ j)) (snd (F <#> g) a))) ∙
          snd (< A > < A > comp₁ j ∘ nat δ j ∘ F <#> g) a
            =⟪ ap (λ p → p ∙
                    ap (fst (comp₁ j))
                      (ap (fst (G <#> g)) (snd (nat δ i) a) ∙
                      snd (G <#> g) a ∙
                      ! (snd (nat δ j) a) ∙
                      ! (ap (fst (nat δ j)) (snd (F <#> g) a))) ∙
                    snd (< A > < A > comp₁ j ∘ nat δ j ∘ F <#> g) a)
                 (hmtpy-nat-! (fst (comTri₁ g)) (snd (nat δ i) a)) ⟫
          (ap (fst (comp₁ i)) (snd (nat δ i) a) ∙
          ! (fst (comTri₁ g) (str (G # i) a)) ∙
          ! (ap (fst (< A > comp₁ j ∘ G <#> g)) (snd (nat δ i) a))) ∙
          ap (fst (comp₁ j))
            (ap (fst (G <#> g)) (snd (nat δ i) a) ∙
            snd (G <#> g) a ∙
            ! (snd (nat δ j) a) ∙
            ! (ap (fst (nat δ j)) (snd (F <#> g) a))) ∙
          snd (< A > < A > comp₁ j ∘ nat δ j ∘ F <#> g) a
            =⟪ CCeq-coh-path-ya (fst (comp₁ j)) (fst (G <#> g)) (fst (nat δ j))
                 (ap (fst (comp₁ i)) (snd (nat δ i) a)) (snd (nat δ i) a)
                 (! (fst (comTri₁ g) (str (G # i) a)))
                 (snd (G <#> g) a) (snd (F <#> g) a) (snd (nat δ j) a) (snd (comp₁ j) a) ⟫
          ap (fst (comp₁ i)) (snd (nat δ i) a) ∙
          ! (fst (comTri₁ g) (str (G # i) a)) ∙
          snd (< A > comp₁ j ∘ G <#> g) a
            =⟪ ap (λ p → ap (fst (comp₁ i)) (snd (nat δ i) a) ∙ p) (snd (comTri₁ g) a) ⟫
          snd (< A > comp₁ i ∘ nat δ i) a ∎∎

