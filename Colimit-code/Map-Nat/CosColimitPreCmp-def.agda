{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import Coslice
open import Diagram-Cos

-- action of CosCocone (i.e., Limit) on morphisms of A-diagrams

module CosColimitPreCmp-def where

module _ {ℓ} {A : Type ℓ} where

  !-!-∙-pth : {x y z w : A} (p : x == y) (q : x == z) {c : y == w} → ! (! p ∙ q) ∙ c == ! q ∙ p ∙ c
  !-!-∙-pth idp idp = idp

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} (f : A → B) where

  ap-rid-∙ : {x y : A} (s : x == y) {w : B} (r : f y == w) → ap f (s ∙ idp) ∙ r == ap f s ∙ r
  ap-rid-∙ idp r = idp

  rid-ap-!-!-rid-ap : {y v z : A} {x w : B} (q : z == v) (p : x == f y) (s : y == v) (r : f v == w)
    → (p ∙ idp) ∙ ap f (s ∙ ! q ∙ idp) ∙ ap f q ∙ r == p ∙ ap f s ∙ r
  rid-ap-!-!-rid-ap idp idp s r = ap-rid-∙ s r

module _ {ℓ₀ ℓ₁ ℓ₂ ℓ₃} {A₁ : Type ℓ₀} {A₂ : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (f : B → C) (h : A₂ → B) (g : A₁ → B) where

  long-path-red-ya : {c₁ c₂ : C} (p₁ : c₁ == c₂) {a₁ a₂ : A₂} (p₂ : a₁ == a₂) (p₃ : c₂ == f (h a₂))
    {b : B} (p₄ : h a₂ == b) {z₁ z₂ : A₁} (p₆ : z₁  == z₂) (p₅ : g z₂ == b) {c : C} (p₇ : f b == c) →
    (p₁ ∙ p₃ ∙ ! (ap (f ∘ h) p₂)) ∙ ap f (ap h p₂ ∙ p₄ ∙ ! p₅ ∙ ! (ap g p₆)) ∙ ap (f ∘ g) p₆ ∙ ap f p₅ ∙ p₇
      ==
    p₁ ∙ p₃ ∙ ap f p₄ ∙ p₇
  long-path-red-ya idp idp p₃ p₄ idp p₅ p₇ = rid-ap-!-!-rid-ap f p₅ p₃ p₄ p₇

module _ {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  Diag-to-Lim-map : ∀ {ℓc} {T : Coslice ℓc ℓ A} → CosCocone A G T → CosCocone A F T
  Diag-to-Lim-map (comp₁ & comTri₁) =
    (λ i → < A > comp₁ i ∘ nat δ i) &
    λ {j} {i} g → (λ x → ! (ap (fst (comp₁ j)) (comSq δ g x)) ∙ fst (comTri₁ g) (fst (nat δ i) x)) , λ a → ↯ (V g a)
      where
        V : {j i : Obj Γ} (g : Hom Γ i j) (a : A) →
          ! (! (ap (fst (comp₁ j)) (comSq δ g (fun (F # i) a))) ∙ fst (comTri₁ g) (fst (nat δ i) (fun (F # i) a))) ∙
          snd (< A > < A > comp₁ j ∘ nat δ j ∘ F <#> g) a
            =-=
          snd (< A > comp₁ i ∘ nat δ i) a
        V {j} {i} g a =
          ! (! (ap (fst (comp₁ j)) (comSq δ g (fun (F # i) a))) ∙ fst (comTri₁ g) (fst (nat δ i) (fun (F # i) a))) ∙
          snd (< A > < A > comp₁ j ∘ nat δ j ∘ F <#> g) a
            =⟪ !-!-∙-pth (ap (fst (comp₁ j)) (comSq δ g (fun (F # i) a))) (fst (comTri₁ g) (fst (nat δ i) (fun (F # i) a))) ⟫
          ! (fst (comTri₁ g) (fst (nat δ i) (fun (F # i) a))) ∙
          ap (fst (comp₁ j)) (comSq δ g (fun (F # i) a)) ∙
          snd (< A > < A > comp₁ j ∘ nat δ j ∘ F <#> g) a
            =⟪ ap (λ p → ! (fst (comTri₁ g) (fst (nat δ i) (fun (F # i) a))) ∙ ap (fst (comp₁ j)) p ∙
                 snd (< A > < A > comp₁ j ∘ nat δ j ∘ F <#> g) a) (comSq-coher δ g a) ⟫
          ! (fst (comTri₁ g) (fst (nat δ i) (fun (F # i) a))) ∙
          ap (fst (comp₁ j)) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙
          snd (G <#> g) a ∙
          ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a))) ∙
          snd (< A > < A > comp₁ j ∘ nat δ j ∘ F <#> g) a
            =⟪ ap (λ p → p ∙ ap (fst (comp₁ j)) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙
                   ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a))) ∙ snd (< A > < A > comp₁ j ∘ nat δ j ∘ F <#> g) a)
                 (hmtpy-nat-! (fst (comTri₁ g)) (snd (nat δ i) a)) ⟫
          (ap (λ z → fst (comp₁ i) z) (snd (nat δ i) a) ∙
          ! (fst (comTri₁ g) (fun (G # i) a)) ∙
          ! (ap (λ z → fst (< A > comp₁ j ∘ G <#> g) z) (snd (nat δ i) a))) ∙
          ap (fst (comp₁ j))
            (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a))) ∙
          snd (< A > < A > comp₁ j ∘ nat δ j ∘ F <#> g) a
            =⟪ long-path-red-ya  (fst (comp₁ j)) (fst (G <#> g)) (fst (nat δ j)) (ap (fst (comp₁ i)) (snd (nat δ i) a))
                 (snd (nat δ i) a) (! (fst (comTri₁ g) (fun (G # i) a)))
                 (snd (G <#> g) a) (snd (F <#> g) a) (snd (nat δ j) a) (snd (comp₁ j) a) ⟫
          ap (fst (comp₁ i)) (snd (nat δ i) a) ∙
          ! (fst (comTri₁ g) (fun (G # i) a)) ∙
          snd (< A > comp₁ j ∘ G <#> g) a
            =⟪ ap (λ p → ap (fst (comp₁ i)) (snd (nat δ i) a) ∙ p) (snd (comTri₁ g) a) ⟫
          snd (< A > comp₁ i ∘ nat δ i) a ∎∎

