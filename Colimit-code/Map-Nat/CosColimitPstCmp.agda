{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import Helper-paths
open import SIP-Cos
open import Coslice
open import Diagram-Cos
open import lib.types.Colim
open import Cocone-po

module CosColimitPstCmp where

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (h : B → C) (f : A → B) where 

  ap-∘-∙-∙ : {x y : A} (p₁ : x == y) {z : B} (p₂ : f y == z) {c : C} {s : h z == c} 
    → ap h (ap f p₁ ∙ p₂) ∙ s == ap (h ∘ f) p₁ ∙ ap h p₂ ∙ s
  ap-∘-∙-∙ idp p₂ = idp

module _ {ℓv ℓe ℓ ℓd ℓc₁ ℓc₂} {Γ : Graph ℓv ℓe} {A : Type ℓ} (F : CosDiag ℓd ℓ A Γ) {T : Coslice ℓc₁ ℓ A} {U : Coslice ℓc₂ ℓ A}
  (φ : < A > T *→ U) where

  open MapsCos A

  open Id Γ A

  open Maps F

  φ₁ = fst φ
  φ₂ = snd φ

  Map-to-Lim-map : CosCocone A F T →  CosCocone A F U
  comp (Map-to-Lim-map (comp₁ & comTri₁)) = λ i → φ ∘* comp₁ i
  comTri (Map-to-Lim-map (comp₁ & comTri₁)) {j} {i} =
    λ g → (λ x → ap φ₁ (fst (comTri₁ g) x)) ,
    λ a →
      !-ap-ap-∘-ap-∙ φ₁ (fst (comp₁ j)) (snd (F <#> g) a) {r = snd (comp₁ j) a} {s = snd φ a} (fst (comTri₁ g) (fun (F # i) a)) ∙
      ap (λ p → ap φ₁ p ∙ φ₂ a) (snd (comTri₁ g) a)

  module _ (f : P → ty T) (fₚ : (a : A) → f (left a) == fun T a) where

    NatSq-1-Λ-aux : {i j : Obj Γ} (g : Hom Γ i j) (a : A) {x z : P} {y : ty (F # j)}
      (p₁ : right (cin j (fst (F <#> g) (fun (F # i) a))) == x)
      (p₂ : fst (F <#> g) (fun (F # i) a) == y) (p₃ : right (cin j y) == z)
      {u : ty T} (p₄ : f z == u) {v : ty U} (p₅ : φ₁ u == v) →
      ! (ap (λ x → φ₁ (f x)) p₁) ∙
      ap (λ x → φ₁ (f (right (cin j x)))) p₂ ∙
      ap (λ x → φ₁ (f x)) p₃ ∙
      ap φ₁ p₄ ∙ p₅
        =-=
      ! (ap φ₁ (ap f p₁)) ∙
      ap (λ v → φ₁ (f (right (cin j v)))) p₂ ∙
      ap φ₁ (ap f p₃ ∙ p₄) ∙ p₅
    NatSq-1-Λ-aux g a idp idp idp p₄ p₅ = idp ◃∎ 

    NatSq-1-Λ-red : {i j : Obj Γ} (g : Hom Γ i j) (a : A) {x z : P} {y : ty (F # j)}
      (p₁ : right (cin j (fst (F <#> g) (fun (F # i) a))) == x)
      (p₂ : fst (F <#> g) (fun (F # i) a) == y) (p₃ : right (cin j y) == z) {u : ty T}
      (p₄ : f z == u) {v : ty U} (p₅ : φ₁ u == v)  →
      ! (ap (λ p → ! p ∙ ap (φ₁ ∘ f ∘ right ∘ cin j) p₂ ∙ ap (φ₁ ∘ f) p₃ ∙ ap φ₁ p₄ ∙ p₅) (∘-ap φ₁ f p₁)) ◃∙
      ap (λ p →  ! (p ∙ ap φ₁ (ap f p₁)) ∙ ap (φ₁ ∘ f ∘ right ∘ cin j) p₂ ∙ ap (φ₁ ∘ f) p₃ ∙ ap φ₁ p₄ ∙ p₅)
        (hmtpy-nat-rev {f = φ₁ ∘ f ∘ right ∘ cin j} (λ x → idp) p₂  (ap φ₁ (ap f p₃ ∙ p₄) ∙ p₅)) ◃∙
      ap (λ p →  (! ((ap (λ z → (φ₁ ∘ f ∘ right ∘ cin j) z) p₂ ∙ (p ∙ ! (ap φ₁ (ap f p₃ ∙ p₄) ∙ p₅)) ∙
          ! (ap (φ₁ ∘ f ∘ right ∘ cin j) p₂)) ∙
          ap φ₁ (ap f p₁)) ∙ ap (φ₁ ∘ f ∘ right ∘ cin j) p₂ ∙
          ap (φ₁ ∘ f) p₃ ∙ ap φ₁ p₄ ∙ p₅))
        (ap-∘-∙-∙ φ₁ f p₃ p₄) ◃∙
      long-path-red p₂ (ap (φ₁ ∘ f) p₃ ∙ ap φ₁ p₄ ∙ p₅) (ap φ₁ (ap f p₃ ∙ p₄) ∙ p₅) (ap φ₁ (ap f p₁)) idp ◃∎
        =ₛ
      ↯ (NatSq-1-Λ-aux g a p₁ p₂ p₃ p₄ p₅) ◃∎
    NatSq-1-Λ-red g a idp idp idp idp idp = =ₛ-in idp 

    NatSq-1-Λ-red2 : {i j : Obj Γ} (g : Hom Γ i j) (a : A) {x : P} {y : ty (F # j)}
      (p₁ : right (cin j (fst (F <#> g) (fun (F # i) a))) == x)
      (p₂ : fst (F <#> g) (fun (F # i) a) == y) (p₃ : right (cin j y) == left a)
      {σ : x == left a} (τ : ! p₁ ∙ ap (right ∘ cin j) p₂ ∙ p₃ == σ) →
      ↯ (NatSq-1-Λ-aux g a p₁ p₂ p₃ (fₚ a) (φ₂ a)) ◃∙
      ap (λ q → q)
        (!-ap-ap-∘-ap-∙ φ₁ (f ∘ right ∘ cin j) p₂ (ap f p₁) ∙
        ap (λ p → ap φ₁ p ∙ φ₂ a) (!-ap-ap-∘-ap-∙ f (right ∘ cin j) p₂ p₁ ∙
        ap (λ p → p ∙ fₚ a) (ap (ap f) τ))) ◃∙
      ap-∘-∙-∙ φ₁ f σ (fₚ a) ◃∎
        =ₛ
      (!-ap-ap-∘-ap-∙ (φ₁ ∘ f) (right ∘ cin j) p₂ p₁ ∙
      ap (λ p → p ∙ ap (fst φ) (fₚ a) ∙ φ₂ a) (ap (ap (φ₁ ∘ f)) τ)) ◃∎
    NatSq-1-Λ-red2 {i} {j} g a idp idp p₃ idp = =ₛ-in (lemma p₃ (fₚ a))
      where
        lemma : {z : P} (p : right (cin j (fst (F <#> g) (fun (F # i) a))) == z) (c : f z == fun T a)
          → ↯ (NatSq-1-Λ-aux g a idp idp p c (φ₂ a)) ∙ ap-∘-∙-∙ φ₁ f p c == idp
        lemma idp c = idp

    CosColim-NatSq1 : CosCocEq F U (Map-to-Lim-map (PostComp-cos ColCoC-cos (f , fₚ))) (PostComp-cos ColCoC-cos (φ ∘* (f , fₚ)))
    W CosColim-NatSq1 = λ i x → idp
    u CosColim-NatSq1 = λ i a → ap-∘-∙-∙ φ₁ f (! (glue (cin i a))) (fₚ a)  
    Λ CosColim-NatSq1 {i} {j} g = (λ x → ∘-ap φ₁ f (fst (comTri ColCoC-cos g) x)) , λ a → lemma a
      where
        lemma : (a : A) → 
          ! (ap (λ p → ! p ∙  ap (φ₁ ∘ f ∘ fst (comp ColCoC-cos j)) (snd (F <#> g) a) ∙
                ap (φ₁ ∘ f) (snd (comp ColCoC-cos j) a) ∙ snd (φ ∘* f , fₚ) a)
              (∘-ap φ₁ f (ap right (cglue g (fun (F # i) a))))) ◃∙
          ap (λ p → ! (p ∙ ap φ₁ (ap f (fst (comTri ColCoC-cos g) (fun (F # i) a)))) ∙
              ap (φ₁ ∘ f ∘ fst (comp ColCoC-cos j)) (snd (F <#> g) a) ∙
              ap (φ₁ ∘ f) (snd (comp ColCoC-cos j) a) ∙
              snd (φ ∘* f , fₚ) a)
            (hmtpy-nat-rev (λ x → idp) (snd (F <#> g) a)
              (snd (φ ∘* f ∘ fst (comp ColCoC-cos j) , (λ a₁ → ap f (snd (comp ColCoC-cos j) a₁) ∙ fₚ a₁))  a)) ◃∙
          ap (λ p → ! ((ap (φ₁ ∘ f ∘ fst (comp ColCoC-cos j)) (snd (F <#> g) a) ∙
              (p ∙ ! (snd (φ ∘* f ∘ fst (comp ColCoC-cos j) , (λ a₁ → ap f (snd (comp ColCoC-cos j) a₁) ∙ fₚ a₁)) a)) ∙
              ! (ap (fst (φ ∘* f ∘ fst (comp ColCoC-cos j) , (λ a₁ → ap f (snd (comp ColCoC-cos j) a₁) ∙ fₚ a₁))) (snd (F <#> g) a))) ∙
              ap φ₁ (ap f (fst (comTri ColCoC-cos g) (fun (F # i) a)))) ∙
              ap (φ₁ ∘ f ∘ fst (comp ColCoC-cos j)) (snd (F <#> g) a) ∙
              ap (φ₁ ∘ f) (snd (comp ColCoC-cos j) a) ∙ snd (φ ∘* f , fₚ) a)
            (ap-∘-∙-∙ φ₁ f (! (glue (cin j a))) (fₚ a)) ◃∙
          long-path-red (snd (F <#> g) a)
            (ap (φ₁ ∘ f) (! (glue (cin j a))) ∙ ap (fst φ) (fₚ a) ∙ snd φ a)
            (ap (fst φ) (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ snd φ a)
            (ap φ₁ (ap f (ap right (cglue g (fun (F # i) a))))) idp ◃∙
          ap (λ q → q)
            (!-ap-ap-∘-ap-∙ φ₁ (f ∘ fst (comp ColCoC-cos j)) (snd (F <#> g) a)
              (ap f (fst (comTri ColCoC-cos g) (fun (F # i) a))) ∙
              ap (λ p → ap φ₁ p ∙ φ₂ a)
            (!-ap-ap-∘-ap-∙ f (fst (comp ColCoC-cos j)) (snd (F <#> g) a) (fst (comTri ColCoC-cos g) (fun (F # i) a)) ∙
            ap (λ p → p ∙ fₚ a) (ap (ap f) (snd (comTri ColCoC-cos g) a)))) ◃∙
          ap-∘-∙-∙ φ₁ f (! (glue (cin i a))) (fₚ a) ◃∎
            =ₛ
          (!-ap-ap-∘-ap-∙ (φ₁ ∘ f) (fst (comp ColCoC-cos j)) (snd (F <#> g) a) (fst (comTri ColCoC-cos g) (fun (F # i) a)) ∙
          ap (λ p → p ∙ snd (φ ∘* f , fₚ) a) (ap (ap (φ₁ ∘ f)) (snd (comTri ColCoC-cos g) a))) ◃∎
        lemma a =
          ! (ap (λ p → ! p ∙ ap (φ₁ ∘ f ∘ fst (comp ColCoC-cos j)) (snd (F <#> g) a) ∙
                ap (φ₁ ∘ f) (snd (comp ColCoC-cos j) a) ∙ snd (φ ∘* f , fₚ) a)
              (∘-ap φ₁ f (ap right (cglue g (fun (F # i) a))))) ◃∙
          ap (λ p → ! (p ∙ ap φ₁ (ap f (fst (comTri ColCoC-cos g) (fun (F # i) a)))) ∙
              ap (φ₁ ∘ f ∘ fst (comp ColCoC-cos j)) (snd (F <#> g) a) ∙
              ap (φ₁ ∘ f) (snd (comp ColCoC-cos j) a) ∙
              snd (φ ∘* f , fₚ) a)
            (hmtpy-nat-rev (λ x → idp) (snd (F <#> g) a)
              (snd (φ ∘* f ∘ fst (comp ColCoC-cos j) , (λ a₁ → ap f (snd (comp ColCoC-cos j) a₁) ∙ fₚ a₁))  a)) ◃∙
          ap (λ p → ! ((ap (φ₁ ∘ f ∘ fst (comp ColCoC-cos j)) (snd (F <#> g) a) ∙
              (p ∙ ! (snd (φ ∘* f ∘ fst (comp ColCoC-cos j) , (λ a₁ → ap f (snd (comp ColCoC-cos j) a₁) ∙ fₚ a₁)) a)) ∙
              ! (ap (fst (φ ∘* f ∘ fst (comp ColCoC-cos j) , (λ a₁ → ap f (snd (comp ColCoC-cos j) a₁) ∙ fₚ a₁))) (snd (F <#> g) a))) ∙
              ap φ₁ (ap f (fst (comTri ColCoC-cos g) (fun (F # i) a)))) ∙
              ap (φ₁ ∘ f ∘ fst (comp ColCoC-cos j)) (snd (F <#> g) a) ∙
              ap (φ₁ ∘ f) (snd (comp ColCoC-cos j) a) ∙ snd (φ ∘* f , fₚ) a)
            (ap-∘-∙-∙ φ₁ f (! (glue (cin j a))) (fₚ a)) ◃∙
          long-path-red (snd (F <#> g) a)
            (ap (φ₁ ∘ f) (! (glue (cin j a))) ∙ ap (fst φ) (fₚ a) ∙ snd φ a)
            (ap (fst φ) (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ snd φ a)
            (ap φ₁ (ap f (ap right (cglue g (fun (F # i) a))))) idp ◃∙
          ap (λ q → q)
            (!-ap-ap-∘-ap-∙ φ₁ (f ∘ fst (comp ColCoC-cos j)) (snd (F <#> g) a)
              (ap f (fst (comTri ColCoC-cos g) (fun (F # i) a))) ∙
              ap (λ p → ap φ₁ p ∙ φ₂ a)
            (!-ap-ap-∘-ap-∙ f (fst (comp ColCoC-cos j)) (snd (F <#> g) a) (fst (comTri ColCoC-cos g) (fun (F # i) a)) ∙
            ap (λ p → p ∙ fₚ a) (ap (ap f) (snd (comTri ColCoC-cos g) a)))) ◃∙
          ap-∘-∙-∙ φ₁ f (! (glue (cin i a))) (fₚ a) ◃∎
            =ₛ⟨ 0 & 4 & NatSq-1-Λ-red g a (ap right (cglue g (fun (F # i) a))) (snd (F <#> g) a) (! (glue (cin j a))) (fₚ a) (φ₂ a) ⟩
          ↯ (NatSq-1-Λ-aux g a (ap right (cglue g (fun (F # i) a))) (snd (F <#> g) a) (! (glue (cin j a))) (fₚ a) (φ₂ a)) ◃∙ 
          ap (λ q → q)
            (!-ap-ap-∘-ap-∙ φ₁ (f ∘ fst (comp ColCoC-cos j)) (snd (F <#> g) a)
              (ap f (fst (comTri ColCoC-cos g) (fun (F # i) a))) ∙
            ap (λ p → ap φ₁ p ∙ φ₂ a)
              (!-ap-ap-∘-ap-∙ f (fst (comp ColCoC-cos j)) (snd (F <#> g) a) (fst (comTri ColCoC-cos g) (fun (F # i) a)) ∙
              ap (λ p → p ∙ fₚ a) (ap (ap f) (snd (comTri ColCoC-cos g) a)))) ◃∙
          ap-∘-∙-∙ φ₁ f (! (glue (cin i a))) (fₚ a) ◃∎
            =ₛ⟨ NatSq-1-Λ-red2 g a (ap right (cglue g (fun (F # i) a))) (snd (F <#> g) a) (! (glue (cin j a))) (snd (comTri ColCoC-cos g) a) ⟩          
          (!-ap-ap-∘-ap-∙ (φ₁ ∘ f) (fst (comp ColCoC-cos j)) (snd (F <#> g) a) (fst (comTri ColCoC-cos g) (fun (F # i) a)) ∙
          ap (λ p → p ∙ snd (φ ∘* f , fₚ) a) (ap (ap (φ₁ ∘ f)) (snd (comTri ColCoC-cos g) a))) ◃∎ ∎ₛ

    CosColim-NatSq1-eq : Map-to-Lim-map (PostComp-cos ColCoC-cos (f , fₚ)) == PostComp-cos ColCoC-cos (φ ∘* (f , fₚ))
    CosColim-NatSq1-eq = CosCocEq-to-== F U (Map-to-Lim-map (PostComp-cos ColCoC-cos (f , fₚ))) (CosColim-NatSq1)
