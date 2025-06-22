{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.SIP
open import lib.types.Colim
open import lib.types.Pushout
open import AuxPaths
open import Helper-paths
open import SIP-Cos
open import Coslice
open import Diagram-Cos
open import Cocone-po
open import CosColimitMap00
open import CosColimitPstCmp
open import CosColimitPreCmp-def

module CosColimitMap18 where

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄} (f : C → D) (g : B → C) (h : A → B) where

  ap-∘-∘-!-∙ : {x y : A} (p₁ : x == y) {z : B} (p₂ : h x == z)
    → ap f (ap g (! (ap h p₁) ∙ p₂)) == ! (ap (f ∘ g ∘ h) p₁) ∙ ap f (ap g p₂)
  ap-∘-∘-!-∙ idp idp = idp

module ConstrMap19 {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ}
  (δ : CosDiagMor A F G) where

  open Id Γ A

  open Maps G

  open ConstrMap δ

  module _ {ℓc} (T : Coslice ℓc ℓ A) (f : P₂ → ty T) (fₚ : (a : A) → f (left a) == str T a) where

    module _ {i j : Obj Γ} (g : Hom Γ i j) (a : A) where

      NatSq2-Λ-coher-aux3 : {w y : ty (G # i)} (τ₁₀ : w == y)
        {z : ty (F # j)} (τ₁₃ : fst (G <#> g) y == fst (nat δ j) z) →
        ! (ap (λ p → ! p ∙ idp) (ap-∘-∘-!-∙ f right (cin j) (ap (fst (G <#> g)) τ₁₀ ∙ τ₁₃ ∙ idp) idp)) ∙
        CCeq-coh-path {f = f ∘ right ∘ cin j ∘ fst (nat δ j)} {g = f ∘ right ∘ cin j ∘ fst (nat δ j)}
          idp idp idp (ap f (ap right (! (ap (cin j) (ap (fst (G <#> g)) τ₁₀ ∙ τ₁₃ ∙ idp)) ∙ idp))) idp ∙
        ap (λ q → q)
          (!-ap-ap-∘-ap-∙ f (right ∘ cin j ∘ fst (nat δ j)) idp (ap right (! (ap (cin j) (ap (fst (G <#> g)) τ₁₀ ∙ τ₁₃ ∙ idp)) ∙ idp)) ∙
          ap (λ p → ap f p ∙ idp)
            (ap (λ p → ! (ap right (! (ap (cin j) (ap (fst (G <#> g)) τ₁₀ ∙ τ₁₃ ∙ idp)) ∙ p)) ∙ idp)
              (apCommSq2 (λ x → cin j (fst (G <#> g) x)) (λ v → cin j (fst (G <#> g) v)) (λ x → idp) τ₁₀) ∙
              !-!-!-∘-∘-∘-rid (cin j) (fst (G <#> g)) (λ v → cin j (fst (G <#> g) v)) right τ₁₀ τ₁₃ idp idp idp ∙ idp)) ∙
        ap-∘-∙-∙ f (right ∘ (λ v → cin j (fst (G <#> g) v))) τ₁₀ (ap (right ∘ cin j) τ₁₃ ∙ idp)
          ==
        !-!-∙-pth (ap (λ x → f (right (cin j x))) (ap (fst (G <#> g)) τ₁₀ ∙ τ₁₃ ∙ idp)) idp ∙
        ap (λ p → p ∙ ap (λ x → f (right (cin j x))) (ap (fst (G <#> g)) τ₁₀ ∙ τ₁₃ ∙ idp) ∙ idp) (hmtpy-nat-! (λ x → idp) τ₁₀) ∙
        CCeq-coh-path-ya (λ x → f (right (cin j x))) (fst (G <#> g)) (fst (nat δ j))
          (ap (λ x → f (right (cin j (fst (G <#> g) x)))) τ₁₀) τ₁₀ idp τ₁₃ idp idp idp ∙
        ap (_∙_ (ap (λ x → f (right (cin j (fst (G <#> g) x)))) τ₁₀)) (!-ap-ap-∘-ap-∙ f (λ x → right (cin j x)) τ₁₃ idp ∙ idp)
      NatSq2-Λ-coher-aux3 {w} idp τ₁₃ = lemma τ₁₃
        where
          lemma : {z : ty (G # j)} (τ : fst (G <#> g) w == z) →
            ! (ap (λ p → ! p ∙ idp) (ap-∘-∘-!-∙ f right (cin j) (τ ∙ idp) idp)) ∙
            !-∙-!-rid-∙ (ap f (ap right (! (ap (cin j) (τ ∙ idp)) ∙ idp))) idp idp ∙
            ap (λ q → q)
              (!-ap-∙-s f (ap right (! (ap (cin j) (τ ∙ idp)) ∙ idp)) ∙
              ap (λ p → ap f p ∙ idp) (!-!-!-∘-rid (cin j) right τ idp idp idp ∙ idp)) ∙ idp
              ==
            !-!-∙-pth (ap (λ x → f (right (cin j x))) (τ ∙ idp)) idp ∙
            ap-rid-∙ (λ x → f (right (cin j x))) τ idp ∙
            ap (λ q → q) (!-ap-ap-∘-ap-∙ f (λ x → right (cin j x)) τ idp ∙ idp)
          lemma idp = idp

      NatSq2-Λ-coher-aux2 : (τ₁₀ : fst (nat δ i) (str (F # i) a) == str (G # i) a)
        {x : ty (F # j)} (τ₁₃ : fst (G <#> g) (str (G # i) a) == fst (nat δ j) x) →
        ! (ap (λ p → ! p ∙ idp)
            (ap-∘-∘-!-∙ f right (cin j) (ap (fst (G <#> g)) τ₁₀ ∙ τ₁₃ ∙ idp) (cglue g (fst (nat δ i) (str (F # i) a))))) ∙
        CCeq-coh-path {f = f ∘ right ∘ cin j ∘ fst (nat δ j)} {g = f ∘ right ∘ cin j ∘ fst (nat δ j)} idp idp idp
          (ap f (ap right (! (ap (cin j) (ap (fst (G <#> g)) τ₁₀ ∙ τ₁₃ ∙ idp)) ∙ cglue g (fst (nat δ i) (str (F # i) a))))) idp ∙
        ap (λ q → q)
          (!-ap-ap-∘-ap-∙ f (right ∘ cin j ∘ fst (nat δ j)) idp
            (ap right (! (ap (cin j) (ap (fst (G <#> g)) τ₁₀ ∙ τ₁₃ ∙ idp)) ∙ cglue g (fst (nat δ i) (str (F # i) a)))) ∙
          ap (λ p → ap f p ∙ idp)
            (ap (λ p → ! (ap right (! (ap (cin j) (ap (fst (G <#> g)) τ₁₀ ∙ τ₁₃ ∙ idp)) ∙ p)) ∙ idp)
              (apCommSq2 (λ x → cin j (fst (G <#> g) x)) (cin i) (cglue g) τ₁₀) ∙
            !-!-!-∘-∘-∘-rid (cin j) (fst (G <#> g)) (cin i) right τ₁₀ τ₁₃ idp idp (cglue g (str (G # i) a)) ∙ idp)) ∙
        ap-∘-∙-∙ f (right ∘ cin i) τ₁₀ (! (ap right (cglue g (str (G # i) a))) ∙ ap (right ∘ cin j) τ₁₃ ∙ idp)
          ==
        !-!-∙-pth (ap (λ x → f (right (cin j x))) (ap (fst (G <#> g)) τ₁₀ ∙ τ₁₃ ∙ idp))
          (ap f (ap right (cglue g (fst (nat δ i) (str (F # i) a))))) ∙
        ap (λ p → p ∙ ap (λ x → f (right (cin j x))) (ap (fst (G <#> g)) τ₁₀ ∙ τ₁₃ ∙ idp) ∙ idp)
          (hmtpy-nat-! (λ x → ap f (ap right (cglue g x))) τ₁₀) ∙
        CCeq-coh-path-ya (λ x → f (right (cin j x))) (fst (G <#> g)) (fst (nat δ j))
          (ap (λ x → f (right (cin i x))) τ₁₀) τ₁₀ (! (ap f (ap right (cglue g (str (G # i) a))))) τ₁₃ idp idp idp ∙
        ap (_∙_ (ap (λ x → f (right (cin i x))) τ₁₀))
          (!-ap-ap-∘-ap-∙ f (λ x → right (cin j x)) τ₁₃ (ap right (cglue g (str (G # i) a))) ∙ idp)
      NatSq2-Λ-coher-aux2 τ₁₀ τ₁₃ =
        ∼-ind
          (λ h H →
            ! (ap (λ p → ! p ∙ idp) (ap-∘-∘-!-∙ f right (cin j) (ap (fst (G <#> g)) τ₁₀ ∙ τ₁₃ ∙ idp)
              (H (fst (nat δ i) (str (F # i) a))))) ∙
            CCeq-coh-path {f = f ∘ right ∘ cin j ∘ fst (nat δ j)} {g = f ∘ right ∘ cin j ∘ fst (nat δ j)} idp idp idp
              (ap f (ap right (! (ap (cin j) (ap (fst (G <#> g)) τ₁₀ ∙ τ₁₃ ∙ idp)) ∙ H (fst (nat δ i) (str (F # i) a))))) idp ∙
            ap (λ q → q)
              (!-ap-ap-∘-ap-∙ f (right ∘ cin j ∘ fst (nat δ j)) idp
              (ap right (! (ap (cin j) (ap (fst (G <#> g)) τ₁₀ ∙ τ₁₃ ∙ idp)) ∙ H (fst (nat δ i) (str (F # i) a)))) ∙
              ap (λ p → ap f p ∙ idp)
                (ap (λ p → ! (ap right (! (ap (cin j) (ap (fst (G <#> g)) τ₁₀ ∙ τ₁₃ ∙ idp)) ∙ p)) ∙ idp)
                  (apCommSq2 (λ x → cin j (fst (G <#> g) x)) h H τ₁₀) ∙
                !-!-!-∘-∘-∘-rid (cin j) (fst (G <#> g)) h right τ₁₀ τ₁₃ idp idp (H (str (G # i) a)) ∙ idp)) ∙
            ap-∘-∙-∙ f (right ∘ h) τ₁₀ (! (ap right (H (str (G # i) a))) ∙ ap (right ∘ cin j) τ₁₃ ∙ idp)
              ==
            !-!-∙-pth (ap (λ x → f (right (cin j x))) (ap (fst (G <#> g)) τ₁₀ ∙ τ₁₃ ∙ idp))
              (ap f (ap right (H (fst (nat δ i) (str (F # i) a))))) ∙
            ap (λ p → p ∙ ap (λ x → f (right (cin j x))) (ap (fst (G <#> g)) τ₁₀ ∙ τ₁₃ ∙ idp) ∙ idp)
              (hmtpy-nat-! (λ x → ap f (ap right (H x))) τ₁₀) ∙
            CCeq-coh-path-ya (λ x → f (right (cin j x))) (fst (G <#> g))
              (fst (nat δ j)) (ap (λ x → f (right (h x))) τ₁₀) τ₁₀
              (! (ap f (ap right (H (str (G # i) a))))) τ₁₃ idp idp idp ∙
            ap (_∙_ (ap (λ x → f (right (h x))) τ₁₀))
              (!-ap-ap-∘-ap-∙ f (λ x → right (cin j x)) τ₁₃ (ap right (H (str (G # i) a))) ∙ idp))
          (NatSq2-Λ-coher-aux3 τ₁₀ τ₁₃)
          (cin i) (cglue g)

      NatSq2-Λ-coher-aux : (τ₁₀ : fst (nat δ i) (str (F # i) a) == str (G # i) a)
        (τ₁₃ : fst (G <#> g) (str (G # i) a) == fst (nat δ j) (fst (F <#> g) (str (F # i) a)))
        {σ₁ : fst (G <#> g) (fst (nat δ i) (str (F # i) a)) == fst (nat δ j) (fst (F <#> g) (str (F # i) a))}
        (τ₁₄ : σ₁ == ap (fst (G <#> g)) τ₁₀ ∙ τ₁₃ ∙ idp) →
        ! (ap (λ p → ! p ∙ idp) (ap-∘-∘-!-∙ f right (cin j) σ₁ (cglue g (fst (nat δ i) (str (F # i) a))))) ∙
        CCeq-coh-path {f = f ∘ right ∘ cin j ∘ fst (nat δ j)} {g = f ∘ right ∘ cin j ∘ fst (nat δ j)} idp idp idp
          (ap f (ap right (! (ap (cin j) σ₁) ∙ cglue g (fst (nat δ i) (str (F # i) a))))) idp ∙
        ap (λ q → q)
          (!-ap-ap-∘-ap-∙ f (right ∘ cin j ∘ fst (nat δ j)) idp
          (ap right (! (ap (cin j) σ₁) ∙ cglue g (fst (nat δ i) (str (F # i) a)))) ∙
          ap (λ p → ap f p ∙ idp)
            (ap (λ p → ! (ap right p) ∙ idp)
              (ap (λ p → ! (ap (cin j) p) ∙ cglue g (fst (nat δ i) (str (F # i) a))) τ₁₄) ∙
            ap (λ p → ! (ap right (! (ap (cin j) (ap (fst (G <#> g)) τ₁₀ ∙ τ₁₃ ∙ idp)) ∙ p)) ∙ idp)
              (apCommSq2 (λ x → cin j (fst (G <#> g) x)) (cin i) (cglue g) τ₁₀) ∙
            !-!-!-∘-∘-∘-rid (cin j) (fst (G <#> g)) (cin i) right τ₁₀ τ₁₃ idp idp (cglue g (str (G # i) a)) ∙ idp)) ∙
        ap-∘-∙-∙ f (right ∘ cin i) τ₁₀ (! (ap right (cglue g (str (G # i) a))) ∙
        ap (right ∘ cin j) τ₁₃ ∙ idp)
          ==
        !-!-∙-pth (ap (λ x → f (right (cin j x))) σ₁)
          (ap f (ap right (cglue g (fst (nat δ i) (str (F # i) a))))) ∙
        ap (λ p → ! (ap f (ap right (cglue g (fst (nat δ i) (str (F # i) a))))) ∙ ap (λ x → f (right (cin j x))) p ∙ idp) τ₁₄ ∙
        ap (λ p → p ∙ ap (λ x → f (right (cin j x))) (ap (fst (G <#> g)) τ₁₀ ∙ τ₁₃ ∙ idp) ∙ idp)
          (hmtpy-nat-! (λ x → ap f (ap right (cglue g x))) τ₁₀) ∙
        CCeq-coh-path-ya (λ x → f (right (cin j x))) (fst (G <#> g)) (fst (nat δ j))
          (ap (λ x → f (right (cin i x))) τ₁₀) τ₁₀
          (! (ap f (ap right (cglue g (str (G # i) a))))) τ₁₃ idp idp idp ∙
        ap (_∙_ (ap (λ x → f (right (cin i x))) τ₁₀))
          (!-ap-ap-∘-ap-∙ f (λ x → right (cin j x)) τ₁₃ (ap right (cglue g (str (G # i) a))) ∙ idp)
      NatSq2-Λ-coher-aux τ₁₀ τ₁₃ idp = NatSq2-Λ-coher-aux2 τ₁₀ τ₁₃

      NatSq2-Λ-coher : {x : ty (F # j)} (τ₅ : fst (F <#> g) (str (F # i) a) == x) {y : ty (G # j)} (τ₆ : fst (nat δ j) x == y)
        {z : P₂} (τ₇ : right (cin j y) == z) {w : ty T} (τ₈ : f z == w)
        (τ₁₀ : fst (nat δ i) (str (F # i) a) == str (G # i) a) (τ₁₃ : fst (G <#> g) (str (G # i) a) == y)
        (τ₁₄ : comSq δ g (str (F # i) a) == (ap (fst (G <#> g)) τ₁₀ ∙ τ₁₃ ∙ ! τ₆ ∙ ! (ap (fst (nat δ j)) τ₅)))
        {τ₁₁ : right (cin i (str (G # i) a)) == z}
        (τ₁ : ! (ap right (cglue g (str (G # i) a))) ∙ ap (right ∘ cin j) τ₁₃ ∙ τ₇ == τ₁₁) → 
        ! (ap (λ p → ! p ∙ ap (f ∘ right ∘ cin j ∘ fst (nat δ j)) τ₅ ∙ ap (f ∘ right ∘ cin j) τ₆ ∙ ap f τ₇ ∙ τ₈)
            (ap-∘-∘-!-∙ f right (cin j) (comSq δ g (str (F # i) a)) (cglue g (fst (nat δ i) (str (F # i) a))))) ◃∙
        ap (λ p → ! (p ∙ ap f (ap right (! (ap (cin j) (comSq δ g (str (F # i) a))) ∙
               (cglue g (fst (nat δ i) (str (F # i) a)))))) ∙
             ap (f ∘ right ∘ cin j ∘ fst (nat δ j)) τ₅ ∙
             ap (f ∘ right ∘ cin j) τ₆ ∙ ap f τ₇ ∙ τ₈)
          (hmtpy-nat-rev (λ x → idp) τ₅ (ap f (ap (λ x → right (cin j x)) τ₆ ∙ τ₇) ∙ τ₈)) ◃∙
        ap (λ p → ! ((ap (f ∘ right ∘ cin j ∘ fst (nat δ j)) τ₅ ∙ (p ∙ ! (ap f (ap (λ x → right (cin j x)) τ₆ ∙ τ₇) ∙ τ₈)) ∙
              ! (ap (f ∘ right ∘ cin j ∘ fst (nat δ j)) τ₅)) ∙
            ap f (ap right (! (ap (cin j) (comSq δ g (str (F # i) a))) ∙ (cglue g (fst (nat δ i) (str (F # i) a)))))) ∙
            ap (f ∘ right ∘ cin j ∘ fst (nat δ j)) τ₅ ∙
            ap (f ∘ right ∘ cin j) τ₆ ∙ ap f τ₇ ∙ τ₈)
          (ap-∘-∙-∙ f (right ∘ cin j) τ₆ τ₇) ◃∙
        CCeq-coh-path τ₅
          (ap (f ∘ right ∘ cin j) τ₆ ∙ ap f τ₇ ∙ τ₈)
          (ap f (ap (λ x → right (cin j x)) τ₆ ∙ τ₇) ∙ τ₈)
          (ap f (ap right (! (ap (cin j) (comSq δ g (str (F # i) a))) ∙ (cglue g (fst (nat δ i) (str (F # i) a)))))) idp ◃∙
        ap (λ q → q)
          (!-ap-ap-∘-ap-∙ f (right ∘ cin j ∘ fst (nat δ j)) τ₅
            (ap right (! (ap (cin j) (comSq δ g (str (F # i) a))) ∙ (cglue g (fst (nat δ i) (str (F # i) a))))) ∙
          ap (λ p → ap f p ∙ τ₈)
            (ap (λ p → ! (ap right p) ∙
                ap (λ x → right (cin j (fst (nat δ j) x))) τ₅ ∙
                ap (λ x → right (cin j x)) τ₆ ∙ τ₇)
              (ap (λ p → ! (ap (cin j) p) ∙ (cglue g (fst (nat δ i) (str (F # i) a)))) τ₁₄) ∙
            ap (λ p → ! (ap right (! (ap (cin j)  (ap (fst (G <#> g)) τ₁₀ ∙ τ₁₃ ∙ ! τ₆ ∙ ! (ap (fst (nat δ j)) τ₅))) ∙ p)) ∙
              ap (λ x → right (cin j (fst (nat δ j) x))) τ₅ ∙ ap (λ x → right (cin j x)) τ₆ ∙ τ₇)
            (apCommSq2 (λ x → cin j (fst (G <#> g) x)) (cin i) (cglue g) τ₁₀) ∙
            act-dmap-CC-coh (cin j) (fst (nat δ j)) (fst (G <#> g)) (cin i) right τ₁₀ τ₁₃ τ₅ τ₆ (cglue g (str (G # i) a)) τ₇ ∙
            ap (_∙_ (ap (λ x → right (cin i x)) τ₁₀)) τ₁)) ◃∙
        ap-∘-∙-∙ f (right ∘ cin i) τ₁₀ τ₁₁ ◃∎
          =ₛ
        (!-!-∙-pth (ap (λ x → f (right (cin j x))) (comSq δ g (str (F # i) a)))
          (ap f (ap right (cglue g (fst (nat δ i) (str (F # i) a))))) ∙
        ap (λ p →
             ! (ap f (ap right (cglue g (fst (nat δ i) (str (F # i) a))))) ∙
             ap (λ x → f (right (cin j x))) p ∙
             ap (λ x → f (right (cin j (fst (nat δ j) x)))) τ₅ ∙
             ap (λ x → f (right (cin j x))) τ₆ ∙
             ap f τ₇ ∙ τ₈)
           τ₁₄ ∙
        ap
          (λ p → p ∙
              ap (λ x → f (right (cin j x))) (ap (fst (G <#> g)) τ₁₀ ∙ τ₁₃ ∙ ! τ₆ ∙ ! (ap (fst (nat δ j)) τ₅)) ∙
              ap (λ x → f (right (cin j (fst (nat δ j) x)))) τ₅ ∙
              ap (λ x → f (right (cin j x))) τ₆ ∙
              ap f τ₇ ∙ τ₈)
            (hmtpy-nat-! (λ x → ap f (ap right (cglue g x))) τ₁₀) ∙
        CCeq-coh-path-ya (λ x → f (right (cin j x))) (fst (G <#> g))
          (fst (nat δ j)) (ap (λ x → f (right (cin i x))) τ₁₀) τ₁₀
          (! (ap f (ap right (cglue g (str (G # i) a))))) τ₁₃ τ₅ τ₆ (ap f τ₇ ∙ τ₈) ∙
        ap (_∙_ (ap (λ x → f (right (cin i x))) τ₁₀))
          (!-ap-ap-∘-ap-∙ f (λ x → right (cin j x)) τ₁₃ (ap right (cglue g (str (G # i) a))) ∙
            ap (λ p → p ∙ τ₈) (ap (ap f) τ₁))) ◃∎
      NatSq2-Λ-coher idp idp idp idp τ₁₀ τ₁₃ τ₁₄ idp = =ₛ-in (NatSq2-Λ-coher-aux τ₁₀ τ₁₃ τ₁₄)

    abstract
      CosColim-NatSq2 : CosCocEq (Map-to-Lim-map F (f , fₚ) CC-from-diagmap) (Diag-to-Lim-map δ (PostComp-cos ColCoC-cos (f , fₚ)))
      W CosColim-NatSq2 i x = idp
      u CosColim-NatSq2 i a = ap-∘-∙-∙ f (right ∘ cin i) (snd (nat δ i) a) (! (glue (cin i a)))
      Λ CosColim-NatSq2 {i} {j} g =
        (λ x → ap-∘-∘-!-∙ f right (cin j) (comSq δ g x) (cglue g (fst (nat δ i) x))) ,
        λ a → NatSq2-Λ-coher g a (snd (F <#> g) a) (snd (nat δ j) a) (! (glue (cin j a))) (fₚ a)
          (snd (nat δ i) a) (snd (G <#> g) a) (comSq-coher δ g a)
          (E₁ (snd (G <#> g) a) (! (glue (cin j a))) ∙
          ! (ap (λ p → ! (ap right (! (ap (cin j) (snd (G <#> g) a)) ∙ cglue g (str (G # i) a))) ∙ ! (glue (cin j a)) ∙ p)
              (ap (ap left) (id-βr g a))) ∙
          E₃ (λ x → ! (glue x)) (cglue g a) (ψ₂-βr g a) (λ x → idp) ∙
          ∙-unit-r (! (glue (cin i a))))

    CosColim-NatSq2-eq : Map-to-Lim-map F (f , fₚ) CC-from-diagmap == Diag-to-Lim-map δ (PostComp-cos ColCoC-cos (f , fₚ))
    CosColim-NatSq2-eq = CosCocEq-to-== CosColim-NatSq2
