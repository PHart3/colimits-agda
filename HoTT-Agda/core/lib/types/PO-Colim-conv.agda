{-# OPTIONS --without-K  --rewriting #-}

open import lib.Basics
open import lib.types.Graph
open import lib.types.Diagram
open import lib.types.Span
open import lib.types.Colim
open import lib.types.Pushout

-- the Colim HIT on a span is equivalent to the Pushout

module lib.types.PO-Colim-conv where 

module _ {ℓ} (σ : Span {ℓ} {ℓ} {ℓ}) where

  private
  
    span-inclusion : (i : Triple) → span-to-grhom σ # i → Pushout σ
    span-inclusion lft = left
    span-inclusion mid = right ∘ Span.g σ
    span-inclusion rght = right

    span-inclusion-tri : (i j : Triple) (g : Hom Graph-span i j) (x : span-to-grhom σ # i) →
      span-inclusion j ((span-to-grhom σ <#> g) x) == span-inclusion i x
    span-inclusion-tri lft lft () x
    span-inclusion-tri lft mid () x
    span-inclusion-tri lft rght () x
    span-inclusion-tri mid lft unit x = glue x
    span-inclusion-tri mid mid () x
    span-inclusion-tri mid rght unit x = idp
    span-inclusion-tri rght lft () x
    span-inclusion-tri rght mid () x
    span-inclusion-tri rght rght () x

  Colim-PO-ty-to : Colim (span-to-grhom σ) → Pushout σ
  Colim-PO-ty-to = colimR span-inclusion span-inclusion-tri

  Colim-PO-ty-from : Pushout σ → Colim (span-to-grhom σ)
  Colim-PO-ty-from = Pushout-rec (cin lft) (cin rght) λ x → cglue {i = mid} unit x ∙ ! (cglue unit x)

  Colim-PO-ty-≃ : Colim (span-to-grhom σ) ≃ Pushout σ 
  Colim-PO-ty-≃ = equiv Colim-PO-ty-to Colim-PO-ty-from
    (PushoutMapEq _ _ (λ _ → idp) (λ _ → idp) λ x →
      ap (λ q → (! q ∙ idp) ∙ ap (λ z → z) (glue x))
        (ap-∘ Colim-PO-ty-to Colim-PO-ty-from (glue x) ∙
        ap (ap Colim-PO-ty-to) (PushoutRec.glue-β _ _ _ x) ∙
        ! (!r-ap-∙ Colim-PO-ty-to (cglue unit x) (cglue unit x)) ∙
        ap2 _∙_ (cglue-βr _ _ unit x) (ap ! (cglue-βr _ _ unit x))) ∙
      aux1 (glue x))
    (ColimMapEq _ _ ColimMapEq-leg ColimMapEq-tri)
    where
    
      module _ {l} {X : Type l} where

        aux1 : {x y : X} (p : x == y) → (! (p ∙ idp) ∙ idp) ∙ ap (λ z → z) p == idp
        aux1 idp = idp

        aux2 : {x y z : X} (p : x == y) (q : z == y) → ! (p ∙ ! q) ∙ ap (λ z → z) p == q
        aux2 idp idp = idp

      ColimMapEq-leg : (i : Triple) → (Colim-PO-ty-from ∘ Colim-PO-ty-to) ∘ cin i ∼ cin i
      ColimMapEq-leg lft _ = idp
      ColimMapEq-leg mid x = cglue unit x
      ColimMapEq-leg rght _ = idp

      abstract
        ColimMapEq-tri : (i j : Triple) (g : Hom Graph-span i j) (x : span-to-grhom σ # i) →
          ! (ap (Colim-PO-ty-from ∘ Colim-PO-ty-to) (cglue g x)) ∙
          ColimMapEq-leg j ((span-to-grhom σ <#> g) x) ∙
          ap (λ z → z) (cglue g x)
            ==
          ColimMapEq-leg i x
        ColimMapEq-tri lft lft () x
        ColimMapEq-tri lft mid () x
        ColimMapEq-tri lft rght () x
        ColimMapEq-tri mid lft unit x =
          ap (λ q → ! q ∙ ap (λ z → z) (cglue unit x)) (
            ap-∘ Colim-PO-ty-from Colim-PO-ty-to (cglue unit x) ∙
            ap (ap Colim-PO-ty-from) (cglue-βr _ _ unit x) ∙
            PushoutRec.glue-β _ _ _ x) ∙ 
          aux2 (cglue unit x) (cglue unit x)
        ColimMapEq-tri mid mid () x
        ColimMapEq-tri mid rght unit x = 
          ap (λ q → ! q ∙ ap (λ z → z) (cglue unit x)) (
            ap-∘ Colim-PO-ty-from Colim-PO-ty-to (cglue unit x) ∙
            ap (ap Colim-PO-ty-from) (cglue-βr _ _ unit x) ∙
            ! (!-inv-r (cglue unit x))) ∙ 
          aux2 (cglue unit x) (cglue unit x)
        ColimMapEq-tri rght lft () x
        ColimMapEq-tri rght mid () x
        ColimMapEq-tri rght rght () x

-- naturality of Colim-PO-ty-≃

module _ {ℓ₁ ℓ₂} {σ₁ : Span {ℓ₁} {ℓ₁} {ℓ₁}} {σ₂ : Span {ℓ₂} {ℓ₂} {ℓ₂}} (span-map : SpanMap-Rev σ₁ σ₂) where

  private
    module PM = PushoutMap span-map

  Colim-PO-ty-≃-nat : PM.f ∘ Colim-PO-ty-to σ₁ ∼ Colim-PO-ty-to σ₂ ∘ ColMap (diagmor-from-spanmap span-map)
  Colim-PO-ty-≃-nat = ColimMapEq _ _ ColimMapEq-leg ColimMapEq-tri
    where
    
      ColimMapEq-leg : (i : Triple) →
        PM.f ∘ Colim-PO-ty-to σ₁ ∘ cin i ∼ Colim-PO-ty-to σ₂ ∘ ColMap (diagmor-from-spanmap span-map) ∘ cin i
      ColimMapEq-leg lft _ = idp
      ColimMapEq-leg mid x = ! (ap right (commutes (SpanMap-Rev.g-commutes span-map) x))
      ColimMapEq-leg rght _ = idp

      abstract
        ColimMapEq-tri : (i j : Triple) (g : Hom Graph-span i j) (x : span-to-grhom σ₁ # i) →
          ! (ap (λ z → (PM.f ∘ Colim-PO-ty-to σ₁) z) (cglue g x)) ∙
          ColimMapEq-leg j ((span-to-grhom σ₁ <#> g) x) ∙
          ap (Colim-PO-ty-to σ₂ ∘ ColMap (diagmor-from-spanmap span-map)) (cglue g x)
            ==
          ColimMapEq-leg i x
        ColimMapEq-tri lft lft () x
        ColimMapEq-tri lft mid () x
        ColimMapEq-tri lft rght () x
        ColimMapEq-tri mid lft unit x = 
          ap2 _∙_
            (ap !
              (ap-∘ PM.f (Colim-PO-ty-to σ₁) (cglue unit x) ∙
              ap (ap PM.f) (cglue-βr _ _ unit x) ∙
              PushoutRec.glue-β _ _ _ x))
            (ap-∘ (Colim-PO-ty-to σ₂) (ColMap (diagmor-from-spanmap span-map)) (cglue unit x) ∙
            ap (ap (Colim-PO-ty-to σ₂)) (cglue-βr _ _ unit x) ∙
            ap-!-∙ (Colim-PO-ty-to σ₂)
              (ap (cin lft) (commutes (SpanMap-Rev.f-commutes span-map) x)) (cglue unit (SpanMap-Rev.hC span-map x)) ∙
            ap2 (λ p q → ! p ∙ q)
              (∘-ap (Colim-PO-ty-to σ₂) (cin lft) (commutes (SpanMap-Rev.f-commutes span-map) x))
              (cglue-βr _ _ unit (SpanMap-Rev.hC span-map x))) ∙
          aux
            (ap left (commutes (SpanMap-Rev.f-commutes span-map) x))
            (glue (SpanMap-Rev.hC span-map x))
            (ap right (commutes (SpanMap-Rev.g-commutes span-map) x))
          where
            aux : ∀ {ℓ} {X : Type ℓ} {x y z w : X} (p₁ : y == x) (p₂ : y == z) (p₃ : z == w)
              → ! (! p₁ ∙ p₂ ∙ p₃) ∙ ! p₁ ∙ p₂ == ! p₃
            aux idp idp idp = idp
        ColimMapEq-tri mid mid () x
        ColimMapEq-tri mid rght unit x =
          ap2 _∙_
            (ap !
              (ap-∘ PM.f (Colim-PO-ty-to σ₁) (cglue unit x) ∙
              ap (ap PM.f) (cglue-βr _ _ unit x)))
            (ap-∘ (Colim-PO-ty-to σ₂) (ColMap (diagmor-from-spanmap span-map)) (cglue unit x) ∙
            ap (ap (Colim-PO-ty-to σ₂)) (cglue-βr _ _ unit x) ∙
            ap-!-∙ (Colim-PO-ty-to σ₂)
              (ap (cin rght) (commutes (SpanMap-Rev.g-commutes span-map) x)) (cglue unit (SpanMap-Rev.hC span-map x)) ∙
            ap2 (λ p q → ! p ∙ q)
              (∘-ap (Colim-PO-ty-to σ₂) (cin rght) (commutes (SpanMap-Rev.g-commutes span-map) x))
              (cglue-βr _ _ unit (SpanMap-Rev.hC span-map x))) ∙
          ∙-unit-r (! (ap right (commutes (SpanMap-Rev.g-commutes span-map) x)))
        ColimMapEq-tri rght lft () x
        ColimMapEq-tri rght mid () x
        ColimMapEq-tri rght rght () x
