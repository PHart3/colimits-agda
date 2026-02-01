{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Colim
open import Coslice
open import Diagram-Cos
open import SIP-CosCoc
open import Cocone-po
open import Helper-paths
open import Map-helpers

module CosColimitMap00-aux where

module _ {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ}
  (δ : CosDiagMor A F G) where

  open Id.Maps Γ A

  private
    SpCos-G = SpCos G

  module _ {i j : Obj Γ} {g : Hom Γ i j} {a : A} where

    private
      lemma : {t₁ : ty (G # i)} (r : fst (nat δ i) (str (F # i) a) == t₁)
        {t₂ : ty (G # j)} {t₃ : ty (F # j)} (r' : fst (nat δ j) t₃ == t₂)
        (s' : fst (F <#> g) (str (F # i) a) == t₃)
        (s : fst (G <#> g) t₁ == t₂) {t₄ : Pushout SpCos-G} (gl : t₄ == right {d = SpCos-G} (cin j t₂)) → 
        ! (ap (λ p →
                ! p ∙ ap (right {d = SpCos-G} ∘ cin j ∘ fst (nat δ j)) s' ∙ ap (right ∘ cin j) r' ∙ ! gl)
            (ap-!-ap-∙ right (cin j)
              (ap (fst (G <#> g)) r ∙ s ∙ ! r' ∙ ! (ap (fst (nat δ j)) s')))) ∙
        ap (λ p → ! (p ∙ ap right (! (ap (cin j)
                 (ap (fst (G <#> g)) r ∙ s ∙ ! r' ∙ ! (ap (fst (nat δ j)) s'))) ∙
               cglue g (fst (nat δ i) (str (F # i) a)))) ∙
             ap (right ∘ cin j ∘ fst (nat δ j)) s' ∙
             ap (right ∘ cin j) r' ∙ ! gl)
           (hmtpy-nat-rev (λ _ → idp) s' (ap (right ∘ cin j) r' ∙ ! gl)) ∙
        CCeq-coh-path s' (ap (right ∘ cin j) r' ∙ ! gl)
          (ap (right ∘ cin j) r' ∙ ! gl)
          (ap right (! (ap (cin j)
              (ap (fst (G <#> g)) r ∙ s ∙ ! r' ∙ ! (ap (fst (nat δ j)) s'))) ∙
            cglue g (fst (nat δ i) (str (F # i) a)))) idp ∙
        ap (λ q → q) (
          ap (λ p → ! (ap right (! (ap (cin j)
                 (ap (fst (G <#> g)) r ∙ s ∙ ! r' ∙ ! (ap (fst (nat δ j)) s'))) ∙ p)) ∙
               ap (right ∘ cin j ∘ fst (nat δ j)) s' ∙
               ap (right ∘ cin j) r' ∙ ! gl)
             (apCommSq2 (cin j ∘ fst (G <#> g)) (cin i) (cglue g) r) ∙
          act-dmap-CC-coh (cin j) (fst (nat δ j)) (fst (G <#> g)) (cin i) right r s s'
            r' (cglue g t₁) (! gl) ∙ idp) ∙ idp
          ==
        !-!-∙-pth
          (ap (right ∘ cin j)
            (ap (fst (G <#> g)) r ∙ s ∙ ! r' ∙ ! (ap (fst (nat δ j)) s')))
          (ap right (cglue g (fst (nat δ i) (str (F # i) a)))) ∙
        ap (λ p →  p ∙ ap (right ∘ cin j)
             (ap (fst (G <#> g)) r ∙ s ∙ ! r' ∙ ! (ap (fst (nat δ j)) s')) ∙
             ap (right ∘ cin j ∘ fst (nat δ j)) s' ∙ ap (right ∘ cin j) r' ∙ ! gl)
           (hmtpy-nat-! (λ x → ap right (cglue g x)) r) ∙
        CCeq-coh-path-ya (right ∘ cin j) (fst (G <#> g)) (fst (nat δ j))
          (ap (right ∘ cin i) r) r
          (! (ap right (cglue g t₁))) s
          s' r' (! gl) ∙ idp
      lemma idp idp idp s idp = lemma2 s (cglue {D = DiagForg A Γ G} g (fst (nat δ i) (str (F # i) a)))
        where abstract
          lemma2 : {t₁ : ty (G # i)} {t₂ : ty (G # j)} (s : fst (G <#> g) t₁ == t₂)
            {t₂ : Colim (DiagForg A Γ G)} (r : cin j (fst (G <#> g) t₁) == t₂) →
            ! (ap (λ p → ! p ∙ idp) (ap-!-ap-∙ (right {d = SpCos-G}) (cin j) (s ∙ idp))) ∙
            !-∙-!-rid-∙ (ap right (! (ap (cin j) (s ∙ idp)) ∙ r)) idp idp ∙
            ap (λ q → q) (
              ap (λ p → ! (ap right (! (ap (cin j) (s ∙ idp)) ∙ p)) ∙ idp) (! (∙-unit-r r)) ∙
              !-!-!-∘-rid (cin j) right s idp idp r ∙ idp) ∙ idp
              ==
            !-!-∙-pth (ap (right ∘ cin j) (s ∙ idp)) (ap right r) ∙
            ap (λ p → p ∙ ap (right ∘ cin j) (s ∙ idp) ∙ idp) (! (∙-unit-r (! (ap right r)))) ∙
            rid-ap-!-!-rid-ap (right ∘ cin j) idp (! (ap right r)) s idp ∙ idp
          lemma2 idp idp = idp

    abstract
      CC-diagmap-lim-eq-coher : 
        {t₁ : fst (G <#> g) (fst (nat δ i) (str (F # i) a)) == fst (nat δ j) (fst (F <#> g) (str (F # i) a))}
        (r₁ :
          t₁
            ==
          ap (fst (G <#> g)) (snd (nat δ i) a) ∙
          snd (G <#> g) a ∙
          ! (snd (nat δ j) a) ∙
          ! (ap (fst (nat δ j)) (snd (F <#> g) a)))
          {t₂ : right (cin i (fst (nat δ i) (str (F # i) a))) == left a}
          (r₂ :
            ap (right ∘ cin i) (snd (nat δ i) a) ∙
            ! (ap right (cglue g (str (G # i) a))) ∙
            ap (right ∘ cin j) (snd (G <#> g) a) ∙
            ! (glue (cin j a))
              ==
            t₂) →
          ! (ap (λ p →
                  ! p ∙
                  ap (right {d = SpCos-G} ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
                  ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
              (ap-!-ap-∙ right (cin j) t₁)) ∙
          ap (λ p →
               ! (p ∙ ap right (! (ap (cin j) t₁) ∙ cglue g (fst (nat δ i) (str (F # i) a)))) ∙
               ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
               ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
            (hmtpy-nat-rev (λ _ → idp) (snd (F <#> g) a)
              (ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))) ∙
          CCeq-coh-path (snd (F <#> g) a) (ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
            (ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
            (ap right (! (ap (cin j) t₁) ∙ cglue g (fst (nat δ i) (str (F # i) a)))) idp ∙
          ap (λ q → q) (ap (λ p →
              ! (ap right p) ∙
              ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
              ap (right ∘ cin j) (snd (nat δ j) a) ∙
              ! (glue (cin j a)))
            (ap (λ p → ! (ap (cin j) p) ∙ cglue g (fst (nat δ i) (str (F # i) a))) r₁) ∙
          ap (λ p → ! (ap right (! (ap (cin j)
                (ap (fst (G <#> g)) (snd (nat δ i) a) ∙
                snd (G <#> g) a ∙
                ! (snd (nat δ j) a) ∙
                ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙ p)) ∙
              ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
              ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
            (apCommSq2 (cin j ∘ fst (G <#> g)) (cin i) (cglue g) (snd (nat δ i) a)) ∙
          act-dmap-CC-coh (cin j) (fst (nat δ j)) (fst (G <#> g)) (cin i) right
            (snd (nat δ i) a) (snd (G <#> g) a) (snd (F <#> g) a) (snd (nat δ j) a)
            (cglue g (str (G # i) a)) (! (glue (cin j a))) ∙ r₂) ∙ idp 
            ==
          !-!-∙-pth (ap (right ∘ cin j) t₁)
            (ap right (cglue g (fst (nat δ i) (str (F # i) a)))) ∙
          ap (λ p →
               ! (ap right (cglue g (fst (nat δ i) (str (F # i) a)))) ∙
               ap (right ∘ cin j) p ∙
               ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
               ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
             r₁ ∙
          ap (λ p →  p ∙ ap (right ∘ cin j)
               (ap (fst (G <#> g)) (snd (nat δ i) a) ∙
               snd (G <#> g) a ∙
               ! (snd (nat δ j) a) ∙
               ! (ap (fst (nat δ j)) (snd (F <#> g) a))) ∙
              ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
              ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
            (hmtpy-nat-! (λ x → ap right (cglue g x)) (snd (nat δ i) a)) ∙
          CCeq-coh-path-ya (right ∘ cin j) (fst (G <#> g)) (fst (nat δ j))
            (ap (right ∘ cin i) (snd (nat δ i) a)) (snd (nat δ i) a)
            (! (ap right (cglue g (str (G # i) a)))) (snd (G <#> g) a) (snd (F <#> g) a)
            (snd (nat δ j) a) (! (glue (cin j a))) ∙
          r₂
      CC-diagmap-lim-eq-coher idp idp =
        lemma (snd (nat δ i) a) (snd (nat δ j) a) (snd (F <#> g) a) (snd (G <#> g) a) (glue (cin j a))
