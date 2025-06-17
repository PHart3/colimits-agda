{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import Coslice
open import Diagram-Cos
open import lib.types.Colim
open import Cocone-po

module CosColimitMap00 where

open import Map-helpers public

-- definition of action on maps of A-diagrams

module ConstrMap {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open Id.Maps Γ A

  ForgF = DiagForg A Γ F

  ForgG = DiagForg A Γ G

  private
    module N = ColimitMap {F = ForgF} {G = ForgG} (diagmor (λ i → fst (nat δ i)) (comSq δ))

  δ₀ : Colim ForgF → Colim ForgG
  δ₀ = N.ColMap

  δ₀-βr = N.ColMap-β

  ψ₁ = ψ F

  ψ₁-βr = ψ-βr F

  ψ₂ = ψ G

  ψ₂-βr = ψ-βr G

  SpCos₁ = SpCos F

  SpCos₂ = SpCos G

  P₁ = Pushout SpCos₁

  P₂ = Pushout SpCos₂

  module _ {i j : Obj Γ} (g : Hom Γ i j) (a : A) where

    ζ : transport (λ z → δ₀ (ψ₁ z) == ψ₂ z) (cglue g a) (ap (cin j) (snd (nat δ j) a)) =-= ap (cin i) (snd (nat δ i) a)
    ζ =
      transport (λ z → δ₀ (ψ₁ z) == ψ₂ z) (cglue g a) (ap (cin j) (snd (nat δ j) a))
        =⟪ transp-pth-cmpL δ₀ ψ₁ ψ₂ (cglue g a) (ap (cin j) (snd (nat δ j) a))  ⟫
      ! (ap δ₀ (ap ψ₁ (cglue g a))) ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a)
        =⟪ ap (λ p → ! (ap δ₀ p) ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a)) (ψ₁-βr g a) ⟫
      ! (ap δ₀ (! (ap (cin j) (snd (F <#> g) a)) ∙ cglue g (str (F # i) a))) ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a)
        =⟪ pre-cmp-!-!-∙ δ₀ (cin j) (snd (F <#> g) a) (cglue g (str (F # i) a)) (ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a)) ⟫
      ! (ap δ₀ (cglue g (str (F # i) a))) ∙ ap (cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a)
        =⟪ ap (λ p → ! p ∙ ap (cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a)) (δ₀-βr g (str (F # i) a)) ⟫
      ! (! (ap (cin j) (comSq δ g (str (F # i) a))) ∙ cglue g (fst (nat δ i) (str (F # i) a))) ∙
      ap (cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙
      ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a) 
        =⟪ ap (λ p → ! p ∙ ap (cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a))
             (ap (λ p → ! (ap (cin j) p) ∙ cglue g (fst (nat δ i) (str (F # i) a))) (comSq-coher δ g a)) ⟫
      ! (! (ap (cin j)
             (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙
         cglue g (fst (nat δ i) (str (F # i) a))) ∙ ap (cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a)
        =⟪ ap (λ p →
             ! (! (ap (cin j)
                    (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙
                  cglue g (fst (nat δ i) (str (F # i) a))) ∙
             ap (cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (cin j) (snd (nat δ j) a) ∙ p)
             (ψ₂-βr g a) ⟫
      ! (! (ap (cin j)
               (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙
             cglue g (fst (nat δ i) (str (F # i) a))) ∙
      ap (cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (cin j) (snd (nat δ j) a) ∙
      ! (ap (cin j) (snd (G <#> g) a)) ∙ cglue g (str (G # i) a)
        =⟪ long-red-!-∙ (cin j) (fst (nat δ j)) (fst (G <#> g)) (snd (nat δ i) a) (snd (G <#> g) a) (snd (F <#> g) a) (snd (nat δ j) a)
             (cglue g (fst (nat δ i) (str (F # i) a))) (cglue g (str (G # i) a))  ⟫
      ! (cglue g (fst (nat δ i) (str (F # i) a))) ∙ ap (cin j ∘ fst (G <#> g)) (snd (nat δ i) a) ∙ cglue g (str (G # i) a)
        =⟪ apCommSq (cin j ∘ fst (G <#> g)) (cin i) (cglue g) (snd (nat δ i) a) ⟫
      ap (cin i) (snd (nat δ i) a) ∎∎

    Θ :
      ! (ap (right {d = SpCos₂}) (! (ap (cin j) (comSq δ g (str (F # i) a))) ∙ cglue g (fst (nat δ i) (str (F # i) a)))) ∙
      ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))
        =-=
      ap (right ∘ cin i) (snd (nat δ i) a) ∙ ! (glue (cin i a))
    Θ =
      ! (ap (right {d = SpCos₂}) (! (ap (cin j) (comSq δ g (str (F # i) a))) ∙ cglue g (fst (nat δ i) (str (F # i) a)))) ∙
      ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))
        =⟪ ap (λ p → ! (ap (right {d = SpCos₂}) p) ∙
                ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
             (ap (λ p → ! (ap (cin j) p) ∙ cglue g (fst (nat δ i) (str (F # i) a))) (comSq-coher δ g a)) ⟫
      ! (ap (right {d = SpCos₂})
          (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙
          cglue g (fst (nat δ i) (str (F # i) a)))) ∙
      ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))
        =⟪ ap (λ p →
                ! (ap (right {d = SpCos₂}) (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙
                  ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙ p)) ∙
                ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
                ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
              (apCommSq2 (cin j ∘ fst (G <#> g)) (cin i) (cglue g) (snd (nat δ i) a))  ⟫
      ! (ap right
          (! (ap (cin j)
               (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙
          ap (cin j ∘ fst (G <#> g)) (snd (nat δ i) a) ∙
          cglue g (str (G # i) a) ∙ ! (ap (cin i) (snd (nat δ i) a)))) ∙
      ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
      ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))
        =⟪ long-red-ap-!-∙ (cin j) (fst (nat δ j)) (fst (G <#> g)) (cin i) right (snd (nat δ i) a) (snd (G <#> g) a) (snd (F <#> g) a)
             (snd (nat δ j) a) (cglue g (str (G # i) a)) (! (glue (cin j a))) ⟫
      ap (right ∘ cin i) (snd (nat δ i) a) ∙ ! (ap right (cglue g (str (G # i) a))) ∙ ap (right ∘ cin j) (snd (G <#> g) a) ∙ ! (glue (cin j a))
        =⟪ ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) (↯ (ε G g g a)) ⟫
      ap (right ∘ cin i) (snd (nat δ i) a) ∙ ! (glue (cin i a)) ∎∎

  -- map of A-diagrams induces A-cocone
  CC-from-diagmap : CosCocone A F (Cos P₂ left)
  fst (comp CC-from-diagmap i) = right ∘ cin i ∘ fst (nat δ i)
  snd (comp CC-from-diagmap i) a = ap (right ∘ cin i) (snd (nat δ i) a) ∙ ! (glue (cin i a))
  fst (comTri CC-from-diagmap {j} {i} g) x = ap right (! (ap (cin j) (comSq δ g x)) ∙ cglue g (fst (nat δ i) x))
  snd (comTri CC-from-diagmap g) a = ↯ (Θ g a)

  ℂ : δ₀ ∘ ψ₁ ∼ ψ₂
  ℂ = colimE (λ i a → ap (cin i) (snd (nat δ i) a))
        (λ i j g a →  from-transp-g (λ z → δ₀ (ψ₁ z) == ψ₂ z) (cglue g a) (↯ (ζ g a)))

  ℂ-β : {i j : Obj Γ} (g : Hom Γ i j) (a : A) → apd-tr ℂ (cglue g a) ◃∎ =ₛ ζ g a
  ℂ-β {i} {j} g a = =ₛ-in (
    apd-to-tr (λ z → δ₀ (ψ₁ z) == ψ₂ z) ℂ (cglue g a)
    (↯ (ζ g a))
    (cglue-β
      (λ i a → ap (cin i) (snd (nat δ i) a))
      (λ i j g a →  from-transp-g (λ z → δ₀ (ψ₁ z) == ψ₂ z) (cglue g a) (↯ (ζ g a))) g a) ) 

  span-map-forg : SpanMap-Rev SpCos₁ SpCos₂
  SpanMap-Rev.hA span-map-forg = idf A
  SpanMap-Rev.hB span-map-forg = δ₀
  SpanMap-Rev.hC span-map-forg = idf (Colim (ConsDiag Γ A))
  SpanMap-Rev.f-commutes span-map-forg = comm-sqr λ z → idp
  SpanMap-Rev.g-commutes span-map-forg = comm-sqr (λ z → ! (ℂ z))

  private
    module PM = PushoutMap span-map-forg

  -- colimit action on maps
  𝕕 : < A > Cos P₁ left *→ Cos P₂ left
  𝕕 = PM.f , (λ a → idp)

  𝕕₀ = fst 𝕕
  
  𝕕-βr = PM.glue-β

  ForgMap =
    colimR (λ i → right {d = SpCos₂} ∘ cin i ∘ (fst (nat δ i)))
      (λ i j g x → ap right (! (ap (cin j) (comSq δ g x)) ∙ cglue g (fst (nat δ i) x)))

  FM-βr =
    cglue-βr (λ i → right {d = SpCos₂} ∘ cin i ∘ fst (nat δ i))
      (λ i j g x → ap right (! (ap (cin j) (comSq δ g x)) ∙ cglue g (fst (nat δ i) x)))
