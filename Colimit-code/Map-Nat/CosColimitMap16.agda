{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pushout
open import Coslice
open import Diagram-Cos
open import lib.types.Colim
open import Cocone-po
open import SIP-CosCoc
open import AuxPaths
open import Helper-paths
open import CosColimitMap00
open import CosColimitMap03
open import CosColimitMap15

module CosColimitMap16 where

module _ {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open ConstrMap δ

  open Id Γ A

  open Maps

  module _ {i j : Obj Γ} (g : Hom Γ i j) (a : A) where

    open ConstrMap4.MapCoher3 δ g a

    open ConstrMap16.MapCoher15 δ g a    

    abstract

      fib-coher : 
        ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
            (∘-ap 𝕕₀ right (cglue g (str (F # i) a)) ∙ ap-∘ right δ₀ (cglue g (str (F # i) a)) ∙ ap (ap right) (δ₀-βr g (str (F # i) a)))) ◃∙
        ap (λ p → ! (p ∙ ap 𝕕₀ (ap right (cglue g (str (F # i) a)))) ∙
             ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙
             ! (glue (cin j a))) (hmtpy-nat-rev (λ x → idp) (snd (F <#> g) a) (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)) ◃∙
        ap (λ p → ! ((ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙ (p ∙ ! (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)) ∙
            ! (ap (𝕕₀ ∘ right ∘ cin j) (snd (F <#> g) a))) ∙ ap 𝕕₀ (ap right (cglue g (str (F # i) a)))) ∙
            ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
          (ap-inv-rid 𝕕₀ (glue (cin j a)) ∙ ap ! (𝕕-βr (cin j a)) ∙ !-!-ap-∘ (cin j) right (snd (nat δ j) a) (glue (cin j a))) ◃∙
        CCeq-coh-path (snd (F <#> g) a) (ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
          (ap 𝕕₀ (! (glue (cin j a))) ∙ idp) (ap 𝕕₀ (ap right (cglue g (str (F # i) a)))) idp ◃∙
        ap (λ q → q)
          (!-ap-ap-∘-ap-∙ 𝕕₀ (right ∘ cin j) (snd (F <#> g) a) (ap right (cglue g (str (F # i) a))) ∙
            ap (λ p → p ∙ idp)
              (ap (ap 𝕕₀)
                (E₁ (snd (F <#> g) a) (! (glue {d = SpCos₁} (cin j a))) ∙
                ! (ap (λ p → ! (ap right (! (ap (cin j) (snd (F <#> g) a)) ∙ cglue g (str (F # i) a))) ∙ ! (glue (cin j a)) ∙ p)
                    (ap (ap left) (id-βr g a))) ∙
                E₃ (λ x → ! (glue x)) (cglue g a) (ψ₁-βr g a) (λ x → idp) ∙ ∙-unit-r (! (glue (cin i a)))))) ◃∙
        ap-inv-rid 𝕕₀ (glue (cin i a)) ◃∙
        ap ! (𝕕-βr (cin i a)) ◃∙
        !-!-ap-∘ (cin i) right (snd (nat δ i) a) (glue (cin i a)) ◃∎
          =ₛ
        ap
          (λ p → ! (ap (right {d = SpCos₂}) p) ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
              ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
            (ap (λ p → ! (ap (cin j) p) ∙ cglue g (fst (nat δ i) (str (F # i) a))) (comSq-coher δ g a)) ◃∙
        ap (λ p → ! (ap (right {d = SpCos₂}) (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙
            snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙ p)) ∙
            ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
            ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
          (apCommSq2 (cin j ∘ fst (G <#> g)) (cin i) (cglue g) (snd (nat δ i) a)) ◃∙
        act-dmap-CC-coh (cin j) (fst (nat δ j)) (fst (G <#> g)) (cin i) right (snd (nat δ i) a)
          (snd (G <#> g) a) (snd (F <#> g) a) (snd (nat δ j) a) (cglue g (str (G # i) a)) (! (glue (cin j a))) ◃∙
        ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) (E₁ (snd (G <#> g) a) (! (glue (cin j a)))) ◃∙
        ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p)
          (! (ap (λ p → ! (ap right (! (ap (cin j) (snd (G <#> g) a)) ∙ cglue g (str (G # i) a))) ∙ ! (glue (cin j a)) ∙ p)
            (ap (ap left) (id-βr g a)))) ◃∙
        ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) (E₃ (λ x → ! (glue x)) (cglue g a) (ψ₂-βr g a) (λ x → idp)) ◃∙
        ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) (∙-unit-r (! (glue (cin i a)))) ◃∎
      fib-coher = post-rotate'-seq-out-idp (fib-coher3 ∙ₛ fib-coher-pre)

      fib-coher-post :
        ap (λ p → ! (ap (right {d = SpCos₂}) p) ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
          (ap (λ p → ! (ap (cin j) p) ∙ cglue g (fst (nat δ i) (str (F # i) a))) (comSq-coher δ g a)) ◃∙
        ap (λ p → ! (ap (right {d = SpCos₂}) (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙
             ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙ p)) ∙
             ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
           (apCommSq2 (cin j ∘ fst (G <#> g)) (cin i) (cglue g) (snd (nat δ i) a)) ◃∙
        act-dmap-CC-coh (cin j) (fst (nat δ j)) (fst (G <#> g)) (cin i) right (snd (nat δ i) a) (snd (G <#> g) a)
          (snd (F <#> g) a) (snd (nat δ j) a) (cglue g (str (G # i) a)) (! (glue (cin j a))) ◃∙
        ap-seq (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) (ε G g g a)
          =ₛ
        ap (λ p → ! (ap (right {d = SpCos₂}) p) ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
            ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
            (ap (λ p → ! (ap (cin j) p) ∙ cglue g (fst (nat δ i) (str (F # i) a))) (comSq-coher δ g a)) ◃∙
        ap (λ p → ! (ap (right {d = SpCos₂}) (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙
            ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙ p)) ∙
            ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
          (apCommSq2 (cin j ∘ fst (G <#> g)) (cin i) (cglue g) (snd (nat δ i) a)) ◃∙
        act-dmap-CC-coh (cin j) (fst (nat δ j)) (fst (G <#> g)) (cin i) right (snd (nat δ i) a) (snd (G <#> g) a)
          (snd (F <#> g) a) (snd (nat δ j) a) (cglue g (str (G # i) a)) (! (glue (cin j a))) ◃∙
        ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) (↯ (ε G g g a)) ◃∎
      fib-coher-post =
        ap (λ p → ! (ap (right {d = SpCos₂}) p) ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
          (ap (λ p → ! (ap (cin j) p) ∙ cglue g (fst (nat δ i) (str (F # i) a))) (comSq-coher δ g a)) ◃∙
        ap (λ p → ! (ap (right {d = SpCos₂}) (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙
             ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙ p)) ∙
             ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
           (apCommSq2 (cin j ∘ fst (G <#> g)) (cin i) (cglue g) (snd (nat δ i) a)) ◃∙
        act-dmap-CC-coh (cin j) (fst (nat δ j)) (fst (G <#> g)) (cin i) right (snd (nat δ i) a) (snd (G <#> g) a)
          (snd (F <#> g) a) (snd (nat δ j) a) (cglue g (str (G # i) a)) (! (glue (cin j a))) ◃∙
        ap-seq (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) (ε G g g a)
          =ₛ⟨ 3 & 4 & ∙-ap-seq (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) (ε G g g a) ⟩
        ap (λ p → ! (ap (right {d = SpCos₂}) p) ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
            ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
            (ap (λ p → ! (ap (cin j) p) ∙ cglue g (fst (nat δ i) (str (F # i) a))) (comSq-coher δ g a)) ◃∙
        ap (λ p → ! (ap (right {d = SpCos₂}) (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙
            ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙ p)) ∙
            ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
          (apCommSq2 (cin j ∘ fst (G <#> g)) (cin i) (cglue g) (snd (nat δ i) a)) ◃∙
        act-dmap-CC-coh (cin j) (fst (nat δ j)) (fst (G <#> g)) (cin i) right (snd (nat δ i) a) (snd (G <#> g) a)
          (snd (F <#> g) a) (snd (nat δ j) a) (cglue g (str (G # i) a)) (! (glue (cin j a))) ◃∙
        ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) (↯ (ε G g g a)) ◃∎ ∎ₛ      

  fib-inhab : CosCocEq (PostComp-cos (ColCoC-cos F) 𝕕) CC-from-diagmap
  W fib-inhab i x = idp
  u fib-inhab i a = ↯ $
    ap 𝕕₀ (! (glue (cin i a))) ∙ idp
      =⟪ ap-inv-rid 𝕕₀ (glue (cin i a)) ⟫
    ! (ap 𝕕₀ (glue (cin i a)))
      =⟪ ap ! (𝕕-βr (cin i a)) ⟫
    ! (glue (cin i a) ∙ ap right (! (ap (cin i) (snd (nat δ i) a))))
      =⟪ !-!-ap-∘ (cin i) right (snd (nat δ i) a) (glue (cin i a)) ⟫
    ap (right ∘ cin i) (snd (nat δ i) a) ∙ ! (glue (cin i a)) ∎∎
  fst (Λ fib-inhab {i} {j} g) x = ↯ $
    ap 𝕕₀ (ap right (cglue g x))
      =⟪ ∘-ap 𝕕₀ right (cglue g x) ⟫
    ap (right ∘ δ₀) (cglue g x)
      =⟪ ap-∘ right δ₀ (cglue g x) ⟫
    ap right (ap δ₀ (cglue g x))
      =⟪ ap (ap right) (δ₀-βr g x) ⟫
    ap right (! (ap (cin j) (comSq δ g x)) ∙ cglue g (fst (nat δ i) x)) ∎∎
  snd (Λ fib-inhab {i} {j} g) a = =ₛ-in (=ₛ-out (fib-coher g a ∙ₛ fib-coher-post g a))
