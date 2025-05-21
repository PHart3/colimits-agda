{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import Coslice
open import Diagram
open import Colim
open import Cocone

module CosColimitMap00 where

-- A long list of helper paths

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (f : A → B) (h : C → A) where

  pre-cmp-!-!-∙ : {x y : C} (q : x == y) {a : A} (p : h x == a) {b : B} (r : f (h y) == b)
    → ! (ap f (! (ap h q) ∙ p)) ∙ r == ! (ap f p) ∙ ap (f ∘ h) q ∙ r
  pre-cmp-!-!-∙ idp p r = idp

  pre-cmp-!-∙ : {x y : C} (p : x == y) {a : A} (q : h x == a) → ! (ap (f ∘ h) p) ∙ ap f q == ap f (! (ap h p) ∙ q)
  pre-cmp-!-∙ idp idp = idp

  !-!-ap-cmp-rid3 : {x y : C} (p : x == y) {a : A} (q : h y == a)
    → ! (ap f (! (ap h (! p ∙ idp)) ∙ q ∙ idp)) ∙ ap (f ∘ h) p ∙ idp == ! (ap f q) ∙ idp
  !-!-ap-cmp-rid3 idp idp = idp

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} (f : A → B) where

  ap-!-!-!-rid : {x y : A} (p₂ : x == y) {b₁ b₂ : B} (p₅ : f x == b₁) (p₆ : f x == b₂)
    → ! (! (ap f (p₂ ∙ idp)) ∙ p₅) ∙ ! (ap f p₂) ∙ p₆ == ! p₅ ∙ p₆
  ap-!-!-!-rid idp p₅ p₆ = idp 

  ap-!-!-!-!-rid : {x y z : A} (p₃ : x == y) (p₂ : z == y) {b₁ b₂ : B} (p₅ : f z == b₁) (p₆ : f z == b₂)
    → ! (! (ap f (p₂ ∙ ! p₃ ∙ idp)) ∙ p₅) ∙ ap f p₃ ∙ ! (ap f p₂) ∙ p₆ == ! p₅ ∙ p₆
  ap-!-!-!-!-rid idp p₂ p₅ p₆ = ap-!-!-!-rid p₂ p₅ p₆ 

  ap-!-!-rid-rid : {x y : A} (p : x == y) {b : B} (q : f y == b) → ! (! (ap f (! p ∙ idp)) ∙ idp) ∙ ap f p ∙ q == q
  ap-!-!-rid-rid idp q = idp

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (f : A → B) (m : B → C) where

  !-!-!-∘-rid : {y z : A} (p₂ : y == z) {b : A} (p₃ : b == z) {e : C} (p₆ : m (f z) == e) {t : B} (p₅ : f y == t)
    → ! (ap m (! (ap f (p₂ ∙ ! p₃ ∙ idp)) ∙ p₅ ∙ idp)) ∙ ap (m ∘ f) p₃ ∙ p₆ == ! (ap m p₅) ∙ ap (m ∘ f) p₂ ∙ p₆
  !-!-!-∘-rid idp p₃ idp p₅ = !-!-ap-cmp-rid3 m f p₃ p₅ 

  ap-∘-!-!-rid-rid : {a₁ a₂ : A} (p₁ : a₁ == a₂) {b z : B} (p₃ : z == b) (p₂ : f a₂ == b) {c₁ c₂ : C} (p₅ : m (f a₁) == c₁) (p₆ : m (f a₂) == c₂)
    → ! (! (ap m (ap f p₁ ∙ p₂ ∙ ! p₃ ∙ idp)) ∙ p₅) ∙ ap m p₃ ∙ ! (ap m p₂) ∙ p₆ == ! p₅ ∙ ap (m ∘ f) p₁ ∙ p₆
  ap-∘-!-!-rid-rid idp p₃ p₂ p₅ p₆ = ap-!-!-!-!-rid m p₃ p₂ p₅ p₆ 

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄} (f : A → B) (h : C → A) (k : C → B) (m : B → D) where

  !-!-!-∘-∘-∘-rid : {x y : C} (p₁ : x == y) {z : A} (p₂ : h y == z) {b : A} (p₃ : b == z) {e : D} (p₆ : m (f z) == e) (p₅ : f (h y) == k y)
    →
    ! (ap m (! (ap f (ap h p₁ ∙ p₂ ∙ ! p₃ ∙ idp)) ∙ ap (f ∘ h) p₁ ∙ p₅ ∙ ! (ap k p₁))) ∙ ap (m ∘ f) p₃ ∙ p₆
      ==
    ap (m ∘ k) p₁ ∙ ! (ap m p₅) ∙ ap (m ∘ f) p₂ ∙ p₆
  !-!-!-∘-∘-∘-rid idp p₂ p₃ p₆ p₅ = !-!-!-∘-rid f m p₂ p₃ p₆ p₅ 

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄} (f : A → B) (g : D → A) (h : C → A) where

  long-red-!-∙ : {c₁ c₂ : C} (p₁ : c₁ == c₂) {a : A} (p₂ : h c₂ == a) {d₁ d₂ : D} (p₄ : d₁ == d₂) (p₃ : g d₂ == a)
    {b₁ b₂ : B} (p₅ : f (h c₁) == b₁) (p₆ : f (h c₂) == b₂)
    → ! (! (ap f (ap h p₁ ∙ p₂ ∙ ! p₃  ∙ ! (ap g p₄))) ∙ p₅) ∙ ap (f ∘ g) p₄ ∙ ap f p₃ ∙ ! (ap f p₂) ∙ p₆ == ! p₅ ∙ ap (f ∘ h) p₁ ∙ p₆
  long-red-!-∙ p₁ p₂ idp p₃ p₅ p₆ = ap-∘-!-!-rid-rid h f p₁ p₃ p₂ p₅ p₆

  long-red-ap-!-∙ : ∀ {ℓ₅} {H : Type ℓ₅} (k : C → B) (m : B → H) {c₁ c₂ : C} (p₁ : c₁ == c₂) {a : A} (p₂ : h c₂ == a) {d₁ d₂ : D}
    (p₄ : d₁ == d₂) (p₃ : g d₂ == a) {e : H} (p₅ : f (h c₂) == k c₂) (p₆ : m (f a) == e)
    → ! (ap m (! (ap f (ap h p₁ ∙ p₂ ∙ ! p₃  ∙ ! (ap g p₄))) ∙ ap (f ∘ h) p₁ ∙ p₅ ∙ ! (ap k p₁))) ∙ ap (m ∘ f ∘ g) p₄ ∙ ap (m ∘ f) p₃ ∙ p₆ ==
      ap (m ∘ k) p₁ ∙ ! (ap m p₅) ∙ ap (m ∘ f) p₂ ∙ p₆
  long-red-ap-!-∙ k m p₁ p₂ idp p₃ p₅ p₆ = !-!-!-∘-∘-∘-rid f h k m p₁ p₂ p₃ p₆ p₅ 

-- Start of map naturality proof

module ConstrMap {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open Id.Maps Γ A

  ForgF = DiagForg A Γ F

  ForgG = DiagForg A Γ G

  private
    module N = ColimitMap {F = ForgF} {G = ForgG} (Δ (λ i → fst (nat δ i)) (comSq δ))

  δ₀ : Colim ForgF → Colim ForgG
  δ₀ = N.ColMap

  δ₀-βr = N.MapComp

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
      ! (ap δ₀ (! (ap (cin j) (snd (F <#> g) a)) ∙ cglue g (fun (F # i) a))) ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a)
        =⟪ pre-cmp-!-!-∙ δ₀ (cin j) (snd (F <#> g) a) (cglue g (fun (F # i) a)) (ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a)) ⟫
      ! (ap δ₀ (cglue g (fun (F # i) a))) ∙ ap (cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a)
        =⟪ ap (λ p → ! p ∙ ap (cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a)) (δ₀-βr g (fun (F # i) a)) ⟫
      ! (! (ap (cin j) (comSq δ g (fun (F # i) a))) ∙ cglue g (fst (nat δ i) (fun (F # i) a))) ∙
      ap (cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙
      ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a) 
        =⟪ ap (λ p → ! p ∙ ap (cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a))
             (ap (λ p → ! (ap (cin j) p) ∙ cglue g (fst (nat δ i) (fun (F # i) a))) (comSq-coher δ g a)) ⟫
      ! (! (ap (cin j)
             (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙
         cglue g (fst (nat δ i) (fun (F # i) a))) ∙ ap (cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a)
        =⟪ ap (λ p →
             ! (! (ap (cin j)
                    (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙
                  cglue g (fst (nat δ i) (fun (F # i) a))) ∙
             ap (cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (cin j) (snd (nat δ j) a) ∙ p)
             (ψ₂-βr g a) ⟫
      ! (! (ap (cin j)
               (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙
             cglue g (fst (nat δ i) (fun (F # i) a))) ∙
      ap (cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (cin j) (snd (nat δ j) a) ∙
      ! (ap (cin j) (snd (G <#> g) a)) ∙ cglue g (fun (G # i) a)
        =⟪ long-red-!-∙ (cin j) (fst (nat δ j)) (fst (G <#> g)) (snd (nat δ i) a) (snd (G <#> g) a) (snd (F <#> g) a) (snd (nat δ j) a)
             (cglue g (fst (nat δ i) (fun (F # i) a))) (cglue g (fun (G # i) a))  ⟫
      ! (cglue g (fst (nat δ i) (fun (F # i) a))) ∙ ap (cin j ∘ fst (G <#> g)) (snd (nat δ i) a) ∙ cglue g (fun (G # i) a)
        =⟪ apCommSq (cin j ∘ fst (G <#> g)) (cin i) (cglue g) (snd (nat δ i) a) ⟫
      ap (cin i) (snd (nat δ i) a) ∎∎

    Θ : ! (ap (right {d = SpCos₂}) (! (ap (cin j) (comSq δ g (fun (F # i) a))) ∙ cglue g (fst (nat δ i) (fun (F # i) a)))) ∙
        ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))
          =-=
      ap (right ∘ cin i) (snd (nat δ i) a) ∙ ! (glue (cin i a))
    Θ =
      ! (ap (right {d = SpCos₂}) (! (ap (cin j) (comSq δ g (fun (F # i) a))) ∙ cglue g (fst (nat δ i) (fun (F # i) a)))) ∙
      ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))
        =⟪ ap (λ p → ! (ap (right {d = SpCos₂}) p) ∙
                ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
             (ap (λ p → ! (ap (cin j) p) ∙ cglue g (fst (nat δ i) (fun (F # i) a))) (comSq-coher δ g a)) ⟫
      ! (ap (right {d = SpCos₂})
          (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙
          cglue g (fst (nat δ i) (fun (F # i) a)))) ∙
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
          cglue g (fun (G # i) a) ∙ ! (ap (cin i) (snd (nat δ i) a)))) ∙
      ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
      ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))
        =⟪ long-red-ap-!-∙ (cin j) (fst (nat δ j)) (fst (G <#> g)) (cin i) right (snd (nat δ i) a) (snd (G <#> g) a) (snd (F <#> g) a)
             (snd (nat δ j) a) (cglue g (fun (G # i) a)) (! (glue (cin j a))) ⟫
      ap (right ∘ cin i) (snd (nat δ i) a) ∙ ! (ap right (cglue g (fun (G # i) a))) ∙ ap (right ∘ cin j) (snd (G <#> g) a) ∙ ! (glue (cin j a))
        =⟪ ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) (↯ (ε G g g a)) ⟫
      ap (right ∘ cin i) (snd (nat δ i) a) ∙ ! (glue (cin i a)) ∎∎

  K-diag : CosCocone A F (Cos P₂ left)
  fst (comp K-diag i) = right ∘ cin i ∘ (fst (nat δ i))
  snd (comp K-diag i) a = ap (right ∘ cin i) (snd (nat δ i) a) ∙ ! (glue (cin i a))
  fst (comTri K-diag {j} {i} g) x = ap right (! (ap (cin j) (comSq δ g x)) ∙ cglue g (fst (nat δ i) x))
  snd (comTri K-diag g) a = ↯ (Θ g a)

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

  𝕕 : < A > Cos P₁ left *→ Cos P₂ left
  𝕕 = PM.f , (λ a → idp)

  𝕕₀ = fst 𝕕
  
  𝕕-βr = PM.glue-β

  ForgMap =
    colimR (λ i → right {d = SpCos₂} ∘ cin i ∘ (fst (nat δ i))) (λ i j g x → ap right (! (ap (cin j) (comSq δ g x)) ∙ cglue g (fst (nat δ i) x)))

  FM-βr =
    cglue-βr (λ i₁ → right {d = SpCos₂} ∘ cin i₁ ∘ fst (nat δ i₁)) (λ i₁ j₁ g₁ x₁ → ap right (! (ap (cin j₁) (comSq δ g₁ x₁)) ∙ cglue g₁ (fst (nat δ i₁) x₁)))
