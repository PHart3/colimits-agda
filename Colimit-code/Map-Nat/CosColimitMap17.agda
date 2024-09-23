{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import lib.PathSeq
open import Coslice
open import Diagram
open import AuxPaths
open import Colim
open import CosColimitMap2
open import CosColimitMap7
open import CosColimitMap16

module CosColimitMap17 where


module _ {i j} {A : Type i} {B : Type j} {f g h : A →  B} (F : (x : A) → f x == g x) (G : (x : A) → g x == h x) where

  apd-∙-r-coher-! : {x y : A} (κ : x == y) → ! (apd-tr (λ z → F z ∙ G z) κ) ◃∎ =ₛ ! (ap (λ p → p ∙ G y) (apd-tr F κ)) ◃∙ ! (apd-∙-r {F = F} {G = G} κ) ◃∎
  apd-∙-r-coher-! idp = =ₛ-in idp

module _ {i j} {A : Type i} {B : Type j} (f : A → B) where

  ap-!-inv-l : {x y : A} (p : x == y) → ap f (! p) ∙ ap f p == idp
  ap-!-inv-l idp = idp

module _ {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open ConstrMap7 δ

  module MapRed (i j : Obj Γ) (g : Hom Γ i j) (a : A) where

    open MapCoher4 i j g a public

    abstract
      𝕪-red-abs : 𝕪 =ₛ ap-∘-!-!-rid (cin i) right (snd (nat δ i) a) (glue (cin i a)) ◃∎
      𝕪-red-abs = 𝕪-red δ i j g a

    map-MainRed1 = transport (λ z → ap 𝕂₀ (glue {d = SpCos₁} z) ∙ 𝕃 (ψ₁ z) == ap 𝕕₀ (glue {d = SpCos₁} z)) (cglue g a) (↯ (𝔻 j a)) ◃∎
                     =ₛ⟨ dtransp-pth-s (λ z → ap 𝕂₀ (glue {d = SpCos₁} z) ∙ 𝕃 (ψ₁ z)) (λ z →  ap 𝕕₀ (glue {d = SpCos₁} z)) (cglue g a) (↯ (𝔻 j a))  ⟩
                   (! (apd-tr (λ z → ap 𝕂₀ (glue z) ∙ 𝕃 (ψ₁ z)) (cglue g a)) ◃∙
                   ap (transport (λ z → 𝕂₀ (left (Span.f SpCos₁ z)) == (right ∘ δ₀) (ψ₁ z)) (cglue g a))
                     (ap (λ p → p ∙ idp) (FPrecc-βr 𝕂 (cin j a)) ∙
                     ap-∘-!-!-rid (cin j) right (snd (nat δ j) a) (glue (cin j a)) ∙
                     ! (𝕕-βr (cin j a))) ◃∙
                   apd-tr (λ z → ap 𝕕₀ (glue z)) (cglue g a) ◃∎)
                     =ₛ⟨ 0 & 1 & dtransp-nat-rev-s (λ z → ap 𝕂₀ (glue z) ∙ 𝕃 (ψ₁ z)) (λ z → σ (comp 𝕂) (comTri 𝕂) z ∙ 𝕃 (ψ₁ z))
                       (λ z → ap (λ p → p ∙ 𝕃 (ψ₁ z)) (FPrecc-βr 𝕂 z)) (cglue g a) ⟩
                   (ap (λ p → p ∙ 𝕃 (ψ₁ (cin i a))) (FPrecc-βr 𝕂 (cin i a)) ◃∙
                   ! (apd-tr (λ z → σ (comp 𝕂) (comTri 𝕂) z ∙ 𝕃 (ψ₁ z)) (cglue g a)) ◃∙
                   ! (ap (transport (λ z → 𝕂₀ (left ([id] z)) == (right ∘ δ₀) (ψ₁ z)) (cglue g a))
                     (ap (λ p → p ∙ 𝕃 (ψ₁ (cin j (idf A a)))) (FPrecc-βr 𝕂 (cin j (idf A a))))) ◃∙
                   ap (transport (λ z → 𝕂₀ (left (Span.f SpCos₁ z)) == (right ∘ δ₀) (ψ₁ z)) (cglue g a))
                     (ap (λ p → p ∙ idp) (FPrecc-βr 𝕂 (cin j a)) ∙
                     ap-∘-!-!-rid (cin j) right (snd (nat δ j) a) (glue (cin j a)) ∙ ! (𝕕-βr (cin j a))) ◃∙
                   apd-tr (λ z → ap 𝕕₀ (glue z)) (cglue g a) ◃∎)
                     =ₛ⟨ 1 & 1  & apd-∙-r-coher-! (σ (comp 𝕂) (comTri 𝕂)) (λ z → 𝕃 (ψ₁ z)) (cglue g a)  ⟩
                   (ap (λ p → p ∙ 𝕃 (ψ₁ (cin i a))) (FPrecc-βr 𝕂 (cin i a)) ◃∙
                   ! (ap (λ p → p ∙ 𝕃 (ψ₁ (cin i a))) (apd-tr (σ (comp 𝕂) (comTri 𝕂)) (cglue g a))) ◃∙
                   ! (apd-∙-r {F = σ (comp 𝕂) (comTri 𝕂)} {G = λ z → 𝕃 (ψ₁ z)} (cglue g a)) ◃∙
                   ! (ap (transport (λ z → 𝕂₀ (left ([id] z)) == (right ∘ δ₀) (ψ₁ z)) (cglue g a)) (ap (λ p → p ∙ 𝕃 (ψ₁ (cin j (idf A a))))
                     (FPrecc-βr 𝕂 (cin j (idf A a))))) ◃∙
                   ap (transport (λ z → 𝕂₀ (left (Span.f SpCos₁ z)) == (right ∘ δ₀) (ψ₁ z)) (cglue g a)) (ap (λ p → p ∙ idp) (FPrecc-βr 𝕂 (cin j a)) ∙
                     ap-∘-!-!-rid (cin j) right (snd (nat δ j) a) (glue (cin j a)) ∙  ! (𝕕-βr (cin j a))) ◃∙
                   apd-tr (λ z → ap 𝕕₀ (glue z)) (cglue g a) ◃∎) 
                     =ₛ⟨ 4 & 1 & ap-seq-∙ (transport (λ z → 𝕂₀ (left (Span.f SpCos₁ z)) == (right ∘ δ₀) (ψ₁ z)) (cglue g a)) (𝔻 j a) ⟩
                   (ap (λ p → p ∙ 𝕃 (ψ₁ (cin i a))) (FPrecc-βr 𝕂 (cin i a)) ◃∙
                   ! (ap (λ p → p ∙ 𝕃 (ψ₁ (cin i a))) (apd-tr (σ (comp 𝕂) (comTri 𝕂)) (cglue g a))) ◃∙
                   ! (apd-∙-r {F = σ (comp 𝕂) (comTri 𝕂)} {G = λ z → 𝕃 (ψ₁ z)} (cglue g a)) ◃∙
                   ! (ap (transport (λ z → 𝕂₀ (left ([id] z)) == (right ∘ δ₀) (ψ₁ z)) (cglue g a))
                     (ap (λ p → p ∙ 𝕃 (ψ₁ (cin j (idf A a)))) (FPrecc-βr 𝕂 (cin j a)))) ◃∙
                   ap (transport (λ z → 𝕂₀ (left (Span.f SpCos₁ z)) == (right ∘ δ₀) (ψ₁ z)) (cglue g a)) (ap (λ p → p ∙ idp) (FPrecc-βr 𝕂 (cin j a))) ◃∙
                   ap (transport (λ z → 𝕂₀ (left (Span.f SpCos₁ z)) == (right ∘ δ₀) (ψ₁ z)) (cglue g a))
                     (ap-∘-!-!-rid (cin j) right (snd (nat δ j) a) (glue (cin j a))) ◃∙
                   ap (transport (λ z → 𝕂₀ (left (Span.f SpCos₁ z)) == (right ∘ δ₀) (ψ₁ z)) (cglue g a)) (! (𝕕-βr (cin j a))) ◃∙
                   apd-tr (λ z → ap 𝕕₀ (glue z)) (cglue g a) ◃∎) 
                     =ₛ₁⟨ 3 & 2 & !-inv-l (ap (transport (λ z → 𝕂₀ (left (Span.f SpCos₁ z)) == (right ∘ δ₀) (ψ₁ z)) (cglue g a))
                       (ap (λ p → p ∙ idp) (FPrecc-βr 𝕂 (cin j a))))  ⟩
                   (ap (λ p → p ∙ 𝕃 (ψ₁ (cin i a))) (FPrecc-βr 𝕂 (cin i a)) ◃∙
                   ! (ap (λ p → p ∙ 𝕃 (ψ₁ (cin i a))) (apd-tr (σ (comp 𝕂) (comTri 𝕂)) (cglue g a))) ◃∙
                   ! (apd-∙-r {F = σ (comp 𝕂) (comTri 𝕂)} {G = λ z → 𝕃 (ψ₁ z)} (cglue g a)) ◃∙
                   idp ◃∙
                   ap (transport (λ z → 𝕂₀ (left (Span.f SpCos₁ z)) == (right ∘ δ₀) (ψ₁ z)) (cglue g a))
                     (ap-∘-!-!-rid (cin j) right (snd (nat δ j) a) (glue (cin j a))) ◃∙
                   ap (transport (λ z → 𝕂₀ (left (Span.f SpCos₁ z)) == (right ∘ δ₀) (ψ₁ z)) (cglue g a)) (! (𝕕-βr (cin j a))) ◃∙
                   apd-tr (λ z → ap 𝕕₀ (glue z)) (cglue g a) ◃∎)
                     =ₛ⟨ 6 & 1 & dtransp-nat-s (λ z → ap 𝕕₀ (glue z)) (λ z → glue z ∙ ap right (! (ℂ z))) 𝕕-βr (cglue g a)  ⟩
                   (ap (λ p → p ∙ 𝕃 (ψ₁ (cin i a))) (FPrecc-βr 𝕂 (cin i a)) ◃∙
                   ! (ap (λ p → p ∙ 𝕃 (ψ₁ (cin i a))) (apd-tr (σ (comp 𝕂) (comTri 𝕂)) (cglue g a))) ◃∙
                   ! (apd-∙-r {F = σ (comp 𝕂) (comTri 𝕂)} {G = λ z → 𝕃 (ψ₁ z)} (cglue g a)) ◃∙
                   idp ◃∙
                   ap (transport (λ z → 𝕂₀ (left (Span.f SpCos₁ z)) == (right ∘ δ₀) (ψ₁ z)) (cglue g a))
                     (ap-∘-!-!-rid (cin j) right (snd (nat δ j) a) (glue (cin j a))) ◃∙
                   ap (transport (λ z → 𝕂₀ (left (Span.f SpCos₁ z)) == (right ∘ δ₀) (ψ₁ z)) (cglue g a)) (! (𝕕-βr (cin j a))) ◃∙
                   ap (transport (λ z → 𝕕₀ (left ([id] z)) == 𝕕₀ (right (Maps.ψ F z)))  (cglue g a)) (𝕕-βr (cin j (idf A a))) ◃∙
                   apd-tr (λ z → glue z ∙ ap right (! (ℂ z))) (cglue g a) ◃∙
                   ! (𝕕-βr (cin i a)) ◃∎) ∎ₛ

    map-MainRed2 = (ap (λ p → p ∙ 𝕃 (ψ₁ (cin i a))) (FPrecc-βr 𝕂 (cin i a)) ◃∙
                   ! (ap (λ p → p ∙ 𝕃 (ψ₁ (cin i a))) (apd-tr (σ (comp 𝕂) (comTri 𝕂)) (cglue g a))) ◃∙
                   ! (apd-∙-r {F = σ (comp 𝕂) (comTri 𝕂)} {G = λ z → 𝕃 (ψ₁ z)} (cglue g a)) ◃∙
                   idp ◃∙
                   ap (transport (λ z → 𝕂₀ (left (Span.f SpCos₁ z)) == (right ∘ δ₀) (ψ₁ z)) (cglue g a))
                     (ap-∘-!-!-rid (cin j) right (snd (nat δ j) a) (glue (cin j a))) ◃∙
                   ap (transport (λ z → 𝕂₀ (left (Span.f SpCos₁ z)) == (right ∘ δ₀) (ψ₁ z)) (cglue g a)) (! (𝕕-βr (cin j a))) ◃∙
                   ap (transport (λ z → 𝕕₀ (left ([id] z)) == 𝕕₀ (right (Maps.ψ F z)))  (cglue g a)) (𝕕-βr (cin j (idf A a))) ◃∙
                   apd-tr (λ z → glue z ∙ ap right (! (ℂ z))) (cglue g a) ◃∙
                   ! (𝕕-βr (cin i a)) ◃∎)
                     =ₛ⟨ 7 & 1 & apd-ap-∙-l-coher right {F = glue} {G = ℂ} (cglue g a) ⟩
                   (ap (λ p → p ∙ 𝕃 (ψ₁ (cin i a))) (FPrecc-βr 𝕂 (cin i a)) ◃∙
                   ! (ap (λ p → p ∙ 𝕃 (ψ₁ (cin i a))) (apd-tr (σ (comp 𝕂) (comTri 𝕂)) (cglue g a))) ◃∙
                   ! (apd-∙-r {F = σ (comp 𝕂) (comTri 𝕂)} {G = λ z → 𝕃 (ψ₁ z)} (cglue g a)) ◃∙
                   idp ◃∙
                   ap (transport (λ z → 𝕂₀ (left (Span.f SpCos₁ z)) == (right ∘ δ₀) (ψ₁ z)) (cglue g a))
                     (ap-∘-!-!-rid (cin j) right (snd (nat δ j) a) (glue (cin j a))) ◃∙
                   ap (transport (λ z → 𝕂₀ (left (Span.f SpCos₁ z)) == (right ∘ δ₀) (ψ₁ z)) (cglue g a)) (! (𝕕-βr (cin j a))) ◃∙
                   ap (transport (λ z → 𝕕₀ (left ([id] z)) == 𝕕₀ (right (Maps.ψ F z))) (cglue g a)) (𝕕-βr (cin j a)) ◃∙
                   apd-ap-∙-l right {F = glue} {G = ℂ} (cglue g a) ◃∙
                   ap (λ p → glue (cin i a) ∙ ap right (! p)) (apd-tr ℂ (cglue g a)) ◃∙
                   ! (𝕕-βr (cin i a)) ◃∎) 
                     =ₛ₁⟨ 5 & 2 & ap-!-inv-l (transport (λ z → 𝕂₀ (left (Span.f SpCos₁ z)) == (right ∘ δ₀) (ψ₁ z)) (cglue g a)) (𝕕-βr (cin j a)) ⟩
                   (ap (λ p → p ∙ 𝕃 (ψ₁ (cin i a))) (FPrecc-βr 𝕂 (cin i a)) ◃∙
                   ! (ap (λ p → p ∙ 𝕃 (ψ₁ (cin i a))) (apd-tr (σ (comp 𝕂) (comTri 𝕂)) (cglue g a))) ◃∙
                   ! (apd-∙-r {F = σ (comp 𝕂) (comTri 𝕂)} {G = λ z → 𝕃 (ψ₁ z)} (cglue g a)) ◃∙
                   idp ◃∙
                   ap (transport (λ z → 𝕂₀ (left (Span.f SpCos₁ z)) == (right ∘ δ₀) (ψ₁ z)) (cglue g a))
                     (ap-∘-!-!-rid (cin j) (right {d = SpCos₂}) (snd (nat δ j) a) (glue (cin j a))) ◃∙
                   idp ◃∙
                   apd-ap-∙-l right {F = glue} {G = ℂ} (cglue g a) ◃∙
                   ap (λ p → glue (cin i a) ∙ ap right (! p)) (apd-tr ℂ (cglue g a)) ◃∙
                   ! (𝕕-βr (cin i a)) ◃∎) ∎ₛ


    map-MainRed3 = (ap (λ p → p ∙ 𝕃 (ψ₁ (cin i a))) (FPrecc-βr 𝕂 (cin i a)) ◃∙
                   ! (ap (λ p → p ∙ 𝕃 (ψ₁ (cin i a))) (apd-tr (σ (comp 𝕂) (comTri 𝕂)) (cglue g a))) ◃∙
                   ! (apd-∙-r {F = σ (comp 𝕂) (comTri 𝕂)} {G = λ z → 𝕃 (ψ₁ z)} (cglue g a)) ◃∙
                   idp ◃∙
                   ap (transport (λ z → 𝕂₀ (left (Span.f SpCos₁ z)) == (right ∘ δ₀) (ψ₁ z)) (cglue g a))
                     (ap-∘-!-!-rid (cin j) (right {d = SpCos₂}) (snd (nat δ j) a) (glue (cin j a))) ◃∙
                   idp ◃∙
                   apd-ap-∙-l right {F = glue} {G = ℂ} (cglue g a) ◃∙
                   ap (λ p → glue (cin i a) ∙ ap right (! p)) (apd-tr ℂ (cglue g a)) ◃∙
                   ! (𝕕-βr (cin i a)) ◃∎) 
                     =ₛ⟨ =ₛ-in idp  ⟩
                   (ap (λ p → p ∙ 𝕃 (ψ₁ (cin i a))) (FPrecc-βr 𝕂 (cin i a)) ◃∙
                   ! (ap (λ p → p ∙ 𝕃 (ψ₁ (cin i a))) (apd-tr (σ (comp 𝕂) (comTri 𝕂)) (cglue g a))) ◃∙
                   ! (apd-∙-r {F = σ (comp 𝕂) (comTri 𝕂)} {G = λ z → 𝕃 (ψ₁ z)} (cglue g a)) ◃∙
                   ap (transport (λ z → 𝕂₀ (left (Span.f SpCos₁ z)) == (right ∘ δ₀) (ψ₁ z)) (cglue g a))
                     (ap-∘-!-!-rid (cin j) right (snd (nat δ j) a) (glue (cin j a))) ◃∙
                   apd-ap-∙-l right {F = glue} {G = ℂ} (cglue g a) ◃∙
                   ap (λ p → glue (cin i a) ∙ ap right (! p)) (apd-tr ℂ (cglue g a)) ◃∙
                   ! (𝕕-βr (cin i a)) ◃∎) ∎ₛ
