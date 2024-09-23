{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import lib.PathSeq
open import Coslice
open import Diagram
open import FTID-Cos
open import Colim
open import CosColimitMap2

module CosColimitMap21 where

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (f : A → B) (h : A → C) (g : C → B) (H : f ∼ g ∘ h) where

  CommSq-swap-∘ : {x y : A} (p : x == y) → ap f p == H x ∙ ap g (ap h p) ∙ ! (H y)
  CommSq-swap-∘ {x} idp = ! (!-inv-r (H x))

module _ {ℓ} {A : Type ℓ} {x y z : A} where

  !-∙-!-rid : (p : x == y) (q : z == y) → ! (p ∙ ! q) == q ∙ ! p ∙ idp
  !-∙-!-rid idp idp = idp

module ConstrMap21 {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open ConstrMap2 δ public

  module _ {i j : Obj Γ} (g : Hom Γ i j) (x : ty (F # i)) where

    Θ-left : ap (right {d = SpCos₂}) (! (ap (cin j) (comSq δ g x)) ∙ cglue g (fst (nat δ i) x)) =-=
             ap (right {d = SpCos₂}) (! (ap (cin j) (comSq δ g x)) ∙ cglue g (fst (nat δ i) x))
    Θ-left = ap (right {d = SpCos₂}) (! (ap (cin j) (comSq δ g x)) ∙ cglue g (fst (nat δ i) x))
               =⟪ ! (FM-βr g x) ⟫
             ap ForgMap (cglue g x)
               =⟪ CommSq-swap-∘ ForgMap δ₀ right 𝕃 (cglue g x)  ⟫
             ap right (ap δ₀ (cglue g x)) ∙ idp
               =⟪ ∙-unit-r (ap right (ap δ₀ (cglue g x))) ⟫
             ap right (ap δ₀ (cglue g x))
               =⟪ ap (ap right) (δ₀-βr g x)  ⟫
             ap (right {d = SpCos₂}) (! (ap (cin j) (comSq δ g x)) ∙ cglue g (fst (nat δ i) x)) ∎∎

  module _ (i j : Obj Γ) (g₁ : Hom Γ i j) (a : A) where

    𝕂-K-eq-helper3 : {t : ty (F # j)} (σ : t == fun (F # j) a) (𝐌 : fst (G <#> g₁) (fst (nat δ i) (fun (F # i) a)) == fst (nat δ j) t)
      → ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) σ ∙
        ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
        (∙-unit-r (ap right (! (ap (cin j) 𝐌) ∙ cglue g₁ (fst (nat δ i) (fun (F # i) a)))))) ∙
        ap (λ p → ! (p ∙ ap right (! (ap (cin j) 𝐌) ∙ cglue g₁ (fst (nat δ i) (fun (F # i) a))) ∙ idp) ∙ ap (fst (comp K j)) σ ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ x₁ → idp) σ (snd (comp 𝕂 j) a)) ∙
        long-path-red σ (snd (comp K j) a) (snd (comp 𝕂 j) a)
        (ap right (! (ap (cin j) 𝐌) ∙ cglue g₁ (fst (nat δ i) (fun (F # i) a)))) idp ∙
        idp
      == idp
    𝕂-K-eq-helper3 idp 𝐌 = lemma (ap right (! (ap (cin j) 𝐌) ∙ cglue g₁ (fst (nat δ i) (fun (F # i) a))))
      where
        lemma : {z : P₂} (𝐦 : right (cin j (fst (nat δ j) (fun (F # j) a))) == z)
          → ! (ap (λ p → ! p ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
          (∙-unit-r 𝐦)) ∙
          ap (λ p → ! (p ∙ 𝐦 ∙ idp) ∙
            snd (comp K j) a) (hmtpy-nat-rev {f = fst (comp 𝕂 j)} (λ x₁ → idp) idp (snd (comp 𝕂 j) a)) ∙
          long-path-red {f = fst (comp K j)} {g = fst (comp 𝕂 j)} idp (ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (snd (comp 𝕂 j) a) 𝐦 idp ∙
          idp
          == idp
        lemma idp = lemma2 (ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
          where
            lemma2 : {v : P₂} (τ : right (cin j (fst (nat δ j) (fun (F # j) a))) == v)
              → ap (λ p → ! (p ∙ idp) ∙ τ) (hmtpy-nat-rev {f = fst (comp 𝕂 j)} (λ x₁ → idp) idp τ) ∙
              db-neg-rid-db τ τ ∙
              idp
              == idp
            lemma2 idp = idp

-- σ = (snd (F <#> g₁) a)
-- 𝐌  = comSq δ g₁ (fun (F # i) a))

    𝕂-K-eq-helper2 : {e : ForgMap (cin j (fst (F <#> g₁) (fun (F # i) a))) == ForgMap (cin i (fun (F # i) a))} (𝐌 : e == fst (comTri 𝕂 g₁) (fun (F # i) a))
      →  ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (! 𝐌)) ◃∙
         ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
           (∙-unit-r (ap right (! (ap (cin j) (comSq δ g₁ (fun (F # i) a))) ∙
           cglue g₁ (fst (nat δ i) (fun (F # i) a)))))) ◃∙
         ap (λ p → ! (p ∙ fst (comTri 𝕂 g₁) (fun (F # i) a) ∙ idp) ∙
           ap (fst (comp K j)) (snd (F <#> g₁) a) ∙ snd (comp K j) a)
           (hmtpy-nat-rev (λ x₁ → idp) (snd (F <#> g₁) a) (snd (comp 𝕂 j) a)) ◃∙
         idp ◃∙
         long-path-red (snd (F <#> g₁) a) (snd (comp K j) a) (snd (comp 𝕂 j) a) (fst (comTri 𝕂 g₁) (fun (F # i) a)) idp ◃∙
         ap (λ q → q) (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (! 𝐌)) ◃∎
         =ₛ (idp ◃∎)
    𝕂-K-eq-helper2 idp = =ₛ-in (𝕂-K-eq-helper3 (snd (F <#> g₁) a) (comSq δ g₁ (fun (F # i) a)))

-- 𝐌 = (FM-βr g₁ (fun (F # i) a))

    𝕂-K-eq-helper-aux : {v : Colim ForgF} (γ : cin j (fst (F <#> g₁) (fun (F # i) a)) == v)
      → 
      ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
        (CommSq-swap-∘ ForgMap δ₀ right 𝕃 γ)) ◃∙
      idp ◃∙
      ap (λ q → q) (ap (λ p → p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
        (CommSq-swap-∘-! ForgMap δ₀ right 𝕃 γ)) ◃∎
      =ₛ (ap (λ p → p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
           (!-∙-!-rid (ap right (ap δ₀ γ)) (𝕃 v)) ◃∎) 
    𝕂-K-eq-helper-aux idp = =ₛ-in idp  

-- γ = cglue g₁ (fun (F # i) a)

    𝕂-K-eq-helper-aux2 : {v : Colim ForgF} (γ : cin j (fst (F <#> g₁) (fun (F # i) a)) == v)
      → ! (ap (λ p → ! p ∙ ap ((right {d = SpCos₂}) ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
      ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (∙-unit-r (ap right (ap δ₀ γ)))) ∙
      ap (λ p →  p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
        (!-∙-!-rid (ap right (ap δ₀ γ)) idp) ∙
      ap (λ q → q) (ap (λ p → p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
        ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
        (∙-unit-r (! (ap right (ap δ₀ γ))))) ∙
      idp
      == idp
    𝕂-K-eq-helper-aux2 idp = idp

-- γ = cglue g₁ (fun (F # i) a)

    𝕂-K-eq-helper : {t : δ₀ (cin j (fst (F <#> g₁) (fun (F # i) a))) == δ₀ (cin i (fun (F # i) a))} (𝐌 : ap δ₀ (cglue g₁ (fun (F # i) a)) == t) 
      →  ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (ap (ap right) 𝐌)) ◃∙
         ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
           (∙-unit-r (ap right (ap δ₀ (cglue g₁ (fun (F # i) a)))))) ◃∙
         ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
           (CommSq-swap-∘ ForgMap δ₀ right 𝕃 (cglue g₁ (fun (F # i) a)))) ◃∙
         ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (! (FM-βr g₁ (fun (F # i) a)))) ◃∙
         ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
           (∙-unit-r (ap right (! (ap (cin j) (comSq δ g₁ (fun (F # i) a))) ∙
           cglue g₁ (fst (nat δ i) (fun (F # i) a)))))) ◃∙
         ap (λ p → ! (p ∙ fst (comTri 𝕂 g₁) (fun (F # i) a) ∙ idp) ∙
           ap (fst (comp K j)) (snd (F <#> g₁) a) ∙ snd (comp K j) a)
           (hmtpy-nat-rev (λ x₁ → idp) (snd (F <#> g₁) a) (snd (comp 𝕂 j) a)) ◃∙
         idp ◃∙
         long-path-red (snd (F <#> g₁) a) (snd (comp K j) a) (snd (comp 𝕂 j) a) (fst (comTri 𝕂 g₁) (fun (F # i) a)) idp ◃∙
         ap (λ q → q) (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (! (FM-βr g₁ (fun (F # i) a)))) ◃∙
         ap (λ q → q) (ap (λ p →  p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
           (CommSq-swap-∘-! ForgMap δ₀ right 𝕃 (cglue g₁ (fun (F # i) a)))) ◃∙
         ap (λ q → q) (ap (λ p → p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
           (∙-unit-r (! (ap right (ap δ₀ (cglue g₁ (fun (F # i) a))))))) ◃∙
         ap (λ q → q) (ap (λ p → ! (ap right p) ∙
           ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) 𝐌) ◃∎
         =ₛ idp ◃∎
    𝕂-K-eq-helper idp = 
         idp ◃∙
         ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
           (∙-unit-r (ap right (ap δ₀ (cglue g₁ (fun (F # i) a)))))) ◃∙
         ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
           (CommSq-swap-∘ ForgMap δ₀ right 𝕃 (cglue g₁ (fun (F # i) a)))) ◃∙
         ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (! (FM-βr g₁ (fun (F # i) a)))) ◃∙
         ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
           (∙-unit-r (ap right (! (ap (cin j) (comSq δ g₁ (fun (F # i) a))) ∙
           cglue g₁ (fst (nat δ i) (fun (F # i) a)))))) ◃∙
         ap (λ p → ! (p ∙ fst (comTri 𝕂 g₁) (fun (F # i) a) ∙ idp) ∙
           ap (fst (comp K j)) (snd (F <#> g₁) a) ∙ snd (comp K j) a)
           (hmtpy-nat-rev (λ x₁ → idp) (snd (F <#> g₁) a) (snd (comp 𝕂 j) a)) ◃∙
         idp ◃∙
         long-path-red (snd (F <#> g₁) a) (snd (comp K j) a) (snd (comp 𝕂 j) a) (fst (comTri 𝕂 g₁) (fun (F # i) a)) idp ◃∙
         ap (λ q → q) (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (! (FM-βr g₁ (fun (F # i) a)))) ◃∙
         ap (λ q → q) (ap (λ p →  p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
           (CommSq-swap-∘-! ForgMap δ₀ right 𝕃 (cglue g₁ (fun (F # i) a)))) ◃∙
         ap (λ q → q) (ap (λ p → p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
           (∙-unit-r (! (ap right (ap δ₀ (cglue g₁ (fun (F # i) a))))))) ◃∙
         idp ◃∎
           =ₛ⟨ 3 & 6 & 𝕂-K-eq-helper2 (FM-βr g₁ (fun (F # i) a))  ⟩
         idp ◃∙
         ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
           (∙-unit-r (ap right (ap δ₀ (cglue g₁ (fun (F # i) a)))))) ◃∙
         ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
           (CommSq-swap-∘ ForgMap δ₀ right 𝕃 (cglue g₁ (fun (F # i) a)))) ◃∙
         idp ◃∙
         ap (λ q → q) (ap (λ p →  p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
           (CommSq-swap-∘-! ForgMap δ₀ right 𝕃 (cglue g₁ (fun (F # i) a)))) ◃∙
         ap (λ q → q) (ap (λ p → p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
           (∙-unit-r (! (ap right (ap δ₀ (cglue g₁ (fun (F # i) a))))))) ◃∙
         idp ◃∎
           =ₛ⟨ 2 & 3 & 𝕂-K-eq-helper-aux (cglue g₁ (fun (F # i) a)) ⟩
         idp ◃∙
         ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
           (∙-unit-r (ap right (ap δ₀ (cglue g₁ (fun (F # i) a)))))) ◃∙
         ap (λ p → p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
           (!-∙-!-rid (ap right (ap δ₀ (cglue g₁ (fun (F # i) a)))) idp) ◃∙
         ap (λ q → q) (ap (λ p → p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
           (∙-unit-r (! (ap right (ap δ₀ (cglue g₁ (fun (F # i) a))))))) ◃∙
         idp ◃∎
           =ₛ₁⟨ 𝕂-K-eq-helper-aux2 (cglue g₁ (fun (F # i) a)) ⟩
         idp ◃∎ ∎ₛ 
