{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import lib.PathSeq
open import Coslice
open import Diagram
open import FTID
open import AuxPaths
open import AuxPaths-v2
open import Colim
open import Cocone
open import CosColimitMap00
open import CosColimitMap01
open import CosColimitMap02

module CosColimitMap03 where

module _ {ℓ} {A : Type ℓ} where

  four-!-!-!-rid-rid : {x y z w u : A} (p₁ : x == y) (p₄ : y == z) (p₃ : z == w) (p₂ : u == w)
    → (p₁ ∙ ! (p₂ ∙ ! p₃ ∙ ! p₄ ∙ idp)) ∙ idp == (p₁ ∙ p₄ ∙ p₃) ∙ ! p₂
  four-!-!-!-rid-rid idp idp idp idp = idp

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (f : B → C) (g : A → B) where

  ap-∘-∙ : {x y : A} (p : x == y) {z : B} (q : g y == z) → ap (f ∘ g) p ∙ ap f q == ap f (ap g p ∙ q)
  ap-∘-∙ idp q = idp

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f g : A → B} (H : f ∼ g) where

  ∼-nat : {x y : A} (p : x == y) → H x ∙ ap g p ∙ ! (H y) == ap f p
  ∼-nat {x = x} idp = !-inv-r (H x)

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} (f : A → B) where

  ap-!-!-!-!-rid-rid : {x y : A} (p : x == y) → idp == ap f (! (! (! (! p ∙ idp) ∙ idp) ∙ p))
  ap-!-!-!-!-rid-rid idp = idp

module ConstrMap4 {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open Id Γ A public

  open ConstrMap2 δ

  open ConstrMap3 δ

  module MapCoher2 (i j : Obj Γ) (g : Hom Γ i j) (a : A) where

    ψ₂-free-helper-pre3 : {x y z : Colim ForgG} (c₁ : x == y) (c₂ : z == y)
      → idp == ap (right {d = SpCos₂}) (! (! (! ((c₁ ∙ ! c₂) ∙ idp) ∙ c₁) ∙ c₂))
    ψ₂-free-helper-pre3 idp c₂ = ap-!-!-!-!-rid-rid right c₂

    ψ₂-free-helper3 : (f : ty (G # i) → Colim ForgG) {y z : ty (G # i)} {u w : ty (G # j)} {x : Colim ForgG}
      (τ₁ : y  == z) (c₁ : x == f y) (τ₂ : w == u) (c₂ : cin j w == f z)
      → ! (ap (right {d = SpCos₂} ∘ f) τ₁) == ap right (! (! (! ((c₁ ∙ ap f τ₁ ∙ ! c₂) ∙ ap (cin j) (τ₂ ∙ idp)) ∙ c₁) ∙ ! (ap (cin j) τ₂) ∙ c₂))
    ψ₂-free-helper3 f idp c₁ idp c₂ = ψ₂-free-helper-pre3 c₁ c₂ 

    ψ₂-free-helper2 : {y z : ty (G # i)} {u w v : ty (G # j)} {x : Colim ForgG}
      (τ₁ : y  == z) (c₁ : x == cin i y) (τ₂ : w == u) (σ₁ : v == u) (c₂ : cin j w == cin i z)
      → ! (ap (right {d = SpCos₂} ∘ cin i) τ₁) ==
      ap right (! (! (! ((c₁ ∙ ap (cin i) τ₁ ∙ ! c₂) ∙ ap (cin j) (τ₂ ∙ ! σ₁ ∙ idp)) ∙ c₁)
      ∙ ap (cin j) σ₁ ∙ ! (ap (cin j) τ₂) ∙ c₂))
    ψ₂-free-helper2 τ₁ c₁ τ₂ idp c₂ = ψ₂-free-helper3 (cin i) τ₁ c₁ τ₂ c₂

    ψ₂-free-helper : {y z : ty (G # i)} {u w : ty (G # j)} {x : Colim ForgG} {k v : ty (F # j)}
      (τ₁ : y  == z) (c₁ : x == cin i y) (τ₂ : w == u) (σ₃ : k == v) (σ₁ : fst (nat δ j) v == u) (c₂ : cin j w == cin i z) 
      →  ! (ap (right {d = SpCos₂} ∘ cin i) τ₁) ==
      ap right (! (! (! ((c₁ ∙ ap (cin i) τ₁ ∙ ! c₂) ∙ ap (cin j) (τ₂ ∙ ! σ₁ ∙ ! (ap (fst (nat δ j)) σ₃))) ∙ c₁) ∙
      ap (cin j ∘ fst (nat δ j)) σ₃ ∙ ap (cin j) σ₁ ∙ ! (ap (cin j) τ₂) ∙ c₂))
    ψ₂-free-helper τ₁ c₁ τ₂ idp σ₁ c₂ = ψ₂-free-helper2 τ₁ c₁ τ₂ σ₁ c₂

-- τ₁ = snd (nat δ i) a
-- τ₂ = snd (G <#> g) a
-- c₁ = cglue g (fst (nat δ i) (fun (F # i) a))
-- c₂ = cglue g (fun (G # i) a)

    open MapCoher i j g a

    δ₀-free-helper2 : {x y z : Colim ForgG} (D : x == y) (τ : x == z) → ! (! (ap (right {d = SpCos₂}) D) ∙ idp) ∙ idp == ap right τ ∙ ap right (! (! D ∙ τ))
    δ₀-free-helper2 idp idp = idp

    abstract

      δ₀-free-helper-coher : {w z : Colim ForgG} (D : cin j (fun (G # j) a) == w) (τ : cin j (fun (G # j) a) == z)
        → δ₀-free-helper-pre2 idp D τ idp == δ₀-free-helper2 D τ
      δ₀-free-helper-coher idp idp = idp

    ψ₂-free : (q : cin j a == cin i a) {e : ty (F # j)} (s₃ : e == fun (F # j) a) (μ : ψ₂ (cin j a) == ψ₂ (cin i a)) 
      (τ₁ : transport (λ z → left ([id] z) == right {d = SpCos₂} (ψ₂ z)) q (glue (cin j a)) == ! (ap left (ap [id] q)) ∙ glue (cin j a) ∙ ap right μ)
      (τ₂ : transport (λ z → left ([id] z) == right {d = SpCos₂} (ψ₂ z)) q (glue (cin j a)) == glue (cin i a))
      → (! (ap left (ap [id] q)) ∙ ! (ap (right {d = SpCos₂} ∘ cin i) (snd (nat δ i) a) ∙ ! (ap right μ) ∙ ! (glue (cin j a)) ∙ idp)) ∙ idp
      =-= glue (cin i a) ∙ ap right (! (! (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙
          ! (ap (fst (nat δ j)) s₃))) ∙ cglue g (fst (nat δ i) (fun (F # i) a))) ∙ ap (cin j ∘ fst (nat δ j))
          s₃ ∙ ap (cin j) (snd (nat δ j) a) ∙ ! (ap (cin j) (snd (G <#> g) a)) ∙ cglue g (fun (G # i) a)))
    ψ₂-free q s₃ μ τ₁ τ₂ =
              (! (ap left (ap [id] q)) ∙ ! (ap (right {d = SpCos₂} ∘ cin i) (snd (nat δ i) a) ∙ ! (ap right μ) ∙ ! (glue (cin j a)) ∙ idp)) ∙ idp
                =⟪ four-!-!-!-rid-rid (! (ap left (ap [id] q))) (glue (cin j a)) (ap right μ) (ap (right {d = SpCos₂} ∘ cin i) (snd (nat δ i) a))  ⟫ 
              (! (ap left (ap [id] q)) ∙ glue (cin j a) ∙ ap right μ) ∙ ! (ap (right {d = SpCos₂} ∘ cin i) (snd (nat δ i) a))
                =⟪ ! (ap (λ p → p ∙ ! (ap (right {d = SpCos₂} ∘ cin i) (snd (nat δ i) a))) τ₁) ⟫
              transport (λ z → left ([id] z) == right {d = SpCos₂} (ψ₂ z)) q (glue (cin j a)) ∙ ! (ap (right {d = SpCos₂} ∘ cin i) (snd (nat δ i) a))
                =⟪ ap (λ p → p ∙ ! (ap (right {d = SpCos₂} ∘ cin i) (snd (nat δ i) a))) τ₂ ⟫
              glue (cin i a) ∙ ! (ap (right {d = SpCos₂} ∘ cin i) (snd (nat δ i) a))
                =⟪ ap (λ p → glue (cin i a) ∙ p) (ψ₂-free-helper (snd (nat δ i) a) (cglue g (fst (nat δ i) (fun (F # i) a))) (snd (G <#> g) a) s₃
                  (snd (nat δ j) a) (cglue g (fun (G # i) a))) ⟫  
              glue (cin i a) ∙ ap right (! (! (! ((cglue g (fst (nat δ i) (fun (F # i) a)) ∙ ap (cin i) (snd (nat δ i) a) ∙ ! (cglue g (fun (G # i) a))) ∙
                ap (cin j) (snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙
                ! (ap (fst (nat δ j)) s₃))) ∙ cglue g (fst (nat δ i) (fun (F # i) a))) ∙ ap (cin j ∘ fst (nat δ j))
                s₃ ∙ ap (cin j) (snd (nat δ j) a) ∙ ! (ap (cin j) (snd (G <#> g) a)) ∙ cglue g (fun (G # i) a)))
                =⟪ ap (λ p → glue (cin i a) ∙ ap right (! (! (! (p ∙ ap (cin j) (snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙
                  ! (ap (fst (nat δ j)) s₃))) ∙ cglue g (fst (nat δ i) (fun (F # i) a))) ∙ ap (cin j ∘ fst (nat δ j))
                  s₃ ∙ ap (cin j) (snd (nat δ j) a) ∙ ! (ap (cin j) (snd (G <#> g) a)) ∙ cglue g (fun (G # i) a)))) (∼-nat (cglue g) (snd (nat δ i) a)) ⟫
              glue (cin i a) ∙ ap right (! (! (! (ap (cin j ∘ fst (G <#> g)) (snd (nat δ i) a) ∙ ap (cin j) (snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙
                ! (ap (fst (nat δ j)) s₃))) ∙ cglue g (fst (nat δ i) (fun (F # i) a))) ∙ ap (cin j ∘ fst (nat δ j))
                s₃ ∙ ap (cin j) (snd (nat δ j) a) ∙ ! (ap (cin j) (snd (G <#> g) a)) ∙ cglue g (fun (G # i) a)))
                =⟪ ap (λ p → glue (cin i a) ∙ ap right (! (! (! p ∙ cglue g (fst (nat δ i) (fun (F # i) a))) ∙ ap (cin j ∘ fst (nat δ j))
                  s₃ ∙ ap (cin j) (snd (nat δ j) a) ∙ ! (ap (cin j) (snd (G <#> g) a)) ∙ cglue g (fun (G # i) a))))
                  (ap-∘-∙ (cin j) (fst (G <#> g)) (snd (nat δ i) a) (snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) s₃))) ⟫
              glue (cin i a) ∙ ap right (! (! (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙
                ! (ap (fst (nat δ j)) s₃))) ∙ cglue g (fst (nat δ i) (fun (F # i) a))) ∙ ap (cin j ∘ fst (nat δ j))
                s₃ ∙ ap (cin j) (snd (nat δ j) a) ∙ ! (ap (cin j) (snd (G <#> g) a)) ∙ cglue g (fun (G # i) a))) ∎∎

-- τ₁ = transp-pth-cmp (cglue g a) (glue (cin j a))
-- τ₂ = apd-tr glue (cglue g a)
-- μ = ap ψ₂ (cglue g a)

    ψ₂-red-helper3 : {z : P₂} (κ : z == right (ψ₂ (cin j a))) {t : ty (G # i)} (e : fst (G <#> g) t == fun (G # j) a)
      → ! (ap (λ p → p ∙ idp) (ap (λ q₁ → q₁) (ap ! (ap (λ q₁₁ → q₁₁) (E₂-v2 {f = right {d = SpCos₂}} idp (! κ)))))) ◃∙
      ! (ap (λ p → p ∙ idp) (ap (λ q₁ → q₁) (ap ! (ap (λ q₁₁ → q₁₁) (E₁-v2 {f = right {d = SpCos₂}} {g = cin j} e))))) ◃∙
      ! (ap (λ p → p ∙ idp) (ap (λ q₁ → q₁) (ap ! (!-!-!-∘-rid (cin j) right e idp (! κ) idp)))) ◃∙
      δ₀-free-helper-pre2 idp (! (ap (cin j) (e ∙ idp)) ∙ idp) (! (ap (cin j) e) ∙ idp) κ ◃∙
      idp ◃∎
        =ₛ
      four-!-!-!-rid-rid idp κ (ap right (! (ap (cin j) e) ∙ idp)) idp ◃∙
      ap (_∙_ (κ ∙ ap right (! (ap (cin j) e) ∙ idp))) (ψ₂-free-helper3 (λ z → cin j (fst (G <#> g) z)) idp idp e idp)
      ◃∙ idp ◃∎
    ψ₂-red-helper3 idp {t = t} e =
      idp ◃∙
      ! (ap (λ p → p ∙ idp) (ap (λ q₁ → q₁) (ap ! (ap (λ q₁₁ → q₁₁) (E₁-v2 e))))) ◃∙
      ! (ap (λ p → p ∙ idp) (ap (λ q₁ → q₁) (ap ! (!-!-!-∘-rid (cin j) right e idp (! idp) idp)))) ◃∙
      δ₀-free-helper-pre2 idp (! (ap (cin j) (e ∙ idp)) ∙ idp) (! (ap (cin j) e) ∙ idp) idp ◃∙
      idp ◃∎
        =ₛ₁⟨ 3 & 1 & δ₀-free-helper-coher (! (ap (cin j) (e ∙ idp)) ∙ idp) (! (ap (cin j) e) ∙ idp)  ⟩
      idp ◃∙
      ! (ap (λ p → p ∙ idp) (ap (λ q₁ → q₁) (ap ! (ap (λ q₁₁ → q₁₁) (E₁-v2 e))))) ◃∙
      ! (ap (λ p → p ∙ idp) (ap (λ q₁ → q₁) (ap ! (!-!-!-∘-rid (cin j) right e idp (! idp) idp)))) ◃∙
      δ₀-free-helper2 (! (ap (cin j) (e ∙ idp)) ∙ idp) (! (ap (cin j) e) ∙ idp) ◃∙
      idp ◃∎
        =ₛ⟨ lemma e  ⟩
      four-!-!-!-rid-rid idp idp (ap right (! (ap (cin j) e) ∙ idp)) idp ◃∙
      ap (_∙_ (ap right (! (ap (cin j) e) ∙ idp))) (ψ₂-free-helper3 (λ z → cin j (fst (G <#> g) z)) idp idp e idp) ◃∙ idp ◃∎ ∎ₛ
        where
          lemma : {w : ty (G # j)} (m : fst (G <#> g) t == w)
            → idp ◃∙
            ! (ap (λ p → p ∙ idp) (ap (λ q₁ → q₁) (ap ! (ap (λ q₁₁ → q₁₁) (E₁-v2 m))))) ◃∙
            ! (ap (λ p → p ∙ idp) (ap (λ q₁ → q₁) (ap ! (!-!-!-∘-rid (cin j) right m idp idp idp)))) ◃∙
            δ₀-free-helper2 (! (ap (cin j) (m ∙ idp)) ∙ idp) (! (ap (cin j) m) ∙ idp) ◃∙
            idp ◃∎
              =ₛ
            four-!-!-!-rid-rid idp idp (ap right (! (ap (cin j) m) ∙ idp)) idp ◃∙
            ap (_∙_ (ap right (! (ap (cin j) m) ∙ idp))) (ψ₂-free-helper3 (λ z → cin j (fst (G <#> g) z)) idp idp m idp) ◃∙ idp ◃∎
          lemma idp = =ₛ-in idp 

    module _ (q : cin j a == cin i a)  where

      ψ₂-red-helper2 : {f : ty (G # i) → Colim ForgG} (H : cin j ∘ fst (G <#> g) ∼ f) {ρ γ : left a == right (f (fun (G # i) a))}
        (τ₁ : ρ == ! (ap left (ap [id] q)) ∙ glue (cin j a) ∙ ap right (! (ap (cin j) (snd (G <#> g) a)) ∙ H (fun (G # i) a))) (τ₂ : ρ == γ)
        → ! (ap (λ p → p ∙ idp) (ap (_∙_ (! (ap left (ap [id] q)))) (ap !  (ap (_∙_ (ap (right ∘ f) (snd (nat δ i) a))) (E₂-v2 {f = right {d = SpCos₂}} idp (! (glue (cin j a)))))))) ∙
        ! (ap (λ p → p ∙ idp) (ap (_∙_ (! (ap left (ap [id] q)))) (ap ! (ap (_∙_ (ap (right ∘ f) (snd (nat δ i) a))) (E₁-v2 {f = right {d = SpCos₂}} {g = cin j}
          (snd (G <#> g) a)))))) ∙
        ! (ap (λ p → p ∙ idp) (ap (_∙_ (! (ap left (ap [id] q)))) (ap ! (!-!-!-∘-∘-∘-rid (cin j) (fst (G <#> g)) f right
          (snd (nat δ i) a) (snd (G <#> g) a) idp (! (glue (cin j a))) (H (fun (G # i) a)))))) ∙
        ! (ap (λ p → p ∙ idp) (ap (_∙_ (! (ap left (ap [id] q))))
        (ap ! (ap (λ p → ! (ap right (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙ idp)) ∙ p)) ∙
          ! (glue (cin j a))) (apCommSq2 (cin j ∘ fst (G <#> g)) f H (snd (nat δ i) a)))))) ∙
        δ₀-free-helper2-delay q idp (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙ idp)) ∙
          H (fst (nat δ i) (fun (F # i) a))) (! (ap (cin j) (snd (G <#> g) a)) ∙ H (fun (G # i) a)) ∙
        ! (ap (λ p →  p ∙ ap right (! (! (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙ idp)) ∙
          H (fst (nat δ i) (fun (F # i) a))) ∙
          ! (ap (cin j) (snd (G <#> g) a)) ∙ H (fun (G # i) a)))) τ₁) ∙
        ap (λ p → p ∙ ap right (! (! (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙ idp)) ∙
          H (fst (nat δ i) (fun (F # i) a))) ∙
          ! (ap (cin j) (snd (G <#> g) a)) ∙ H (fun (G # i) a)))) τ₂ ∙ idp
        ==
        four-!-!-!-rid-rid (! (ap left (ap [id] q))) (glue (cin j a))
          (ap right (! (ap (cin j) (snd (G <#> g) a)) ∙ H (fun (G # i) a)))
          (ap (right ∘ f) (snd (nat δ i) a)) ∙
          ! (ap (λ p → p ∙ ! (ap (right ∘ f) (snd (nat δ i) a))) τ₁) ∙
          ap (λ p → p ∙ ! (ap (right ∘ f) (snd (nat δ i) a))) τ₂ ∙
          ap (_∙_ γ) (ψ₂-free-helper3 f (snd (nat δ i) a)
          (H (fst (nat δ i) (fun (F # i) a))) (snd (G <#> g) a) (H (fun (G # i) a))) ∙
        ap (λ p → γ ∙ ap right (! (! (! (p ∙ ap (cin j) (snd (G <#> g) a ∙ idp)) ∙
          H (fst (nat δ i) (fun (F # i) a))) ∙ ! (ap (cin j) (snd (G <#> g) a)) ∙ H (fun (G # i) a))))
          (∼-nat H (snd (nat δ i) a)) ∙
        ap (λ p →  γ ∙ ap right (! (! (! p ∙ H (fst (nat δ i) (fun (F # i) a))) ∙
          ! (ap (cin j) (snd (G <#> g) a)) ∙ H (fun (G # i) a))))
          (ap-∘-∙ (cin j) (fst (G <#> g)) (snd (nat δ i) a) (snd (G <#> g) a ∙ idp))
      ψ₂-red-helper2 {f} H idp idp = IndFunHom {P = λ f₁ H₁ →
        ! (ap (λ p → p ∙ idp) (ap (_∙_ (! (ap left (ap [id] q)))) (ap ! (ap (_∙_ (ap (right ∘ f₁) (snd (nat δ i) a)))
        (E₂-v2 {f = right {d = SpCos₂}} idp (! (glue (cin j a)))))))) ∙
        ! (ap (λ p → p ∙ idp) (ap (_∙_ (! (ap left (ap [id] q))))
        (ap ! (ap (_∙_ (ap (right ∘ f₁) (snd (nat δ i) a))) (E₁-v2 {f = right {d = SpCos₂}} {g = cin j} (snd (G <#> g) a)))))) ∙
        ! (ap (λ p → p ∙ idp) (ap (_∙_ (! (ap left (ap [id] q)))) (ap !
        (!-!-!-∘-∘-∘-rid (cin j) (fst (G <#> g)) f₁ right (snd (nat δ i) a)
        (snd (G <#> g) a) idp (! (glue (cin j a))) (H₁ (fun (G # i) a)))))) ∙
        ! (ap (λ p → p ∙ idp) (ap (_∙_ (! (ap left (ap [id] q))))
        (ap ! (ap (λ p → ! (ap right (! (ap (cin j)
        (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙ idp)) ∙ p)) ∙ ! (glue (cin j a)))
        (apCommSq2 (cin j ∘ fst (G <#> g)) f₁ H₁ (snd (nat δ i) a)))))) ∙ δ₀-free-helper2-delay q idp
        (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙ idp)) ∙ H₁ (fst (nat δ i) (fun (F # i) a)))
        (! (ap (cin j) (snd (G <#> g) a)) ∙ H₁ (fun (G # i) a)) ∙ idp
          ==
        four-!-!-!-rid-rid (! (ap left (ap [id] q))) (glue (cin j a))
        (ap right (! (ap (cin j) (snd (G <#> g) a)) ∙ H₁ (fun (G # i) a)))
        (ap (right ∘ f₁) (snd (nat δ i) a)) ∙
        ap (_∙_ (! (ap left (ap [id] q)) ∙ glue (cin j a) ∙ ap right (! (ap (cin j) (snd (G <#> g) a)) ∙ H₁ (fun (G # i) a))))
        (ψ₂-free-helper3 f₁ (snd (nat δ i) a)
        (H₁ (fst (nat δ i) (fun (F # i) a))) (snd (G <#> g) a)
        (H₁ (fun (G # i) a))) ∙ ap (λ p → (! (ap left (ap [id] q)) ∙ glue (cin j a) ∙
        ap right (! (ap (cin j) (snd (G <#> g) a)) ∙ H₁ (fun (G # i) a))) ∙
        ap right (! (! (! (p ∙ ap (cin j) (snd (G <#> g) a ∙ idp)) ∙ H₁ (fst (nat δ i) (fun (F # i) a))) ∙
        ! (ap (cin j) (snd (G <#> g) a)) ∙ H₁ (fun (G # i) a)))) (∼-nat H₁ (snd (nat δ i) a)) ∙
        ap (λ p →  (! (ap left (ap [id] q)) ∙ glue (cin j a) ∙
        ap right (! (ap (cin j) (snd (G <#> g) a)) ∙ H₁ (fun (G # i) a))) ∙
        ap right (! (! (! p ∙ H₁ (fst (nat δ i) (fun (F # i) a))) ∙
        ! (ap (cin j) (snd (G <#> g) a)) ∙ H₁ (fun (G # i) a))))
        (ap-∘-∙ (cin j) (fst (G <#> g)) (snd (nat δ i) a) (snd (G <#> g) a ∙ idp))} (lemma (snd (nat δ i) a) (snd (G <#> g) a)) f H
          where
            lemma : {t : ty (G # i)} (c : fst (nat δ i) (fun (F # i) a)  == t) (e : fst (G <#> g) t == fun (G # j) a) →
              ! (ap (λ p → p ∙ idp) (ap (_∙_ (! (ap left (ap [id] q))))
              (ap ! (ap (_∙_  (ap (right ∘ (λ z → cin j (fst (G <#> g) z))) c))
              (E₂-v2 {f = right {d = SpCos₂}} idp (! (glue (cin j a)))))))) ∙
              ! (ap (λ p → p ∙ idp) (ap (_∙_ (! (ap left (ap [id] q))))
              (ap ! (ap (_∙_ (ap (right ∘ (λ z → cin j (fst (G <#> g) z))) c)) (E₁-v2 {f = right {d = SpCos₂}} {g = cin j} e))))) ∙
              ! (ap (λ p → p ∙ idp) (ap (_∙_ (! (ap left (ap [id] q))))
              (ap ! (!-!-!-∘-∘-∘-rid (cin j) (λ v → fst (G <#> g) v)
              (λ z → cin j (fst (G <#> g) z)) right c e idp (! (glue (cin j a))) idp)))) ∙
              ! (ap (λ p → p ∙ idp) (ap (_∙_ (! (ap left (ap [id] q))))
              (ap ! (ap (λ p → ! (ap right (! (ap (cin j) (ap (fst (G <#> g)) c ∙ e ∙ idp)) ∙ p)) ∙ ! (glue (cin j a)))
              (apCommSq2 (cin j ∘ fst (G <#> g)) (λ z → cin j (fst (G <#> g) z)) (λ x → idp) c))))) ∙
              δ₀-free-helper2-delay q idp (! (ap (cin j) (ap (fst (G <#> g)) c ∙ e ∙ idp)) ∙ idp) (! (ap (cin j) e) ∙ idp) ∙ idp
                ==
              four-!-!-!-rid-rid (! (ap left (ap [id] q))) (glue (cin j a))
              (ap right (! (ap (cin j) e) ∙ idp))
              (ap (right ∘ (λ z → cin j (fst (G <#> g) z))) c) ∙
              ap (_∙_ (! (ap left (ap [id] q)) ∙ glue (cin j a) ∙ ap right (! (ap (cin j) e) ∙ idp)))
              (ψ₂-free-helper3 (λ z → cin j (fst (G <#> g) z)) c idp e idp) ∙
              ap (λ p →  (! (ap left (ap [id] q)) ∙ glue (cin j a) ∙ ap right (! (ap (cin j) e) ∙ idp)) ∙
              ap right (! (! (! (p ∙ ap (cin j) (e ∙ idp)) ∙ idp) ∙ ! (ap (cin j) e) ∙ idp))) (∼-nat (λ x → idp) c) ∙
              ap (λ p → (! (ap left (ap [id] q)) ∙ glue (cin j a) ∙ ap right (! (ap (cin j) e) ∙ idp)) ∙
              ap right  (! (! (! p ∙ idp) ∙ ! (ap (cin j) e) ∙ idp)))
              (ap-∘-∙ (cin j) (λ v → fst (G <#> g) v) c (e ∙ idp))
            lemma idp e = lemma2 q
              where
                lemma2 : {y : Colim (ConsDiag Γ A)} (q₁ : cin j a == y) 
                  → ! (ap (λ p → p ∙ idp) (ap (_∙_ (! (ap left (ap [id] q₁)))) (ap ! (ap (λ q₁₁ → q₁₁) (E₂-v2 {f = right {d = SpCos₂}} idp (! (glue (cin j a)))))))) ∙
                  ! (ap (λ p → p ∙ idp) (ap (_∙_ (! (ap left (ap [id] q₁)))) (ap ! (ap (λ q₁₁ → q₁₁) (E₁-v2 {f = right {d = SpCos₂}} {g = cin j} e))))) ∙
                  ! (ap (λ p → p ∙ idp) (ap (_∙_ (! (ap left (ap [id] q₁)))) (ap ! (!-!-!-∘-∘-∘-rid (cin j) (fst (G <#> g))
                  (λ z → cin j (fst (G <#> g) z)) right idp e idp (! (glue (cin j a))) idp)))) ∙
                  δ₀-free-helper2-delay q₁ idp (! (ap (cin j) (e ∙ idp)) ∙ idp) (! (ap (cin j) e) ∙ idp) ∙ idp
                    ==
                  four-!-!-!-rid-rid (! (ap left (ap [id] q₁))) (glue (cin j a))
                  (ap right (! (ap (cin j) e) ∙ idp)) idp ∙
                  ap (_∙_ (! (ap left (ap [id] q₁)) ∙ glue (cin j a) ∙ ap right (! (ap (cin j) e) ∙ idp)))
                  (ψ₂-free-helper3 (λ z → cin j (fst (G <#> g) z)) idp idp e idp) ∙ idp
                lemma2 idp = =ₛ-out (ψ₂-red-helper3 (glue (cin j a)) e)
                
-- γ = glue (cin i a)
-- ρ = transport (λ z → left ([id] z) == right {d = SpCos₂} (ψ₂ z)) q (glue (cin j a))


    𝕗 = λ {e : ty (F # j)} (s₃ : e == fun (F # j) a) →
      ! (ap (cin {D = ForgG} j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) s₃))) ∙ cglue g (fst (nat δ i) (fun (F # i) a))

    module _ (q : cin j a == cin i a) (τ₂ : transport (λ z → left ([id] z) == right {d = SpCos₂} (ψ₂ z)) q (glue (cin j a)) == glue (cin i a)) where

      ψ₂-red-helper : {u : ty (G # j)} (s : u  == fun (G # j) a) (τ : transport (λ z → left ([id] z) == right {d = SpCos₂} (ψ₂ z)) q (glue (cin j a))
          == ! (ap left (ap [id] q)) ∙ glue (cin j a) ∙ ap right (! (ap (cin j) (snd (G <#> g) a)) ∙ cglue g (fun (G # i) a)))
        → ! (ap (λ p → p ∙ idp) (ap (_∙_ (! (ap left (ap [id] q)))) (ap ! (ap (_∙_ (ap (right ∘ cin i) (snd (nat δ i) a))) (E₂-v2 {f = right {d = SpCos₂}} idp
          (! (glue (cin j a)))))))) ∙
        ! (ap (λ p → p ∙ idp) (ap (_∙_ (! (ap left (ap [id] q)))) (ap ! (ap (_∙_ (ap (right ∘ cin i) (snd (nat δ i) a))) (E₁-v2 {f = right {d = SpCos₂}} {g = cin j}
          (snd (G <#> g) a)))))) ∙
        ! (ap (λ p → p ∙ idp) (ap (_∙_ (! (ap left (ap [id] q)))) (ap ! (!-!-!-∘-∘-∘-rid (cin j) (fst (G <#> g)) (cin i) (right {d = SpCos₂}) (snd (nat δ i) a) (snd (G <#> g) a) s
          (! (glue (cin j a))) (cglue g (fun (G # i) a)))))) ∙
        ! (ap (λ p → p ∙ idp) (ap (_∙_ (! (ap left (ap [id] q)))) (ap ! (ap (λ p → ! (ap right (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙
          snd (G <#> g) a ∙ ! s ∙ idp)) ∙ p)) ∙ ap (right ∘ cin j) s ∙ ! (glue (cin j a)))
          (apCommSq2 (cin j ∘ fst (G <#> g)) (cin i) (cglue g) (snd (nat δ i) a)))))) ∙
        δ₀-free-helper2-delay q s (! (ap (cin {D = ForgG} j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙ ! s ∙ idp)) ∙ cglue g (fst (nat δ i) (fun (F # i) a)))
          (! (ap (cin j) (snd (G <#> g) a)) ∙ cglue g (fun (G # i) a)) ∙
        ! (ap (λ p →  p ∙ ap right (! (! (! (ap (cin {D = ForgG} j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙ ! s ∙ idp)) ∙ cglue g (fst (nat δ i) (fun (F # i) a))) ∙
          ap (cin j) s ∙ ! (ap (cin j) (snd (G <#> g) a)) ∙ cglue g (fun (G # i) a)))) τ) ∙
        ap (λ p →  p ∙ ap right (! (! (! (ap (cin {D = ForgG} j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙ ! s ∙ idp)) ∙ cglue g (fst (nat δ i) (fun (F # i) a))) ∙
          ap (cin j) s ∙ ! (ap (cin j) (snd (G <#> g) a)) ∙ cglue g (fun (G # i) a)))) τ₂ ∙ idp
        ==
        four-!-!-!-rid-rid (! (ap left (ap [id] q))) (glue (cin j a)) (ap (right {d = SpCos₂}) (! (ap (cin j) (snd (G <#> g) a)) ∙ cglue g (fun (G # i) a)))
          (ap (right ∘ cin i) (snd (nat δ i) a)) ∙
        ! (ap (λ p → p ∙ ! (ap (right ∘ cin i) (snd (nat δ i) a))) τ) ∙
        ap (λ p → p ∙ ! (ap (right ∘ cin i) (snd (nat δ i) a))) τ₂ ∙
        ap (_∙_ (glue (cin i a))) (ψ₂-free-helper2 (snd (nat δ i) a)
          (cglue g (fst (nat δ i) (fun (F # i) a))) (snd (G <#> g) a) s (cglue g (fun (G # i) a))) ∙
        ap (λ p → glue (cin i a) ∙
        ap right (! (! (! (p ∙ ap (cin j) (snd (G <#> g) a ∙ ! s ∙ idp)) ∙
        cglue g (fst (nat δ i) (fun (F # i) a))) ∙
        ap (cin j) s ∙
        ! (ap (cin j) (snd (G <#> g) a)) ∙ cglue g (fun (G # i) a)))) (∼-nat (cglue g) (snd (nat δ i) a)) ∙
        ap (λ p → glue (cin i a) ∙ ap right (! (! (! p ∙ cglue g (fst (nat δ i) (fun (F # i) a))) ∙ ap (cin j) s ∙
          ! (ap (cin j) (snd (G <#> g) a)) ∙ cglue g (fun (G # i) a))))
          (ap-∘-∙ (cin j) (fst (G <#> g)) (snd (nat δ i) a) (snd (G <#> g) a ∙ ! s ∙ idp))
      ψ₂-red-helper idp τ = ψ₂-red-helper2 q (cglue g) τ τ₂

      abstract

        ψ₂-red : {e : ty (F # j)} (s₃ : e == fun (F # j) a) {μ : ψ₂ (cin j a) == ψ₂ (cin i a)} (T : μ == ! (ap (cin j) (snd (G <#> g) a)) ∙ cglue g (fun (G # i) a))
          (τ₁ : transport (λ z → left ([id] z) == right {d = SpCos₂} (ψ₂ z)) q (glue (cin j a)) == ! (ap left (ap [id] q)) ∙ glue (cin j a) ∙ ap right μ)
          → ! (ap (λ p → p ∙ idp) (ap (λ p → ! (ap left (ap [id] q)) ∙ p) (ap ! (ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) (E₂-v2 T (! (glue (cin j a)))))))) ◃∙
          ! (ap (λ p → p ∙ idp) (ap (λ p → ! (ap left (ap [id] q)) ∙ p) (ap ! (ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) (E₁-v2 (snd (G <#> g) a)))))) ◃∙
          ! (ap (λ p → p ∙ idp) (ap (λ p → ! (ap left (ap [id] q)) ∙ p) (ap ! (long-red-ap-!-∙ (cin j) (fst (nat δ j))
            (fst (G <#> g)) (cin i) right (snd (nat δ i) a) (snd (G <#> g) a) s₃
              (snd (nat δ j) a) (cglue g (fun (G # i) a)) (! (glue (cin j a))))))) ◃∙
          ! (ap (λ p → p ∙ idp) (ap (λ p → ! (ap left (ap [id] q)) ∙ p) (ap ! (ap (λ p → ! (ap (right {d = SpCos₂}) (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙
            snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) s₃))) ∙ p)) ∙ ap (right ∘ cin j ∘ fst (nat δ j)) s₃ ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙
              ! (glue (cin j a))) (apCommSq2 (cin j ∘ fst (G <#> g)) (cin i) (cglue g) (snd (nat δ i) a)))))) ◃∙
          δ₀-free-helper q s₃ (snd (nat δ j) a) (𝕗 s₃) μ ◃∙
          ! (ap (λ p → p ∙ ap right (! (! (𝕗 s₃) ∙ ap (cin j ∘ fst (nat δ j)) s₃ ∙ ap (cin j) (snd (nat δ j) a) ∙ μ))) τ₁) ◃∙
          ap (λ p → p ∙ ap right (! (! (𝕗 s₃) ∙ ap (cin j ∘ fst (nat δ j)) s₃ ∙ ap (cin j) (snd (nat δ j) a) ∙ μ))) τ₂ ◃∙
          ap (λ p → glue (cin i a) ∙ ap right (! p)) (ap (λ p → ! (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙
            ! (ap (fst (nat δ j)) s₃))) ∙ cglue g (fst (nat δ i) (fun (F # i) a))) ∙ ap (cin j ∘ fst (nat δ j))
            s₃ ∙ ap (cin j) (snd (nat δ j) a) ∙ p) T) ◃∎
          =ₛ ↯ (ψ₂-free q s₃ μ τ₁ τ₂) ◃∎
        ψ₂-red idp idp τ₁ = =ₛ-in (ψ₂-red-helper (snd (nat δ j) a) τ₁)
