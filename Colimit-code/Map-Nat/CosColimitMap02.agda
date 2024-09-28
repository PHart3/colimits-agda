{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import lib.PathSeq
open import Coslice
open import Diagram
open import AuxPaths
open import AuxPaths-v2
open import Colim
open import Cocone
open import CosColimitMap00
open import CosColimitMap01

module CosColimitMap02 where

module _ {ℓ} {A : Type ℓ} where

  ∙-rid-rid : {x y z : A} (p : x == y) (q : y == z) → (p ∙ q) ∙ idp == (p ∙ q ∙ idp) ∙ idp
  ∙-rid-rid idp idp = idp

  !-!-rid : {x y : A} (q : x == y) → (! (! q) ∙ idp) ∙ idp == q ∙ idp
  !-!-rid idp = idp

  !-!-rid2 : {x y : A} (p : x == y) → ! (! p) ∙ idp == (p ∙ idp) ∙ idp
  !-!-rid2 idp = idp

  rid-coher : {x y : A} (p : x == y) → ∙-rid-rid idp (! (! p)) ∙ !-!-rid p == !-!-rid2 p ∙ ! (ap (λ q → q ∙ idp) (! (∙-unit-r p))) ∙ idp
  rid-coher idp = idp

  ap-!-loop : {x y : A} (q : x == y) (p : y == y) → p ∙ ! (q ∙ p) =-= ! p ∙ p ∙ ! q
  ap-!-loop idp p = !-inv-r p ◃∙ ! (!-inv-l p) ◃∙ ap (λ z → ! p ∙ z) (! (∙-unit-r p)) ◃∎

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} (f : A → B) where

  !-!-∙-rid : {x y : A} (p : x == y) {b : B} (q : b == f x) → ! (! q) ∙ idp == (q ∙ ap f p) ∙ ap f (! p)
  !-!-∙-rid idp q = !-!-rid2 q

module ConstrMap3 {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open Id Γ A

  open ConstrMap2 δ

  module MapCoher (i j : Obj Γ) (g : Hom Γ i j) (a : A) where

    id-free-helper : {x y z : P₂} (U : x == y) (p : z == y) → ! (U ∙ ! p ∙ idp) =-= ! (U ∙ ! p)
    id-free-helper idp p = ap ! (∙-unit-r (! p)) ◃∎

    id-free : (q : (z : Colim (ConsDiag Γ A)) →  left ([id] z) == right {d = SpCos₂} (ψ₂ z)) {x y : Colim (ConsDiag Γ A)} (p : x == y) {u : P₂} (U : u == right (ψ₂ y))
      → ! (ap left (ap [id] p)) ∙ ! (U ∙ ! (ap right (ap ψ₂ p)) ∙ ! (q x) ∙ idp) =-= idp ∙ ! (U ∙ ! (q y))
    id-free q {x = x} idp U = id-free-helper U (q x)   

    cglue-switch : (q : (z : Colim (ConsDiag Γ A)) →  left ([id] z) == right {d = SpCos₂} (ψ₂ z)) {x y : Colim (ConsDiag Γ A)} (p : x == y)
      {u : P₂} (U : u == right (ψ₂ y)) {a₁ a₂ : P₂} (V₁ : left ([id] x) == a₁) (V₂ : a₂ == left ([id] y)) 
      → ! (ap left (ap [id] p)) ∙ V₁ ∙ ! (U ∙ ! (ap right (ap ψ₂ p)) ∙ ! (q x) ∙ V₁) =-= ! V₂ ∙ V₂ ∙ ! (U ∙ ! (q y))
    cglue-switch q {x = x} idp idp idp idp = ap ! (∙-unit-r (! (q x))) ◃∎ 

    id-free=switch : (q : (z : Colim (ConsDiag Γ A)) →  left ([id] z) == right {d = SpCos₂} (ψ₂ z)) {x y : Colim (ConsDiag Γ A)} (p : x == y)
      →  cglue-switch q p idp idp idp =ₛ ↯ (id-free q p idp) ◃∎
    id-free=switch q idp = =ₛ-in idp

    E₃-v2-red : (q : (z : Colim (ConsDiag Γ A)) → left ([id] z) == right {d = SpCos₂} (ψ₂ z)) {y : Colim (ConsDiag Γ A)} (p : cin j a == y) {V : a == [id] y} (T : ap [id] p == V)
      → ap (λ c → ! (ap left (ap [id] p)) ∙ ap left V ∙ c) (ap ! (ap (λ z → z) (E₃-v2 {f = left} {v = ψ₂} {u = right} (λ z → ! (q z)) p T))) ◃∙
      ap (λ n → n ∙ ap left V ∙ ! (! (q y))) (ap (λ m → ! (ap left m)) T) ◃∎
        =ₛ cglue-switch q p idp (ap left V) (ap left V)  
    E₃-v2-red q idp idp = =ₛ-in (∙-unit-r (ap (λ c → c) (ap ! (ap (λ z → z) (∙-unit-r (! (q (cin j a))))))) ∙
      ap-idf (ap ! (ap (λ z → z) (∙-unit-r (! (q (cin j a)))))) ∙
      ap (ap !) (ap-idf (∙-unit-r (! (q (cin j a))))))

    abstract

      id-red : {u : P₂} (V : u == right (ψ₂ (cin i a))) (s : cin j a == cin i a) (R : ap [id] s == idp)
        → ap (λ p → ! (ap left (ap [id] s)) ∙ p) (ap ! (ap (λ p → V ∙ p) (E₃-v2 {f = left} (λ x → ! (glue x)) s R))) ◃∙
          ap (λ p → p ∙ ! (V ∙ ! (glue (cin i a)))) (ap (λ p → ! (ap left p)) R) ◃∎
          =ₛ
          ↯ (id-free glue s V) ◃∎
      id-red idp s R =
        ap (_∙_ (! (ap left (ap [id] s)))) (ap ! (ap (λ q → q) (E₃-v2 (λ x → ! (glue x)) s R))) ◃∙
        ap (λ p → p ∙ ! (! (glue (cin i a)))) (ap (λ p → ! (ap left p)) R) ◃∎
          =ₛ⟨ E₃-v2-red glue s R  ⟩
        cglue-switch glue s idp idp idp
          =ₛ⟨ id-free=switch glue s  ⟩
        (↯ (id-free glue s idp) ◃∎) ∎ₛ

-- s = cglue g a
-- V = ap (right ∘ cin i) (snd (nat δ i) a)


    recc-free : {x y : Colim (ConsDiag Γ A)} (p : x == y) {u₁ u₂ : ty (F # j)} (s₃ : u₁ == u₂) {e : Colim ForgF} (c : cin j u₁ == e)
      {v : ty (G # j)} (s₁ : fst (nat δ j) u₂ == v) (s₂ : left ([id] x) == right (cin j v)) → 
      ! (ap left (ap [id] p)) ∙ ! (ap (right ∘ cin j) s₁ ∙ ! s₂) ∙ ap ForgMap (! (ap (cin j) s₃) ∙ c)
        =-=
      ! (ap left (ap [id] p)) ∙ (! (! (ap ForgMap c) ∙
        ap (ForgMap ∘ cin j) s₃ ∙ ap (right ∘ cin j) s₁ ∙ ! s₂))
    recc-free p idp idp s₁ s₂ = ap (λ r → ! (ap left (ap [id] p)) ∙ r) (∙-unit-r (! (ap (right ∘ cin j) s₁ ∙ ! s₂))) ◃∎ 

-- p = cglue g a
-- c = cglue g (fun (F # i) a)
-- s₁ = (snd (nat δ j) a)
-- s₂ = (glue (cin j a))
-- s₃ = (snd (F <#> g) a)

    abstract

      recc-red : {u₁ u₂ : ty (F # j)} (s₃ : u₁ == u₂) {e : Colim ForgF} (c : cin j u₁ == e)
        {v : ty (G # j)} (s₁ : fst (nat δ j) u₂ == v) (s₂ : left a == right (cin j v)) {R : ForgMap (cin j u₁) == ForgMap e} (φ : ap ForgMap c == R) →
        H₂ s₃ (ap (right ∘ cin j) s₁ ∙ ! s₂) c φ ◃∙
        ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) s₃ ∙ ap (right ∘ cin j) s₁ ∙ ! s₂) (! φ))) ◃∎
        =ₛ
        ↯ (recc-free (cglue g a) s₃ c s₁ s₂) ◃∎
      recc-red idp idp idp s₂ idp = =ₛ-in (∙-unit-r (ap (_∙_ (! (ap left (ap [id] (cglue g a))))) (∙-unit-r (! (! s₂)))))

-- φ = (FM-βr g (fun (F # i) a))

    ψ₁-free-coher : {y : Colim (ConsDiag Γ A)} (p : cin j a == y) {u : ty (F # j)} (s : fst (nat δ j) u == fun (G # j) a) →
      (! (ap left (ap [id] p)) ∙ ! (ap (right {d = SpCos₂} ∘ cin j) s ∙ ! (glue (cin j a))) ∙ idp) ∙ idp
      =-= glue y ∙ ap right (! (ap (cin j) s ∙ ap ψ₂ p))
    ψ₁-free-coher idp s = ψ₁-free-coher2 s
      module _ where
        ψ₁-free-coher2 : {v : ty (G # j)} (σ : v == fun (G # j) a)
          → (! (ap (right ∘ cin j) σ ∙ ! (glue (cin j a))) ∙ idp) ∙ idp =-= glue (cin j a) ∙ ap right (! (ap (cin j) σ ∙ idp))
        ψ₁-free-coher2 idp = !-!-rid (glue (cin j a)) ◃∎

    ψ₁-free : {y : Colim (ConsDiag Γ A)} (p : cin j a == y) {u e : ty (F # j)} (s₃ : e == u) {z : Colim ForgF} (c : cin j e == z) (s₁ : fst (nat δ j) u == fun (G # j) a) →
      (! (ap left (ap [id] p)) ∙ (! (ap (right ∘ cin j) s₁ ∙ ! (glue (cin j a)))) ∙ ap ForgMap (! (ap (cin j) s₃) ∙ c)) ∙ 𝕃 z
      =-=
      glue y ∙ ap right (! (! (ap δ₀ (! (ap (cin j) s₃) ∙ c)) ∙ ap (cin j) s₁ ∙ ap ψ₂ p))
    ψ₁-free p idp idp s₁ = ψ₁-free-coher p s₁ 

    abstract

      ψ₁-red : {y : Colim (ConsDiag Γ A)} (q : cin j a == y) {e : ty (F # j)} (s₃ : e == fun (F # j) a) (c : cin j e == ψ₁ y) (T : ap ψ₁ q == ! (ap (cin j) s₃) ∙ c) →
        ! (ap (λ p → p ∙ 𝕃 (ψ₁ y)) (H₁ q (! (ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))) T)) ◃∙
        ! (apd-∙-r {F = σ (comp 𝕂) (comTri 𝕂)} {G = λ z → 𝕃 (ψ₁ z)} q) ◃∙
        ap (transport (λ z → left ([id] z) == right (δ₀ (ψ₁ z))) q) (ap-∘-!-!-rid (cin j) right (snd (nat δ j) a) (glue (cin j a))) ◃∙
        apd-ap-∙-l right {F = glue} {G = ℂ} q ◃∙
        ap (λ p → glue y ∙ ap right (! p)) (transp-pth-cmpL δ₀ ψ₁ ψ₂ q (ap (cin j) (snd (nat δ j) a))) ◃∙
        ap (λ p → glue y ∙ ap right (! p)) (ap (λ p → ! (ap δ₀ p) ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ q) T) ◃∎
        =ₛ
        ↯ (ψ₁-free q s₃ c (snd (nat δ j) a)) ◃∎
      ψ₁-red idp idp c T = =ₛ-in (lemma T)
        where
          lemma : {C : cin j (fun (F # j) a) == ψ₁ (cin j a)} (τ : idp == C) →
            ! (ap (λ p → p ∙ 𝕃 (ψ₁ (cin j a))) (H₁ {u = ForgMap} {h = [id]} {f = left} {v = ψ₁} {c = cin j a} idp (! (ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))) τ)) ∙
            ap (λ z → z) (ap-∘-!-!-rid (cin j) right (snd (nat δ j) a) (glue (cin j a))) ∙
            ap (λ p → glue (cin j a) ∙ ap right (! p)) (! (∙-unit-r (ap (cin j) (snd (nat δ j) a)))) ∙
            ap (λ p → glue (cin j a) ∙ ap right (! p)) (ap (λ p → ! (ap δ₀ p) ∙ ap (cin j) (snd (nat δ j) a) ∙ idp) τ)
            ==
            ↯ (ψ₁-free idp idp C (snd (nat δ j) a))
          lemma idp = lemma2 (snd (nat δ j) a)
            where
              lemma2 : {v : ty (G # j)} (σ : v == fun (G # j) a) →
                ! (ap (λ p → p ∙ idp) (! (∙-unit-r (! (ap (right ∘ cin j) σ ∙ ! (glue (cin j a))))))) ∙
                  ap (λ z → z) (ap-∘-!-!-rid (cin j) right σ (glue (cin j a))) ∙
                  ap (λ p → glue (cin j a) ∙ ap right (! p)) (! (∙-unit-r (ap (cin j) σ))) ∙ idp
                ==
                ↯ (ψ₁-free-coher2 (snd (nat δ j) a) σ)
              lemma2 idp = lemma3 (glue (cin j a))
                where
                  lemma3 : {r : P₂} (γ : r == right (ψ₂ (cin j a)))
                    → ! (ap (λ p → p ∙ idp) (! (∙-unit-r (! (! γ))))) ∙
                    ap (λ z → z) (ap-∘-!-!-rid (cin j) right idp γ) ∙ idp
                    == !-!-rid γ
                  lemma3 idp = idp

    δ₀-free : {y : Colim (ConsDiag Γ A)} (q : cin j a == y) {u e : ty (F # j)} (s₃ : e == u) (s₁ : fst (nat δ j) u == fun (G # j) a)
      {v : Colim ForgG} (D : cin j (fst (nat δ j) e) == v) {m : P₂} (ξ : m == right v)  →
      (! (ap left (ap [id] q)) ∙ ! ((ξ ∙ ! (ap (right {d = SpCos₂}) D)) ∙
          ap (right ∘ cin j ∘ fst (nat δ j)) s₃ ∙ ap (right ∘ cin j) s₁ ∙ ! (glue (cin j a)))) ∙ ξ
        =-=
      glue y ∙ ap right (! (! D ∙ ap (cin j ∘ fst (nat δ j)) s₃ ∙ ap (cin j) s₁ ∙ ap ψ₂ q))
    δ₀-free q idp s₁ idp idp = ∙-rid-rid (! (ap left (ap [id] q))) (! (ap (right ∘ cin j) s₁ ∙ ! (glue (cin j a)))) ◃∙ ψ₁-free-coher q s₁

-- D = ! (ap (cin j) (comSq δ g (fun (F # i) a))) ∙ cglue g (fst (nat δ i) (fun (F # i) a))

    δ₀-red3 : {z : Colim ForgF} (c : cin j (fun (F # j) a) == z)
      → ! (ap (λ p → p ∙ 𝕃 z) (ap (λ q → q) (ap ! (ap (λ p → (𝕃 z ∙ p) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
        (∙-unit-r (! (ap right (ap δ₀ c)))))))) ∙
        ! (ap (λ p → p ∙ 𝕃 z) (ap (λ q → q) (ap ! (ap (λ p →  p ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (CommSq-swap-∘-! ForgMap δ₀ right 𝕃 c))))) ∙
        ! (ap (λ p → p ∙ 𝕃 z) (↯ (recc-free {x = cin j a} idp idp c (snd (nat δ j) a) (glue (cin j a))))) ∙
        ↯ (ψ₁-free idp idp c (snd (nat δ j) a)) ∙ idp
        ==  ↯ (δ₀-free idp idp (snd (nat δ j) a) (ap δ₀ c) (𝕃 z))
    δ₀-red3 idp = lemma (snd (nat δ j) a)
      where
        lemma : {x : ty (G # j)} (σ : x == fun (G # j) a)
          → ! (ap (λ p → p ∙ idp) (ap (λ q → q) (∙-unit-r
            (! (ap (right ∘ cin j) σ ∙ ! (glue (cin j a))))))) ∙
            ↯ (ψ₁-free-coher2 (snd (nat δ j) a) σ) ∙ idp
          == ↯ (∙-rid-rid idp (! (ap (right ∘ cin j) σ ∙ ! (glue (cin j a))))
            ◃∙ ψ₁-free-coher2 (snd (nat δ j) a) σ)
        lemma idp = lemma2 (glue (cin j a))
          where
            lemma2 : {x y : P₂} (γ : x == y)
              → ! (ap (λ p → p ∙ idp) (ap (λ q → q) (∙-unit-r (! (! γ)))))
                ∙ !-!-rid γ ∙ idp
              == ∙-rid-rid idp (! (! γ)) ∙ !-!-rid γ
            lemma2 idp = idp

    δ₀-red2 : {y : Colim (ConsDiag Γ A)} (q : cin j a == y) (c : cin j (fun (F # j) a) == ψ₁ (cin i a)) →
      ! (ap (λ p → p ∙ idp) (ap (_∙_ (! (ap left (ap [id] q)))) (ap ! (ap (λ p → p ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
        (∙-unit-r (! (ap right (ap δ₀ c)))))))) ∙
      ! (ap (λ p → p ∙ idp) (ap (_∙_ (! (ap left (ap [id] q)))) (ap ! (ap (λ p →
        p ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (CommSq-swap-∘-! ForgMap δ₀ right 𝕃 c))))) ∙
      ! (ap (λ p → p ∙ idp) (↯ (recc-free q idp c (snd (nat δ j) a) (glue (cin j a))))) ∙
      ↯ (ψ₁-free q idp c (snd (nat δ j) a)) ∙ idp
      == ↯ (δ₀-free q idp (snd (nat δ j) a) (ap δ₀ c) idp)
    δ₀-red2 idp c = δ₀-red3 c

    abstract

      δ₀-red : {e : ty (F # j)} (s₃ : e == fun (F # j) a) (c : cin j e == ψ₁ (cin i a)) {R : δ₀ (cin j e) == δ₀ (ψ₁ (cin i a))} (T : ap δ₀ c == R) → 
        ! (ap (λ p → p ∙ idp) (ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap ! (ap (λ p → ! (ap right p) ∙
          ap (right ∘ cin j ∘ fst (nat δ j)) s₃ ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) T)))) ◃∙
        ! (ap (λ p → p ∙ idp) (ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap ! (ap (λ p → p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) s₃ ∙
          ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (∙-unit-r (! (ap right (ap δ₀ c)))))))) ◃∙
        ! (ap (λ p → p ∙ idp) (ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap ! (ap (λ p → p ∙
          ap (right ∘ cin j ∘ fst (nat δ j)) s₃ ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
          (CommSq-swap-∘-! ForgMap δ₀ right 𝕃 c))))) ◃∙
        ! (ap (λ p → p ∙ idp) (↯ (recc-free (cglue g a) s₃ c (snd (nat δ j) a) (glue (cin j a))))) ◃∙
        ↯ (ψ₁-free (cglue g a) s₃ c (snd (nat δ j) a)) ◃∙
        ap (λ p → glue (cin i a) ∙ ap right (! p)) (pre-cmp-!-!-∙ δ₀ (cin j) s₃ c (ap (cin j) (snd (nat δ j) a) ∙
          ap ψ₂ (cglue g a))) ◃∙
        ap (λ p → glue (cin i a) ∙ ap right (! p)) (ap (λ p → ! p ∙ ap (cin j ∘ (fst (nat δ j))) s₃ ∙ ap (cin j) (snd (nat δ j) a) ∙
          ap ψ₂ (cglue g a)) T) ◃∎
        =ₛ
        ↯ (δ₀-free (cglue g a) s₃ (snd (nat δ j) a) R idp) ◃∎
      δ₀-red idp c idp = =ₛ-in (δ₀-red2 (cglue g a) c)

      commSq-red : {e : ty (F # j)} (s₃ : e == fun (F # j) a) {R₁ R₂ : δ₀ (cin j e) == δ₀ (ψ₁ (cin i a))} (T : R₁ == R₂) →
        ! (ap (λ p → p ∙ idp) (ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap ! (ap (λ p → ! (ap (right {d = SpCos₂}) p) ∙
          ap (right ∘ cin j ∘ fst (nat δ j)) s₃ ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) T)))) ◃∙
        ↯ (δ₀-free (cglue g a) s₃ (snd (nat δ j) a) R₁ idp) ◃∙
        ap (λ p → glue (cin i a) ∙ ap right (! p)) (ap (λ p → ! p ∙ ap (cin j ∘ fst (nat δ j))
          s₃ ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a)) T) ◃∎
        =ₛ
        ↯ (δ₀-free (cglue g a) s₃ (snd (nat δ j) a) R₂ idp) ◃∎
      commSq-red s₃ {R₁ = R₁} idp = =ₛ-in (∙-unit-r (↯ (δ₀-free (cglue g a) s₃ (snd (nat δ j) a) R₁ idp)))

-- T = ap (λ p → ! (ap (cin j) p) ∙ cglue g (fst (nat δ i) (fun (F # i) a))) (comSq-coher δ g a)

    δ₀-free-helper-pre2 : {e : ty (G # j)} (s : e == fun (G # j) a) {w z : Colim ForgG} (D : cin j e == w) (τ : cin j (fun (G # j) a) == z)
      {t : P₂} (κ : t == right (cin j (fun (G # j) a)))
      → ! (! (ap right D) ∙ ap (right ∘ cin j) s ∙ ! κ) ∙ idp == (κ ∙ ap right τ) ∙ ap right (! (! D ∙ ap (cin j) s ∙ τ))
    δ₀-free-helper-pre2 idp idp τ κ =  !-!-∙-rid right τ κ  

    δ₀-free-helper2-delay : {y : Colim (ConsDiag Γ A)} (q : cin j a == y) {e : ty (G # j)} (s : e == fun (G # j) a)
      {w z : Colim ForgG} (D : cin j e == w) (τ : cin j (fun (G # j) a) == z)
      → (! (ap left (ap [id] q)) ∙ ! (! (ap right D) ∙ ap (right {d = SpCos₂} ∘ cin j) s ∙ ! (glue (cin j a)))) ∙ idp
      == (! (ap left (ap [id] q)) ∙ glue (cin j a) ∙ ap right τ) ∙ ap right (! (! D ∙ ap (cin j) s ∙ τ))
    δ₀-free-helper2-delay idp s D τ = δ₀-free-helper-pre2 s D τ (glue (cin j a))

    δ₀-free-helper : {y : Colim (ConsDiag Γ A)} (q : cin j a == y) {u e : ty (F # j)} (σ : e == u) (s :  fst (nat δ j) u == fun (G # j) a)
      {w z : Colim ForgG} (D : cin j (fst (nat δ j) e) == w) (τ : cin j (fun (G # j) a) == z)  
      → (! (ap left (ap [id] q)) ∙ ! ((! (ap (right {d = SpCos₂}) D)) ∙
          ap (right ∘ cin j ∘ fst (nat δ j)) σ ∙ ap (right ∘ cin j) s ∙ ! (glue (cin j a)))) ∙ idp
      ==
      (! (ap left (ap [id] q)) ∙ glue (cin j a) ∙ ap right τ) ∙ ap right (! (! D ∙ ap (cin j ∘ fst (nat δ j)) σ ∙ ap (cin j) s ∙ τ))
    δ₀-free-helper q idp s D τ = δ₀-free-helper2-delay q s D τ  

-- τ = ap ψ₂ q

    δ₀-free-v2 : {y : Colim (ConsDiag Γ A)} (q : cin j a == y) {u e : ty (F # j)} (s₃ : e == u) (s₁ : fst (nat δ j) u == fun (G # j) a)
      {v : Colim ForgG} (D : cin j (fst (nat δ j) e) == v) {m : P₂} (ξ : m == right v) →
      (! (ap left (ap [id] q)) ∙ ! ((ξ ∙ ! (ap (right {d = SpCos₂}) D)) ∙
          ap (right ∘ cin j ∘ fst (nat δ j)) s₃ ∙ ap (right ∘ cin j) s₁ ∙ ! (glue (cin j a)))) ∙ ξ
        =-=
      glue y ∙ ap right (! (! D ∙ ap (cin j ∘ fst (nat δ j)) s₃ ∙ ap (cin j) s₁ ∙ ap ψ₂ q))
    δ₀-free-v2 {y} q s₃ s₁ D idp = 
      (! (ap left (ap [id] q)) ∙ ! ((! (ap (right {d = SpCos₂}) D)) ∙
          ap (right ∘ cin j ∘ fst (nat δ j)) s₃ ∙ ap (right ∘ cin j) s₁ ∙ ! (glue (cin j a)))) ∙ idp
        =⟪ δ₀-free-helper q s₃ s₁ D (ap ψ₂ q)  ⟫ 
      (! (ap left (ap [id] q)) ∙ glue (cin j a) ∙ ap right (ap ψ₂ q)) ∙ ap right (! (! D ∙ ap (cin j ∘ fst (nat δ j)) s₃ ∙ ap (cin j) s₁ ∙ ap ψ₂ q))
        =⟪ ! (ap (λ p → p ∙ ap right (! (! D ∙ ap (cin j ∘ fst (nat δ j)) s₃ ∙ ap (cin j) s₁ ∙ ap ψ₂ q))) (transp-pth-cmp q (glue (cin j a))))  ⟫
      (transport (λ z → left ([id] z) == right (ψ₂ z)) q (glue (cin j a))) ∙ ap right (! (! D ∙ ap (cin j ∘ fst (nat δ j)) s₃ ∙ ap (cin j) s₁ ∙ ap ψ₂ q))
        =⟪ ap (λ p → p ∙ ap right (! (! D ∙ ap (cin j ∘ fst (nat δ j)) s₃ ∙ ap (cin j) s₁ ∙ ap ψ₂ q))) (apd-tr glue q) ⟫
      glue y ∙ ap right (! (! D ∙ ap (cin j ∘ fst (nat δ j)) s₃ ∙ ap (cin j) s₁ ∙ ap ψ₂ q)) ∎∎ 

    abstract

      δ₀-free-eq :  {y : Colim (ConsDiag Γ A)} (q : cin j a == y) {u e : ty (F # j)} (s₃ : e == u) (s₁ : fst (nat δ j) u == fun (G # j) a)
        {v : Colim ForgG} (D : cin j (fst (nat δ j) e) == v) {m : P₂} (ξ : m == right v) →
        ↯ (δ₀-free q s₃ s₁ D ξ) ◃∎ =ₛ δ₀-free-v2 q s₃ s₁ D ξ
      δ₀-free-eq idp idp s₁ idp idp = lemma s₁
        where
          lemma : {u : ty (G # j)} (s : u == fun (G # j) a)
            → (↯ (∙-rid-rid idp (! (ap (right ∘ cin j) s ∙ ! (glue (cin j a)))) ◃∙ ψ₁-free-coher2 s₁ s) ◃∎) =ₛ
             δ₀-free-helper-pre2 s idp idp (glue (cin j a)) ◃∙
             ! (ap (λ p → p ∙ ap right (! (ap (cin j) s ∙ idp))) (! (∙-unit-r (glue (cin j a))))) ◃∙
             idp ◃∎ 
          lemma idp = =ₛ-in (rid-coher (glue (cin j a)))
