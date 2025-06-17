{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.SIP
open import lib.types.Colim
open import lib.types.Pushout
open import lib.types.Span
open import Coslice
open import Diagram-Cos
open import SIP-Cos
open import AuxPaths-v2
open import CC-Equiv-LRL-0
open import CC-v2-rewrite

module CC-Equiv-LRL-1 where

module Constr2 {ℓv ℓe ℓ ℓd ℓc} {Γ : Graph ℓv ℓe} {A : Type ℓ} (F : CosDiag ℓd ℓ A Γ) (T : Coslice ℓc ℓ A) where

  open Constr F T

  module DiagCoher2 (i j : Obj Γ) (f : P → ty T) (fₚ : (a : A) → f (left a)  == str T a) (g : Hom Γ i j) (a : A) where

    H : P → ty T
    H = fst (RLfun (f , fₚ))

    K = κ F g a T f fₚ
    
    abstract
      γ-β : apd-tr (RfunEq (f , fₚ)) (cglue g (str (F # i) a)) == ↯ (V f fₚ i j g (str (F # i) a))
      γ-β =
        apd-to-tr (λ x → f (right x) == H (right x)) (RfunEq (f , fₚ)) (cglue g (str (F # i) a))
          (↯ (V f fₚ i j g (str (F # i) a)))
          (cglue-β (λ i x → idp)
            (λ i j g x → from-transp-g (λ z → (f ∘ right) z == (fst (RLfun (f , fₚ)) ∘ right) z) (cglue g x) (↯ (V f fₚ i j g x)))
            g (str (F # i) a))

    abstract
      apd-rw2 :
        apd-tr (λ x → RfunEq (f , fₚ) (ψ x)) (cglue g a) ◃∎
          =ₛ
        apd-comp-ap {γ = RfunEq (f , fₚ)} (cglue g a) ◃∙
        ap (λ p → transport (λ x → f (right x) == H (right x)) p idp) (ψ-βr g a) ◃∙
        transp-over-∙ {F = λ x → f (right x) == H (right x)} {γ = RfunEq (f , fₚ)} (! (ap (cin j) (snd (F <#> g) a))) ◃∙
        ↯ (V f fₚ i j g (str (F # i) a)) ◃∎
      apd-rw2 =
        apd-tr (λ x → RfunEq (f , fₚ) (ψ x)) (cglue g a) ◃∎
          =ₛ⟨ apd-comp-◃ (cglue g a) ⟩
        apd-comp-ap (cglue g a) ◃∙ apd-tr (RfunEq (f , fₚ)) (ap ψ (cglue g a)) ◃∎
          =ₛ⟨ 1 & 1 & apd-comp-eq-◃ (cglue g a) (ψ-βr g a) ⟩
        apd-comp-ap (cglue g a) ◃∙
        ap (λ p → transport (λ x → f (right x) == H (right x)) p idp) (ψ-βr g a) ◃∙
        apd-tr (RfunEq (f , fₚ)) (! (ap (cin j) (snd (F <#> g) a)) ∙ cglue g (str (F # i) a)) ◃∎
          =ₛ⟨ 2 & 1 & apd-concat-arg (! (ap (cin j) (snd (F <#> g) a))) (cglue g (str (F # i) a)) ⟩
        apd-comp-ap (cglue g a) ◃∙
        ap (λ p → transport (λ x → f (right x) == H (right x)) p idp) (ψ-βr g a) ◃∙
        transp-over-∙ {F = λ x → f (right x) == H (right x)} {γ = RfunEq (f , fₚ)} (! (ap (cin j) (snd (F <#> g) a))) ◃∙
        apd-tr (RfunEq (f , fₚ)) (cglue g (str (F # i) a)) ◃∎
          =ₛ⟨ 3 & 1 & =ₛ-in γ-β ⟩
        apd-comp-ap (cglue g a) ◃∙
        ap (λ p → transport (λ x → f (right x) == H (right x)) p idp) (ψ-βr g a) ◃∙
        transp-over-∙ {F = λ x → f (right x) == H (right x)} {γ = RfunEq (f , fₚ)} (! (ap (cin j) (snd (F <#> g) a))) ◃∙
        ↯ (V f fₚ i j g (str (F # i) a)) ◃∎ ∎ₛ

    transpEq-◃ : (s : f (right (ψ (cin j a))) == H (right (ψ (cin j a))))
      →
      transport (λ x → f (right (ψ x)) == H (right (ψ x))) (cglue g a) s
        =-=
      transport (λ x →  f (right (ψ x)) == f (right (ψ x))) (cglue g a) s
    transpEq-◃ s =
      transport (λ x → f (right (ψ x)) == H (right (ψ x))) (cglue g a) s
        =⟪ O₁ s (cglue g a) (ψ-βr g a) ⟫
      (! (ap (f ∘ right) (ap ψ (cglue g a)))) ∙ s ∙ ap (reccForg K) (! (ap (cin j) (snd (F <#> g) a)) ∙ (cglue g (str (F # i) a)))
        =⟪ O₂ {p = (! (ap (f ∘ right) (ap ψ (cglue g a))))} (snd (F <#> g) a) (ap f (! (glue (cin j a))) ∙ fₚ a) (cglue g (str (F # i) a))
             (recc-βr K g (str (F # i) a)) ⟫  
      (! (ap (f ∘ right) (ap ψ (cglue g a)))) ∙ s ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙
      ! (! (ap f (ap right (cglue g (str (F # i) a)))) ∙ ap (f ∘ right ∘ cin j) (snd (F <#> g) a) ∙ ap f (! (glue (cin j a))) ∙ fₚ a)
        =⟪ ap (λ p → (! (ap (f ∘ right) (ap ψ (cglue g a)))) ∙ s ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ p) (ap ! (snd (comTri K g) a)) ⟫
      ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ s ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin i a))) ∙ fₚ a)
        =⟪ ap (λ p → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ s ∙ p ∙ ! (ap f (! (glue (cin i a))) ∙ fₚ a) )
             (O₄ (λ x → ap f (! (glue x)) ∙ fₚ ([id] x)) (cglue g a) (id-βr g a)) ⟫
      ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ s ∙ (ap (f ∘ right) (ap ψ (cglue g a)) ∙ (ap f (! (glue (cin i a))) ∙ fₚ a) ∙ idp) ∙ ! (ap f (! (glue (cin i a))) ∙ fₚ a)
        =⟪ O₅ s (cglue g a) (ap f (! (glue (cin i a))) ∙ fₚ a) ⟫
      transport (λ x →  f (right (ψ x)) == f (right (ψ x))) (cglue g a) s ∎∎

    Mid-rw :
      ap (transport (λ x → f (right (ψ x)) == H (right (ψ x))) (cglue g a)) (ap-inv-canc f (glue (cin j a)) (fₚ a)) ◃∎                                                                                                                              
        =ₛ
      ↯ (transpEq-◃ ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a))) ◃∙
      ap (transport (λ x → f (right (ψ x)) == f (right (ψ x))) (cglue g a))
        (ap-inv-canc f (glue (cin j a)) (fₚ a)) ◃∙
      ! (↯ (transpEq-◃ idp)) ◃∎
    Mid-rw = =ₛ-in (apeq-rev (λ s → ↯ (transpEq-◃ s)) (ap-inv-canc f (glue (cin j a)) (fₚ a)))

    abstract
    
      CoherLemma : {z : Colim (ConsDiag Γ A)} (Q : z == cin i a) →
        ! (O₅ idp Q (ap f (! (glue (cin i a))) ∙ idp)) ∙
        (CMPH.coher1 {τ = left} {h = [id]} {v = ψ} {u = right} {f = f} (cglue g a) idp (λ x → ! (glue x)) (λ x₁ → idp) idp Q (! (glue (cin i a))) ∙
        CMPH.coher2 {τ = left} {h = [id]} {v = ψ} {u = right} {f = f} (cglue g a) idp (λ x → ! (glue x)) (λ x₁ → idp) idp Q (! (glue z))) ∙
        inv-canc-cmp f right (ap ψ Q) (! (glue z)) idp
          ==
        apd-tr-refl {f = f ∘ right} {h = ψ} Q
      CoherLemma idp = lemma (! (glue (cin i a)))
        where
          lemma : {x : P} (R : right (ψ (cin i a)) == x)
            →
            ! (O₅ {f = f ∘ right} {h = ψ} {b = cin i a} idp idp (ap f R ∙ idp)) ∙
            (fun-rid-inv1 {f = f} R ∙ fun-rid-inv2 {f = f} R) ∙
            inv-canc-cmp f right idp R idp
              ==
            idp
          lemma idp = idp

      ζ₂ : {k : A → ty T} (κ : f ∘ left ∼ k) →
        ! (O₅ idp (cglue g a) (ap f (! (glue (cin i a))) ∙ κ a)) ◃∙
        cmp-helper {f = f} (cglue g a) idp (λ x → ! (glue x)) κ ◃∙
        inv-canc-cmp f right (ap ψ (cglue g a)) (! (glue (cin j a))) (κ a) ◃∎
          =ₛ
        apd-tr-refl {f = f ∘ right} {h = ψ} (cglue g a) ◃∎
      ζ₂ {k} κ =
        ∼-ind
          (λ k₁ κ₁ →
            ! (O₅ idp (cglue g a) (ap f (! (glue (cin i a))) ∙ κ₁ a)) ◃∙
            cmp-helper {τ = left} {h = [id]} {v = ψ} {u = right} {f = f} (cglue g a) idp (λ x → ! (glue x)) κ₁ ◃∙
            inv-canc-cmp f right (ap ψ (cglue g a)) (! (glue (cin j a))) (κ₁ a) ◃∎
              =ₛ
            apd-tr-refl {f = f ∘ right} {h = ψ} (cglue g a) ◃∎)
          lemma k κ
        where
          lemma :
            ! (O₅ idp (cglue g a) (ap f (! (glue (cin i a))) ∙ idp)) ◃∙
            cmp-helper {τ = left} {h = [id]} {v = ψ} {u = right} {f = f} (cglue g a) idp (λ x → ! (glue x)) (λ x → idp) ◃∙
            inv-canc-cmp f right (ap ψ (cglue g a)) (! (glue (cin j a))) idp ◃∎
              =ₛ
            apd-tr-refl {f = f ∘ right} {h = ψ} (cglue g a) ◃∎
          lemma =
            ! (O₅ idp (cglue g a) (ap f (! (glue (cin i a))) ∙ idp)) ◃∙
            cmp-helper {τ = left} {h = [id]} {v = ψ} {u = right} {f = f} (cglue g a) idp (λ x → ! (glue x)) (λ x → idp) ◃∙
            inv-canc-cmp f right (ap ψ (cglue g a)) (! (glue (cin j a))) idp ◃∎
              =ₛ₁⟨ 1 & 1 &
                   ∼-ind-β
                     {P = λ m F →
                       ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap (f ∘ right) (ap ψ (cglue g a)) ∙ (ap f (! (glue (cin i a))) ∙ F a) ∙ idp) ∙ ! (ap f (! (glue (cin i a))) ∙ F a)
                         ==
                       ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ F a) ∙ ! (ap f (! (ap right (ap ψ (cglue g a))) ∙ ! (glue (cin j a)) ∙ idp) ∙ F a)}
                   (CMPH.coher1 {τ = left} {h = [id]} {v = ψ} {u = right} (cglue g a) idp (λ x → ! (glue x)) (λ x₁ → idp) idp (cglue g a) (! (glue (cin i a))) ∙
                   CMPH.coher2 {τ = left} {h = [id]} {v = ψ} {u = right} (cglue g a) idp (λ x → ! (glue x)) (λ x₁ → idp) idp (cglue g a) (! (glue (cin j a))) ) ⟩
              ! (O₅ idp (cglue g a) (ap f (! (glue (cin i a))) ∙ idp)) ◃∙
              (CMPH.coher1 {τ = left} {h = [id]} {v = ψ} {u = right} (cglue g a) idp (λ x → ! (glue x)) (λ x₁ → idp) idp (cglue g a) (! (glue (cin i a))) ∙
              CMPH.coher2 {τ = left} {h = [id]} {v = ψ} {u = right} (cglue g a) idp (λ x → ! (glue x)) (λ x₁ → idp) idp (cglue g a) (! (glue (cin j a)))) ◃∙
              inv-canc-cmp f right (ap ψ (cglue g a)) (! (glue (cin j a))) idp ◃∎
                =ₛ₁⟨ CoherLemma (cglue g a) ⟩
            apd-tr-refl {f = f ∘ right} {h = ψ} (cglue g a) ◃∎ ∎ₛ

    abstract

      Right-rw2a :
        ! (O₅ idp (cglue g a) (ap f (! (glue (cin i a))) ∙ fₚ a)) ◃∙
        ! (ap (λ p → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ p ∙ ! (ap f (! (glue (cin i a))) ∙ fₚ a))
          (O₄ {f = f ∘ right} {h = ψ} {u = str T} (λ x → ap f (! (glue x)) ∙ fₚ ([id] x)) (cglue g a) (id-βr g a))) ◃∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
          (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₃-v2 {f = left} {v = ψ} {u = right} (λ x → ! (glue x)) (cglue g a) (id-βr g a)))))) ◃∙
        inv-canc-cmp f right (ap ψ (cglue g a)) (! (glue (cin j (idf A a)))) (fₚ a) ◃∎                  
          =ₛ
        ! (O₅ idp (cglue g a) (ap f (! (glue (cin i a))) ∙ fₚ a)) ◃∙
        cmp-helper {f = f} (cglue g a) idp (λ x → ! (glue x)) fₚ ◃∙
        inv-canc-cmp f right (ap ψ (cglue g a)) (! (glue (cin j a))) (fₚ a) ◃∎
      Right-rw2a =
        ! (O₅ idp (cglue g a) (ap f (! (glue (cin i a))) ∙ fₚ a)) ◃∙
        ! (ap (λ p → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ p ∙ ! (ap f (! (glue (cin i a))) ∙ fₚ a))
          (O₄ {f = f ∘ right} {h = ψ} {u = str T} (λ x → ap f (! (glue x)) ∙ fₚ ([id] x)) (cglue g a) (id-βr g a))) ◃∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
          (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₃-v2 {f = left} {v = ψ} {u = right} (λ x → ! (glue x)) (cglue g a) (id-βr g a)))))) ◃∙
        inv-canc-cmp f right (ap ψ (cglue g a)) (! (glue (cin j (idf A a)))) (fₚ a) ◃∎
          =ₛ⟨ =ₛ-in
                (assoc4
                  (! (O₅ idp (cglue g a) (ap f (! (glue (cin i a))) ∙ fₚ a)))
                  (! (ap (λ p → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ p ∙ ! (ap f (! (glue (cin i a))) ∙ fₚ a))
                    (O₄ {f = f ∘ right} {h = ψ} {u = str T} (λ x → ap f (! (glue x)) ∙ fₚ ([id] x)) (cglue g a) (id-βr g a))))
                  (! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
                       (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₃-v2 {f = left} {v = ψ} {u = right} (λ x → ! (glue x)) (cglue g a) (id-βr g a)))))))
                  (inv-canc-cmp f right (ap ψ (cglue g a)) (! (glue (cin j (idf A a)))) (fₚ a)) ∙
                ap (λ r →
                     ! (O₅ idp (cglue g a) (ap f (! (glue (cin i a))) ∙ fₚ a)) ∙
                     r ∙
                     inv-canc-cmp f right (ap ψ (cglue g a)) (! (glue (cin j (idf A a)))) (fₚ a))
                   (𝕏 (cglue g a) (id-βr g a) (λ x → ! (glue x)) fₚ)) ⟩
         ! (O₅ idp (cglue g a) (ap f (! (glue (cin i a))) ∙ fₚ a)) ◃∙
         cmp-helper {f = f} (cglue g a) idp (λ x → ! (glue x)) fₚ ◃∙
         inv-canc-cmp f right (ap ψ (cglue g a)) (! (glue (cin j a))) (fₚ a) ◃∎ ∎ₛ
          where
            assoc4 : ∀ {lev : ULevel} {W : Type lev} {s w x y z : W} (p₁ : s == w) (p₂ : w == x) (p₃ : x == y) (p₄ : y == z)
              → p₁ ∙ p₂ ∙ p₃ ∙ p₄ == p₁ ∙ (p₂ ∙ p₃) ∙ p₄
            assoc4 idp idp idp p₄ = idp

      Right-rw₂ :
        seq-! (transpEq-◃ idp) ∙∙ apd-comp-ap {γ = RfunEq (f , fₚ)} (cglue g a) ◃∙
        ap (λ p → transport (λ x → f (right x) == H (right x)) p idp) (ψ-βr g a) ◃∙
        transp-over-∙ {F = λ x → f (right x) == H (right x)} {γ = RfunEq (f , fₚ)} (! (ap (cin j) (snd (F <#> g) a))) ◃∙
        ↯ (V f fₚ i j g (str (F # i) a)) ◃∎
          =ₛ
        ! (O₅ idp (cglue g a) (ap f (! (glue (cin i a))) ∙ fₚ a)) ◃∙
        ! (ap (λ p → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ p ∙ ! (ap f (! (glue (cin i a))) ∙ fₚ a))
            (O₄ (λ x → ap f (! (glue x)) ∙ fₚ ([id] x)) (cglue g a) (id-βr g a))) ◃∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
          (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₃-v2 (λ x → ! (glue x)) (cglue g a) (id-βr g a)))))) ◃∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₂-v2 (ψ-βr g a) (! (glue (cin j (idf A a))))))))) ◃∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₁-v2 (snd (F <#> g) a)))))) ◃∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (!-ap-ap-∘-ap-∙ f (right ∘ cin j) (snd (F <#> g) a) (ap right (cglue g (str (F # i) a)))))) ◃∙
        ! (O₂ {p = ! (ap (f ∘ right) (ap ψ (cglue g a)))} {g = cin j} {q = idp} (snd (F <#> g) a) (ap f (! (glue (cin j a))) ∙ fₚ a)
          (cglue g (str (F # i) a)) (recc-βr K g (str (F # i) a))) ◃∙
        ! (O₁ {g = H ∘ right} idp (cglue g a) (ψ-βr g a)) ◃∙
        apd-comp-ap {γ = RfunEq (f , fₚ)} (cglue g a) ◃∙
        ap (λ p → transport (λ x → f (right x) == H (right x)) p idp) (ψ-βr g a) ◃∙
        transp-over-∙ {γ = RfunEq (f , fₚ)} (! (ap (cin j) (snd (F <#> g) a))) ◃∙
        (transp-pth (cglue g (str (F # i) a)) idp ∙
        ap (_∙_ (! (ap (f ∘ right) (cglue g (str (F # i) a))))) (recc-βr (PostComp-cos ColCoC-cos (f , fₚ)) g (str (F # i) a)) ∙
        cmp-inv-l {f = right} {g = f} (cglue g (str (F # i) a))) ◃∎ 
      Right-rw₂ =
        seq-! (transpEq-◃ idp) ∙∙ apd-comp-ap {γ = RfunEq (f , fₚ)} (cglue g a) ◃∙
        ap (λ p → transport (λ x → f (right x) == H (right x)) p idp) (ψ-βr g a) ◃∙
        transp-over-∙ {F = λ x → f (right x) == H (right x)} {γ = RfunEq (f , fₚ)} (! (ap (cin j) (snd (F <#> g) a))) ◃∙
        ↯ (V f fₚ i j g (str (F # i) a)) ◃∎
          =ₛ⟨ 2 & 1 &  PathSeq2 F g a T f fₚ ⟩
        ! (O₅ idp (cglue g a) (ap f (! (glue (cin i a))) ∙ fₚ a)) ◃∙
        ! (ap (λ p → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ p ∙ ! (ap f (! (glue (cin i a))) ∙ fₚ a))
            (O₄ (λ x → ap f (! (glue x)) ∙ fₚ ([id] x)) (cglue g a) (id-βr g a))) ◃∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₃-v2 (λ x → ! (glue x)) (cglue g a) (id-βr g a)))))) ◃∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₂-v2 (ψ-βr g a) (! (glue (cin j (idf A a))))))))) ◃∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₁-v2 (snd (F <#> g) a)))))) ◃∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (!-ap-ap-∘-ap-∙ f (right ∘ cin j) (snd (F <#> g) a) (ap right (cglue g (str (F # i) a)))))) ◃∙
        ! (O₂ {p = ! (ap (f ∘ right) (ap ψ (cglue g a)))} {g = cin j} {q = idp} (snd (F <#> g) a) (ap f (! (glue (cin j a))) ∙ fₚ a)
          (cglue g (str (F # i) a)) (recc-βr K g (str (F # i) a))) ◃∙
        ! (O₁ {g = H ∘ right} idp (cglue g a) (ψ-βr g a)) ◃∙
        apd-comp-ap {γ = RfunEq (f , fₚ)} (cglue g a) ◃∙
        ap (λ p → transport (λ x → f (right x) == H (right x)) p idp) (ψ-βr g a) ◃∙
        transp-over-∙ {γ = RfunEq (f , fₚ)} (! (ap (cin j) (snd (F <#> g) a))) ◃∙
        (transp-pth (cglue g (str (F # i) a)) idp ∙
        ap (_∙_ (! (ap (f ∘ right) (cglue g (str (F # i) a))))) (recc-βr (PostComp-cos ColCoC-cos (f , fₚ)) g (str (F # i) a)) ∙
        cmp-inv-l {f = right} {g = f} (cglue g (str (F # i) a))) ◃∎ ∎ₛ

    abstract
      ζ₁ : {x : Colim (ConsDiag Γ A)} (Q : cin j a == x) {w : ty (F # j)} (u : w == str (F # j) a)
        (v : cin j w == ψ x) (T₁ : ap ψ Q == ! (ap (cin j) u) ∙ v)
        {L : f (right (cin j w)) == reccForg K (ψ x)} (T₂ : ap (reccForg K) v == L)
        {z : ty T} (σ : f (right (cin j (str (F # j) a))) == z) →
        ! (O₂ {p = ! (ap (f ∘ right) (ap ψ Q))} {g = cin j} {q = idp} u σ v T₂) ∙
        ! (O₁ {g = H ∘ right} idp Q T₁) ∙
        apd-comp-ap {γ = RfunEq (f , fₚ)} Q ∙
        ap (λ p → transport (λ x → f (right x) == H (right x)) p idp) T₁ ∙
        transp-over-∙ {γ = RfunEq (f , fₚ)} (! (ap (cin j) u)) ∙
        transp-pth v idp ∙
        ap (λ p → ! (ap (f ∘ right) v) ∙ p) T₂
          ==
        ∙-∙-!-!-∙-ap-∘-∙ u L σ v (ap (λ p → ! (ap (f ∘ right) p)) T₁)
      ζ₁ idp idp v T₁ idp idp = lemma T₁
        where
          lemma : {V : ψ (cin j a) == ψ (cin j a)} (T : idp == V)
            → ! (O₂ {p = idp} {g = cin j} {q = idp} idp idp V idp) ∙
              ! (O₁ {f = f ∘ right} {h = ψ} {b = cin j a} idp idp T) ∙
              ap (λ p → transport (λ x → f (right x) == H (right x)) p idp) T ∙
              transp-pth V (RfunEq (f , fₚ) (cin j (str (F # j) a))) ∙ idp
                ==
              ∙-∙-!-!-∙-ap-∘-∙ {g = cin j} idp (ap (reccForg K) V) idp V (ap (λ p → ! (ap (f ∘ right) p)) T)
          lemma idp = idp

    abstract
      Right-rw1a :
        ! (O₅ idp (cglue g a) (ap f (! (glue (cin i a))) ∙ fₚ a)) ◃∙
        ! (ap (λ p → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ p ∙ ! (ap f (! (glue (cin i a))) ∙ fₚ a))
            (O₄ (λ x → ap f (! (glue x)) ∙ fₚ ([id] x)) (cglue g a) (id-βr g a))) ◃∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
          (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₃-v2 (λ x → ! (glue x)) (cglue g a) (id-βr g a)))))) ◃∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₂-v2 (ψ-βr g a) (! (glue (cin j (idf A a))))))))) ◃∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₁-v2 (snd (F <#> g) a)))))) ◃∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (!-ap-ap-∘-ap-∙ f (right ∘ cin j) (snd (F <#> g) a) (ap right (cglue g (str (F # i) a)))))) ◃∙
        ! (O₂ {p = ! (ap (f ∘ right) (ap ψ (cglue g a)))} {g = cin j} {q = idp} (snd (F <#> g) a) (ap f (! (glue (cin j a))) ∙ fₚ a)
          (cglue g (str (F # i) a)) (recc-βr K g (str (F # i) a))) ◃∙
        ! (O₁ {g = H ∘ right} idp (cglue g a) (ψ-βr g a)) ◃∙
        apd-comp-ap {γ = RfunEq (f , fₚ)} (cglue g a) ◃∙
        ap (λ p → transport (λ x → f (right x) == H (right x)) p idp) (ψ-βr g a) ◃∙
        transp-over-∙ {γ = RfunEq (f , fₚ)} (! (ap (cin j) (snd (F <#> g) a))) ◃∙
        (transp-pth (cglue g (str (F # i) a)) idp ∙
        ap (_∙_ (! (ap (f ∘ right) (cglue g (str (F # i) a))))) (recc-βr (PostComp-cos ColCoC-cos (f , fₚ)) g (str (F # i) a)) ∙
        cmp-inv-l {f = right} {g = f} (cglue g (str (F # i) a))) ◃∎
          =ₛ
        (! (O₅ idp (cglue g a) (ap f (! (glue (cin i a))) ∙ fₚ a)) ∙
        ! (ap (λ p → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ p ∙ ! (ap f (! (glue (cin i a))) ∙ fₚ a))
            (O₄ (λ x → ap f (! (glue x)) ∙ fₚ ([id] x)) (cglue g a) (id-βr g a)) ) ∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₃-v2 (λ x → ! (glue x)) (cglue g a) (id-βr g a)))))) ∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₂-v2 (ψ-βr g a) (! (glue (cin j (idf A a))))))))) ∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₁-v2 (snd (F <#> g) a)))))) ∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (!-ap-ap-∘-ap-∙ f (right ∘ cin j) (snd (F <#> g) a) (ap right (cglue g (str (F # i) a)))))) ∙
        ! (O₂ {p = ! (ap (f ∘ right) (ap ψ (cglue g a)))} {g = cin j} {q = idp} (snd (F <#> g) a) (ap f (! (glue (cin j a))) ∙ fₚ a)
          (cglue g (str (F # i) a)) (recc-βr K g (str (F # i) a))) ∙
        ! (O₁ {g = H ∘ right} idp (cglue g a) (ψ-βr g a)) ∙
        apd-comp-ap {γ = RfunEq (f , fₚ)} (cglue g a) ∙
        ap (λ p → transport (λ x → f (right x) == H (right x)) p idp) (ψ-βr g a) ∙
        transp-over-∙ {γ = RfunEq (f , fₚ)} (! (ap (cin j) (snd (F <#> g) a))) ∙
        (transp-pth (cglue g (str (F # i) a)) idp ∙
        ap (_∙_ (! (ap (f ∘ right) (cglue g (str (F # i) a))))) (recc-βr (PostComp-cos ColCoC-cos (f , fₚ)) g (str (F # i) a)) ∙
        cmp-inv-l {f = right} {g = f} (cglue g (str (F # i) a)))) ◃∎
      Right-rw1a = =ₛ-in idp      

    abstract
      Right-rw₁ :
        ! (↯ (transpEq-◃ idp)) ◃∙ apd-tr (λ x → RfunEq (f , fₚ) (ψ x)) (cglue g a) ◃∎
          =ₛ
        seq-! (transpEq-◃ idp) ∙∙ apd-comp-ap {γ = RfunEq (f , fₚ)} (cglue g a) ◃∙
        ap (λ p → transport (λ x → f (right x) == H (right x)) p idp) (ψ-βr g a) ◃∙
        transp-over-∙ {F = λ x → f (right x) == H (right x)} {γ = RfunEq (f , fₚ)} (! (ap (cin j) (snd (F <#> g) a))) ◃∙
        ↯ (V f fₚ i j g (str (F # i) a)) ◃∎ 
      Right-rw₁ =
        ! (↯ (transpEq-◃ idp)) ◃∙
        apd-tr (λ x → RfunEq (f , fₚ) (ψ x)) (cglue g a) ◃∎
          =ₛ⟨ 1 & 1 & apd-rw2 ⟩
        ! (↯ (transpEq-◃ idp)) ◃∙
        apd-comp-ap {γ = RfunEq (f , fₚ)} (cglue g a) ◃∙
        ap (λ p → transport (λ x → f (right x) == H (right x)) p idp) (ψ-βr g a) ◃∙
        transp-over-∙ {F = λ x → f (right x) == H (right x)} {γ = RfunEq (f , fₚ)} (! (ap (cin j) (snd (F <#> g) a))) ◃∙
        ↯ (V f fₚ i j g (str (F # i) a)) ◃∎
          =ₛ⟨ 0 & 1 & !-∙-seq (transpEq-◃ idp) ⟩
        seq-! (transpEq-◃ idp) ∙∙ apd-comp-ap {γ = RfunEq (f , fₚ)} (cglue g a) ◃∙
        ap (λ p → transport (λ x → f (right x) == H (right x)) p idp) (ψ-βr g a) ◃∙
        transp-over-∙ {F = λ x → f (right x) == H (right x)} {γ = RfunEq (f , fₚ)} (! (ap (cin j) (snd (F <#> g) a))) ◃∙
        ↯ (V f fₚ i j g (str (F # i) a)) ◃∎ ∎ₛ
