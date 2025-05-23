{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.SIP
open import SIP-Cos
module AuxPaths-v2 where

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B} {x : A} {z : B} where

  E₁-v2 : ∀ {ℓ₃} {C : Type ℓ₃} {g : C → A} {c d : C} {R : g c == x} {S : f (g d) == z} (Q : c == d)
    → ! (ap f R) ∙ ap (f ∘ g) Q ∙ S == ! (ap f (! (ap g Q) ∙ R)) ∙ S
  E₁-v2 idp = idp

  E₂-v2 : {y : A} {p q : x == y} (R : p == q) (S : f x == z)
    → ! (ap f q)  ∙ S == ! (ap f p) ∙ S ∙ idp
  E₂-v2 idp idp = idp

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B} {C : Type ℓ₃} {D : Type ℓ₄}
  {h : C → A} {v : C → D} {u : D → B} where

  E₃-v2 : (q : (z : C) →  u (v z) == f (h z)) {x y : C} (p : x == y) {S : h x == h y} (T : ap h p == S)
    → ! (ap u (ap v p)) ∙ q x ∙ ap f S == q y
  E₃-v2 q {x = x} idp idp = ∙-unit-r (q x)

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {f g : C → A} {h : B → C} {b : B} (s : f (h b) == g (h b)) where

  O₁ : {x : B} (Q : b == x) {R : h b == h x} (T : ap h Q == R)
    → transport (λ x → f (h x) == g (h x)) Q s == ! (ap f (ap h Q)) ∙ s ∙ ap g R
  O₁ idp idp = ! (∙-unit-r s)

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {a x : C} {p : a == x} {g : B → A} {f : A → C} {z : B} {q : x == f (g z)} where

  O₂ : {w : B} (u : w == z) {y : C} (s : f (g z) == y) {t : A} (v : g w == t) {R : f (g w) == f t} (T : ap f v == R)
    → p ∙ q ∙ ap f (! (ap g u) ∙ v) == p ∙ q ∙ s ∙ ! (! R ∙ ap (f ∘ g) u ∙ s)
  O₂ idp idp idp idp = idp

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B} {C : Type ℓ₃} {D : Type ℓ₄} {h : C → A} {v : C → D} {u : D → B} {c : C} where

  O₄ : (q : (x : C) → f (h x) == u (v x)) {d : C} (p : c == d) {S : v c == v d} (R : ap v p == S)
    → q c == ap f (ap h p) ∙ q d ∙ ! (ap u S)
  O₄ q idp idp = ! (∙-unit-r (q c))

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {f : C → A} {h : B → C} {b : B} where

  O₅ : (s : f (h b) == f (h b)) {x : B} (K : b == x) {a : A} (r : f (h x) == a)
    → ! (ap f (ap h K)) ∙ s ∙ (ap f (ap h K) ∙ r ∙ idp) ∙ ! r  == transport (λ x → f (h x) == f (h x)) K s
  O₅ s idp idp = ∙-unit-r s

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {g : B → A} {f : A → C}  where

  Δ-red : {t u : B} (v : t == u) {c : C} (R : f (g t) == c) {d : C} (σ : f (g u) == d) {z : A} (D : g t == z)
    {W : f z == f (g u)} (τ : W == ! (ap f (! (ap g v) ∙ D)))
    → W ∙ σ ∙ ! (! R ∙ (ap (f ∘ g) v) ∙ σ) == ! (ap f D) ∙ R
  Δ-red idp idp idp idp idp = idp

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄} {h : D → A} {g : A → B} {f : B → C} where

  abstract
    𝕐 : {c d : D} (Q : c == d) {x : A} (R₁ : h c == x) {z : B} (S : g (h d) == z) {p : h d == x}
      (R₂ : p == ! (ap h Q) ∙ R₁) {w : C} (fₚ : f z == w)
      →
      ! (ap (λ q → ! (ap (f ∘ g) p) ∙ (ap f S ∙ fₚ) ∙ q) (ap ! (ap (λ q → q ∙ fₚ) (ap (ap f) (E₂-v2 {p = p} R₂ S))))) ∙
      ! (ap (λ q → ! (ap (f ∘ g) p) ∙ (ap f S ∙ fₚ) ∙ q) (ap ! (ap (λ q → q ∙ fₚ) (ap (ap f) (E₁-v2 {g = h} {R = R₁} Q))))) ∙
      ! (ap (λ q → ! (ap (f ∘ g) p) ∙ (ap f S ∙ fₚ) ∙ q) (ap ! (!-ap-ap-∘-ap-∙ f (g ∘ h) Q (ap g R₁)))) ∙
      Δ-red Q (ap f (ap g R₁)) (ap f S ∙ fₚ) R₁ (ap (λ q → ! (ap (f ∘ g) q)) R₂) ∙ cmp-inv-l {f = g} {g = f} R₁
        ==
      inv-canc-cmp f g p S fₚ
    𝕐 idp idp idp idp idp = idp 

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄} {E : Type ℓ₅}
  {τ : A → B} {h : C → A} {v : C → D} {u : D → B} {f : B → E} where

  abstract
    𝕏 : {x y : C} (p : x == y) {S : h x == h y} (T : ap h p == S) (r : (z : C) →  u (v z) == τ (h z)) {k : A → E} (fₚ : f ∘ τ ∼ k)
      →
      ! (ap (λ q → ! (ap (f ∘ u) (ap v p)) ∙ q ∙ ap k S ∙ ! (ap f (r y) ∙ fₚ (h y)))
          (O₄ {f = f ∘ u} {h = v} {u = k} (λ z → ap f (r z) ∙ fₚ (h z)) p T)) ∙
      ! (ap (λ q → ! (ap (f ∘ u) (ap v p)) ∙ (ap f (r x) ∙ fₚ (h x)) ∙ ap k S ∙ q)
          (ap ! (ap (λ q → q ∙ fₚ (h y)) (ap (ap f) (E₃-v2 {f = τ} {v = v} {u = u} r p T)))))
        ==
      cmp-helper {f = f} p S r fₚ
    𝕏 {x = x} idp idp r {k = k} fₚ =
      ∼-ind
        (λ g F →
          ! (ap (λ q → q ∙ ! (ap f (r x) ∙ F (h x))) (! (∙-unit-r (ap f (r x) ∙ F (h x))))) ∙
          ! (ap (λ q → (ap f (r x) ∙ F (h x)) ∙ q) (ap ! (ap (λ q → q ∙ F (h x))
            (ap (ap f) (∙-unit-r (r x))))))
            ==
          cmp-helper {v = v} {u = u} {f = f} idp idp r {k = g} F)
        (ap-pth-unitr {τ = τ} {h = h} {v = v} {u = u} {f = f} x r ∙
        ! (∼-ind-β
            {P = λ _ G → ((ap f (r x) ∙ G (h x)) ∙ idp) ∙ ! (ap f (r x) ∙ G (h x)) == (ap f (r x) ∙ G (h x)) ∙ ! (ap f (r x ∙ idp) ∙ G (h x))}
            (CMPH.coher1 {τ = τ} {h = h} {v = v} {u = u} {x = x} idp idp r (λ x₁ → idp) idp idp (r x) ∙
             CMPH.coher2 {τ = τ} {h = h} {v = v} {u = u} {x = x} idp idp r (λ x₁ → idp) idp idp (r x))))
        k fₚ
