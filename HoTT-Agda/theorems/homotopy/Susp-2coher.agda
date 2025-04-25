{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.PtdMap-conv
open import lib.types.Pushout
open import lib.types.Suspension
open import lib.types.LoopSpace
open import lib.types.Homogeneous
open import homotopy.SuspAdjointLoop
open import lib.wild-cats.WildCat
open import lib.wild-cats.Ptd-wc
open import lib.wild-cats.Adjoint
open import lib.wild-cats.Ladj-2-coher
open import lib.wild-cats.Ladj-colim

{- the nat-dom proof makes Susp a 2-coherent left adjoint to Loop -}

module homotopy.Susp-2coher where

-- an ad-hoc data structure for a messy computation required by our 2-coherence proof

module _ {i j k l ℓ} {A : Type i} {B : Type j} {C : Type k} {D : Type l} {E : Type ℓ}
  (m : A → D) (n : B → A) (s : C → A) (r : E → C) where

  record sev_step_red_inp {x₁ x₂ : D} {x₃ x₄ : A} {x₅ x₆ x₇ : B} {x₈ x₁₃ : C}
    {x₉ x₁₀ x₁₁ x₁₂ : E} (q₁ : x₁ == m x₃) (q₂ : x₄ == n x₅) (q₃ : x₅ == x₆)
    (q₄ : x₆ == x₇) {b : B} (q₅ : x₇ == b) (ϕ : n b  == s x₈) (q₆ : x₈ == r x₉)
    (q₇ : x₉ == x₁₀) (q₈ : x₁₀ == x₁₁) (q₉ : x₁₁ == x₁₂) (q₁₀ : r x₁₂ == x₁₃)
    (q₁₁ : s x₁₃ == x₃) (q₁₂ : m x₄ == x₂) (τ : x₁ == x₂)
    {d₀ d₁ d₂ d₃ d₄ d₅ d₆ d₇ : D}
    (μ₁ : d₀ == d₁) (μ₂ : d₃ == d₄) (μ₃ : d₀ == d₆)
    (p₁ : d₁ == d₂) (p₂ : d₂ == d₃) (p₃ : d₄ == d₅)
    (p₄ : d₅ == x₁) (p₅ : d₆ == d₇) (p₆ : d₇ == x₂)
    {R₁ : d₃ == m (s (r x₁₁))} {R₂ : d₃ == m (n x₇)} {R₃ : d₀ == m (n x₇)}
    {R₄ : d₀ == m (n x₆)} {R₅ : m (n x₆) == d₇}
      : Type (lmax i (lmax j (lmax k l))) where
    constructor sev_step
    field
      red1 : τ == ((q₁ ∙ ! (ap m (q₂ ∙ ap n (q₃ ∙ q₄ ∙ q₅) ∙ ϕ ∙
        ap s (q₆ ∙ ap r (q₇ ∙ q₈ ∙ q₉) ∙ q₁₀) ∙ q₁₁)) ∙ q₁₂) ∙ idp) ∙ idp
      red2 : μ₂ ∙ p₃ ∙ p₄ ∙ q₁ ∙ ! (ap m (ap s (ap r q₉ ∙ q₁₀) ∙ q₁₁)) == R₁
      red3 : R₁ ∙ ! (ap m (ap n q₅ ∙ ϕ ∙ ap s (q₆ ∙ ap r (q₇ ∙ q₈)))) == R₂
      red4 : μ₁ ∙ p₁ ∙ p₂ ∙ R₂ == R₃
      red5 : R₃ ∙ ! (ap m (ap n q₄)) == R₄
      red6 : ! (ap m (q₂ ∙ ap n q₃)) ∙ q₁₂ ∙ ! p₆ == R₅
      red7 : R₄ ∙ R₅ ∙ ! p₅ ∙ ! μ₃ == idp
  open sev_step_red_inp public

module Reduce {i j k l ℓ} {A : Type i} {B : Type j} {C : Type k} {D : Type l} {E : Type ℓ}
  {m : A → D} {n : B → A} {s : C → A} {r : E → C} where

  abstract
    sev_step_reduce : {x₁ x₂ : D} {x₃ x₄ : A} {x₅ x₆ x₇ : B} {x₈ x₁₃ : C}
      {x₉ x₁₀ x₁₁ x₁₂ : E} {q₁ : x₁ == m x₃} {q₂ : x₄ == n x₅} {q₃ : x₅ == x₆}
      {q₄ : x₆ == x₇} {b : B} {q₅ : x₇ == b} {ϕ : n b  == s x₈} {q₆ : x₈ == r x₉}
      {q₇ : x₉ == x₁₀} {q₈ : x₁₀ == x₁₁} {q₉ : x₁₁ == x₁₂} {q₁₀ : r x₁₂ == x₁₃}
      {q₁₁ : s x₁₃ == x₃} {q₁₂ : m x₄ == x₂} {τ : x₁ == x₂}
      {d₀ d₁ d₂ d₃ d₄ d₅ d₆ d₇ : D}
      {μ₁ : d₀ == d₁} {μ₂ : d₃ == d₄} {μ₃ : d₀ == d₆}
      {p₁ : d₁ == d₂} {p₂ : d₂ == d₃} {p₃ : d₄ == d₅}
      {p₄ : d₅ == x₁} {p₅ : d₆ == d₇} {p₆ : d₇ == x₂}
      {R₁ : d₃ == m (s (r x₁₁))} {R₂ : d₃ == m (n x₇)} {R₃ : d₀ == m (n x₇)}
      {R₄ : d₀ == m (n x₆)} {R₅ : m (n x₆) == d₇}
      → sev_step_red_inp m n s r q₁ q₂ q₃ q₄ q₅ ϕ
        q₆ q₇ q₈ q₉ q₁₀ q₁₁ q₁₂ τ μ₁ μ₂ μ₃
        p₁ p₂ p₃ p₄ p₅ p₆ {R₁} {R₂} {R₃} {R₄} {R₅}
      → (μ₁ ∙ p₁ ∙ p₂) ∙ (μ₂ ∙ p₃ ∙ p₄) ∙ τ ∙ ! (μ₃ ∙ p₅ ∙ p₆) == idp
    sev_step_reduce {q₁ = idp} {idp} {idp} {idp} {q₅ = idp}
      {ϕ} {idp} {idp} {idp} {idp} {idp} {idp} {idp} {μ₁ = idp}
      {idp} {idp} {idp} {idp} {idp} {idp} {idp} {p₆}
      (sev_step idp idp idp idp idp idp red7) =
        ap (λ p → p ∙ ! p₆)
          (∙-unit-r ((! (ap m (ϕ ∙ idp)) ∙ idp) ∙ idp) ∙ ∙-unit-r (! (ap m (ϕ ∙ idp)) ∙ idp)) ∙
        ap (λ p → (! (ap m (ϕ ∙ idp)) ∙ idp) ∙ p) (! (∙-unit-r (! p₆))) ∙
        red7

module 2-coher-cmp {i₁ i₂ i₃ i₄} {X : Ptd i₁} {Y : Ptd i₂} {Z : Ptd i₃} {W : Ptd i₄} where

  open Reduce

  -- unfolded version of naturality square for Susp-fmap-∘

  module _ (f₂ : de⊙ Z → de⊙ X) (f₃ : de⊙ W → de⊙ Z) (f₁ : Susp (de⊙ X) → de⊙ Y)
    (x : de⊙ W) where 

    β-free1 : {x : Susp (de⊙ Z)} {ω₁ : left unit == right unit}
      (ω₂ : x == right unit) (ω₃ : left unit == right unit)
      (ω₄ : ap (Susp-fmap f₃) ω₃ == ω₁) →
      ap (f₁ ∘ Susp-fmap f₂) (ω₁ ∙ ! ω₂)
      ==
      ap f₁ (ap (Susp-fmap f₂ ∘ Susp-fmap f₃) ω₃ ∙
        ! (ap (Susp-fmap f₂) ω₂))
    β-free1 {ω₁ = ω₁} ω₂ ω₃ ω₄ =
      ap-∘ f₁ (Susp-fmap f₂) (ω₁ ∙ ! ω₂) ∙
      ap (ap f₁) (ap-∙ (Susp-fmap f₂) ω₁ (! ω₂)) ∙
      ! (ap (ap f₁) (ap (λ p → p ∙ ap (Susp-fmap f₂) (! ω₂))
        (ap-∘ (Susp-fmap f₂) (Susp-fmap f₃) ω₃ ∙
        ap (ap (Susp-fmap f₂)) ω₄))) ∙
      ap (ap f₁) (ap (λ p → ap (Susp-fmap f₂ ∘ Susp-fmap f₃) ω₃ ∙ p)
        (ap-! (Susp-fmap f₂) ω₂))

    β-red1-aux2 : {w : Susp (de⊙ W)} (ω₆ : left unit == w)
      {𝕗 : ap f₁ (! (SuspMapEq (Susp-fmap (f₂ ∘ f₃))
        (Susp-fmap f₂ ∘ Susp-fmap f₃) idp idp (λ x → ↯ (Susp-fmap-∘ f₂ f₃ x)) w)) ∙
      ap f₁ (SuspMapEq (Susp-fmap (f₂ ∘ f₃)) (Susp-fmap f₂ ∘ Susp-fmap f₃)
        idp idp (λ x → ↯ (Susp-fmap-∘ f₂ f₃ x)) w ∙
        ap (Susp-fmap f₂ ∘ Susp-fmap f₃) (! ω₆))
      == ap f₁ (ap (Susp-fmap f₂ ∘ Susp-fmap f₃) (! ω₆))}
      (𝕣 : 𝕗 == ap-!-∙-ap f₁ (Susp-fmap f₂ ∘ Susp-fmap f₃) (! ω₆)
        (SuspMapEq (Susp-fmap (f₂ ∘ f₃)) (Susp-fmap f₂ ∘ Susp-fmap f₃)
        idp idp (λ x → ↯ (Susp-fmap-∘ f₂ f₃ x)) w)) →
      (! (ap (λ q → q) (ap-∘ (f₁ ∘ Susp-fmap f₂) (Susp-fmap f₃) (! ω₆) ∙
        ap (ap (f₁ ∘ Susp-fmap f₂)) (ap-! (Susp-fmap f₃) ω₆))) ∙ idp) ∙
      ap-∘-long f₁ (Susp-fmap f₂ ∘ Susp-fmap f₃) (Susp-fmap (f₂ ∘ f₃))
        (SuspMapEq (Susp-fmap (f₂ ∘ f₃)) (Susp-fmap f₂ ∘ Susp-fmap f₃)
        idp idp (λ x → ↯ (Susp-fmap-∘ f₂ f₃ x))) (! ω₆) ∙
      𝕗 ∙ 
      ! (ap (ap f₁) (ap (λ q → q) (ap ! (! (ap-∘ (Susp-fmap f₂) (Susp-fmap f₃) ω₆)) ∙
        !-ap (Susp-fmap f₂ ∘ Susp-fmap f₃) ω₆) ∙ idp))
      ==
      ap-∘ f₁ (Susp-fmap f₂) (! (ap (Susp-fmap f₃) ω₆)) ∙
      ap (ap f₁) (ap (λ q → q) (ap-! (Susp-fmap f₂) (ap (Susp-fmap f₃) ω₆)))
    β-red1-aux2 idp idp = idp

    β-red1-aux : {w : Susp (de⊙ W)} (ω₃ ω₆ : left unit == w) →
      ap-∙ (f₁ ∘ Susp-fmap f₂) (ap (Susp-fmap f₃) ω₃)
        (! (ap (Susp-fmap f₃) ω₆)) ∙
      (! (ap (_∙_ (ap (f₁ ∘ Susp-fmap f₂) (ap (Susp-fmap f₃) ω₃)))
        (ap-∘ (f₁ ∘ Susp-fmap f₂) (Susp-fmap f₃) (! ω₆) ∙
        ap (ap (f₁ ∘ Susp-fmap f₂)) (ap-! (Susp-fmap f₃) ω₆))) ∙
      ! (ap (λ p → p ∙ ap (f₁ ∘ Susp-fmap f₂ ∘ Susp-fmap f₃) (! ω₆))
        (ap-∘ (f₁ ∘ Susp-fmap f₂) (Susp-fmap f₃) ω₃)) ∙
      ! (ap-∙ (f₁ ∘ Susp-fmap f₂ ∘ Susp-fmap f₃) ω₃ (! ω₆))) ∙
      ap-∘-long f₁ (Susp-fmap f₂ ∘ Susp-fmap f₃) (Susp-fmap (f₂ ∘ f₃))
        (SuspMapEq (Susp-fmap (f₂ ∘ f₃)) (Susp-fmap f₂ ∘ Susp-fmap f₃)
        idp idp (λ x → ↯ (Susp-fmap-∘ f₂ f₃ x))) (ω₃ ∙ ! ω₆) ∙
      ! (ap (ap f₁) (ap (_∙_ (ap (Susp-fmap f₂ ∘ Susp-fmap f₃) ω₃))
        (ap ! (! (ap-∘ (Susp-fmap f₂) (Susp-fmap f₃) ω₆)) ∙
        !-ap (Susp-fmap f₂ ∘ Susp-fmap f₃) ω₆) ∙
        ap (λ p → p) (! (ap-∙ (Susp-fmap f₂ ∘ Susp-fmap f₃) ω₃ (! ω₆)))))
      ==
      ap-∘ f₁ (Susp-fmap f₂) ((ap (Susp-fmap f₃) ω₃) ∙
        ! (ap (Susp-fmap f₃) ω₆)) ∙
      ap (ap f₁) (ap-∙ (Susp-fmap f₂) (ap (Susp-fmap f₃) ω₃)
        (! (ap (Susp-fmap f₃) ω₆))) ∙
      ! (ap (ap f₁) (ap (λ p → p ∙ ap (Susp-fmap f₂) (! (ap (Susp-fmap f₃) ω₆)))
        (ap-∘ (Susp-fmap f₂) (Susp-fmap f₃) ω₃ ∙ idp))) ∙
      ap (ap f₁) (ap (λ p → ap (Susp-fmap f₂ ∘ Susp-fmap f₃) ω₃ ∙ p)
        (ap-! (Susp-fmap f₂) (ap (Susp-fmap f₃) ω₆)))
    β-red1-aux idp ω₆ = β-red1-aux2 ω₆ idp
 
    β-red1 : {ω₁ ω₂ : left unit == right unit}
      (ω₃ : left unit == right unit) (ω₄ : ap (Susp-fmap f₃) ω₃ == ω₁)
      (ω₆ : left unit == right unit) (ω₅ : ap (Susp-fmap f₃) ω₆ == ω₂) → 
      ap-∙ (f₁ ∘ Susp-fmap f₂) ω₁ (! ω₂) ∙
      ! (ap (_∙_ (ap (f₁ ∘ Susp-fmap f₂) ω₁))
        (ap (λ p → ap (f₁ ∘ Susp-fmap f₂) (! p)) ω₅)) ∙
      (! (ap (_∙_ (ap (f₁ ∘ Susp-fmap f₂) ω₁))
        (ap-∘ (f₁ ∘ Susp-fmap f₂) (Susp-fmap f₃) (! ω₆) ∙
        ap (ap (f₁ ∘ Susp-fmap f₂)) (ap-! (Susp-fmap f₃) ω₆))) ∙
      ! (ap (λ p → ap (f₁ ∘ Susp-fmap f₂) p ∙ ap ((f₁ ∘ Susp-fmap f₂) ∘ Susp-fmap f₃)
        (! ω₆)) ω₄) ∙
      ! (ap (λ p → p ∙ ap (f₁ ∘ Susp-fmap f₂ ∘ Susp-fmap f₃) (! ω₆))
        (ap-∘ (f₁ ∘ Susp-fmap f₂) (Susp-fmap f₃) ω₃)) ∙
      ! (ap-∙ (f₁ ∘ Susp-fmap f₂ ∘ Susp-fmap f₃) ω₃ (! ω₆))) ∙
      ap-∘-long f₁ (Susp-fmap f₂ ∘ Susp-fmap f₃) (Susp-fmap (f₂ ∘ f₃))
        (SuspMapEq (Susp-fmap (f₂ ∘ f₃)) (Susp-fmap f₂ ∘ Susp-fmap f₃)
        idp idp (λ x → ↯ (Susp-fmap-∘ f₂ f₃ x))) (ω₃ ∙ ! ω₆) ∙
      ! (ap (ap f₁) (ap (λ p → ap (Susp-fmap f₂ ∘ Susp-fmap f₃) ω₃ ∙ p)
          (ap ! (! (ap (ap (Susp-fmap f₂)) ω₅) ∙
          ! (ap-∘ (Susp-fmap f₂) (Susp-fmap f₃) ω₆)) ∙
          !-ap (Susp-fmap f₂ ∘ Susp-fmap f₃) ω₆) ∙
        ap (λ p → p) (! (ap-∙ (Susp-fmap f₂ ∘ Susp-fmap f₃) ω₃
          (! ω₆)))))
      == β-free1 ω₂ ω₃ ω₄
    β-red1 ω₃ idp ω₆ idp = β-red1-aux ω₃ ω₆

    β-free2 : {x₁ x₂ x₃ : Susp (de⊙ Z)} (ω₁ : x₂ == x₃)
      (ω₂ : x₁ == x₃) {ω₇ : Susp-fmap f₂ x₃ == Susp-fmap f₂ x₁}
      (ω₈ : ω₇ == ! (ap (Susp-fmap f₂) ω₂)) → 
      ap (f₁ ∘ Susp-fmap f₂) (ω₁ ∙ ! ω₂)
      ==
      ap f₁ (ap (Susp-fmap f₂) ω₁ ∙ ω₇)
    β-free2 ω₁ ω₂ ω₈ =
      ap-∘ f₁ (Susp-fmap f₂) (ω₁ ∙ ! ω₂) ∙
      ap (ap f₁) (ap-∙ (Susp-fmap f₂) ω₁ (! ω₂)) ∙
      ap (ap f₁) (ap (λ p → ap (Susp-fmap f₂) ω₁ ∙ p) (ap-! (Susp-fmap f₂) ω₂)) ∙
      ap (ap f₁) (ap (λ p → ap (Susp-fmap f₂) ω₁ ∙ p) (! ω₈))

    β-red2-aux2 : {x₁ x₂ : Susp (de⊙ Z)} (ω₂ : x₁ == x₂)
      {c : Susp-fmap f₂ x₂ == Susp-fmap f₂ x₁}
      (↑ω₈ : c == ! (ap (Susp-fmap f₂) ω₂)) →
      (ap-∘ f₁ (Susp-fmap f₂) (! ω₂) ∙
        ap (ap f₁) (ap (λ q → q) (ap-! (Susp-fmap f₂) ω₂))) ∙
      ! (ap (ap f₁) (ap (λ q → q) ↑ω₈))
      ==
      β-free2 idp ω₂ ↑ω₈
    β-red2-aux2 idp idp = idp

    β-red2-aux : {w : Susp (de⊙ W)} (ω₃ : w == right unit)
      (ω₂ : left unit == right unit)
      (ω₆ : left unit == right unit)
      (ω₈¹ : ap (Susp-fmap (f₂ ∘ f₃)) ω₆ == ap (Susp-fmap f₂) ω₂) → 
      (ap-∘ f₁ (Susp-fmap f₂) (ap (Susp-fmap f₃) ω₃ ∙ ! ω₂) ∙
      ap (ap f₁) (ap-∙ (Susp-fmap f₂) (ap (Susp-fmap f₃) ω₃) (! ω₂)) ∙
      ! (ap (ap f₁) (ap (λ p → p ∙ ap (Susp-fmap f₂) (! ω₂))
        (ap-∘ (Susp-fmap f₂) (Susp-fmap f₃) ω₃ ∙ idp))) ∙
      ap (ap f₁) (ap (λ p → ap (Susp-fmap f₂ ∘ Susp-fmap f₃) ω₃ ∙ p)
        (ap-! (Susp-fmap f₂) ω₂))) ∙
      ! (ap (ap f₁) (ap (λ p → p ∙
        ap (Susp-fmap (f₂ ∘ f₃)) (! ω₆))
        (! (ap-∘ (Susp-fmap f₂) (Susp-fmap f₃) ω₃)) ∙
        ap (_∙_ (ap (Susp-fmap f₂ ∘ Susp-fmap f₃) ω₃))
        (ap-! (Susp-fmap (f₂ ∘ f₃)) ω₆ ∙ ap ! (ω₈¹ ∙ idp))))
      ==
      β-free2 (ap (Susp-fmap f₃) ω₃) ω₂
        (ap-! (Susp-fmap (f₂ ∘ f₃)) ω₆ ∙ ap ! (ω₈¹ ∙ idp))
    β-red2-aux idp ω₂ ω₆ ω₈¹ =
      β-red2-aux2 ω₂ (ap-! (Susp-fmap (f₂ ∘ f₃)) ω₆ ∙ ap ! (ω₈¹ ∙ idp))

    β-red2 : (ω₂ : left unit == right unit)
      (ω₃ : left unit == right unit)
      (ω₆ : left unit == right unit)
      {w : left unit == right unit}
      (ω₈² : ap (Susp-fmap f₂) ω₂ == w)
      (ω₈¹ : ap (Susp-fmap (f₂ ∘ f₃)) ω₆ == w)
      {e : Susp-fmap f₃ (left unit) == Susp-fmap f₃ (right unit)}
      (ω₉ : ap (Susp-fmap f₃) ω₃ == e) →
      β-free1 ω₂ ω₃ ω₉ ∙
      ! (ap (ap f₁) (ap (λ p → p ∙ ap (Susp-fmap (f₂ ∘ f₃)) (! ω₆))
        (! (ap (ap (Susp-fmap f₂)) ω₉) ∙
        ! (ap-∘ (Susp-fmap f₂) (Susp-fmap f₃) ω₃)) ∙
        ap (λ p → ap (Susp-fmap f₂ ∘ Susp-fmap f₃) ω₃ ∙ p)
        (ap-! (Susp-fmap (f₂ ∘ f₃)) ω₆ ∙ ap ! (ω₈¹ ∙ ! ω₈²))))
      ==
      β-free2 e ω₂ ((ap-! (Susp-fmap (f₂ ∘ f₃)) ω₆ ∙ ap ! (ω₈¹ ∙ ! ω₈²)))
    β-red2 ω₂ ω₃ ω₆ idp ω₈¹ idp = β-red2-aux ω₃ ω₂ ω₆ ω₈¹

    β-free3 : {y : Susp (de⊙ Z)} (ω₁ : y == right unit)
      {x : Susp (de⊙ W)} (ω₆ : x == right unit)
      {ω₁₁ : Susp-fmap (f₂ ∘ f₃) x == right unit}
      (ω₈¹ : ap (Susp-fmap (f₂ ∘ f₃)) ω₆ == ω₁₁)
      {ω₁₀ : Susp-fmap f₂ y == right unit}
      (ω₁₂ : ap (Susp-fmap f₂) ω₁ == ω₁₀) → 
      ap f₁ (ω₁₀ ∙ ! ω₁₁)
      ==
      ap f₁ (ap (Susp-fmap f₂) ω₁ ∙
        ap (Susp-fmap (f₂ ∘ f₃)) (! ω₆))
    β-free3 ω₁ ω₆ {ω₁₁} ω₈¹ {ω₁₀} ω₁₂ =
      ap (λ p → ap f₁ (p ∙ ! ω₁₁)) (! ω₁₂) ∙
      ap (λ p → ap f₁ (ap (Susp-fmap f₂) ω₁ ∙ ! p)) (! ω₈¹) ∙
      ap (λ p → ap f₁ (ap (Susp-fmap f₂) ω₁ ∙ p))
        (!-ap (Susp-fmap (f₂ ∘ f₃)) ω₆)  

    β-red3 : {y : Susp (de⊙ Z)} (ω₁ : y == right unit)
      (ω₂ : left unit == right unit)
      (ω₆ : left unit == right unit)
      {ω₁₁ : left unit == right unit}
      (ω₈² : ap (Susp-fmap f₂) ω₂ == ω₁₁)
      (ω₈¹ : ap (Susp-fmap (f₂ ∘ f₃)) ω₆ == ω₁₁)
      {ω₁₀ : Susp-fmap f₂ y == right unit}
      (ω₁₂ : ap (Susp-fmap f₂) ω₁ == ω₁₀) →
      ap-∙ f₁ ω₁₀ (! ω₁₁) ∙
      ! (ap (_∙_ (ap f₁ ω₁₀))
        (ap (λ p → ap f₁ (! p)) ω₈²)) ∙
      (! (ap (_∙_ (ap f₁ ω₁₀))
         (ap-∘ f₁ (Susp-fmap f₂) (! ω₂) ∙
         ap (ap f₁) (ap-! (Susp-fmap f₂) ω₂))) ∙
      ! (ap (λ p → ap f₁ p ∙ ap (f₁ ∘ Susp-fmap f₂) (! ω₂)) ω₁₂) ∙
      ! (ap (λ p → p ∙ ap (f₁ ∘ Susp-fmap f₂) (! ω₂))
        (ap-∘ f₁ (Susp-fmap f₂) ω₁)) ∙
      ! (ap-∙ (f₁ ∘ Susp-fmap f₂) ω₁ (! ω₂))) ∙
      β-free2 ω₁ ω₂ (ap-! (Susp-fmap (f₂ ∘ f₃)) ω₆ ∙
        ap ! (ω₈¹ ∙ ! ω₈²))
      ==
      ap (λ p → ap f₁ (p ∙ ! ω₁₁)) (! ω₁₂) ∙
      ap (λ p → ap f₁ (ap (Susp-fmap f₂) ω₁ ∙ ! p)) (! ω₈¹) ∙
      ap (λ p → ap f₁ (ap (Susp-fmap f₂) ω₁ ∙ p))
        (!-ap (Susp-fmap (f₂ ∘ f₃)) ω₆)
    β-red3 idp ω₂ ω₆ idp ω₈¹ idp = 
      ap-∘2-ap-! f₁ (Susp-fmap f₂) ω₂
        (ap (ap f₁) (ap (λ p → p) (! (ap-! (Susp-fmap (f₂ ∘ f₃)) ω₆ ∙
        ap ! (ω₈¹ ∙ idp))))) ∙
      ap3-!-ap-!-rid (Susp-fmap (f₂ ∘ f₃)) f₁ ω₆ ω₈¹

    β-red4 : {y : Susp (de⊙ Z)} (ω₁ : y == right unit)
      {w : Susp (de⊙ W)} (ω₆ : w == right unit)
      {ω₁₁ : Susp-fmap (f₂ ∘ f₃) w == right unit}
      (ω₈¹ : ap (Susp-fmap (f₂ ∘ f₃)) ω₆ == ω₁₁)
      {ω₁₀ : Susp-fmap f₂ y == right unit}
      (ω₁₂ : ap (Susp-fmap f₂) ω₁ == ω₁₀) → 
      (ap (λ p → ap f₁ (p ∙ ! ω₁₁)) (! ω₁₂) ∙
      ap (λ p → ap f₁ (ap (Susp-fmap f₂) ω₁ ∙ ! p))
        (! ω₈¹) ∙
      ap (λ p → ap f₁ (ap (Susp-fmap f₂) ω₁ ∙ p))
        (!-ap (Susp-fmap (f₂ ∘ f₃)) ω₆)) ∙
      ! (ap (ap f₁) (ap (λ p → p ∙ ap (Susp-fmap (f₂ ∘ f₃))
        (! ω₆)) (! ω₁₂)))
      ==
      ap (λ p → ap f₁ (ω₁₀ ∙ p))
        (! (ap-! (Susp-fmap (f₂ ∘ f₃)) ω₆ ∙ ap ! ω₈¹))
    β-red4 idp idp idp idp = idp

    β-red5 : {w : Susp (de⊙ W)} (ω₆ : w == right unit)
      (ω₃ : left unit == right unit)
      {ω₁₀ : left unit == right unit}
      (ω₁₃ : ap (Susp-fmap (f₂ ∘ f₃)) ω₃ == ω₁₀) → 
      ! (ap (ap f₁) (ap-∙ (Susp-fmap (f₂ ∘ f₃)) ω₃
        (! ω₆) ∙ ap (λ p → p ∙ ap (Susp-fmap (f₂ ∘ f₃))
        (! ω₆)) ω₁₃)) ∙
      ! (ap (λ q → q) (ap-∘ f₁ (Susp-fmap (f₂ ∘ f₃))
        (ω₃ ∙ ! ω₆))) ∙
      ! (! (ap (_∙_ (ap f₁ ω₁₀))
          (ap-∘ f₁ (Susp-fmap (f₂ ∘ f₃)) (! ω₆) ∙
          ap (ap f₁) (ap-! (Susp-fmap (f₂ ∘ f₃)) ω₆))) ∙
        ! (ap (λ p → ap f₁ p ∙ ap (f₁ ∘ Susp-fmap (f₂ ∘ f₃))
          (! ω₆)) ω₁₃) ∙
        ! (ap (λ p → p ∙ ap (f₁ ∘ Susp-fmap (f₂ ∘ f₃)) (! ω₆))
          (ap-∘ f₁ (Susp-fmap (f₂ ∘ f₃)) ω₃)) ∙
        ! (ap-∙ (f₁ ∘ Susp-fmap (f₂ ∘ f₃)) ω₃ (! ω₆)))
      ==
      ap-∙ f₁ ω₁₀ (ap (Susp-fmap (f₂ ∘ f₃)) (! ω₆)) ∙
      ap (λ p → ap f₁ ω₁₀ ∙ ap f₁ p)
        (ap-! (Susp-fmap (f₂ ∘ f₃)) ω₆)
    β-red5 idp ω₃ idp = ap-∘2-ap-∙ f₁ (Susp-fmap (f₂ ∘ f₃)) ω₃

    β-red6 : {x : Susp (de⊙ X)} (ω₁₀ : x == right unit)
      {w : Susp (de⊙ W)} (ω₆ : w == right unit)
      {ω₁₁ : Susp-fmap (f₂ ∘ f₃) w == right unit}
      (ω₈¹ : ap (Susp-fmap (f₂ ∘ f₃)) ω₆ == ω₁₁) →
      ap (λ p → ap f₁ (ω₁₀ ∙ p))
        (! (ap-! (Susp-fmap (f₂ ∘ f₃)) ω₆ ∙
        ap ! ω₈¹)) ∙
      (ap-∙ f₁ ω₁₀ (ap (Susp-fmap (f₂ ∘ f₃)) (! ω₆)) ∙
      ap (λ p → ap f₁ ω₁₀ ∙ ap f₁ p)
        (ap-! (Susp-fmap (f₂ ∘ f₃)) ω₆)) ∙
      ! (! (ap (_∙_ (ap f₁ ω₁₀))
        (ap (λ p → ap f₁ (! p)) ω₈¹))) ∙
      ! (ap-∙ f₁ ω₁₀ (! ω₁₁))
      == idp
    β-red6 idp idp idp = idp

    Susp-fmap-∘-sq-rw : 
      (hmtpy-nat-∙'-r (λ z → ap f₁ (! (Susp-fmap-∘-∼ f₂ f₃ z)))
        (merid x ∙ ! (merid (pt W))) ∙ idp) ∙ idp
        ==
      ((ap-∘-long f₁ (Susp-fmap f₂ ∘ Susp-fmap f₃) (Susp-fmap (f₂ ∘ f₃))
        (SuspMapEq (Susp-fmap (f₂ ∘ f₃)) (Susp-fmap f₂ ∘ Susp-fmap f₃)
        idp idp (λ x → ↯ (Susp-fmap-∘ f₂ f₃ x))) (merid x ∙ ! (merid (pt W))) ∙
      ! (ap (ap f₁) (
        ap-∙ (Susp-fmap (f₂ ∘ f₃)) (merid x) (! (merid (pt W))) ∙
        ap (λ p → p ∙ ap (Susp-fmap (f₂ ∘ f₃)) (! (merid (pt W))))
          (SuspFmap.merid-β (f₂ ∘ f₃) x ∙ ! (SuspFmap.merid-β f₂ (f₃ x)) ∙
          ! (ap (ap (Susp-fmap f₂)) (SuspFmap.merid-β f₃ x)) ∙
          ! (ap-∘ (Susp-fmap f₂) (Susp-fmap f₃) (merid x))) ∙
        ap (_∙_ (ap (Susp-fmap f₂ ∘ Susp-fmap f₃) (merid x)))
          (ap-! (Susp-fmap (f₂ ∘ f₃)) (merid (pt W)) ∙
          ap ! (SuspFmap.merid-β (f₂ ∘ f₃) (pt W) ∙
            ! (SuspFmap.merid-β f₂ (f₃ (pt W))) ∙
            ! (ap (ap (Susp-fmap f₂)) (SuspFmap.merid-β f₃ (pt W))) ∙
            ! (ap-∘ (Susp-fmap f₂) (Susp-fmap f₃) (merid (pt W)))) ∙
          !-ap (Susp-fmap f₂ ∘ Susp-fmap f₃) (merid (pt W))) ∙
        ap (λ p → p) (! (ap-∙ (Susp-fmap f₂ ∘ Susp-fmap f₃) (merid x)
          (! (merid (pt W))))))) ∙
      ! (ap (λ q → q) (ap-∘ f₁ (Susp-fmap (f₂ ∘ f₃))
        (merid x ∙ ! (merid (pt W)))))) ∙
      idp) ∙ idp
    Susp-fmap-∘-sq-rw = ap (λ p → (p ∙ idp) ∙ idp) (SuspMapEq-β-∙-ap! (Susp-fmap (f₂ ∘ f₃))
      (Susp-fmap f₂ ∘ Susp-fmap f₃) idp idp (λ x → ↯ (Susp-fmap-∘ f₂ f₃ x)) f₁ x (pt W))

    -- proof of 2-coherence

    2-coher-Susp-∼ : sev_step_red_inp (ap f₁)
      (λ p → p ∙ ap (Susp-fmap (f₂ ∘ f₃)) (! (merid (pt W))))
      (λ p → ap (Susp-fmap f₂ ∘ Susp-fmap f₃) (merid x) ∙ p) !
      (ap-∘-long f₁ (Susp-fmap f₂ ∘ Susp-fmap f₃) (Susp-fmap (f₂ ∘ f₃))
        (SuspMapEq (Susp-fmap (f₂ ∘ f₃)) (Susp-fmap f₂ ∘ Susp-fmap f₃)
        idp idp (λ x → ↯ (Susp-fmap-∘ f₂ f₃ x))) (merid x ∙ ! (merid (pt W))))
      (ap-∙ (Susp-fmap (f₂ ∘ f₃)) (merid x) (! (merid (pt W))))
      (SuspFmap.merid-β (f₂ ∘ f₃) x)
      (! (SuspFmap.merid-β f₂ (f₃ x)))
      (! (ap (ap (Susp-fmap f₂)) (SuspFmap.merid-β f₃ x)) ∙
        ! (ap-∘ (Susp-fmap f₂) (Susp-fmap f₃) (merid x)))
      idp (ap-! (Susp-fmap (f₂ ∘ f₃)) (merid (pt W)))
      (SuspFmap.merid-β (f₂ ∘ f₃) (pt W))
      (! (SuspFmap.merid-β f₂ (f₃ (pt W))))
      (! (ap (ap (Susp-fmap f₂)) (SuspFmap.merid-β f₃ (pt W))) ∙
        ! (ap-∘ (Susp-fmap f₂) (Susp-fmap f₃) (merid (pt W))))
      (!-ap (Susp-fmap f₂ ∘ Susp-fmap f₃) (merid (pt W)))
      (ap (λ p → p) (! (ap-∙ (Susp-fmap f₂ ∘ Susp-fmap f₃) (merid x)
        (! (merid (pt W))))))
      (! (ap (λ q → q) (ap-∘ f₁ (Susp-fmap (f₂ ∘ f₃))
        (merid x ∙ ! (merid (pt W))))))
      ((hmtpy-nat-∙'-r (λ z → ap f₁ (! (Susp-fmap-∘-∼ f₂ f₃ z)))
        (merid x ∙ ! (merid (pt W))) ∙ idp) ∙ idp)
      (ap-∙ f₁ (merid (f₂ (f₃ x))) (! (merid (f₂ (f₃ (pt W))))))
      (ap-∙ (f₁ ∘ (Susp-fmap f₂)) (merid (f₃ x)) (! (merid (f₃ (pt W)))))
      (ap-∙ f₁ (merid (f₂ (f₃ x))) (! (merid (f₂ (f₃ (pt W))))))
      (! (ap (_∙_ (ap f₁ (merid (f₂ (f₃ x))))) (ap (λ p → ap f₁ (! p))
        (SuspFmap.merid-β f₂ (f₃ (pt W))))))
      (! (ap (_∙_ (ap f₁ (merid (f₂ (f₃ x)))))
        (ap-∘ f₁ (Susp-fmap f₂) (! (merid (f₃ (pt W)))) ∙
        ap (ap f₁) (ap-! (Susp-fmap f₂) (merid (f₃ (pt W)))))) ∙
      ! (ap (λ p → ap f₁ p ∙ ap (f₁ ∘ Susp-fmap f₂) (! (merid (f₃ (pt W)))))
        (SuspFmap.merid-β f₂ (f₃ x))) ∙
      ! (ap (λ p → p ∙ ap (f₁ ∘ Susp-fmap f₂) (! (merid (f₃ (pt W)))))
        (ap-∘ f₁ (Susp-fmap f₂) (merid (f₃ x)))) ∙
      ! (ap-∙ (f₁ ∘ Susp-fmap f₂) (merid (f₃ x)) (! (merid (f₃ (pt W))))))
      (! (ap (_∙_ (ap (f₁ ∘ (Susp-fmap f₂)) (merid (f₃ x))))
        (ap (λ p → ap (f₁ ∘ (Susp-fmap f₂)) (! p))
        (SuspFmap.merid-β f₃ (pt W)))))
      (! (ap (_∙_ (ap (f₁ ∘ (Susp-fmap f₂)) (merid (f₃ x))))
        (ap-∘ (f₁ ∘ (Susp-fmap f₂)) (Susp-fmap f₃) (! (merid (pt W))) ∙
        ap (ap (f₁ ∘ (Susp-fmap f₂))) (ap-! (Susp-fmap f₃) (merid (pt W))))) ∙
      ! (ap (λ p → ap (f₁ ∘ (Susp-fmap f₂)) p ∙
        ap (f₁ ∘ (Susp-fmap f₂) ∘ Susp-fmap f₃) (! (merid (pt W))))
        (SuspFmap.merid-β f₃ x)) ∙
      ! (ap (λ p → p ∙ ap (f₁ ∘ (Susp-fmap f₂) ∘ Susp-fmap f₃)
        (! (merid (pt W)))) (ap-∘ (f₁ ∘ (Susp-fmap f₂)) (Susp-fmap f₃)
        (merid x))) ∙
      ! (ap-∙ (f₁ ∘ (Susp-fmap f₂) ∘ Susp-fmap f₃)
        (merid x) (! (merid (pt W)))))
      (! (ap (_∙_ (ap f₁ (merid (f₂ (f₃ x))))) (ap (λ p → ap f₁ (! p))
        (SuspFmap.merid-β (f₂ ∘ f₃) (pt W)))))
      (! (ap (_∙_ (ap f₁ (merid (f₂ (f₃ x))))) (ap-∘ f₁ (Susp-fmap (f₂ ∘ f₃))
        (! (merid (pt W))) ∙ ap (ap f₁)
        (ap-! (Susp-fmap (f₂ ∘ f₃)) (merid (pt W))))) ∙
      ! (ap (λ p → ap f₁ p ∙ ap (f₁ ∘ Susp-fmap (f₂ ∘ f₃))
        (! (merid (pt W)))) (SuspFmap.merid-β (f₂ ∘ f₃) x)) ∙
      ! (ap (λ p → p ∙ ap (f₁ ∘ Susp-fmap (f₂ ∘ f₃)) (! (merid (pt W))))
        (ap-∘ f₁ (Susp-fmap (f₂ ∘ f₃)) (merid x))) ∙
      ! (ap-∙ (f₁ ∘ Susp-fmap (f₂ ∘ f₃)) (merid x) (! (merid (pt W)))))
    red1 2-coher-Susp-∼ = Susp-fmap-∘-sq-rw
    red2 2-coher-Susp-∼ = 
      β-red1 (merid x) (SuspFmap.merid-β f₃ x) (merid (pt W))
        (SuspFmap.merid-β f₃ (pt W))
    red3 2-coher-Susp-∼ = 
      β-red2 (merid (f₃ (pt W))) (merid x) (merid (pt W))
        (SuspFmap.merid-β f₂ (f₃ (pt W)))
        (SuspFmap.merid-β (f₂ ∘ f₃) (pt W))
        (SuspFmap.merid-β f₃ x)
    red4 2-coher-Susp-∼ =
      β-red3 (merid (f₃ x)) (merid (f₃ (pt W))) (merid (pt W))
      (SuspFmap.merid-β f₂ (f₃ (pt W))) (SuspFmap.merid-β (f₂ ∘ f₃) (pt W))
      (SuspFmap.merid-β f₂ (f₃ x))
    red5 2-coher-Susp-∼ =
      β-red4 (merid (f₃ x)) (merid (pt W))
        (SuspFmap.merid-β (f₂ ∘ f₃) (pt W))
        (SuspFmap.merid-β f₂ (f₃ x))
    red6 2-coher-Susp-∼ =
      β-red5 (merid (pt W)) (merid x) (SuspFmap.merid-β (f₂ ∘ f₃) x) 
    red7 2-coher-Susp-∼ =
      β-red6 (merid (f₂ (f₃ x))) (merid (pt W))
        (SuspFmap.merid-β (f₂ ∘ f₃) (pt W))

  {-
    It suffices to prove that the underlying homotopies are equal
    because loop spaces are coherently homogeneous.
  -}

  abstract
    2-coher-Susp-cmp : (h₁ : ⊙Susp X ⊙→ Y) (h₂ : Z ⊙→ X) (h₃ : W ⊙→ Z) →
      !-⊙∼ (⊙∘-assoc-comp (into X Y h₁) h₂ h₃) ∙⊙∼
      ⊙∘-pre h₃ (nat-dom-cmp h₂ h₁) ∙⊙∼
      nat-dom-cmp h₃ (h₁ ⊙∘ ⊙Susp-fmap h₂) ∙⊙∼
      ap-cmp-into W Y (⊙∘-assoc-comp h₁ (⊙Susp-fmap h₂) (⊙Susp-fmap h₃) ∙⊙∼
        ⊙∘-post h₁ (!-⊙∼ (Susp-fmap-∘-∼ (fst h₂) (fst h₃) , idp))) ∙⊙∼
      !-⊙∼ (nat-dom-cmp (h₂ ⊙∘ h₃) h₁)
        ⊙→∼
      ⊙∼-id ((into X Y h₁) ⊙∘ h₂ ⊙∘ h₃)
    2-coher-Susp-cmp (f₁ , idp) (f₂ , idp) (f₃ , idp) =
      ∼⊙Ωhomog∼ λ x → sev_step_reduce (2-coher-Susp-∼ f₂ f₃ f₁ x)

module _ {i₁ i₂ i₃ i₄} {X : Ptd i₁} {Y : Ptd i₂} {Z : Ptd i₃} {W : Ptd i₄} where

  open 2-coher-cmp

  -- converting 2-coherence property via the SIP
  abstract
    2-coher-Susp : (h₁ : ⊙Susp X ⊙→ Y) (h₂ : Z ⊙→ X) (h₃ : W ⊙→ Z) →
      ! (⊙-comp-to-== (⊙∘-assoc-comp (into X Y h₁) h₂ h₃)) ∙
      ap (λ m → m ⊙∘ h₃) (⊙-comp-to-== (nat-dom-cmp h₂ h₁)) ∙
      ⊙-comp-to-== (nat-dom-cmp h₃ (h₁ ⊙∘ ⊙Susp-fmap h₂)) ∙
      ap (into W Y)
        (⊙-comp-to-== (⊙∘-assoc-comp h₁ (⊙Susp-fmap h₂) (⊙Susp-fmap h₃)) ∙
        ap (λ m →  h₁ ⊙∘ m) (! (⊙Susp-fmap-∘ h₂ h₃))) ∙
      ! (⊙-comp-to-== (nat-dom-cmp (h₂ ⊙∘ h₃) h₁))
        ==
      idp
    2-coher-Susp h₁ h₂ h₃ = =ₛ-out $
      ! (⊙-comp-to-== (⊙∘-assoc-comp (into X Y h₁) h₂ h₃)) ◃∙
      ap (λ m → m ⊙∘ h₃) (⊙-comp-to-== (nat-dom-cmp h₂ h₁)) ◃∙
      ⊙-comp-to-== (nat-dom-cmp h₃ (h₁ ⊙∘ ⊙Susp-fmap h₂)) ◃∙
      ap (into W Y)
        (⊙-comp-to-== (⊙∘-assoc-comp h₁ (⊙Susp-fmap h₂) (⊙Susp-fmap h₃)) ∙
        ap (λ m →  h₁ ⊙∘ m) (! (⊙Susp-fmap-∘ h₂ h₃))) ◃∙
      ! (⊙-comp-to-== (nat-dom-cmp (h₂ ⊙∘ h₃) h₁)) ◃∎
        =ₛ₁⟨ 0 & 1 & ! (!⊙-conv (⊙∘-assoc-comp (into X Y h₁) h₂ h₃)) ⟩
      ⊙-comp-to-== (!-⊙∼ (⊙∘-assoc-comp (into X Y h₁) h₂ h₃)) ◃∙
      ap (λ m → m ⊙∘ h₃) (⊙-comp-to-== (nat-dom-cmp h₂ h₁)) ◃∙
      ⊙-comp-to-== (nat-dom-cmp h₃ (h₁ ⊙∘ ⊙Susp-fmap h₂)) ◃∙
      ap (into W Y)
        (⊙-comp-to-== (⊙∘-assoc-comp h₁ (⊙Susp-fmap h₂) (⊙Susp-fmap h₃)) ∙
        ap (λ m →  h₁ ⊙∘ m) (! (⊙Susp-fmap-∘ h₂ h₃))) ◃∙
      ! (⊙-comp-to-== (nat-dom-cmp (h₂ ⊙∘ h₃) h₁)) ◃∎
        =ₛ₁⟨ 1 & 1 & ! (whisk⊙-conv-r (nat-dom-cmp h₂ h₁)) ⟩
      ⊙-comp-to-== (!-⊙∼ (⊙∘-assoc-comp (into X Y h₁) h₂ h₃)) ◃∙
      ⊙-comp-to-== (⊙∘-pre h₃ (nat-dom-cmp h₂ h₁)) ◃∙
      ⊙-comp-to-== (nat-dom-cmp h₃ (h₁ ⊙∘ ⊙Susp-fmap h₂)) ◃∙
      ap (into W Y)
        (⊙-comp-to-== (⊙∘-assoc-comp h₁ (⊙Susp-fmap h₂) (⊙Susp-fmap h₃)) ∙
        ap (λ m →  h₁ ⊙∘ m) (! (⊙Susp-fmap-∘ h₂ h₃))) ◃∙
      ! (⊙-comp-to-== (nat-dom-cmp (h₂ ⊙∘ h₃) h₁)) ◃∎
        =ₛ₁⟨ 4 & 1 & ! (!⊙-conv (nat-dom-cmp (h₂ ⊙∘ h₃) h₁)) ⟩
      ⊙-comp-to-== (!-⊙∼ (⊙∘-assoc-comp (into X Y h₁) h₂ h₃)) ◃∙
      ⊙-comp-to-== (⊙∘-pre h₃ (nat-dom-cmp h₂ h₁)) ◃∙
      ⊙-comp-to-== (nat-dom-cmp h₃ (h₁ ⊙∘ ⊙Susp-fmap h₂)) ◃∙
      ap (into W Y)
        (⊙-comp-to-== (⊙∘-assoc-comp h₁ (⊙Susp-fmap h₂) (⊙Susp-fmap h₃)) ∙
        ap (λ m →  h₁ ⊙∘ m) (! (⊙Susp-fmap-∘ h₂ h₃))) ◃∙
      ⊙-comp-to-== (!-⊙∼ (nat-dom-cmp (h₂ ⊙∘ h₃) h₁)) ◃∎
        =ₛ₁⟨ 3 & 1 & ap (ap (into W Y)) (
          ap (λ p → ⊙-comp-to-== (⊙∘-assoc-comp h₁ (⊙Susp-fmap h₂) (⊙Susp-fmap h₃)) ∙ p)
            (ap (ap (_⊙∘_ h₁)) (! (!⊙-conv (Susp-fmap-∘-∼ (fst h₂) (fst h₃) , idp))) ∙
            ! (whisk⊙-conv-l (!-⊙∼ (Susp-fmap-∘-∼ (fst h₂) (fst h₃) , idp)))) ∙
          ! (=ₛ-out (⊙∘-conv
            (⊙∘-assoc-comp h₁ (⊙Susp-fmap h₂) (⊙Susp-fmap h₃))
            (⊙∘-post h₁ (!-⊙∼ (Susp-fmap-∘-∼ (fst h₂) (fst h₃) , idp)))))) ⟩
      ⊙-comp-to-== (!-⊙∼ (⊙∘-assoc-comp (into X Y h₁) h₂ h₃)) ◃∙
      ⊙-comp-to-== (⊙∘-pre h₃ (nat-dom-cmp h₂ h₁)) ◃∙
      ⊙-comp-to-== (nat-dom-cmp h₃ (h₁ ⊙∘ ⊙Susp-fmap h₂)) ◃∙
      ap (into W Y) (⊙-comp-to-==
        (⊙∘-assoc-comp h₁ (⊙Susp-fmap h₂) (⊙Susp-fmap h₃) ∙⊙∼
        ⊙∘-post h₁ (!-⊙∼ (Susp-fmap-∘-∼ (fst h₂) (fst h₃) , idp)))) ◃∙
      ⊙-comp-to-== (!-⊙∼ (nat-dom-cmp (h₂ ⊙∘ h₃) h₁)) ◃∎
        =ₛ₁⟨ 3 & 1 & ap-cmp-into-agree W Y
          (⊙∘-assoc-comp h₁ (⊙Susp-fmap h₂) (⊙Susp-fmap h₃) ∙⊙∼
          ⊙∘-post h₁ (!-⊙∼ (Susp-fmap-∘-∼ (fst h₂) (fst h₃) , idp))) ⟩
      ⊙-comp-to-== (!-⊙∼ (⊙∘-assoc-comp (into X Y h₁) h₂ h₃)) ◃∙
      ⊙-comp-to-== (⊙∘-pre h₃ (nat-dom-cmp h₂ h₁)) ◃∙
      ⊙-comp-to-== (nat-dom-cmp h₃ (h₁ ⊙∘ ⊙Susp-fmap h₂)) ◃∙
      ⊙-comp-to-== (ap-cmp-into W Y
        (⊙∘-assoc-comp h₁ (⊙Susp-fmap h₂) (⊙Susp-fmap h₃) ∙⊙∼
        ⊙∘-post h₁ (!-⊙∼ (Susp-fmap-∘-∼ (fst h₂) (fst h₃) , idp)))) ◃∙
      ⊙-comp-to-== (!-⊙∼ (nat-dom-cmp (h₂ ⊙∘ h₃) h₁)) ◃∎
        =ₛ⟨ ⊙∘-conv-quint
              (!-⊙∼ (⊙∘-assoc-comp (into X Y h₁) h₂ h₃))
              (⊙∘-pre h₃ (nat-dom-cmp h₂ h₁))
              (nat-dom-cmp h₃ (h₁ ⊙∘ ⊙Susp-fmap h₂))
              (ap-cmp-into W Y
                (⊙∘-assoc-comp h₁ (⊙Susp-fmap h₂) (⊙Susp-fmap h₃) ∙⊙∼
                ⊙∘-post h₁ (!-⊙∼ (Susp-fmap-∘-∼ (fst h₂) (fst h₃) , idp))))
              (!-⊙∼ (nat-dom-cmp (h₂ ⊙∘ h₃) h₁)) ⟩
      ⊙-comp-to-==
        (!-⊙∼ (⊙∘-assoc-comp (into X Y h₁) h₂ h₃) ∙⊙∼
        ⊙∘-pre h₃ (nat-dom-cmp h₂ h₁) ∙⊙∼
        nat-dom-cmp h₃ (h₁ ⊙∘ ⊙Susp-fmap h₂) ∙⊙∼
        ap-cmp-into W Y
          (⊙∘-assoc-comp h₁ (⊙Susp-fmap h₂) (⊙Susp-fmap h₃) ∙⊙∼
          ⊙∘-post h₁ (!-⊙∼ (Susp-fmap-∘-∼ (fst h₂) (fst h₃) , idp))) ∙⊙∼
        !-⊙∼ (nat-dom-cmp (h₂ ⊙∘ h₃) h₁)) ◃∎
        =ₛ₁⟨ ap ⊙-comp-to-== (⊙→∼-to-== (2-coher-Susp-cmp h₁ h₂ h₃)) ⟩
      ⊙-comp-to-== (⊙∼-id ((into X Y h₁) ⊙∘ h₂ ⊙∘ h₃)) ◃∎
        =ₛ₁⟨ ⊙-comp-to-==-β (into X Y h₁ ⊙∘ h₂ ⊙∘ h₃) ⟩
      idp ◃∎ ∎ₛ
