{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pi
open import lib.types.Graph
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc

module lib.types.Cospan where

record Cospan {i j k : ULevel} : Type (lsucc (lmax (lmax i j) k)) where
  constructor cospan
  field
    A : Type i
    B : Type j
    C : Type k
    f : A → C
    g : B → C

record ⊙Cospan {i j k : ULevel} : Type (lsucc (lmax (lmax i j) k)) where
  constructor ⊙cospan
  field
    X : Ptd i
    Y : Ptd j
    Z : Ptd k
    f : X ⊙→ Z
    g : Y ⊙→ Z

⊙cospan-out : ∀ {i j k} → ⊙Cospan {i} {j} {k} → Cospan {i} {j} {k}
⊙cospan-out (⊙cospan X Y Z f g) =
  cospan (de⊙ X) (de⊙ Y) (de⊙ Z) (fst f) (fst g)

module _ {i j k} (D : Cospan {i} {j} {k}) where

  open Cospan D

  record Cone-csp {ℓ} (T : Type ℓ) : Type (lmax (lmax i j) (lmax k ℓ)) where
    constructor cone-csp
    field
      left : T → A
      right : T → B
      sq : f ∘ left ∼ g ∘ right

module _ {ℓ} (Δ : Diag-cspan (Type-wc ℓ))where

  diag-to-csp : Cospan
  diag-to-csp = cospan (D₀ Δ lft) (D₀ Δ rght) (D₀ Δ mid) (D₁ Δ unit) (D₁ Δ unit)

  open Cone

  con-to-csp : {T : Type ℓ} → Cone Δ T → Cone-csp diag-to-csp T
  con-to-csp K = cone-csp (leg K lft) (leg K rght) (app= (tri K {lft} unit ∙ ! (tri K {rght} unit)))
