{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import lib.types.Colim
open import Coslice
open import Diagram-Cos
open import AuxPaths
open import Id-col

{- formation of A-cocone structure on pushout -}

module Cocone-po where

module _ {ℓ₁ ℓ₂} {B : Type ℓ₁} {D : Type ℓ₂} {u : D → B} where

  H₁ : ∀ {k l} {C : Type k} {A : Type l} {h : C → A} {f : A → B} {v : C → D}
    {c d : C} (Q : c == d) (s : f (h c) == u (v c)) {q : v c == v d} (R : ap v Q == q)
    → transport (λ x → f (h x) == u (v x)) Q s == ! (ap f (ap h Q)) ∙ s ∙ ap u q
  H₁ idp s idp = ! (∙-unit-r s)

  H₂ : ∀ {ℓ₃} {E : Type ℓ₃} {x y : B} {g : E → D} {d e : E} (t : d == e) (q : u (g e) == y)
    {p : x == y} {z : D} (s : g d == z) {R : u (g d) == u z} (T : ap u s == R)
    → p ∙ ! q ∙ ap u (! (ap g t) ∙ s) == p ∙ ! (! R ∙ ap (u ∘ g) t ∙ q)
  H₂ idp q {p = p} idp idp = ap (λ r → p ∙ r) (∙-unit-r (! q))

module Id {ℓv ℓe ℓ} (Γ : Graph ℓv ℓe) (A : Type ℓ) where

  -- the left arrow of the span
  open id-colim Γ A public

  module Maps {ℓd} (F : CosDiag ℓd ℓ A Γ) where

    μ : DiagMor (ConsDiag Γ A) (DiagForg A Γ F)
    nat μ i = str (F # i)
    comSq μ g = snd (F <#> g)

    private
      module N = ColimitMap {F = ConsDiag Γ A} {G = DiagForg A Γ F} μ

    -- the right arrow of the span
    ψ : Colim (ConsDiag Γ A) → Colim (DiagForg A Γ F)
    ψ = N.ColMap

    ψ-βr = N.ColMap-β

    -- The tip of the cocone is the pushout of the two preceding arrows.

    SpCos = span A (Colim (DiagForg A Γ F)) (Colim (ConsDiag Γ A)) [id] ψ

    P = Pushout SpCos

    -- cocone structure on pushout
    ColCoC-cos : CosCocone A F (Cos P left)
    comp ColCoC-cos i = right ∘ cin i , λ a → ! (glue (cin i a))
    comTri ColCoC-cos g = (λ x → ap right (cglue g x)) ,  λ a → ↯ (ε g a)
      module _ where  -- see ../Aux/AuxPaths.agda for defs of E₁ and E₃
      ε : ∀ {i j} (g : Hom Γ i j) (a : A) →
        ! (ap right (cglue g (str (F # i) a))) ∙ ap (right ∘ cin j) (snd (F <#> g) a) ∙ ! (glue (cin j a)) =-= ! (glue (cin i a))
      ε {i} {j} g a =
        ! (ap right  (cglue g (str (F # i) a))) ∙ (ap (right ∘ cin j) (snd (F <#> g) a)) ∙ (! (glue (cin j a)))
          =⟪ E₁ (snd (F <#> g) a) (! (glue (cin j a))) ⟫
        ! (ap right (! (ap (cin j) (snd (F <#> g) a)) ∙ cglue g (str (F # i) a))) ∙ ! (glue (cin j a)) ∙ idp
          =⟪ ! (ap (λ p → ! (ap right (! (ap (cin j) (snd (F <#> g) a)) ∙ cglue g (str (F # i) a))) ∙ ! (glue (cin j a)) ∙ p)
                 (ap (ap left) (id-βr g a))) ⟫
        ! (ap right (! (ap (cin j) (snd (F <#> g) a)) ∙ cglue g (str (F # i) a))) ∙ ! (glue (cin j a)) ∙ ap left (ap [id] (cglue g a))
          =⟪ E₃ (λ x → ! (glue x)) (cglue g a) (ψ-βr g a) (λ x → idp) ⟫
        ! (glue (cin i a)) ∙ idp
          =⟪ ∙-unit-r (! (glue (cin i a))) ⟫
        ! (glue (cin i a)) ∎∎

    module Recc {ℓc} (T : Coslice ℓc ℓ A) where

    -- induced map out of the pushout and some of its properties

      reccForg : CosCocone A F T → Colim (DiagForg A Γ F) → ty T
      reccForg (r & K) = colimR (λ i → fst (r i)) (λ i j g → fst (K g))

      recc-βr : (C : CosCocone A F T) {i j : Obj Γ} (g : Hom Γ i j) (x : ty (F # i))
        → ap (reccForg C) (cglue g x) == fst (comTri C g) x
      recc-βr C g x = cglue-βr (comp (CocForg C)) (λ i j g → fst (comTri C g)) g x

      recCosCoc : CosCocone A F T → (< A > (Cos P left) *→ T)
      fst (recCosCoc (r & K)) = Pushout-rec (str T) recc σ
        module _ where
          recc : Colim (DiagForg A Γ F) → ty T
          recc = reccForg (r & K)

          σ : (x : Colim (ConsDiag Γ A)) → str T ([id] x) == recc (ψ x)
          σ =
            colimE (λ i a → ! (snd (r i) a))
              (λ i j g a → from-transp-g (λ z → str T ([id] z) == recc (ψ z)) (cglue g a) (↯ (η i j g a)))
            module _ where
              η : (i j : Obj Γ) (g : Hom Γ i j) (a : A) →
                transport (λ z → str T ([id] z) == recc (ψ z)) (cglue g a) (! (snd (r j) a)) =-= ! (snd (r i) a)
              η i j g a =
                transport (λ z →  str T ([id] z) == recc (ψ z)) (cglue g a) (! (snd (r j) a))
                  =⟪ H₁ (cglue g a) (! (snd (r j) a)) (ψ-βr g a) ⟫
                ! (ap (str T) (ap [id] (cglue g a))) ∙ (! (snd (r j) a)) ∙ ap recc (! (ap (cin j) (snd (F <#> g) a)) ∙ (cglue g (str (F # i) a)))
                  =⟪ H₂ (snd (F <#> g) a) (snd (r j) a) (cglue g (str (F # i) a)) (recc-βr (r & K) g (str (F # i) a)) ⟫
                ! (ap (str T) (ap [id] (cglue g a))) ∙ ! (! (fst (K g) (str (F # i) a)) ∙ ap (recc ∘ cin j) (snd (F <#> g) a) ∙ (snd (r j) a))
                  =⟪ ap (λ p → p ∙ ! (! (fst (K g) (str (F # i) a)) ∙ ap (recc ∘ cin j) (snd (F <#> g) a) ∙ (snd (r j) a)))
                       (ap (λ p → ! (ap (str T) p)) (id-βr g a)) ⟫
                ! (! (fst (K g) (str (F # i) a)) ∙ ap (recc ∘ cin j) (snd (F <#> g) a) ∙ (snd (r j) a))
                  =⟪ ap ! (snd (K g) a) ⟫
                ! (snd (r i) a) ∎∎
      snd (recCosCoc x) a = idp

      FPrecc-βr = λ (C : CosCocone A F T) → PushoutRec.glue-β {d = SpCos} (str T) (recc (comp C) (comTri C)) (σ (comp C) (comTri C))

      abstract
        σ-β : (C : CosCocone A F T) → ∀ {i j} g a → apd-tr (σ (comp C) (comTri C)) (cglue g a) == ↯ (η (comp C) (comTri C) i j g a)
        σ-β C {i} {j} g a =
          apd-to-tr
            (λ x → str T ([id] x) == recc (comp C) (comTri C) (ψ x)) (σ (comp C) (comTri C)) (cglue g a)
            (↯ (η (comp C) (comTri C) i j g a))
            (cglue-β (λ i → (λ a → ! (snd (comp C i) a)))
              (λ i → (λ j → ( λ g → (λ a →  from-transp-g (λ z → str T ([id] z) == recc (comp C) (comTri C) (ψ z))
                (cglue g a) (↯ (η (comp C) (comTri C) i j g a)))))) g a)
