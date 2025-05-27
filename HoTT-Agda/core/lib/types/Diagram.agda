{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Graph

-- type-valued diagrams over graphs

module lib.types.Diagram where

private variable ℓv ℓe ℓd : ULevel

Diag : ∀ ℓd (G : Graph ℓv ℓe) → Type (lmax (lmax ℓv ℓe) (lsucc ℓd))
Diag ℓd G = GraphHom G (TypeGr ℓd)

record DiagMor {ℓd ℓd'} {G : Graph ℓv ℓe} (F : Diag ℓd G) (F' : Diag ℓd' G)
  : Type (lmax (lmax ℓv ℓe) (lmax ℓd ℓd')) where
  constructor Δ
  field
    nat : ∀ (x : Obj G) → F # x → F' # x
    comSq : ∀ {x y : Obj G} (f : Hom G x y) (z : F # x) → (F' <#> f) (nat x z) == nat y ((F <#> f) z)
open DiagMor public

-- cocones under diagrams

record Cocone {i k} {G : Graph ℓv ℓe} (F : Diag i G) (C : Type k)
  : Type (lmax k (lmax (lmax ℓv ℓe) i)) where
  constructor _&_
  field
    comp : (x : Obj G) → F # x → C
    comTri : ∀ {y x : Obj G} (f : Hom G x y) (z : F # x) → comp y ((F <#> f) z) == comp x z
open Cocone public

record Cocone-mor-str {ℓ k₁ k₂} {Γ : Graph ℓv ℓe} {F : Diag ℓ Γ} {C₁ : Type k₁} {C₂ : Type k₂}
  (K₁ : Cocone F C₁) (K₂ : Cocone F C₂) (f : C₁ → C₂) : Type (lmax (lmax ℓv ℓe) (lmax k₂ ℓ)) where
  constructor cocmorstr
  field
    comp-∼ : (i : Obj Γ) → f ∘ comp K₁ i ∼ comp K₂ i
    comTri-∼ : {i j : Obj Γ} (g : Hom Γ i j) (x : F # i) →
      ! (comp-∼ j ((F <#> g) x)) ∙ ap f (comTri K₁ g x) ∙' comp-∼ i x == comTri K₂ g x
open Cocone-mor-str public

infixr 30 _Cocone-≃_
_Cocone-≃_ : ∀ {ℓ k₁ k₂} {Γ : Graph ℓv ℓe} {F : Diag ℓ Γ} {C₁ : Type k₁} {C₂ : Type k₂}
  (K₁ : Cocone F C₁) (K₂ : Cocone F C₂) → Type (lmax (lmax (lmax (lmax ℓv ℓe) ℓ) k₁) k₂)
_Cocone-≃_ {C₁ = C₁} {C₂} K₁ K₂ = Σ (C₁ → C₂) (Cocone-mor-str K₁ K₂)

module _ {ℓ₁ ℓ₂} {Γ : Graph ℓv ℓe} {F : Diag ℓd Γ} {C : Type ℓ₁} where

  -- canonical post-composition function on cocones
  PostComp : Cocone F C → (D : Type ℓ₂) → (C → D) → Cocone F D
  comp (PostComp K _ f) i = f ∘ comp K i
  comTri (PostComp K _ f) g z = ap f (comTri K g z)
