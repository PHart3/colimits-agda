{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Graph

-- type-valued diagrams over graphs

module lib.types.Diagram where

private variable ℓv ℓe ℓd : ULevel

Diag : ∀ ℓd (Γ : Graph ℓv ℓe) → Type (lmax (lmax ℓv ℓe) (lsucc ℓd))
Diag ℓd G = GraphHom G (TypeGr ℓd)

-- constant diagram at a type
ConsDiag : ∀ {ℓd} (Γ : Graph ℓv ℓe) (A : Type ℓd) → Diag ℓd Γ
(ConsDiag Γ A) # _ = A
(ConsDiag Γ A) <#> _ = idf A

record DiagMor {ℓd ℓd'} {Γ : Graph ℓv ℓe} (F : Diag ℓd Γ) (F' : Diag ℓd' Γ)
  : Type (lmax (lmax ℓv ℓe) (lmax ℓd ℓd')) where
  constructor Δ
  field
    nat : ∀ (x : Obj Γ) → F # x → F' # x
    comSq : ∀ {x y : Obj Γ} (f : Hom Γ x y) (z : F # x) → (F' <#> f) (nat x z) == nat y ((F <#> f) z)
open DiagMor public

-- cocones under diagrams

record Cocone {i k} {Γ : Graph ℓv ℓe} (F : Diag i Γ) (C : Type k)
  : Type (lmax k (lmax (lmax ℓv ℓe) i)) where
  constructor _&_
  field
    comp : (x : Obj Γ) → F # x → C
    comTri : ∀ {y x : Obj Γ} (f : Hom Γ x y) (z : F # x) → comp y ((F <#> f) z) == comp x z
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
_Cocone-≃_ {C₁ = C₁} {C₂} K₁ K₂ = Σ (C₁ ≃ C₂) (λ e → Cocone-mor-str K₁ K₂ (–> e))

module _ {ℓ₁} {Γ : Graph ℓv ℓe} {F : Diag ℓd Γ} {C : Type ℓ₁} where

  -- canonical post-composition function on cocones
  PostComp : ∀ {ℓ₂} → Cocone F C → (D : Type ℓ₂) → (C → D) → Cocone F D
  comp (PostComp K _ f) i = f ∘ comp K i
  comTri (PostComp K _ f) g z = ap f (comTri K g z)

  -- colimiting cocone in the wild category of types
  is-colim : Cocone F C → Agda.Primitive.Setω
  is-colim K = ∀ {ℓ₂} (D : Type ℓ₂) → is-equiv (PostComp K D)
