{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
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

module _ {ℓ₁ ℓ₂} {Γ : Graph ℓv ℓe} {F : Diag ℓd Γ} {C : Type ℓ₁} {D : Type ℓ₂} where

  -- canonical post-composition function on cocones
  PostComp : Cocone F C → (C → D) → Cocone F D
  comp (PostComp K f) x = f ∘ comp K x
  comTri (PostComp K f) g z = ap f (comTri K g z)
