{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.wild-cats.WildCat

module lib.wild-cats.Diagram-wc where

record Graph (ℓv ℓe : ULevel) : Type (lsucc (lmax ℓv ℓe)) where
  field
    Obj : Type ℓv
    Hom : Obj → Obj → Type ℓe

open Graph public

module _ {ℓv ℓe ℓd₁ ℓd₂ : ULevel} where

  record Diagram (G : Graph ℓv ℓe) (C : WildCat {ℓd₁} {ℓd₂}) : Type (lmax (lmax ℓv ℓe) (lmax ℓd₁ ℓd₂)) where
    field
      D₀ : Obj G → ob C
      D₁ : {x y : Obj G} (f : Hom G x y) → hom C (D₀ x) (D₀ y)

  open Diagram public

  record Cocone {G : Graph ℓv ℓe} {C : WildCat {ℓd₁} {ℓd₂}} (D : Diagram G C) (T : ob C) :
    Type (lmax (lmax ℓv ℓe) (lmax ℓd₁ ℓd₂)) where
    field
      comp : (x : Obj G) → hom C (D₀ D x) T
      tri : {x y : Obj G} (f : Hom G x y) → ⟦ C ⟧ comp y ◻ D₁ D f == comp x

  open Cocone public
