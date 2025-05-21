{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.wild-cats.WildCat
open import lib.wild-cats.Adjoint

module lib.wild-cats.Counit-unit where

module _ {i₁ i₂ j₁ j₂} {C : WildCat {i₁} {j₁}} {D : WildCat {i₂} {j₂}} where

  record CounitUnitAdjoint (L : Functor-wc C D) (R : Functor-wc D C) : Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
    constructor counitunitadjoint
    field
      η : (X : ob C) → hom C X (obj R (obj L X))
      ε : (U : ob D) → hom D (obj L (obj R U)) U
      η-natural : {X Y : ob C} (h : hom C X Y) → ⟦ C ⟧ η Y ◻ h == ⟦ C ⟧ arr R (arr L h) ◻ η X 
      ε-natural : {U V : ob D} (k : hom D U V) → ⟦ D ⟧ ε V ◻ arr L (arr R k) == ⟦ D ⟧ k ◻ ε U
      εF-Fη : (X : ob C) → ⟦ D ⟧ ε (obj L X) ◻ arr L (η X) == id₁ D (obj L X)
      Gε-ηG : (U : ob D) → ⟦ C ⟧ arr R (ε U) ◻ η (obj R U) == id₁ C (obj R U)
      
  module _ {L : Functor-wc C D} {R : Functor-wc D C} where

    counit-unit-to-hom : CounitUnitAdjoint L R → Adjunction L R
    counit-unit-to-hom adj = adjunction eqv nat-cd nat-d
      where
      open CounitUnitAdjoint adj
      module _ {X : ob C} {U : ob D} where

        into : hom D (obj L X) U → hom C X (obj R U)
        into f = ⟦ C ⟧ arr R f ◻ η X

        out : hom C X (obj R U) → hom D (obj L X) U
        out f = ⟦ D ⟧ ε U ◻ arr L f

        into-out : into ∘ out ∼ idf (hom C X (obj R U))
        into-out s =
          ⟦ C ⟧ arr R (⟦ D ⟧ ε U ◻ arr L s) ◻ η X
            =⟨ ap (λ m → ⟦ C ⟧ m ◻ η X) (comp R (arr L s) (ε U)) ⟩
          ⟦ C ⟧ (⟦ C ⟧ arr R (ε U) ◻ arr R (arr L s)) ◻ η X
            =⟨ α C (arr R (ε U)) (arr R (arr L s)) (η X) ⟩
          ⟦ C ⟧ arr R (ε U) ◻ ⟦ C ⟧ arr R (arr L s) ◻ η X
            =⟨ ap (λ m → ⟦ C ⟧ arr R (ε U) ◻ m) (! (η-natural s)) ⟩
          ⟦ C ⟧ arr R (ε U) ◻ ⟦ C ⟧ η (obj R U) ◻ s
            =⟨ ! (α C (arr R (ε U)) (η (obj R U)) s) ⟩
          ⟦ C ⟧ (⟦ C ⟧ arr R (ε U) ◻ η (obj R U)) ◻ s
            =⟨ ap (λ m → ⟦ C ⟧ m ◻ s) (Gε-ηG U) ⟩
          ⟦ C ⟧ id₁ C (obj R U) ◻ s
            =⟨ ! (lamb C s) ⟩
          s =∎

        out-into : out ∘ into ∼ idf (hom D (obj L X) U)
        out-into r =
          ⟦ D ⟧ ε U ◻ arr L (⟦ C ⟧ arr R r ◻ η X)
            =⟨ ap (λ m → ⟦ D ⟧ ε U ◻ m) (comp L (η X) (arr R r)) ⟩
          ⟦ D ⟧ ε U ◻ ⟦ D ⟧ arr L (arr R r) ◻ arr L (η X)
            =⟨ ! (α D (ε U) (arr L (arr R r)) (arr L (η X))) ⟩
          ⟦ D ⟧ (⟦ D ⟧ ε U ◻ arr L (arr R r)) ◻ arr L (η X)
            =⟨ ap (λ m → ⟦ D ⟧ m ◻ arr L (η X)) (ε-natural r) ⟩
          ⟦ D ⟧ (⟦ D ⟧ r ◻ ε (obj L X)) ◻ arr L (η X)
            =⟨ α D r (ε (obj L X)) (arr L (η X)) ⟩
          ⟦ D ⟧ r ◻ ⟦ D ⟧ ε (obj L X) ◻ arr L (η X)
            =⟨ ap (λ m → ⟦ D ⟧ r ◻ m) (εF-Fη X) ⟩
          ⟦ D ⟧ r ◻ id₁ D (obj L X)
            =⟨ ! (ρ D r) ⟩
          r =∎

        eqv : hom D (obj L X) U ≃ hom C X (obj R U)
        eqv = equiv into out into-out out-into

      nat-cd : {X : ob C} {U V : ob D} (k : hom D U V) (r : hom D (obj L X) U)
        → ⟦ C ⟧ arr R k ◻ into r == into (⟦ D ⟧ k ◻ r)
      nat-cd {X} k r =
        ⟦ C ⟧ arr R k ◻ (⟦ C ⟧ arr R r ◻ η X)
          =⟨ ! (α C (arr R k) (arr R r) (η X)) ⟩
        ⟦ C ⟧ (⟦ C ⟧ arr R k ◻ arr R r) ◻ η X
          =⟨ ap (λ m → ⟦ C ⟧ m ◻ η X) (! (comp R r k)) ⟩
        ⟦ C ⟧ arr R (⟦ D ⟧ k ◻ r) ◻ η X =∎

      nat-d : {U : ob D} {X Y : ob C} (h : hom C X Y) (r : hom D (obj L Y) U)
        → ⟦ C ⟧ into r ◻ h == into (⟦ D ⟧ r ◻ arr L h)
      nat-d {U} {X} {Y} h r =
        ⟦ C ⟧ (⟦ C ⟧ arr R r ◻ η Y) ◻ h
          =⟨ α C (arr R r) (η Y) h ⟩
        ⟦ C ⟧ arr R r ◻ ⟦ C ⟧ η Y ◻ h
          =⟨ ap (λ m → ⟦ C ⟧ arr R r ◻ m) (η-natural h) ⟩
        ⟦ C ⟧ arr R r ◻ ⟦ C ⟧ arr R (arr L h) ◻ η X
          =⟨ ! (α C (arr R r) (arr R (arr L h)) (η X)) ⟩
        ⟦ C ⟧ (⟦ C ⟧ arr R r ◻ arr R (arr L h)) ◻ η X
          =⟨ ap (λ m → ⟦ C ⟧ m ◻ η X) (! (comp R (arr L h) r)) ⟩
        ⟦ C ⟧ arr R (⟦ D ⟧ r ◻ arr L h) ◻ η X =∎
