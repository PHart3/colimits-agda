{-# OPTIONS --without-K --rewriting #-}

open import lib.Base

module lib.wild-cats.WildCat where

record WildCat {i j} : Type (lmax (lsucc i) (lsucc j)) where
  constructor wildcat
  infixr 82 _◻_
  field
    ob : Type i
    hom : ob → ob → Type j
    id₁ : (a : ob) → hom a a
    _◻_ : {a b c : ob} → hom b c → hom a b → hom a c
    ρ : {a b : ob} (f : hom a b) → f == f ◻ id₁ a
    lamb : {a b : ob} (f : hom a b) → f == id₁ b ◻ f
    α : {a b c d : ob} (h : hom c d) (g : hom b c) (f : hom a b) → (h ◻ g) ◻ f == h ◻ g ◻ f

open WildCat public

infixr 82 ⟦_⟧_◻_
⟦_⟧_◻_ : ∀ {i j} (C : WildCat {i} {j}) {a b c : ob C} → hom C b c → hom C a b → hom C a c
⟦_⟧_◻_ ξ g f = _◻_ ξ g f 

record Functor-wc {i₁ j₁ i₂ j₂} (B : WildCat {i₁} {j₁}) (C : WildCat {i₂} {j₂}) :
  Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
  constructor functor-wc
  field
    F₀ : ob B → ob C
    F₁ : {a b : ob B} → hom B a b → hom C (F₀ a) (F₀ b)
    F-id₁ : (a : ob B) → F₁ (id₁ B a) == id₁ C (F₀ a)
    F-◻ : {a b c : ob B} (f : hom B a b) (g : hom B b c) → F₁ (⟦ B ⟧ g ◻ f) == ⟦ C ⟧ F₁ g ◻ F₁ f

open Functor-wc public

Type-wc : (i : ULevel) → WildCat {lsucc i} {i}
ob (Type-wc i) = Type i
hom (Type-wc i) A B = A → B
id₁ (Type-wc i) = idf
_◻_ (Type-wc i) g f = g ∘ f
ρ (Type-wc i) = λ _ → idp
lamb (Type-wc i) = λ _ → idp
α (Type-wc i) = λ _ _ _ → idp
