{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Sigma hiding (diag)
open import lib.wild-cats.WildCat

-- fillers of commuting squares in a wild category

module lib.wild-cats.Filler-wc where

module _ {i j} {C : WildCat {i} {j}} where

  -- the type of fillers
  record Fill-wc {a b c d : ob C} {l : hom C a b} {r : hom C c d}
    (f : hom C a c) (g : hom C b d) (S : ⟦ C ⟧ g ◻ l == ⟦ C ⟧ r ◻ f) : Type (lmax i j) where
    constructor fillwc
    field
      diag : hom C b c
      tri-top : ⟦ C ⟧ diag ◻ l == f
      tri-bottom : ⟦ C ⟧ r ◻ diag == g
      tri-coh : α C r diag l ∙ ap (λ m → ⟦ C ⟧ r ◻ m) tri-top == ap (λ m → ⟦ C ⟧ m ◻ l) tri-bottom ∙ S
    abstract
    
      tri-coh-◃ : α C r diag l ◃∙ ap (λ m → ⟦ C ⟧ r ◻ m) tri-top ◃∎ =ₛ ap (λ m → ⟦ C ⟧ m ◻ l) tri-bottom ◃∙ S ◃∎
      tri-coh-◃ = =ₛ-in tri-coh

      tri-coh-rot1 : ap (λ m → ⟦ C ⟧ r ◻ m) tri-top ◃∎ =ₛ ! (α C r diag l) ◃∙ ap (λ m → ⟦ C ⟧ m ◻ l) tri-bottom ◃∙ S ◃∎
      tri-coh-rot1 = pre-rotate-in tri-coh-◃

  Fill-wc-Σ : {a b c d : ob C} {l : hom C a b} {r : hom C c d}
    (f : hom C a c) (g : hom C b d) (T : ⟦ C ⟧ g ◻ l == ⟦ C ⟧ r ◻ f) →
    Fill-wc f g T
      ≃
    [ diag ∈ hom C b c ] × [ (tri-top , tri-bottom) ∈ (⟦ C ⟧ diag ◻ l == f) × (⟦ C ⟧ r ◻ diag == g) ]  ×
      (α C r diag l ∙ ap (λ m → ⟦ C ⟧ r ◻ m) tri-top == ap (λ m → ⟦ C ⟧ m ◻ l) tri-bottom ∙ T)
  Fill-wc-Σ f g T = equiv
    (λ (fillwc diag tri-top tri-bottom tri-coh) → diag , ((tri-top , tri-bottom) , tri-coh))
    (λ (diag , (tri-top , tri-bottom) , tri-coh) → fillwc diag tri-top tri-bottom tri-coh)
    (λ _ → idp)
    λ _ → idp

  -- left lifting property against a class of morphisms
  llp-wc : ∀ {k} (H : ∀ {a b} → hom C a b → -1 -Type k) {a b : ob C} (l : hom C a b) → Type (lmax (lmax i j) k)
  llp-wc H {a} {b} l = ∀ {c d} {r : hom C c d} (r-H : fst (H r))
    (f : hom C a c) (g : hom C b d) (S : ⟦ C ⟧ g ◻ l == ⟦ C ⟧ r ◻ f) → is-contr (Fill-wc f g S)
