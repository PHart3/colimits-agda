{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Sigma
open import lib.types.Graph

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

-- underlying graph of a wild category
wc-graph : ∀ {i j} → WildCat {i} {j} → Graph i j
Obj (wc-graph C) = ob C
Hom (wc-graph C) = hom C

infixr 82 ⟦_⟧_◻_
⟦_⟧_◻_ : ∀ {i j} (C : WildCat {i} {j}) {a b c : ob C} → hom C b c → hom C a b → hom C a c
⟦_⟧_◻_ ξ g f = _◻_ ξ g f 

record Functor-wc {i₁ j₁ i₂ j₂} (B : WildCat {i₁} {j₁}) (C : WildCat {i₂} {j₂}) :
  Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
  constructor functor-wc
  field
    obj : ob B → ob C
    arr : {a b : ob B} → hom B a b → hom C (obj a) (obj b)
    id : (a : ob B) → arr (id₁ B a) == id₁ C (obj a)
    comp : {a b c : ob B} (f : hom B a b) (g : hom B b c) → arr (⟦ B ⟧ g ◻ f) == ⟦ C ⟧ arr g ◻ arr f
open Functor-wc public

module _ {i j} (C : WildCat {i} {j}) where

  equiv-wc : {a b : ob C} → hom C a b → Type j
  equiv-wc {a} {b} f = Σ (hom C b a) (λ g → (id₁ C a == ⟦ C ⟧ g ◻ f) × (id₁ C b == ⟦ C ⟧ f ◻ g))
  
  module _ {a b : ob C} {f : hom C a b} (e : equiv-wc f) where

    <–-wc : hom C b a
    <–-wc = fst e

    <–-wc-linv : id₁ C a == ⟦ C ⟧ <–-wc ◻ f
    <–-wc-linv = fst (snd e)

    <–-wc-rinv : id₁ C b == ⟦ C ⟧ f ◻ <–-wc
    <–-wc-rinv = snd (snd e)

    hom-dom-eqv : {c : ob C} → hom C b c ≃ hom C a c
    hom-dom-eqv = equiv (λ g → ⟦ C ⟧ g ◻ f) (λ g → ⟦ C ⟧ g ◻ <–-wc)
      (λ g → α C g <–-wc f ∙ ap (λ m → ⟦ C ⟧ g ◻ m) (! <–-wc-linv) ∙ ! (ρ C g))
      λ g → α C g f <–-wc ∙ ap (λ m → ⟦ C ⟧ g ◻ m) (! <–-wc-rinv) ∙ ! (ρ C g) 

Type-wc : (i : ULevel) → WildCat {lsucc i} {i}
ob (Type-wc i) = Type i
hom (Type-wc i) A B = A → B
id₁ (Type-wc i) = idf
_◻_ (Type-wc i) g f = g ∘ f
ρ (Type-wc i) = λ _ → idp
lamb (Type-wc i) = λ _ → idp
α (Type-wc i) = λ _ _ _ → idp

-- pentagon identity and some variants

pentagon-wc : ∀ {i j} (C : WildCat {i} {j}) → Type (lmax i j)
pentagon-wc C = {a b c d e : ob C} (k : hom C d e) (g : hom C c d) (h : hom C b c) (f : hom C a b) →
  ap (λ m → ⟦ C ⟧ m ◻ f) (α C k g h) ∙ α C k (⟦ C ⟧ g ◻ h) f ∙ ap (λ m → ⟦ C ⟧ k ◻ m) (α C g h f)
    ==
  α C (⟦ C ⟧ k ◻ g) h f ∙ α C k g (⟦ C ⟧ h ◻ f)

module _ {i j} {C : WildCat {i} {j}} (pent : pentagon-wc C)
  {a b c d e : ob C} (k : hom C d e) (g : hom C c d) (h : hom C b c) (f : hom C a b) where

  abstract

    pentagon-wc◃ :
      ap (λ m → ⟦ C ⟧ m ◻ f) (α C k g h) ◃∙ α C k (⟦ C ⟧ g ◻ h) f ◃∙ ap (λ m → ⟦ C ⟧ k ◻ m) (α C g h f) ◃∎
        =ₛ
      α C (⟦ C ⟧ k ◻ g) h f ◃∙ α C k g (⟦ C ⟧ h ◻ f) ◃∎
    pentagon-wc◃ = =ₛ-in (pent k g h f)

    pentagon-wc-! :
      ! (ap (λ m → ⟦ C ⟧ k ◻ m) (α C g h f)) ◃∙ ! (α C k (⟦ C ⟧ g ◻ h) f) ◃∙ ! (ap (λ m → ⟦ C ⟧ m ◻ f) (α C k g h)) ◃∎ 
        =ₛ
      ! (α C k g (⟦ C ⟧ h ◻ f)) ◃∙ ! (α C (⟦ C ⟧ k ◻ g) h f) ◃∎
    pentagon-wc-! = !-=ₛ pentagon-wc◃

    pentagon-wc-rot1 : 
      ! (α C (⟦ C ⟧ k ◻ g) h f) ◃∙ ap (λ m → ⟦ C ⟧ m ◻ f) (α C k g h) ◃∙ α C k (⟦ C ⟧ g ◻ h) f ◃∎
        =ₛ
      α C k g (⟦ C ⟧ h ◻ f) ◃∙ ! (ap (λ m → ⟦ C ⟧ k ◻ m) (α C g h f)) ◃∎
    pentagon-wc-rot1 = post-rotate-in (pre-rotate'-in pentagon-wc◃)

    pentagon-wc-rot2 : 
      ! (α C k (⟦ C ⟧ g ◻ h) f) ◃∙ ap (λ m → ⟦ C ⟧ m ◻ f) (! (α C k g h)) ◃∙ α C (⟦ C ⟧ k ◻ g) h f ◃∎
        =ₛ
      ap (λ m → ⟦ C ⟧ k ◻ m) (α C g h f) ◃∙ ! (α C k g (⟦ C ⟧ h ◻ f)) ◃∎
    pentagon-wc-rot2 = 
      ! (α C k (⟦ C ⟧ g ◻ h) f) ◃∙ ap (λ m → ⟦ C ⟧ m ◻ f) (! (α C k g h)) ◃∙ α C (⟦ C ⟧ k ◻ g) h f ◃∎
        =ₛ₁⟨ 1 & 1 & ap-! (λ m → ⟦ C ⟧ m ◻ f) (α C k g h) ⟩
      ! (α C k (⟦ C ⟧ g ◻ h) f) ◃∙ ! (ap (λ m → ⟦ C ⟧ m ◻ f) (α C k g h)) ◃∙ α C (⟦ C ⟧ k ◻ g) h f ◃∎
        =ₛ₁⟨ 2 & 1 & ! (!-! _) ⟩
      ! (α C k (⟦ C ⟧ g ◻ h) f) ◃∙ ! (ap (λ m → ⟦ C ⟧ m ◻ f) (α C k g h)) ◃∙ ! (! (α C (⟦ C ⟧ k ◻ g) h f)) ◃∎
        =ₛ⟨ !-=ₛ pentagon-wc-rot1 ⟩
      ! (! (ap (λ m → ⟦ C ⟧ k ◻ m) (α C g h f))) ◃∙ ! (α C k g (⟦ C ⟧ h ◻ f)) ◃∎
        =ₛ₁⟨ 0 & 1 & !-! _ ⟩
      ap (λ m → ⟦ C ⟧ k ◻ m) (α C g h f) ◃∙ ! (α C k g (⟦ C ⟧ h ◻ f)) ◃∎ ∎ₛ

    pentagon-wc-rot3 :
      ap (λ m → ⟦ C ⟧ k ◻ m) (α C g h f) ◃∎
          =ₛ
      ! (α C k (⟦ C ⟧ g ◻ h) f) ◃∙ ap (λ m → ⟦ C ⟧ m ◻ f) (! (α C k g h)) ◃∙ α C (⟦ C ⟧ k ◻ g) h f ◃∙ α C k g (⟦ C ⟧ h ◻ f) ◃∎
    pentagon-wc-rot3 = pre-rotate-in (pre-rotate-in pentagon-wc◃) ∙ₛ aux
      where abstract
        aux :
          ! (α C k (⟦ C ⟧ g ◻ h) f) ◃∙ ! (ap (λ m → ⟦ C ⟧ m ◻ f) (α C k g h)) ◃∙ α C (⟦ C ⟧ k ◻ g) h f ◃∙ α C k g (⟦ C ⟧ h ◻ f) ◃∎
            =ₛ
          ! (α C k (⟦ C ⟧ g ◻ h) f) ◃∙ ap (λ m → ⟦ C ⟧ m ◻ f) (! (α C k g h)) ◃∙ α C (⟦ C ⟧ k ◻ g) h f ◃∙ α C k g (⟦ C ⟧ h ◻ f) ◃∎
        aux =
          ! (α C k (⟦ C ⟧ g ◻ h) f) ◃∙ ! (ap (λ m → ⟦ C ⟧ m ◻ f) (α C k g h)) ◃∙ α C (⟦ C ⟧ k ◻ g) h f ◃∙ α C k g (⟦ C ⟧ h ◻ f) ◃∎
            =ₛ₁⟨ 1 & 1 & !-ap (λ m → ⟦ C ⟧ m ◻ f) (α C k g h) ⟩
          ! (α C k (⟦ C ⟧ g ◻ h) f) ◃∙ ap (λ m → ⟦ C ⟧ m ◻ f) (! (α C k g h)) ◃∙ α C (⟦ C ⟧ k ◻ g) h f ◃∙ α C k g (⟦ C ⟧ h ◻ f) ◃∎ ∎ₛ
