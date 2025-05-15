{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc
open import lib.wild-cats.Colim-wc
open import lib.wild-cats.Adjoint

module lib.wild-cats.Ladj-2-coher-id where

module _ {i₁ i₂ j₁ j₂} {C : WildCat {i₁} {j₁}} {D : WildCat {i₂} {j₂}}
  {L : Functor-wc C D} {R : Functor-wc D C} (adj : Adjunction L R) where

  private adj₀ = iso adj

  ladj-is-2coher-id : Type (lmax i₁ j₁)
  ladj-is-2coher-id = {x z w : ob C}
    (h₂ : hom C z x) (h₃ : hom C w z) →
      ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ (id₁ D (obj L x))) ◃∙
      nat-dom adj h₃ (⟦ D ⟧ (id₁ D (obj L x)) ◻ arr L h₂) ◃∙
      ap (–> adj₀)
        (α D (id₁ D (obj L x)) (arr L h₂) (arr L h₃) ∙
        ! (ap (λ m → ⟦ D ⟧ (id₁ D (obj L x)) ◻ m) (comp L h₃ h₂))) ◃∎
        =ₛ
      α C (–> adj₀ (id₁ D (obj L x))) h₂ h₃ ◃∙
      nat-dom adj (⟦ C ⟧ h₂ ◻ h₃) (id₁ D (obj L x)) ◃∎

  ladj-is-2coher-gen : Type (lmax (lmax (lmax i₁ i₂) j₁) j₂)
  ladj-is-2coher-gen = {x z w : ob C} {y : ob D}
    (h₁ : hom D (obj L x) y) (h₂ : hom C z x) (h₃ : hom C w z) →
      ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ h₁) ◃∙
      nat-dom adj h₃ (⟦ D ⟧ h₁ ◻ arr L h₂) ◃∙
      ap (–> adj₀)
        (α D h₁ (arr L h₂) (arr L h₃) ∙
        ! (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (comp L h₃ h₂))) ◃∎
        =ₛ
      α C (–> adj₀ h₁) h₂ h₃ ◃∙
      nat-dom adj (⟦ C ⟧ h₂ ◻ h₃) h₁ ◃∎

  module _ {x z w : ob C} {y : ob D}
    (h₁ : hom D (obj L x) y) (h₂ : hom C z x) (h₃ : hom C w z)
    (κ : ladj-is-2coher-id) where

     ladj-is-2coher-apR :
       ap (λ m → ⟦ C ⟧ arr R h₁ ◻ m) (ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ (id₁ D (obj L x)))) ◃∙
       ap (λ m → ⟦ C ⟧ arr R h₁ ◻ m) (nat-dom adj h₃ (⟦ D ⟧ id₁ D (obj L x) ◻ arr L h₂)) ◃∙
       ap (λ m → ⟦ C ⟧ arr R h₁ ◻ m) (ap (–> adj₀)
         (α D (id₁ D (obj L x)) (arr L h₂) (arr L h₃) ∙
         ! (ap (λ m → ⟦ D ⟧ (id₁ D (obj L x)) ◻ m) (comp L h₃ h₂)))) ◃∎
         =ₛ
       ap (λ m → ⟦ C ⟧ arr R h₁ ◻ m) (α C (–> adj₀ (id₁ D (obj L x))) h₂ h₃) ◃∙
       ap (λ m → ⟦ C ⟧ arr R h₁ ◻ m) (nat-dom adj (⟦ C ⟧ h₂ ◻ h₃) (id₁ D (obj L x))) ◃∎
     ladj-is-2coher-apR = ap-seq-=ₛ (λ m → ⟦ C ⟧ arr R h₁ ◻ m) (κ h₂ h₃)

     ladj-is-2coher-recover-aux = 
       ap (λ m → ⟦ C ⟧ arr R h₁ ◻ m) (ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ (id₁ D (obj L x)))) ◃∙
       ap (λ m → ⟦ C ⟧ arr R h₁ ◻ m) (nat-dom adj h₃ (⟦ D ⟧ id₁ D (obj L x) ◻ arr L h₂)) ◃∙
       ap (λ m → ⟦ C ⟧ arr R h₁ ◻ m) (ap (–> adj₀)
         (α D (id₁ D (obj L x)) (arr L h₂) (arr L h₃) ∙
         ! (ap (λ m → ⟦ D ⟧ (id₁ D (obj L x)) ◻ m) (comp L h₃ h₂)))) ◃∎
         =ₛ₁⟨ 2 & 1 & ∘-ap (λ m → ⟦ C ⟧ arr R h₁ ◻ m) (–> adj₀) _ ⟩
       ap (λ m → ⟦ C ⟧ arr R h₁ ◻ m) (ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ (id₁ D (obj L x)))) ◃∙
       ap (λ m → ⟦ C ⟧ arr R h₁ ◻ m) (nat-dom adj h₃ (⟦ D ⟧ id₁ D (obj L x) ◻ arr L h₂)) ◃∙
       ap (λ m → ⟦ C ⟧ arr R h₁ ◻ –> adj₀ m)
         (α D (id₁ D (obj L x)) (arr L h₂) (arr L h₃) ∙
         ! (ap (λ m → ⟦ D ⟧ (id₁ D (obj L x)) ◻ m) (comp L h₃ h₂))) ◃∎
         =ₛ⟨ 2 & 1 & 
           hmtpy-nat-∙◃ (nat-cod adj h₁)
             (α D (id₁ D (obj L x)) (arr L h₂) (arr L h₃) ∙ ! (ap (λ m → ⟦ D ⟧ id₁ D (obj L x) ◻ m) (comp L h₃ h₂))) ⟩
       ap (λ m → ⟦ C ⟧ arr R h₁ ◻ m) (ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ (id₁ D (obj L x)))) ◃∙
       ap (λ m → ⟦ C ⟧ arr R h₁ ◻ m) (nat-dom adj h₃ (⟦ D ⟧ id₁ D (obj L x) ◻ arr L h₂)) ◃∙
       nat-cod adj h₁ (⟦ D ⟧ (⟦ D ⟧ id₁ D (obj L x) ◻ arr L h₂) ◻ (arr L h₃)) ◃∙
       ap (λ m → –> adj₀ (⟦ D ⟧ h₁ ◻ m))
         (α D (id₁ D (obj L x)) (arr L h₂) (arr L h₃) ∙ ! (ap (λ m → ⟦ D ⟧ id₁ D (obj L x) ◻ m) (comp L h₃ h₂))) ◃∙
       ! (nat-cod adj h₁ (⟦ D ⟧ id₁ D (obj L x) ◻ arr L (⟦ C ⟧ h₂ ◻ h₃))) ◃∎
         =ₛ₁⟨ 3 & 1 & ap-∘ (–> adj₀) (λ m → ⟦ D ⟧ h₁ ◻ m)
           (α D (id₁ D (obj L x)) (arr L h₂) (arr L h₃) ∙ ! (ap (λ m → ⟦ D ⟧ id₁ D (obj L x) ◻ m) (comp L h₃ h₂))) ⟩
       ap (λ m → ⟦ C ⟧ arr R h₁ ◻ m) (ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ (id₁ D (obj L x)))) ◃∙
       ap (λ m → ⟦ C ⟧ arr R h₁ ◻ m) (nat-dom adj h₃ (⟦ D ⟧ id₁ D (obj L x) ◻ arr L h₂)) ◃∙
       nat-cod adj h₁ (⟦ D ⟧ (⟦ D ⟧ id₁ D (obj L x) ◻ arr L h₂) ◻ (arr L h₃)) ◃∙
       ap (–> adj₀) (ap (λ m →  ⟦ D ⟧ h₁ ◻ m)
         (α D (id₁ D (obj L x)) (arr L h₂) (arr L h₃) ∙ ! (ap (λ m → ⟦ D ⟧ id₁ D (obj L x) ◻ m) (comp L h₃ h₂)))) ◃∙
       ! (nat-cod adj h₁ (⟦ D ⟧ id₁ D (obj L x) ◻ arr L (⟦ C ⟧ h₂ ◻ h₃))) ◃∎
         =ₛ₁⟨ 3 & 1 & ap (ap (–> adj₀)) (ap-∙-! (λ m → ⟦ D ⟧ h₁ ◻ m)
           (α D (id₁ D (obj L x)) (arr L h₂) (arr L h₃))
           (ap (λ m → ⟦ D ⟧ id₁ D (obj L x) ◻ m) (comp L h₃ h₂))) ⟩
       ap (λ m → ⟦ C ⟧ arr R h₁ ◻ m) (ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ (id₁ D (obj L x)))) ◃∙
       ap (λ m → ⟦ C ⟧ arr R h₁ ◻ m) (nat-dom adj h₃ (⟦ D ⟧ id₁ D (obj L x) ◻ arr L h₂)) ◃∙
       nat-cod adj h₁ (⟦ D ⟧ (⟦ D ⟧ id₁ D (obj L x) ◻ arr L h₂) ◻ (arr L h₃)) ◃∙
       ap (–> adj₀)
         (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (α D (id₁ D (obj L x)) (arr L h₂) (arr L h₃)) ∙
         ! (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (ap (λ m → ⟦ D ⟧ id₁ D (obj L x) ◻ m) (comp L h₃ h₂)))) ◃∙
       ! (nat-cod adj h₁ (⟦ D ⟧ id₁ D (obj L x) ◻ arr L (⟦ C ⟧ h₂ ◻ h₃))) ◃∎
         =ₛ₁⟨ 3 & 1 & ap (λ p → ap (–> adj₀) (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (α D (id₁ D (obj L x)) (arr L h₂) (arr L h₃)) ∙ ! p))
           (∘-ap (λ m → ⟦ D ⟧ h₁ ◻ m) (λ m → ⟦ D ⟧ id₁ D (obj L x) ◻ m) (comp L h₃ h₂)) ⟩
       ap (λ m → ⟦ C ⟧ arr R h₁ ◻ m) (ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ (id₁ D (obj L x)))) ◃∙
       ap (λ m → ⟦ C ⟧ arr R h₁ ◻ m) (nat-dom adj h₃ (⟦ D ⟧ id₁ D (obj L x) ◻ arr L h₂)) ◃∙
       nat-cod adj h₁ (⟦ D ⟧ (⟦ D ⟧ id₁ D (obj L x) ◻ arr L h₂) ◻ (arr L h₃)) ◃∙
       ap (–> adj₀)
         (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (α D (id₁ D (obj L x)) (arr L h₂) (arr L h₃)) ∙
         ! (ap (λ m → ⟦ D ⟧ h₁ ◻ ⟦ D ⟧ id₁ D (obj L x) ◻ m) (comp L h₃ h₂))) ◃∙
       ! (nat-cod adj h₁ (⟦ D ⟧ id₁ D (obj L x) ◻ arr L (⟦ C ⟧ h₂ ◻ h₃))) ◃∎
         =ₛ₁⟨ 3 & 1 & ap (λ p → ap (–> adj₀) (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (α D (id₁ D (obj L x)) (arr L h₂) (arr L h₃)) ∙ p))
           (=ₛ-out (apCommSq◃-! (λ m → ap (λ m → ⟦ D ⟧ h₁ ◻ m) (lamb D m)) (comp L h₃ h₂))) ⟩
       ap (λ m → ⟦ C ⟧ arr R h₁ ◻ m) (ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ (id₁ D (obj L x)))) ◃∙
       ap (λ m → ⟦ C ⟧ arr R h₁ ◻ m) (nat-dom adj h₃ (⟦ D ⟧ id₁ D (obj L x) ◻ arr L h₂)) ◃∙
       nat-cod adj h₁ (⟦ D ⟧ (⟦ D ⟧ id₁ D (obj L x) ◻ arr L h₂) ◻ (arr L h₃)) ◃∙
       ap (–> adj₀)
         (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (α D (id₁ D (obj L x)) (arr L h₂) (arr L h₃)) ∙
         ! (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (lamb D (⟦ D ⟧ arr L h₂ ◻ arr L h₃))) ∙
         ! (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (comp L h₃ h₂)) ∙
         ap (λ m → ⟦ D ⟧ h₁ ◻ m) (lamb D (arr L (⟦ C ⟧ h₂ ◻ h₃)))) ◃∙
       ! (nat-cod adj h₁ (⟦ D ⟧ id₁ D (obj L x) ◻ arr L (⟦ C ⟧ h₂ ◻ h₃))) ◃∎
         =ₛ₁⟨ 3 & 1 & ap (ap (–> adj₀)) {!!} ⟩
       ap (λ m → ⟦ C ⟧ arr R h₁ ◻ m) (ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ (id₁ D (obj L x)))) ◃∙
       ap (λ m → ⟦ C ⟧ arr R h₁ ◻ m) (nat-dom adj h₃ (⟦ D ⟧ id₁ D (obj L x) ◻ arr L h₂)) ◃∙
       nat-cod adj h₁ (⟦ D ⟧ (⟦ D ⟧ id₁ D (obj L x) ◻ arr L h₂) ◻ (arr L h₃)) ◃∙
       ap (–> adj₀)
         (((ap (λ m → ⟦ D ⟧ h₁ ◻ m) (α D (id₁ D (obj L x)) (arr L h₂) (arr L h₃)) ∙
         ! (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (lamb D (⟦ D ⟧ arr L h₂ ◻ arr L h₃)))) ∙
         ! (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (comp L h₃ h₂))) ∙
         ap (λ m → ⟦ D ⟧ h₁ ◻ m) (lamb D (arr L (⟦ C ⟧ h₂ ◻ h₃)))) ◃∙
       ! (nat-cod adj h₁ (⟦ D ⟧ id₁ D (obj L x) ◻ arr L (⟦ C ⟧ h₂ ◻ h₃))) ◃∎
         =ₛ⟨ 3 & 1 & ap-∙◃ (–> adj₀)
           ((ap (λ m → ⟦ D ⟧ h₁ ◻ m) (α D (id₁ D (obj L x)) (arr L h₂) (arr L h₃)) ∙
           ! (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (lamb D (⟦ D ⟧ arr L h₂ ◻ arr L h₃)))) ∙
           ! (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (comp L h₃ h₂)))
           (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (lamb D (arr L (⟦ C ⟧ h₂ ◻ h₃)))) ⟩
       ap (λ m → ⟦ C ⟧ arr R h₁ ◻ m) (ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ (id₁ D (obj L x)))) ◃∙
       ap (λ m → ⟦ C ⟧ arr R h₁ ◻ m) (nat-dom adj h₃ (⟦ D ⟧ id₁ D (obj L x) ◻ arr L h₂)) ◃∙
       nat-cod adj h₁ (⟦ D ⟧ (⟦ D ⟧ id₁ D (obj L x) ◻ arr L h₂) ◻ (arr L h₃)) ◃∙
       ap (–> adj₀)
         ((ap (λ m → ⟦ D ⟧ h₁ ◻ m) (α D (id₁ D (obj L x)) (arr L h₂) (arr L h₃)) ∙
         ! (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (lamb D (⟦ D ⟧ arr L h₂ ◻ arr L h₃)))) ∙
         ! (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (comp L h₃ h₂))) ◃∙
       ap (–> adj₀) (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (lamb D (arr L (⟦ C ⟧ h₂ ◻ h₃)))) ◃∙
       ! (nat-cod adj h₁ (⟦ D ⟧ id₁ D (obj L x) ◻ arr L (⟦ C ⟧ h₂ ◻ h₃))) ◃∎
         =ₛ₁⟨ 4 & 1 & ∘-ap (–> adj₀) (λ m → ⟦ D ⟧ h₁ ◻ m) (lamb D (arr L (⟦ C ⟧ h₂ ◻ h₃))) ⟩
       ap (λ m → ⟦ C ⟧ arr R h₁ ◻ m) (ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ (id₁ D (obj L x)))) ◃∙
       ap (λ m → ⟦ C ⟧ arr R h₁ ◻ m) (nat-dom adj h₃ (⟦ D ⟧ id₁ D (obj L x) ◻ arr L h₂)) ◃∙
       nat-cod adj h₁ (⟦ D ⟧ (⟦ D ⟧ id₁ D (obj L x) ◻ arr L h₂) ◻ (arr L h₃)) ◃∙
       ap (–> adj₀)
         ((ap (λ m → ⟦ D ⟧ h₁ ◻ m) (α D (id₁ D (obj L x)) (arr L h₂) (arr L h₃)) ∙
         ! (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (lamb D (⟦ D ⟧ arr L h₂ ◻ arr L h₃)))) ∙
         ! (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (comp L h₃ h₂))) ◃∙
       ap (λ m → –> adj₀ (⟦ D ⟧ h₁ ◻ m)) (lamb D (arr L (⟦ C ⟧ h₂ ◻ h₃))) ◃∙
       ! (nat-cod adj h₁ (⟦ D ⟧ id₁ D (obj L x) ◻ arr L (⟦ C ⟧ h₂ ◻ h₃))) ◃∎
         =ₛ⟨ 4 & 2 & {!!} ⟩
       {!!}
       where abstract
         rearrange :
           ap (λ m → ⟦ D ⟧ h₁ ◻ m) (α D (id₁ D (obj L x)) (arr L h₂) (arr L h₃)) ∙
           ! (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (lamb D (⟦ D ⟧ arr L h₂ ◻ arr L h₃))) ∙
           ! (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (comp L h₃ h₂)) ∙
           ap (λ m → ⟦ D ⟧ h₁ ◻ m) (lamb D (arr L (⟦ C ⟧ h₂ ◻ h₃)))
             ==
           ((ap (λ m → ⟦ D ⟧ h₁ ◻ m) (α D (id₁ D (obj L x)) (arr L h₂) (arr L h₃)) ∙
           ! (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (lamb D (⟦ D ⟧ arr L h₂ ◻ arr L h₃)))) ∙
           ! (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (comp L h₃ h₂))) ∙
           ap (λ m → ⟦ D ⟧ h₁ ◻ m) (lamb D (arr L (⟦ C ⟧ h₂ ◻ h₃)))
         rearrange = =ₛ-out $
           ap (λ m → ⟦ D ⟧ h₁ ◻ m) (α D (id₁ D (obj L x)) (arr L h₂) (arr L h₃)) ◃∙
           ! (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (lamb D (⟦ D ⟧ arr L h₂ ◻ arr L h₃))) ◃∙
           ! (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (comp L h₃ h₂)) ◃∙
           ap (λ m → ⟦ D ⟧ h₁ ◻ m) (lamb D (arr L (⟦ C ⟧ h₂ ◻ h₃))) ◃∎
             =ₛ₁⟨ 0 & 2 & idp ⟩
           (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (α D (id₁ D (obj L x)) (arr L h₂) (arr L h₃)) ∙
           ! (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (lamb D (⟦ D ⟧ arr L h₂ ◻ arr L h₃)))) ◃∙
           ! (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (comp L h₃ h₂)) ◃∙
           ap (λ m → ⟦ D ⟧ h₁ ◻ m) (lamb D (arr L (⟦ C ⟧ h₂ ◻ h₃))) ◃∎
             =ₛ₁⟨ 0 & 2 & idp ⟩
           ((ap (λ m → ⟦ D ⟧ h₁ ◻ m) (α D (id₁ D (obj L x)) (arr L h₂) (arr L h₃)) ∙
           ! (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (lamb D (⟦ D ⟧ arr L h₂ ◻ arr L h₃)))) ∙
           ! (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (comp L h₃ h₂))) ◃∙
           ap (λ m → ⟦ D ⟧ h₁ ◻ m) (lamb D (arr L (⟦ C ⟧ h₂ ◻ h₃))) ◃∎ ∎ₛ
           
{-
     ladj-is-2coher-recover :
       ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ h₁) ◃∙
       nat-dom adj h₃ (⟦ D ⟧ h₁ ◻ arr L h₂) ◃∙
       ap (–> adj₀)
         (α D h₁ (arr L h₂) (arr L h₃) ∙
         ! (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (comp L h₃ h₂))) ◃∎
         =ₛ
       α C (–> adj₀ h₁) h₂ h₃ ◃∙
       nat-dom adj (⟦ C ⟧ h₂ ◻ h₃) h₁ ◃∎
     ladj-is-2coher-recover = 
       ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ h₁) ◃∙
       nat-dom adj h₃ (⟦ D ⟧ h₁ ◻ arr L h₂) ◃∙
       ap (–> adj₀)
         (α D h₁ (arr L h₂) (arr L h₃) ∙
         ! (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (comp L h₃ h₂))) ◃∎
         =ₛ⟨ 2 & 1 & {!!} ⟩
       {!!}
-}
