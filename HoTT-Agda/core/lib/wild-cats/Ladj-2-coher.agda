{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc
open import lib.wild-cats.Colim-wc
open import lib.wild-cats.Adjoint

module lib.wild-cats.Ladj-2-coher where

module _ {i₁ i₂ j₁ j₂} {C : WildCat {i₁} {j₁}} {D : WildCat {i₂} {j₂}}
  {L : Functor-wc C D} {R : Functor-wc D C} (adj : Adjunction L R) where

  private adj₀ = comp adj

  ladj-is-2coher : Type (lmax (lmax i₁ i₂) (lmax j₁ j₂))
  ladj-is-2coher =
    {x z w : ob C} {y : ob D} (h₁ : hom D (F₀ L x) y) (h₂ : hom C z x) (h₃ : hom C w z) →
      ! (α C (–> adj₀ h₁) h₂ h₃) ∙
      ap (λ m → ⟦ C ⟧ m ◻ h₃) (sq₂ adj h₂ h₁) ∙
      sq₂ adj h₃ (⟦ D ⟧ h₁ ◻ F₁ L h₂) ∙
      ap (–> adj₀)
        (α D h₁ (F₁ L h₂) (F₁ L h₃) ∙ ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (F-◻ L h₃ h₂))) ∙
      ! (sq₂ adj (⟦ C ⟧ h₂ ◻ h₃) h₁)
        ==
      idp

  module _ (p : ladj-is-2coher)
    {x z w : ob C} {y : ob D} (h₁ : hom D (F₀ L x) y) (h₂ : hom C z x) (h₃ : hom C w z) where

    2coher-other-aux =
      ! (ap (<– adj₀) (α C (–> adj₀ h₁) h₂ h₃)) ◃∙
      ap (<– adj₀) (ap (λ m → ⟦ C ⟧ m ◻ h₃) (sq₂ adj h₂ h₁)) ◃∙
      ap (<– adj₀) (sq₂ adj h₃ (⟦ D ⟧ h₁ ◻ F₁ L h₂)) ◃∙
      <–-inv-l adj₀ ((D ◻ (D ◻ h₁) (F₁ L h₂)) (F₁ L h₃)) ◃∙
      α D h₁ (F₁ L h₂) (F₁ L h₃) ◃∙
      ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (F-◻ L h₃ h₂)) ◃∙
      ! (<–-inv-l adj₀ (⟦ D ⟧ h₁ ◻ F₁ L (⟦ C ⟧ h₂ ◻ h₃))) ◃∙
      ! (ap (<– adj₀) (sq₂ adj (⟦ C ⟧ h₂ ◻ h₃) h₁)) ◃∎
        =ₛ₁⟨ 0 & 1 & !-ap (<– adj₀) (α C (–> adj₀ h₁) h₂ h₃) ⟩
      ap (<– adj₀) (! (α C (–> adj₀ h₁) h₂ h₃)) ◃∙
      ap (<– adj₀) (ap (λ m → ⟦ C ⟧ m ◻ h₃) (sq₂ adj h₂ h₁)) ◃∙
      ap (<– adj₀) (sq₂ adj h₃ (⟦ D ⟧ h₁ ◻ F₁ L h₂)) ◃∙
      <–-inv-l adj₀ ((D ◻ (D ◻ h₁) (F₁ L h₂)) (F₁ L h₃)) ◃∙
      α D h₁ (F₁ L h₂) (F₁ L h₃) ◃∙
      ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (F-◻ L h₃ h₂)) ◃∙
      ! (<–-inv-l adj₀ (⟦ D ⟧ h₁ ◻ F₁ L (⟦ C ⟧ h₂ ◻ h₃))) ◃∙
      ! (ap (<– adj₀) (sq₂ adj (⟦ C ⟧ h₂ ◻ h₃) h₁)) ◃∎
        =ₛ₁⟨ 7 & 1 & !-ap (<– adj₀) (sq₂ adj (⟦ C ⟧ h₂ ◻ h₃) h₁) ⟩
      ap (<– adj₀) (! (α C (–> adj₀ h₁) h₂ h₃)) ◃∙
      ap (<– adj₀) (ap (λ m → ⟦ C ⟧ m ◻ h₃) (sq₂ adj h₂ h₁)) ◃∙
      ap (<– adj₀) (sq₂ adj h₃ (⟦ D ⟧ h₁ ◻ F₁ L h₂)) ◃∙
      <–-inv-l adj₀ ((D ◻ (D ◻ h₁) (F₁ L h₂)) (F₁ L h₃)) ◃∙
      α D h₁ (F₁ L h₂) (F₁ L h₃) ◃∙
      ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (F-◻ L h₃ h₂)) ◃∙
      ! (<–-inv-l adj₀ (⟦ D ⟧ h₁ ◻ F₁ L (⟦ C ⟧ h₂ ◻ h₃))) ◃∙
      ap (<– adj₀) (! (sq₂ adj (⟦ C ⟧ h₂ ◻ h₃) h₁)) ◃∎
        =ₑ⟨ 4 & 2 & (α D h₁ (F₁ L h₂) (F₁ L h₃) ∙ ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (F-◻ L h₃ h₂))) ◃∎ %  =ₛ-in idp ⟩
      ap (<– adj₀) (! (α C (–> adj₀ h₁) h₂ h₃)) ◃∙
      ap (<– adj₀) (ap (λ m → ⟦ C ⟧ m ◻ h₃) (sq₂ adj h₂ h₁)) ◃∙
      ap (<– adj₀) (sq₂ adj h₃ (⟦ D ⟧ h₁ ◻ F₁ L h₂)) ◃∙
      <–-inv-l adj₀ ((D ◻ (D ◻ h₁) (F₁ L h₂)) (F₁ L h₃)) ◃∙
      (α D h₁ (F₁ L h₂) (F₁ L h₃) ∙ ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (F-◻ L h₃ h₂))) ◃∙
      ! (<–-inv-l adj₀ (⟦ D ⟧ h₁ ◻ F₁ L (⟦ C ⟧ h₂ ◻ h₃))) ◃∙
      ap (<– adj₀) (! (sq₂ adj (⟦ C ⟧ h₂ ◻ h₃) h₁)) ◃∎
        =ₛ₁⟨ 4 & 1 & ! (ap-idf (α D h₁ (F₁ L h₂) (F₁ L h₃) ∙ ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (F-◻ L h₃ h₂)))) ⟩
      ap (<– adj₀) (! (α C (–> adj₀ h₁) h₂ h₃)) ◃∙
      ap (<– adj₀) (ap (λ m → ⟦ C ⟧ m ◻ h₃) (sq₂ adj h₂ h₁)) ◃∙
      ap (<– adj₀) (sq₂ adj h₃ (⟦ D ⟧ h₁ ◻ F₁ L h₂)) ◃∙
      <–-inv-l adj₀ ((D ◻ (D ◻ h₁) (F₁ L h₂)) (F₁ L h₃)) ◃∙
      ap (λ z → z) (α D h₁ (F₁ L h₂) (F₁ L h₃) ∙ ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (F-◻ L h₃ h₂))) ◃∙
      ! (<–-inv-l adj₀ (⟦ D ⟧ h₁ ◻ F₁ L (⟦ C ⟧ h₂ ◻ h₃))) ◃∙
      ap (<– adj₀) (! (sq₂ adj (⟦ C ⟧ h₂ ◻ h₃) h₁)) ◃∎
        =ₛ⟨ 3 & 3 & !ₛ $
          hmtpy-nat-∙◃ (<–-inv-l adj₀) (α D h₁ (F₁ L h₂) (F₁ L h₃) ∙ ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (F-◻ L h₃ h₂))) ⟩
      ap (<– adj₀) (! (α C (–> adj₀ h₁) h₂ h₃)) ◃∙
      ap (<– adj₀) (ap (λ m → ⟦ C ⟧ m ◻ h₃) (sq₂ adj h₂ h₁)) ◃∙
      ap (<– adj₀) (sq₂ adj h₃ (⟦ D ⟧ h₁ ◻ F₁ L h₂)) ◃∙
      ap (<– adj₀ ∘ –> adj₀) (α D h₁ (F₁ L h₂) (F₁ L h₃) ∙ ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (F-◻ L h₃ h₂))) ◃∙
      ap (<– adj₀) (! (sq₂ adj (⟦ C ⟧ h₂ ◻ h₃) h₁)) ◃∎
        =ₛ₁⟨ 3 & 1 & ap-∘ (<– adj₀) (–> adj₀) (α D h₁ (F₁ L h₂) (F₁ L h₃) ∙ ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (F-◻ L h₃ h₂))) ⟩
      ap (<– adj₀) (! (α C (–> adj₀ h₁) h₂ h₃)) ◃∙
      ap (<– adj₀) (ap (λ m → ⟦ C ⟧ m ◻ h₃) (sq₂ adj h₂ h₁)) ◃∙
      ap (<– adj₀) (sq₂ adj h₃ (⟦ D ⟧ h₁ ◻ F₁ L h₂)) ◃∙
      ap (<– adj₀) (ap (–> adj₀) (α D h₁ (F₁ L h₂) (F₁ L h₃) ∙ ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (F-◻ L h₃ h₂)))) ◃∙
      ap (<– adj₀) (! (sq₂ adj (⟦ C ⟧ h₂ ◻ h₃) h₁)) ◃∎
        =ₛ⟨ ap-seq-=ₛ (<– adj₀) (=ₛ-in (p h₁ h₂ h₃)) ⟩ 
      idp ◃∎ ∎ₛ

    abstract
      2coher-other :
        α D h₁ (F₁ L h₂) (F₁ L h₃) ◃∙
        ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (F-◻ L h₃ h₂)) ◃∎
          =ₛ
        ! (<–-inv-l adj₀ ((D ◻ (D ◻ h₁) (F₁ L h₂)) (F₁ L h₃))) ◃∙
        ! (ap (<– adj₀) (sq₂ adj h₃ (⟦ D ⟧ h₁ ◻ F₁ L h₂))) ◃∙
        ! (ap (λ m → <– adj₀ (⟦ C ⟧ m ◻ h₃)) (sq₂ adj h₂ h₁)) ◃∙
        ap (<– adj₀) (α C (–> adj₀ h₁) h₂ h₃) ◃∙
        ap (<– adj₀) (sq₂ adj (⟦ C ⟧ h₂ ◻ h₃) h₁) ◃∙
        <–-inv-l adj₀ (⟦ D ⟧ h₁ ◻ F₁ L (⟦ C ⟧ h₂ ◻ h₃)) ◃∎
      2coher-other =
        α D h₁ (F₁ L h₂) (F₁ L h₃) ◃∙
        ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (F-◻ L h₃ h₂)) ◃∎
          =ₛ⟨ pre-rotate-in $
            pre-rotate-in (pre-rotate-in (pre-rotate'-out (post-rotate'-out (post-rotate'-out (2coher-other-aux))))) ⟩
        ! (<–-inv-l adj₀ ((D ◻ (D ◻ h₁) (F₁ L h₂)) (F₁ L h₃))) ◃∙
        ! (ap (<– adj₀) (sq₂ adj h₃ (⟦ D ⟧ h₁ ◻ F₁ L h₂))) ◃∙
        ! (ap (<– adj₀) (ap (λ m → ⟦ C ⟧ m ◻ h₃) (sq₂ adj h₂ h₁))) ◃∙
        ap (<– adj₀) (α C (–> adj₀ h₁) h₂ h₃) ◃∙
        idp ◃∙
        ap (<– adj₀) (sq₂ adj (⟦ C ⟧ h₂ ◻ h₃) h₁) ◃∙
        <–-inv-l adj₀ (⟦ D ⟧ h₁ ◻ F₁ L (⟦ C ⟧ h₂ ◻ h₃)) ◃∎
          =ₛ₁⟨ 4 & 2 & idp ⟩
        ! (<–-inv-l adj₀ ((D ◻ (D ◻ h₁) (F₁ L h₂)) (F₁ L h₃))) ◃∙
        ! (ap (<– adj₀) (sq₂ adj h₃ (⟦ D ⟧ h₁ ◻ F₁ L h₂))) ◃∙
        ! (ap (<– adj₀) (ap (λ m → ⟦ C ⟧ m ◻ h₃) (sq₂ adj h₂ h₁))) ◃∙
        ap (<– adj₀) (α C (–> adj₀ h₁) h₂ h₃) ◃∙
        ap (<– adj₀) (sq₂ adj (⟦ C ⟧ h₂ ◻ h₃) h₁) ◃∙
        <–-inv-l adj₀ (⟦ D ⟧ h₁ ◻ F₁ L (⟦ C ⟧ h₂ ◻ h₃)) ◃∎
          =ₛ₁⟨ 2 & 1 & ap ! (∘-ap (<– adj₀) (λ m → ⟦ C ⟧ m ◻ h₃) (sq₂ adj h₂ h₁)) ⟩
        ! (<–-inv-l adj₀ ((D ◻ (D ◻ h₁) (F₁ L h₂)) (F₁ L h₃))) ◃∙
        ! (ap (<– adj₀) (sq₂ adj h₃ (⟦ D ⟧ h₁ ◻ F₁ L h₂))) ◃∙
        ! (ap (λ m → <– adj₀ (⟦ C ⟧ m ◻ h₃)) (sq₂ adj h₂ h₁)) ◃∙
        ap (<– adj₀) (α C (–> adj₀ h₁) h₂ h₃) ◃∙
        ap (<– adj₀) (sq₂ adj (⟦ C ⟧ h₂ ◻ h₃) h₁) ◃∙
        <–-inv-l adj₀ (⟦ D ⟧ h₁ ◻ F₁ L (⟦ C ⟧ h₂ ◻ h₃)) ◃∎ ∎ₛ
        
