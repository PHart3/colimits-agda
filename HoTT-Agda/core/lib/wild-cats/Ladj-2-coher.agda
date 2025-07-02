{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc
open import lib.wild-cats.Colim-wc
open import lib.wild-cats.Adjoint

module lib.wild-cats.Ladj-2-coher where

module _ {i₁ i₂ j₁ j₂} {C : WildCat {i₁} {j₁}} {D : WildCat {i₂} {j₂}}
  {L : Functor-wc C D} {R : Functor-wc D C} (adj : Adjunction L R) where

  private adj₀ = iso adj

  ladj-is-2coher : Type (lmax (lmax i₁ i₂) (lmax j₁ j₂))
  ladj-is-2coher =
    {x z w : ob C} {y : ob D} (h₁ : hom D (obj L x) y) (h₂ : hom C z x) (h₃ : hom C w z) →
      ! (α C (–> adj₀ h₁) h₂ h₃) ∙
      ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ h₁) ∙
      nat-dom adj h₃ (⟦ D ⟧ h₁ ◻ arr L h₂) ∙
      ap (–> adj₀)
        (α D h₁ (arr L h₂) (arr L h₃) ∙ ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (comp L h₃ h₂))) ∙
      ! (nat-dom adj (⟦ C ⟧ h₂ ◻ h₃) h₁)
        ==
      idp

  module _ {x z w : ob C} {y : ob D} (h₁ : hom D (obj L x) y) (h₂ : hom C z x) (h₃ : hom C w z) where

    abstract
      -- an alternative form of the 2-coherence equality
      2coher-rot :
        ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ h₁) ◃∙
        nat-dom adj h₃ (⟦ D ⟧ h₁ ◻ arr L h₂) ◃∙
        ap (–> adj₀) (α D h₁ (arr L h₂) (arr L h₃)) ◃∎
          =ₛ
        α C (–> adj₀ h₁) h₂ h₃ ◃∙
        nat-dom adj (⟦ C ⟧ h₂ ◻ h₃) h₁ ◃∙
        ap (–> adj₀) (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (comp L h₃ h₂)) ◃∎
        →
        ! (α C (–> adj₀ h₁) h₂ h₃) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ h₁) ◃∙
        nat-dom adj h₃ (⟦ D ⟧ h₁ ◻ arr L h₂) ◃∙
        ap (–> adj₀)
          (α D h₁ (arr L h₂) (arr L h₃) ∙ ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (comp L h₃ h₂))) ◃∙
        ! (nat-dom adj (⟦ C ⟧ h₂ ◻ h₃) h₁) ◃∎
          =ₛ
        idp ◃∎
      2coher-rot p =
        ! (α C (–> adj₀ h₁) h₂ h₃) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ h₁) ◃∙
        nat-dom adj h₃ (⟦ D ⟧ h₁ ◻ arr L h₂) ◃∙
        ap (–> adj₀)
          (α D h₁ (arr L h₂) (arr L h₃) ∙ ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (comp L h₃ h₂))) ◃∙
        ! (nat-dom adj (⟦ C ⟧ h₂ ◻ h₃) h₁) ◃∎
          =ₛ⟨ 3 & 1 & ap-∙◃ (–> adj₀) (α D h₁ (arr L h₂) (arr L h₃)) (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (comp L h₃ h₂))) ⟩
        ! (α C (–> adj₀ h₁) h₂ h₃) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ h₁) ◃∙
        nat-dom adj h₃ (⟦ D ⟧ h₁ ◻ arr L h₂) ◃∙
        ap (–> adj₀) (α D h₁ (arr L h₂) (arr L h₃)) ◃∙
        ap (–> adj₀) (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (comp L h₃ h₂))) ◃∙
        ! (nat-dom adj (⟦ C ⟧ h₂ ◻ h₃) h₁) ◃∎
          =ₛ₁⟨ 4 & 1 & ap-∘-! (–> adj₀) (λ m → ⟦ D ⟧ h₁ ◻ m) (comp L h₃ h₂) ⟩
        ! (α C (–> adj₀ h₁) h₂ h₃) ◃∙
        ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ h₁) ◃∙
        nat-dom adj h₃ (⟦ D ⟧ h₁ ◻ arr L h₂) ◃∙
        ap (–> adj₀) (α D h₁ (arr L h₂) (arr L h₃)) ◃∙
        ! (ap (–> adj₀) (ap (λ m → ⟦ D ⟧ h₁ ◻ m) (comp L h₃ h₂))) ◃∙
        ! (nat-dom adj (⟦ C ⟧ h₂ ◻ h₃) h₁) ◃∎
          =ₛ⟨ post-rotate'-in (post-rotate'-in (pre-rotate'-in p)) ⟩
        []
          =ₛ₁⟨ idp ⟩
        idp ◃∎ ∎ₛ
        
    -- another rotation of the 2-coherence equality
    module _ (p : ladj-is-2coher) where

      2coher-rot2-aux =
        ! (ap (<– adj₀) (α C (–> adj₀ h₁) h₂ h₃)) ◃∙
        ap (<– adj₀) (ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ h₁)) ◃∙
        ap (<– adj₀) (nat-dom adj h₃ (⟦ D ⟧ h₁ ◻ arr L h₂)) ◃∙
        <–-inv-l adj₀ ((D ◻ (D ◻ h₁) (arr L h₂)) (arr L h₃)) ◃∙
        α D h₁ (arr L h₂) (arr L h₃) ◃∙
        ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (comp L h₃ h₂)) ◃∙
        ! (<–-inv-l adj₀ (⟦ D ⟧ h₁ ◻ arr L (⟦ C ⟧ h₂ ◻ h₃))) ◃∙
        ! (ap (<– adj₀) (nat-dom adj (⟦ C ⟧ h₂ ◻ h₃) h₁)) ◃∎
          =ₛ₁⟨ 0 & 1 & !-ap (<– adj₀) (α C (–> adj₀ h₁) h₂ h₃) ⟩
        ap (<– adj₀) (! (α C (–> adj₀ h₁) h₂ h₃)) ◃∙
        ap (<– adj₀) (ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ h₁)) ◃∙
        ap (<– adj₀) (nat-dom adj h₃ (⟦ D ⟧ h₁ ◻ arr L h₂)) ◃∙
        <–-inv-l adj₀ ((D ◻ (D ◻ h₁) (arr L h₂)) (arr L h₃)) ◃∙
        α D h₁ (arr L h₂) (arr L h₃) ◃∙
        ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (comp L h₃ h₂)) ◃∙
        ! (<–-inv-l adj₀ (⟦ D ⟧ h₁ ◻ arr L (⟦ C ⟧ h₂ ◻ h₃))) ◃∙
        ! (ap (<– adj₀) (nat-dom adj (⟦ C ⟧ h₂ ◻ h₃) h₁)) ◃∎
          =ₛ₁⟨ 7 & 1 & !-ap (<– adj₀) (nat-dom adj (⟦ C ⟧ h₂ ◻ h₃) h₁) ⟩
        ap (<– adj₀) (! (α C (–> adj₀ h₁) h₂ h₃)) ◃∙
        ap (<– adj₀) (ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ h₁)) ◃∙
        ap (<– adj₀) (nat-dom adj h₃ (⟦ D ⟧ h₁ ◻ arr L h₂)) ◃∙
        <–-inv-l adj₀ ((D ◻ (D ◻ h₁) (arr L h₂)) (arr L h₃)) ◃∙
        α D h₁ (arr L h₂) (arr L h₃) ◃∙
        ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (comp L h₃ h₂)) ◃∙
        ! (<–-inv-l adj₀ (⟦ D ⟧ h₁ ◻ arr L (⟦ C ⟧ h₂ ◻ h₃))) ◃∙
        ap (<– adj₀) (! (nat-dom adj (⟦ C ⟧ h₂ ◻ h₃) h₁)) ◃∎
          =ₑ⟨ 4 & 2 & (α D h₁ (arr L h₂) (arr L h₃) ∙ ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (comp L h₃ h₂))) ◃∎ %  =ₛ-in idp ⟩
        ap (<– adj₀) (! (α C (–> adj₀ h₁) h₂ h₃)) ◃∙
        ap (<– adj₀) (ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ h₁)) ◃∙
        ap (<– adj₀) (nat-dom adj h₃ (⟦ D ⟧ h₁ ◻ arr L h₂)) ◃∙
        <–-inv-l adj₀ ((D ◻ (D ◻ h₁) (arr L h₂)) (arr L h₃)) ◃∙
        (α D h₁ (arr L h₂) (arr L h₃) ∙ ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (comp L h₃ h₂))) ◃∙
        ! (<–-inv-l adj₀ (⟦ D ⟧ h₁ ◻ arr L (⟦ C ⟧ h₂ ◻ h₃))) ◃∙
        ap (<– adj₀) (! (nat-dom adj (⟦ C ⟧ h₂ ◻ h₃) h₁)) ◃∎
          =ₛ₁⟨ 4 & 1 & ! (ap-idf (α D h₁ (arr L h₂) (arr L h₃) ∙ ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (comp L h₃ h₂)))) ⟩
        ap (<– adj₀) (! (α C (–> adj₀ h₁) h₂ h₃)) ◃∙
        ap (<– adj₀) (ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ h₁)) ◃∙
        ap (<– adj₀) (nat-dom adj h₃ (⟦ D ⟧ h₁ ◻ arr L h₂)) ◃∙
        <–-inv-l adj₀ ((D ◻ (D ◻ h₁) (arr L h₂)) (arr L h₃)) ◃∙
        ap (λ z → z) (α D h₁ (arr L h₂) (arr L h₃) ∙ ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (comp L h₃ h₂))) ◃∙
        ! (<–-inv-l adj₀ (⟦ D ⟧ h₁ ◻ arr L (⟦ C ⟧ h₂ ◻ h₃))) ◃∙
        ap (<– adj₀) (! (nat-dom adj (⟦ C ⟧ h₂ ◻ h₃) h₁)) ◃∎
          =ₛ⟨ 3 & 3 & !ₛ $
            hmtpy-nat-∙◃ (<–-inv-l adj₀) (α D h₁ (arr L h₂) (arr L h₃) ∙ ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (comp L h₃ h₂))) ⟩
        ap (<– adj₀) (! (α C (–> adj₀ h₁) h₂ h₃)) ◃∙
        ap (<– adj₀) (ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ h₁)) ◃∙
        ap (<– adj₀) (nat-dom adj h₃ (⟦ D ⟧ h₁ ◻ arr L h₂)) ◃∙
        ap (<– adj₀ ∘ –> adj₀) (α D h₁ (arr L h₂) (arr L h₃) ∙ ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (comp L h₃ h₂))) ◃∙
        ap (<– adj₀) (! (nat-dom adj (⟦ C ⟧ h₂ ◻ h₃) h₁)) ◃∎
          =ₛ₁⟨ 3 & 1 & ap-∘ (<– adj₀) (–> adj₀) (α D h₁ (arr L h₂) (arr L h₃) ∙ ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (comp L h₃ h₂))) ⟩
        ap (<– adj₀) (! (α C (–> adj₀ h₁) h₂ h₃)) ◃∙
        ap (<– adj₀) (ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ h₁)) ◃∙
        ap (<– adj₀) (nat-dom adj h₃ (⟦ D ⟧ h₁ ◻ arr L h₂)) ◃∙
        ap (<– adj₀) (ap (–> adj₀) (α D h₁ (arr L h₂) (arr L h₃) ∙ ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (comp L h₃ h₂)))) ◃∙
        ap (<– adj₀) (! (nat-dom adj (⟦ C ⟧ h₂ ◻ h₃) h₁)) ◃∎
          =ₛ⟨ ap-seq-=ₛ (<– adj₀) (=ₛ-in (p h₁ h₂ h₃)) ⟩ 
        idp ◃∎ ∎ₛ

      abstract
        2coher-rot2 :
          α D h₁ (arr L h₂) (arr L h₃) ◃∙
          ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (comp L h₃ h₂)) ◃∎
            =ₛ
          ! (<–-inv-l adj₀ ((D ◻ (D ◻ h₁) (arr L h₂)) (arr L h₃))) ◃∙
          ! (ap (<– adj₀) (nat-dom adj h₃ (⟦ D ⟧ h₁ ◻ arr L h₂))) ◃∙
          ! (ap (λ m → <– adj₀ (⟦ C ⟧ m ◻ h₃)) (nat-dom adj h₂ h₁)) ◃∙
          ap (<– adj₀) (α C (–> adj₀ h₁) h₂ h₃) ◃∙
          ap (<– adj₀) (nat-dom adj (⟦ C ⟧ h₂ ◻ h₃) h₁) ◃∙
          <–-inv-l adj₀ (⟦ D ⟧ h₁ ◻ arr L (⟦ C ⟧ h₂ ◻ h₃)) ◃∎
        2coher-rot2 =
          α D h₁ (arr L h₂) (arr L h₃) ◃∙
          ap (λ m → ⟦ D ⟧ h₁ ◻ m) (! (comp L h₃ h₂)) ◃∎
            =ₛ⟨ pre-rotate-in $
              pre-rotate-in (pre-rotate-in (pre-rotate'-out (post-rotate'-out (post-rotate'-out (2coher-rot2-aux))))) ⟩
          ! (<–-inv-l adj₀ ((D ◻ (D ◻ h₁) (arr L h₂)) (arr L h₃))) ◃∙
          ! (ap (<– adj₀) (nat-dom adj h₃ (⟦ D ⟧ h₁ ◻ arr L h₂))) ◃∙
          ! (ap (<– adj₀) (ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ h₁))) ◃∙
          ap (<– adj₀) (α C (–> adj₀ h₁) h₂ h₃) ◃∙
          idp ◃∙
          ap (<– adj₀) (nat-dom adj (⟦ C ⟧ h₂ ◻ h₃) h₁) ◃∙
          <–-inv-l adj₀ (⟦ D ⟧ h₁ ◻ arr L (⟦ C ⟧ h₂ ◻ h₃)) ◃∎
            =ₛ₁⟨ 4 & 2 & idp ⟩
          ! (<–-inv-l adj₀ ((D ◻ (D ◻ h₁) (arr L h₂)) (arr L h₃))) ◃∙
          ! (ap (<– adj₀) (nat-dom adj h₃ (⟦ D ⟧ h₁ ◻ arr L h₂))) ◃∙
          ! (ap (<– adj₀) (ap (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ h₁))) ◃∙
          ap (<– adj₀) (α C (–> adj₀ h₁) h₂ h₃) ◃∙
          ap (<– adj₀) (nat-dom adj (⟦ C ⟧ h₂ ◻ h₃) h₁) ◃∙
          <–-inv-l adj₀ (⟦ D ⟧ h₁ ◻ arr L (⟦ C ⟧ h₂ ◻ h₃)) ◃∎
            =ₛ₁⟨ 2 & 1 & ap ! (∘-ap (<– adj₀) (λ m → ⟦ C ⟧ m ◻ h₃) (nat-dom adj h₂ h₁)) ⟩
          ! (<–-inv-l adj₀ ((D ◻ (D ◻ h₁) (arr L h₂)) (arr L h₃))) ◃∙
          ! (ap (<– adj₀) (nat-dom adj h₃ (⟦ D ⟧ h₁ ◻ arr L h₂))) ◃∙
          ! (ap (λ m → <– adj₀ (⟦ C ⟧ m ◻ h₃)) (nat-dom adj h₂ h₁)) ◃∙
          ap (<– adj₀) (α C (–> adj₀ h₁) h₂ h₃) ◃∙
          ap (<– adj₀) (nat-dom adj (⟦ C ⟧ h₂ ◻ h₃) h₁) ◃∙
          <–-inv-l adj₀ (⟦ D ⟧ h₁ ◻ arr L (⟦ C ⟧ h₂ ◻ h₃)) ◃∎ ∎ₛ

