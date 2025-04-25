{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Graph
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc
open import lib.wild-cats.Colim-wc
open import lib.wild-cats.Adjoint
open import lib.wild-cats.Cocone-wc-SIP
open import lib.wild-cats.Ladj-2-coher
open import lib.wild-cats.Limit

module lib.wild-cats.Ladj-colim where

module _ {i₁ i₂ j₁ j₂} {C : WildCat {i₁} {j₁}} {D : WildCat {i₂} {j₂}}
  {ℓv ℓe} {G : Graph ℓv ℓe} {Δ : Diagram G C}
  {L : Functor-wc C D} {R : Functor-wc D C} {adj : Adjunction L R}
  {c : ob C} {K : Cocone Δ c} (cl : is-colim K) 
  (κ : ladj-is-2coher adj) where

  private adj₀ = iso adj

  hom-to-lim : (y : ob D) → hom D (obj L c) y ≃ Cocone (F-diag L Δ) y
  hom-to-lim y = Cocone-adj-eqv ∘e is-colim-≃  K cl (obj R y) ∘e adj₀
    where
      Cocone-adj-eqv : Cocone Δ (obj R y) ≃ Cocone (F-diag L Δ) y
      Cocone-adj-eqv = 
        Cocone Δ (obj R y)
          ≃⟨ cocone-wc-Σ ⟩
        Limit (Diagram-hom (obj R y) Δ)
          ≃⟨ (adj-lim-map-eqv adj) ⁻¹ ⟩
        Limit (Diagram-hom y (F-diag L Δ))
          ≃⟨ cocone-wc-Σ ⁻¹ ⟩
        Cocone (F-diag L Δ) y ≃∎

  module comps-eq (y : ob D) (h : hom D (obj L c) y) where

    leg-eq : (i : Obj G) → <– adj₀ (⟦ C ⟧ –> adj₀ h ◻ leg K i) == ⟦ D ⟧ h ◻ arr L (leg K i)
    leg-eq i = ap (<– adj₀) (nat-dom adj (leg K i) h) ∙ <–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (leg K i))

    abstract
      tri-eq : {i j : Obj G} (f : Hom G i j) →
        (↯ (↑nat-dom adj (D₁ Δ f) (⟦ C ⟧ –> adj₀ h ◻ leg K j)) ∙
        ap (<– adj₀) (α C (–> adj₀ h) (leg K j) (D₁ Δ f) ∙ ap (λ m → ⟦ C ⟧ –> adj₀ h ◻ m) (tri K f))) ◃∙
        leg-eq i ◃∎
          =ₛ
        ap (λ m → ⟦ D ⟧ m ◻ arr L (D₁ Δ f)) (leg-eq j) ◃∙
        α D h (arr L (leg K j)) (arr L (D₁ Δ f)) ◃∙
        ap (λ m → ⟦ D ⟧ h ◻ m) (tri (F-coc L K) f) ◃∎
      tri-eq {i} {j} f =
        (↯ (↑nat-dom adj (D₁ Δ f) (⟦ C ⟧ –> adj₀ h ◻ leg K j)) ∙
        ap (<– adj₀) (α C (–> adj₀ h) (leg K j) (D₁ Δ f) ∙ ap (λ m → ⟦ C ⟧ –> adj₀ h ◻ m) (tri K f))) ◃∙
        leg-eq i ◃∎
          =ₑ⟨ 0 & 1 &
            (↯ (↑nat-dom adj (D₁ Δ f) (⟦ C ⟧ –> adj₀ h ◻ leg K j)) ◃∙
            ap (<– adj₀) (α C (–> adj₀ h) (leg K j) (D₁ Δ f) ∙ ap (λ m → ⟦ C ⟧ –> adj₀ h ◻ m) (tri K f)) ◃∎)
              %  =ₛ-in idp ⟩
        ↯ (↑nat-dom adj (D₁ Δ f) (⟦ C ⟧ –> adj₀ h ◻ leg K j)) ◃∙
        ap (<– adj₀) (α C (–> adj₀ h) (leg K j) (D₁ Δ f) ∙ ap (λ m → ⟦ C ⟧ –> adj₀ h ◻ m) (tri K f)) ◃∙
        leg-eq i ◃∎
          =ₛ⟨ 2 & 1 & =ₛ-in idp ⟩
        ↯ (↑nat-dom adj (D₁ Δ f) (⟦ C ⟧ –> adj₀ h ◻ leg K j)) ◃∙
        ap (<– adj₀) (α C (–> adj₀ h) (leg K j) (D₁ Δ f) ∙ ap (λ m → ⟦ C ⟧ –> adj₀ h ◻ m) (tri K f)) ◃∙
        ap (<– adj₀) (nat-dom adj (leg K i) h) ◃∙
        <–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (leg K i)) ◃∎
          =ₛ⟨ 0 & 1 & apCommSq2◃' (λ m → ↯ (↑nat-dom adj (D₁ Δ f) m)) (nat-dom adj (leg K j) h) ⟩
        ap (λ z → ⟦ D ⟧ <– adj₀ z ◻ arr L (D₁ Δ f)) (nat-dom adj (leg K j) h) ◃∙
        ↯ (↑nat-dom adj (D₁ Δ f) (–> adj₀ (⟦ D ⟧ h ◻ arr L (leg K j)))) ◃∙
        ! (ap (λ z → <– adj₀ (⟦ C ⟧ z ◻ D₁ Δ f)) (nat-dom adj (leg K j) h)) ◃∙
        ap (<– adj₀) (α C (–> adj₀ h) (leg K j) (D₁ Δ f) ∙ ap (λ m → ⟦ C ⟧ –> adj₀ h ◻ m) (tri K f)) ◃∙
        ap (<– adj₀) (nat-dom adj (leg K i) h) ◃∙
        <–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (leg K i)) ◃∎
          =ₛ₁⟨ 1 & 1 & =ₛ-out (nat-dom-exch adj (D₁ Δ f) (⟦ D ⟧ h ◻ arr L (leg K j))) ⟩
        ap (λ z → ⟦ D ⟧ <– adj₀ z ◻ arr L (D₁ Δ f)) (nat-dom adj (leg K j) h) ◃∙
        (ap (λ m → ⟦ D ⟧ m ◻ arr L (D₁ Δ f)) (<–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (leg K j))) ∙
        ! (<–-inv-l adj₀ (⟦ D ⟧ ⟦ D ⟧ h ◻ arr L (leg K j) ◻ arr L (D₁ Δ f))) ∙
        ! (ap (<– adj₀) (nat-dom adj (D₁ Δ f) (⟦ D ⟧ h ◻ arr L (leg K j))))) ◃∙
        ! (ap (λ z → <– adj₀ (⟦ C ⟧ z ◻ D₁ Δ f)) (nat-dom adj (leg K j) h)) ◃∙
        ap (<– adj₀) (α C (–> adj₀ h) (leg K j) (D₁ Δ f) ∙ ap (λ m → ⟦ C ⟧ –> adj₀ h ◻ m) (tri K f)) ◃∙
        ap (<– adj₀) (nat-dom adj (leg K i) h) ◃∙
        <–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (leg K i)) ◃∎
          =ₛ⟨ 3 & 1 & 
            ap-∙◃ (<– adj₀) (α C (–> adj₀ h) (leg K j) (D₁ Δ f)) (ap (λ m → ⟦ C ⟧ –> adj₀ h ◻ m) (tri K f)) ⟩
        ap (λ z → ⟦ D ⟧ <– adj₀ z ◻ arr L (D₁ Δ f)) (nat-dom adj (leg K j) h) ◃∙
        (ap (λ m → ⟦ D ⟧ m ◻ arr L (D₁ Δ f)) (<–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (leg K j))) ∙
        ! (<–-inv-l adj₀ (⟦ D ⟧ ⟦ D ⟧ h ◻ arr L (leg K j) ◻ arr L (D₁ Δ f))) ∙
        ! (ap (<– adj₀) (nat-dom adj (D₁ Δ f) (⟦ D ⟧ h ◻ arr L (leg K j))))) ◃∙
        ! (ap (λ z → <– adj₀ (⟦ C ⟧ z ◻ D₁ Δ f)) (nat-dom adj (leg K j) h)) ◃∙
        ap (<– adj₀) (α C (–> adj₀ h) (leg K j) (D₁ Δ f)) ◃∙
        ap (<– adj₀) (ap (λ m → ⟦ C ⟧ –> adj₀ h ◻ m) (tri K f)) ◃∙
        ap (<– adj₀) (nat-dom adj (leg K i) h) ◃∙
        <–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (leg K i)) ◃∎
          =ₛ⟨ 4 & 1 & ap-seq-=ₛ (<– adj₀) (hmtpy-nat-∙◃ (λ m → nat-dom adj m h) (tri K f)) ⟩
        ap (λ z → ⟦ D ⟧ <– adj₀ z ◻ arr L (D₁ Δ f)) (nat-dom adj (leg K j) h) ◃∙
        (ap (λ m → ⟦ D ⟧ m ◻ arr L (D₁ Δ f)) (<–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (leg K j))) ∙
        ! (<–-inv-l adj₀ (⟦ D ⟧ ⟦ D ⟧ h ◻ arr L (leg K j) ◻ arr L (D₁ Δ f))) ∙
        ! (ap (<– adj₀) (nat-dom adj (D₁ Δ f) (⟦ D ⟧ h ◻ arr L (leg K j))))) ◃∙
        ! (ap (λ z → <– adj₀ (⟦ C ⟧ z ◻ D₁ Δ f)) (nat-dom adj (leg K j) h)) ◃∙
        ap (<– adj₀) (α C (–> adj₀ h) (leg K j) (D₁ Δ f)) ◃∙
        ap (<– adj₀) (nat-dom adj (⟦ C ⟧ leg K j ◻ D₁ Δ f) h) ◃∙
        ap (<– adj₀) (ap (λ m → –> adj₀ (⟦ D ⟧ h ◻ arr L m)) (tri K f)) ◃∙
        ap (<– adj₀) (! (nat-dom adj (leg K i) h)) ◃∙
        ap (<– adj₀) (nat-dom adj (leg K i) h) ◃∙
        <–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (leg K i)) ◃∎
          =ₛ₁⟨ 5 & 1 & ∘-ap (<– adj₀) (λ m → –> adj₀ (⟦ D ⟧ h ◻ arr L m)) (tri K f) ⟩
        ap (λ z → ⟦ D ⟧ <– adj₀ z ◻ arr L (D₁ Δ f)) (nat-dom adj (leg K j) h) ◃∙
        (ap (λ m → ⟦ D ⟧ m ◻ arr L (D₁ Δ f)) (<–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (leg K j))) ∙
        ! (<–-inv-l adj₀ (⟦ D ⟧ ⟦ D ⟧ h ◻ arr L (leg K j) ◻ arr L (D₁ Δ f))) ∙
        ! (ap (<– adj₀) (nat-dom adj (D₁ Δ f) (⟦ D ⟧ h ◻ arr L (leg K j))))) ◃∙
        ! (ap (λ z → <– adj₀ (⟦ C ⟧ z ◻ D₁ Δ f)) (nat-dom adj (leg K j) h)) ◃∙
        ap (<– adj₀) (α C (–> adj₀ h) (leg K j) (D₁ Δ f)) ◃∙
        ap (<– adj₀) (nat-dom adj (⟦ C ⟧ leg K j ◻ D₁ Δ f) h) ◃∙
        ap (<– adj₀ ∘ –> adj₀ ∘ (λ m → ⟦ D ⟧ h ◻ arr L m)) (tri K f) ◃∙
        ap (<– adj₀) (! (nat-dom adj (leg K i) h)) ◃∙
        ap (<– adj₀) (nat-dom adj (leg K i) h) ◃∙
        <–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (leg K i)) ◃∎
          =ₛ₁⟨ 5 & 1 & ap-∘ (<– adj₀ ∘ –> adj₀) (λ m → ⟦ D ⟧ h ◻ arr L m) (tri K f) ⟩
        ap (λ z → ⟦ D ⟧ <– adj₀ z ◻ arr L (D₁ Δ f)) (nat-dom adj (leg K j) h) ◃∙
        (ap (λ m → ⟦ D ⟧ m ◻ arr L (D₁ Δ f)) (<–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (leg K j))) ∙
        ! (<–-inv-l adj₀ (⟦ D ⟧ ⟦ D ⟧ h ◻ arr L (leg K j) ◻ arr L (D₁ Δ f))) ∙
        ! (ap (<– adj₀) (nat-dom adj (D₁ Δ f) (⟦ D ⟧ h ◻ arr L (leg K j))))) ◃∙
        ! (ap (λ z → <– adj₀ (⟦ C ⟧ z ◻ D₁ Δ f)) (nat-dom adj (leg K j) h)) ◃∙
        ap (<– adj₀) (α C (–> adj₀ h) (leg K j) (D₁ Δ f)) ◃∙
        ap (<– adj₀) (nat-dom adj (⟦ C ⟧ leg K j ◻ D₁ Δ f) h) ◃∙
        ap (<– adj₀ ∘ –> adj₀) (ap (λ m → ⟦ D ⟧ h ◻ arr L m) (tri K f)) ◃∙
        ap (<– adj₀) (! (nat-dom adj (leg K i) h)) ◃∙
        ap (<– adj₀) (nat-dom adj (leg K i) h) ◃∙
        <–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (leg K i)) ◃∎
          =ₛ⟨ 5 & 1 & hmtpy-nat-∙◃ (<–-inv-l adj₀) (ap (λ m → ⟦ D ⟧ h ◻ arr L m) (tri K f)) ⟩
        ap (λ m → ⟦ D ⟧ <– adj₀ m ◻ arr L (D₁ Δ f)) (nat-dom adj (leg K j) h) ◃∙
        (ap (λ m → ⟦ D ⟧ m ◻ arr L (D₁ Δ f)) (<–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (leg K j))) ∙
        ! (<–-inv-l adj₀ (⟦ D ⟧ ⟦ D ⟧ h ◻ arr L (leg K j) ◻ arr L (D₁ Δ f))) ∙
        ! (ap (<– adj₀) (nat-dom adj (D₁ Δ f) (⟦ D ⟧ h ◻ arr L (leg K j))))) ◃∙
        ! (ap (λ m → <– adj₀ (⟦ C ⟧ m ◻ D₁ Δ f)) (nat-dom adj (leg K j) h)) ◃∙
        ap (<– adj₀) (α C (–> adj₀ h) (leg K j) (D₁ Δ f)) ◃∙
        ap (<– adj₀) (nat-dom adj (⟦ C ⟧ leg K j ◻ D₁ Δ f) h) ◃∙
        <–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (⟦ C ⟧ leg K j ◻ D₁ Δ f)) ◃∙
        ap (λ z → z) (ap (λ m → ⟦ D ⟧ h ◻ arr L m) (tri K f)) ◃∙
        ! (<–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (leg K i))) ◃∙
        ap (<– adj₀) (! (nat-dom adj (leg K i) h)) ◃∙
        ap (<– adj₀) (nat-dom adj (leg K i) h) ◃∙
        <–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (leg K i)) ◃∎
          =ₛ₁⟨ 8 & 2 & ap-!-inv-l (<– adj₀) (nat-dom adj (leg K i) h) ⟩
        ap (λ m → ⟦ D ⟧ <– adj₀ m ◻ arr L (D₁ Δ f)) (nat-dom adj (leg K j) h) ◃∙
        (ap (λ m → ⟦ D ⟧ m ◻ arr L (D₁ Δ f)) (<–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (leg K j))) ∙
        ! (<–-inv-l adj₀ (⟦ D ⟧ ⟦ D ⟧ h ◻ arr L (leg K j) ◻ arr L (D₁ Δ f))) ∙
        ! (ap (<– adj₀) (nat-dom adj (D₁ Δ f) (⟦ D ⟧ h ◻ arr L (leg K j))))) ◃∙
        ! (ap (λ m → <– adj₀ (⟦ C ⟧ m ◻ D₁ Δ f)) (nat-dom adj (leg K j) h)) ◃∙
        ap (<– adj₀) (α C (–> adj₀ h) (leg K j) (D₁ Δ f)) ◃∙
        ap (<– adj₀) (nat-dom adj (⟦ C ⟧ leg K j ◻ D₁ Δ f) h) ◃∙
        <–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (⟦ C ⟧ leg K j ◻ D₁ Δ f)) ◃∙
        ap (λ z → z) (ap (λ m → ⟦ D ⟧ h ◻ arr L m) (tri K f)) ◃∙
        ! (<–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (leg K i))) ◃∙
        idp ◃∙
        <–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (leg K i)) ◃∎
          =ₛ₁⟨ 7 & 3 & !-inv-l (<–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (leg K i))) ⟩
        ap (λ m → ⟦ D ⟧ <– adj₀ m ◻ arr L (D₁ Δ f)) (nat-dom adj (leg K j) h) ◃∙
        (ap (λ m → ⟦ D ⟧ m ◻ arr L (D₁ Δ f)) (<–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (leg K j))) ∙
        ! (<–-inv-l adj₀ (⟦ D ⟧ ⟦ D ⟧ h ◻ arr L (leg K j) ◻ arr L (D₁ Δ f))) ∙
        ! (ap (<– adj₀) (nat-dom adj (D₁ Δ f) (⟦ D ⟧ h ◻ arr L (leg K j))))) ◃∙
        ! (ap (λ m → <– adj₀ (⟦ C ⟧ m ◻ D₁ Δ f)) (nat-dom adj (leg K j) h)) ◃∙
        ap (<– adj₀) (α C (–> adj₀ h) (leg K j) (D₁ Δ f)) ◃∙
        ap (<– adj₀) (nat-dom adj (⟦ C ⟧ leg K j ◻ D₁ Δ f) h) ◃∙
        <–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (⟦ C ⟧ leg K j ◻ D₁ Δ f)) ◃∙
        ap (λ z → z) (ap (λ m → ⟦ D ⟧ h ◻ arr L m) (tri K f)) ◃∙
        idp ◃∎
          =ₑ⟨ 1 & 1 &
            (ap (λ m → ⟦ D ⟧ m ◻ arr L (D₁ Δ f)) (<–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (leg K j))) ◃∙
            ! (<–-inv-l adj₀ (⟦ D ⟧ ⟦ D ⟧ h ◻ arr L (leg K j) ◻ arr L (D₁ Δ f))) ◃∙
            ! (ap (<– adj₀) (nat-dom adj (D₁ Δ f) (⟦ D ⟧ h ◻ arr L (leg K j)))) ◃∎)
              % =ₛ-in idp ⟩
        ap (λ m → ⟦ D ⟧ <– adj₀ m ◻ arr L (D₁ Δ f)) (nat-dom adj (leg K j) h) ◃∙
        ap (λ m → ⟦ D ⟧ m ◻ arr L (D₁ Δ f)) (<–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (leg K j))) ◃∙
        ! (<–-inv-l adj₀ (⟦ D ⟧ ⟦ D ⟧ h ◻ arr L (leg K j) ◻ arr L (D₁ Δ f))) ◃∙
        ! (ap (<– adj₀) (nat-dom adj (D₁ Δ f) (⟦ D ⟧ h ◻ arr L (leg K j)))) ◃∙
        ! (ap (λ m → <– adj₀ (⟦ C ⟧ m ◻ D₁ Δ f)) (nat-dom adj (leg K j) h)) ◃∙
        ap (<– adj₀) (α C (–> adj₀ h) (leg K j) (D₁ Δ f)) ◃∙
        ap (<– adj₀) (nat-dom adj (⟦ C ⟧ leg K j ◻ D₁ Δ f) h) ◃∙
        <–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (⟦ C ⟧ leg K j ◻ D₁ Δ f)) ◃∙
        ap (λ z → z) (ap (λ m → ⟦ D ⟧ h ◻ arr L m) (tri K f)) ◃∙
        idp ◃∎
          =ₛ₁⟨ 0 & 1 & ap-∘ (λ m → ⟦ D ⟧ m ◻ arr L (D₁ Δ f)) (<– adj₀) (nat-dom adj (leg K j) h) ⟩
        ap (λ m → ⟦ D ⟧ m ◻ arr L (D₁ Δ f)) (ap (<– adj₀) (nat-dom adj (leg K j) h)) ◃∙
        ap (λ m → ⟦ D ⟧ m ◻ arr L (D₁ Δ f)) (<–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (leg K j))) ◃∙
        ! (<–-inv-l adj₀ (⟦ D ⟧ ⟦ D ⟧ h ◻ arr L (leg K j) ◻ arr L (D₁ Δ f))) ◃∙
        ! (ap (<– adj₀) (nat-dom adj (D₁ Δ f) (⟦ D ⟧ h ◻ arr L (leg K j)))) ◃∙
        ! (ap (λ m → <– adj₀ (⟦ C ⟧ m ◻ D₁ Δ f)) (nat-dom adj (leg K j) h)) ◃∙
        ap (<– adj₀) (α C (–> adj₀ h) (leg K j) (D₁ Δ f)) ◃∙
        ap (<– adj₀) (nat-dom adj (⟦ C ⟧ leg K j ◻ D₁ Δ f) h) ◃∙
        <–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (⟦ C ⟧ leg K j ◻ D₁ Δ f)) ◃∙
        ap (λ z → z) (ap (λ m → ⟦ D ⟧ h ◻ arr L m) (tri K f)) ◃∙
        idp ◃∎
          =ₛ₁⟨ 0 & 2 & 
            ∙-ap (λ m → ⟦ D ⟧ m ◻ arr L (D₁ Δ f))
              (ap (<– adj₀) (nat-dom adj (leg K j) h))
              (<–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (leg K j))) ⟩
        ap (λ m → ⟦ D ⟧ m ◻ arr L (D₁ Δ f)) (leg-eq j) ◃∙
        ! (<–-inv-l adj₀ (⟦ D ⟧ ⟦ D ⟧ h ◻ arr L (leg K j) ◻ arr L (D₁ Δ f))) ◃∙
        ! (ap (<– adj₀) (nat-dom adj (D₁ Δ f) (⟦ D ⟧ h ◻ arr L (leg K j)))) ◃∙
        ! (ap (λ m → <– adj₀ (⟦ C ⟧ m ◻ D₁ Δ f)) (nat-dom adj (leg K j) h)) ◃∙
        ap (<– adj₀) (α C (–> adj₀ h) (leg K j) (D₁ Δ f)) ◃∙
        ap (<– adj₀) (nat-dom adj (⟦ C ⟧ leg K j ◻ D₁ Δ f) h) ◃∙
        <–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (⟦ C ⟧ leg K j ◻ D₁ Δ f)) ◃∙
        ap (λ z → z) (ap (λ m → ⟦ D ⟧ h ◻ arr L m) (tri K f)) ◃∙
        idp ◃∎
          =ₛ₁⟨ 7 & 2 &
            ∙-unit-r (ap (λ z → z) (ap (λ m → ⟦ D ⟧ h ◻ arr L m) (tri K f))) ∙
            ap-idf (ap (λ m → ⟦ D ⟧ h ◻ arr L m) (tri K f)) ⟩
        ap (λ m → ⟦ D ⟧ m ◻ arr L (D₁ Δ f)) (leg-eq j) ◃∙
        ! (<–-inv-l adj₀ (⟦ D ⟧ ⟦ D ⟧ h ◻ arr L (leg K j) ◻ arr L (D₁ Δ f))) ◃∙
        ! (ap (<– adj₀) (nat-dom adj (D₁ Δ f) (⟦ D ⟧ h ◻ arr L (leg K j)))) ◃∙
        ! (ap (λ m → <– adj₀ (⟦ C ⟧ m ◻ D₁ Δ f)) (nat-dom adj (leg K j) h)) ◃∙
        ap (<– adj₀) (α C (–> adj₀ h) (leg K j) (D₁ Δ f)) ◃∙
        ap (<– adj₀) (nat-dom adj (⟦ C ⟧ leg K j ◻ D₁ Δ f) h) ◃∙
        <–-inv-l adj₀ (⟦ D ⟧ h ◻ arr L (⟦ C ⟧ leg K j ◻ D₁ Δ f)) ◃∙
        ap (λ m → ⟦ D ⟧ h ◻ arr L m) (tri K f) ◃∎
          =ₛ⟨ 1 & 6 & !ₛ (2coher-other adj κ h (leg K j) (D₁ Δ f)) ⟩
        ap (λ m → ⟦ D ⟧ m ◻ arr L (D₁ Δ f)) (leg-eq j) ◃∙
        α D h (arr L (leg K j)) (arr L (D₁ Δ f)) ◃∙
        ap (λ m → ⟦ D ⟧ h ◻ m) (! (comp L (D₁ Δ f) (leg K j))) ◃∙
        ap (λ m → ⟦ D ⟧ h ◻ arr L m) (tri K f) ◃∎
          =ₛ₁⟨ 2 & 2 & 
            ap (λ m → ap (λ m → ⟦ D ⟧ h ◻ m) (! (comp L (D₁ Δ f) (leg K j))) ∙ m)
              (ap-∘ (λ m → ⟦ D ⟧ h ◻ m) (arr L) (tri K f)) ∙
            ∙-ap (λ m → ⟦ D ⟧ h ◻ m) (! (comp L (D₁ Δ f) (leg K j))) (ap (arr L) (tri K f)) ⟩
        ap (λ m → ⟦ D ⟧ m ◻ arr L (D₁ Δ f)) (leg-eq j) ◃∙
        α D h (arr L (leg K j)) (arr L (D₁ Δ f)) ◃∙
        ap (λ m → ⟦ D ⟧ h ◻ m) (! (comp L (D₁ Δ f) (leg K j)) ∙ ap (arr L) (tri K f)) ◃∎ ∎ₛ

  open comps-eq

  abstract
    Ladj-prsrv-clim : is-colim {D = F-diag L Δ} (F-coc L K)
    Ladj-prsrv-clim y = ∼-preserves-equiv {f₀ = –> (hom-to-lim y)}
      (λ h → coc-to-== G
        (leg-eq y h , λ {x} f → 
          (∙'=∙ _
            (ap (is-equiv.g (snd (iso adj))) (nat-dom adj (leg K x) h) ∙
            is-equiv.g-f (snd (iso adj)) ((D ◻ h) (arr L (leg K x))))) ∙
          =ₛ-out (tri-eq y h f)))
      (snd (hom-to-lim y))
