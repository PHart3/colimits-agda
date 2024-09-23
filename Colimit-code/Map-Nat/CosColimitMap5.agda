{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import lib.PathSeq
open import Coslice
open import Diagram
open import AuxPaths-v2
open import Colim
open import Cocone
open import CosColimitMap
open import CosColimitMap2
open import CosColimitMap3
open import CosColimitMap4

module CosColimitMap5 where

module ConstrMap5 {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open ConstrMap δ

  open ConstrMap3 δ

  open ConstrMap4 δ

  module _ (i j : Obj Γ) (g : Hom Γ i j) (a : A) where

    open MapCoher i j g a

    open MapCoher2 i j g a

    MainRed-helper : (q : cin {D = ConsDiag Γ A} j a == cin i a) {u : ty (G # j)} (s : u  == fun (G # j) a)
      → (! (ap (λ p → p ∙ idp) (↯ (id-free glue q (ap (right ∘ cin i) (snd (nat δ i) a))))) ◃∙
      (four-!-!-!-rid-rid (! (ap left (ap (Id.[id] Γ A) q))) (glue (cin j a)) (ap right (ap ψ₂ q)) (ap (right ∘ cin i) (snd (nat δ i) a)) ∙
      ! (ap (λ p → p ∙ ! (ap (right ∘ cin i) (snd (nat δ i) a))) (transp-pth-cmp q (glue (cin j a)))) ∙
      ap (λ p → p ∙ ! (ap (right ∘ cin i) (snd (nat δ i) a))) (apd-tr glue q) ∙
      ap (_∙_ (glue (cin i a))) (ψ₂-free-helper2 (snd (nat δ i) a) (cglue g (fst (nat δ i) (fun (F # i) a))) (snd (G <#> g) a)
        s (cglue g (fun (G # i) a))) ∙
      ap (λ p → glue (cin i a) ∙ ap right (! (! (! (p ∙ ap (cin j) (snd (G <#> g) a ∙
        ! s ∙ idp)) ∙
        cglue g (fst (nat δ i) (fun (F # i) a))) ∙
        ap (cin j) s ∙
        ! (ap (cin j) (snd (G <#> g) a)) ∙ cglue g (fun (G # i) a))))
        (∼-nat (cglue g) (snd (nat δ i) a)) ∙
      ap (λ p → glue (cin i a) ∙ ap right
        (! (! (! p ∙ cglue g (fst (nat δ i) (fun (F # i) a))) ∙
        ap (cin j) s ∙
        ! (ap (cin j) (snd (G <#> g) a)) ∙ cglue g (fun (G # i) a))))
        (ap-∘-∙ (cin j) (fst (G <#> g)) (snd (nat δ i) a)
        (snd (G <#> g) a ∙ ! s ∙ idp))) ◃∙
      ap (λ p → glue (cin i a) ∙ ap right (! p))
        (ap-∘-!-!-rid-rid (fst (G <#> g)) (cin j)
        (snd (nat δ i) a) s (snd (G <#> g) a)
        (cglue g (fst (nat δ i) (fun (F # i) a)))
        (cglue g (fun (G # i) a))) ◃∙
      ap (λ p → glue (cin i a) ∙ ap right (! p))
        (apCommSq (cin j ∘ fst (G <#> g)) (cin i) (cglue g)
        (snd (nat δ i) a)) ◃∎)
      =ₛ
      (ap-∘-!-!-rid (cin i) right (snd (nat δ i) a) (glue (cin i a)) ◃∎)
    MainRed-helper q idp = lemma q (snd (nat δ i) a) (snd (G <#> g) a)
      where
        lemma : {x : Colim (ConsDiag Γ A)} (q₁ : x == cin i a) (c : fst (nat δ i) (fun (F # i) a)  == fun (G # i) a) (e : fst (G <#> g) (fun (G # i) a) == fun (G # j) a)
          → (! (ap (λ p → p ∙ idp) (↯ (id-free glue q₁ (ap (right ∘ cin i) c)))) ◃∙
          (four-!-!-!-rid-rid (! (ap left (ap [id] q₁))) (glue x) (ap right (ap ψ₂ q₁)) (ap (right ∘ cin i) c) ∙
          ! (ap (λ p → p ∙ ! (ap (right ∘ cin i) c)) (transp-pth-cmp q₁ (glue x))) ∙
          ap (λ p → p ∙ ! (ap (right ∘ cin i) c)) (apd-tr glue q₁) ∙
          ap (_∙_ (glue (cin i a))) (ψ₂-free-helper2 c (cglue g (fst (nat δ i) (fun (F # i) a)))
            e idp  (cglue g (fun (G # i) a))) ∙
          ap (λ p → glue (cin i a) ∙ ap right (! (! (! (p ∙ ap (cin j) (e ∙ idp)) ∙
            cglue g (fst (nat δ i) (fun (F # i) a))) ∙ ! (ap (cin j) e) ∙ cglue g (fun (G # i) a)))) (∼-nat (cglue g) c) ∙
          ap (λ p → glue (cin i a) ∙ ap right (! (! (! p ∙ cglue g (fst (nat δ i) (fun (F # i) a))) ∙
            ! (ap (cin j) e) ∙ cglue g (fun (G # i) a))))
            (ap-∘-∙ (cin j) (fst (G <#> g)) c (e ∙ idp))) ◃∙
          ap (λ p → glue (cin i a) ∙ ap right (! p)) (ap-∘-!-!-rid-rid (fst (G <#> g)) (cin j) c idp
            e (cglue g (fst (nat δ i) (fun (F # i) a))) (cglue g (fun (G # i) a))) ◃∙
          ap (λ p → glue (cin i a) ∙ ap right (! p)) (apCommSq (cin j ∘ fst (G <#> g)) (cin i) (cglue g) c) ◃∎)
          =ₛ
          (ap-∘-!-!-rid (cin i) right c (glue (cin i a)) ◃∎)
        lemma idp c e = =ₛ-in (lemma2 (glue (cin i a)))
          where
            lemma2 : {w : P₂} (γ : w == right {d = SpCos₂} (cin i (fun (G # i) a)))
              → ! (ap (λ p → p ∙ idp) (↯ (id-free-helper (ap (right ∘ cin i) c) γ))) ∙
              (four-!-!-!-rid-rid idp γ idp (ap (right ∘ cin i) c) ∙
              ! (ap (λ p → p ∙ ! (ap (right ∘ cin i) c)) (! (∙-unit-r γ))) ∙
              ap (_∙_ γ) (ψ₂-free-helper2 c (cglue g (fst (nat δ i) (fun (F # i) a)))
                e idp  (cglue g (fun (G # i) a))) ∙
              ap (λ p → γ ∙ ap right (! (! (! (p ∙ ap (cin j) (e ∙ idp)) ∙
                cglue g (fst (nat δ i) (fun (F # i) a))) ∙ ! (ap (cin j) e) ∙ cglue g (fun (G # i) a)))) (∼-nat (cglue g) c) ∙
              ap (λ p → γ ∙ ap right (! (! (! p ∙ cglue g (fst (nat δ i) (fun (F # i) a))) ∙
                ! (ap (cin j) e) ∙ cglue g (fun (G # i) a))))
                (ap-∘-∙ (cin j) (fst (G <#> g)) c (e ∙ idp))) ∙
              ap (λ p → γ ∙ ap right (! p)) (ap-∘-!-!-rid-rid (fst (G <#> g)) (cin j) c idp
                e (cglue g (fst (nat δ i) (fun (F # i) a))) (cglue g (fun (G # i) a))) ∙
              ap (λ p → γ ∙ ap right (! p)) (apCommSq (cin j ∘ fst (G <#> g)) (cin i) (cglue g) c) 
              ==
              ap-∘-!-!-rid (cin i) right c γ
            lemma2 idp = lemma3 e c
              where
                lemma3 : {t : ty (G # j)} (e : fst (G <#> g) (fun (G # i) a) == t) {w : ty (G # i)} (c : w == fun (G # i) a)
                  → ! (ap (λ p → p ∙ idp) (↯ (id-free-helper (ap (right ∘ cin i) c) idp))) ∙
                  (four-!-!-!-rid-rid idp idp idp (ap (right ∘ cin i) c) ∙
                  ap (_∙_ idp) (ψ₂-free-helper3 (cin i) c (cglue g w)
                    e (cglue g (fun (G # i) a))) ∙
                  ap (λ p → ap right (! (! (! (p ∙ ap (cin j) (e ∙ idp)) ∙
                    cglue g w) ∙ ! (ap (cin j) e) ∙ cglue g (fun (G # i) a)))) (∼-nat (cglue g) c) ∙
                  ap (λ p → ap right (! (! (! p ∙ cglue g w) ∙
                    ! (ap (cin j) e) ∙ cglue g (fun (G # i) a))))
                    (ap-∘-∙ (cin j) (fst (G <#> g)) c (e ∙ idp))) ∙
                  ap (λ p → ap right (! p)) (ap-∘-!-!-rid-rid (fst (G <#> g)) (cin j) c idp
                    e (cglue g w) (cglue g (fun (G # i) a))) ∙
                  ap (λ p → ap right (! p)) (apCommSq (cin j ∘ fst (G <#> g)) (cin i) (cglue g) c) 
                  ==
                  ap-∘-!-!-rid (cin i) right c idp 
                lemma3 idp idp = lemma4 (cglue g (fun (G # i) a))
                  where
                    lemma4 : {x y : Colim ForgG} (α : x == y)
                      → (ap (λ q₁ → q₁) (ψ₂-free-helper-pre3 α α) ∙
                      ap (λ p → ap right (! (! (! (p ∙ idp) ∙ α) ∙ α))) (!-inv-r α) ∙ idp) ∙
                      ap (λ p → ap right (! p)) (!-inv-l α)
                      == idp
                    lemma4 idp = idp

    abstract

      map-MainRed0 : (q : cin {D = ConsDiag Γ A} j a == cin i a) {e : ty (F # j)} (s₃ : e == fun (F # j) a)
        → ! (ap (λ p → p ∙ idp) (↯ (id-free glue q (ap (right ∘ cin i) (snd (nat δ i) a))))) ◃∙
        ↯ (ψ₂-free q s₃ (ap ψ₂ q) (transp-pth-cmp q (glue (cin j a))) (apd-tr glue q)) ◃∙
        ap (λ p → glue (cin i a) ∙ ap right (! p)) (long-red-!-∙ (cin j) (fst (nat δ j)) (fst (G <#> g)) (snd (nat δ i) a) (snd (G <#> g) a) s₃ (snd (nat δ j) a)
          (cglue g (fst (nat δ i) (fun (F # i) a))) (cglue g (fun (G # i) a))) ◃∙
        ap (λ p → glue (cin i a) ∙ ap right (! p)) (apCommSq (cin j ∘ fst (G <#> g)) (cin i) (cglue g) (snd (nat δ i) a)) ◃∎
        =ₛ
        ap-∘-!-!-rid (cin i) right (snd (nat δ i) a) (glue (cin i a)) ◃∎
      map-MainRed0 q idp = MainRed-helper q (snd (nat δ j) a) 
