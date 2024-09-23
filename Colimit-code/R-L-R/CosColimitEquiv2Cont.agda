{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import lib.PathSeq
open import Coslice
open import Diagram
open import Colim
open import Cocone
open import FTID-Cos
open import AuxPaths
open import Helper-paths
open import CosColimitEquiv2

module CosColimitEquiv2Cont where

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (e : A → B) (f : C → A) where

  Ξ-coher1-trip : {y z : C} (q : y == z) {x : A} (p : f y == x) {w : C} (r : z == w)  
    →  ap e (! p ∙ ap f q ∙ ap f r) ∙ idp == (ap e (! p) ∙ ap (e ∘ f) q) ∙ ap (e ∘ f) r
  Ξ-coher1-trip idp idp idp = idp 

  ap-∙-cmp2 : {x : A} {y z : C} (p : x == f y) (q : y == z)
    → ap e (p ∙ ap f q) == ap e p ∙ ap (e ∘ f) q
  ap-∙-cmp2 idp idp = idp

module _ {ℓ} {C : Type ℓ} {x y : C} where

  Ξ-coher2 : {z : C} (p : x == y) (q : y == z) →  ! (! p) ∙ q == ! (! q ∙ ! p ∙ idp)
  Ξ-coher2 idp idp = idp

  ap-rid-transf : {c₁ c₂ : x == y} (p : c₁ == c₂) →  (∙-unit-r c₁) ∙ p ∙ ! (∙-unit-r c₂) == ap (λ q → q ∙ idp) p
  ap-rid-transf {c₁ = c₁} idp = !-inv-r (∙-unit-r c₁)

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} (f : A → B) where

  ap-dbl-inv-∙-del : {x y : A} (p : x == y) {b : B} (w : b == f x) → w ∙ ap f p == ! (! (ap f p) ∙ ! w)
  ap-dbl-inv-∙-del idp w = ∙-unit-r w ∙ ! (!-! w)

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {E : Type ℓ₄} (f : A → B) (e : B → C) (k : E → B) where

  Ξ-helper1-delay : {a₁ a₂ : A} (p₁ : a₂ == a₁) {d₃ : E} (p₂ : k d₃ == f a₂) {d₁ d₂ : E} (p₄ : d₁ == d₂) (p₃ : d₃ == d₁)  
    → ap e (! (ap f p₁) ∙ ! p₂ ∙ ap k p₃ ∙ ap k p₄) ∙ idp == ap e (! (ap f p₁)) ∙ (ap e (! p₂) ∙ ap (e ∘ k) p₃) ∙ ap (e ∘ k) p₄
  Ξ-helper1-delay idp p₂ p₄ p₃ = Ξ-coher1-trip e k p₃ p₂ p₄      

  Ξ-helper2-delay : {a₁ a₂ : A} (p₁ : a₂ == a₁) {z₁ z₂ : E} (p₃ : z₁ == z₂) (p₂ : e (f a₂) == e (k z₁))  
    → ap e (! (ap f p₁)) ∙ ! (! p₂) ∙ ap (e ∘ k) p₃ ==
    ! (! (ap (e ∘ k) p₃) ∙ ! p₂ ∙ ap (e ∘ f) p₁)
  Ξ-helper2-delay idp p₃ p₂ = Ξ-coher2 p₂ (ap (e ∘ k) p₃) --  

module ConstrE2Cont {ℓv ℓe ℓ ℓd ℓc} {Γ : Graph ℓv ℓe} {A : Type ℓ} (F : CosDiag ℓd ℓ A Γ) (T : Coslice ℓc ℓ A) (K : CosCocone A F T) where

  open ConstrE2 F T K public

  module Equiv2b (i j : Obj Γ) (g : Hom Γ i j) (a : A) where

    open Equiv2a i j g a public

    abstract

      Ξ-rewrite : Ξ-inst =ₛ
        ap (λ p → ! (p ∙  fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a)
          (snd (comp LRfun j) a)) ◃∙
        ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a))) ◃∙
        ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap ! (FPrecc-βr K (cin j a))) ◃∙
        ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (!-! (snd (comp K j) a)) ◃∙
        long-path-red (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (fun (F # i) a)) idp ◃∙
        ap-cp-revR (fst (recCosCoc K)) (fst (comp ColCoC j)) (snd (F <#> g) a)  (fst (comTri ColCoC g) (fun (F # i) a)) ◃∙
        ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (E₁ (snd (F <#> g) a) (! (glue (cin j a))))) ◃∙
        ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K)))
          (! (ap (λ p → ! (ap right (! (ap (cin j) (snd (F <#> g) a)) ∙ cglue g (fun (F # i) a))) ∙ ! (glue (cin j a)) ∙ p) (ap (ap left) (id-βr g a))))) ◃∙
        ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (E₃ (λ z → ! (glue z)) (cglue g a) (ψ-βr g a) (λ z → idp))) ◃∙
        ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (∙-unit-r (! (glue (cin i a))))) ◃∙
        ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
        ap (transport (λ z → reccForg K (ψ z) == fun T ([id] z)) (cglue g a)) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
        tranp-inv-comm (fun T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
        ap ! (H₁ (cglue g a) (! (snd (comp K j) a)) (ψ-βr g a)) ◃∙
        ap ! (H₂ (snd (F <#> g) a) (snd (comp K j) a) (cglue g (fun (F # i) a)) (recc-βr K g (fun (F # i) a))) ◃∙
        ap ! (ap (λ p → p ∙ ! (! (fst (comTri K g) (fun (F # i) a)) ∙ ap (recc (comp K) (comTri K) ∘ cin j) (snd (F <#> g) a) ∙
          (snd (comp K j) a))) (ap (λ p → ! (ap (fun T) p)) (id-βr g a))) ◃∙
        ap ! (ap ! (snd (comTri K g) a)) ◃∙
        !-! (snd (comp K i) a) ◃∎
      Ξ-rewrite = Ξ-RW1 ∙ₛ (Ξ-RW2 ∙ₛ (Ξ-RW3 ∙ₛ (Ξ-RW4 ∙ₛ (Ξ-RW5 ∙ₛ Ξ-RW6))))

      Ξ-rewrite-refine : {x : Colim (ConsDiag Γ A)} (q : cin j a == x) {U : ψ (cin j a) == ψ x} (E : ap ψ q == U)
        → ap (λ p → p ∙ idp) (ap (ap (fst (recCosCoc K))) (E₃ {f = left} {h = [id]} {u = right} (λ z → ! (glue z)) q E (λ z → idp))) ◃∙
        ap (λ p → p ∙ idp) (ap (ap (fst (recCosCoc K))) (∙-unit-r (! (glue x)))) ◃∙
        ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) q) ◃∎
          =ₛ
        ap (λ p → p ∙ idp) (ap (ap (fst (recCosCoc K))) (E₃ {f = left} {h = [id]} {u = right} (λ z → ! (glue z)) q E (λ z → idp))) ◃∙
        ∙-unit-r (ap (fst (recCosCoc K)) (! (glue x) ∙ idp)) ◃∙
        ap-∙-cmp2 (fst (recCosCoc K)) left (! (glue x)) idp ◃∙
        ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) q) ◃∎
      Ξ-rewrite-refine idp idp = =ₛ-in (lemma (glue (cin j a)))
        where
          lemma : {y : P} (G : left a == y)
            → ap (λ p → p ∙ idp) (ap (ap (fst (recCosCoc K))) (∙-unit-r (! G))) ∙ idp
              ==
            ∙-unit-r (ap (fst (recCosCoc K)) ((! G) ∙ idp)) ∙
            ap-∙-cmp2 (fst (recCosCoc K)) left (! G) idp ∙ idp
          lemma idp = idp

    abstract

      Ξ-rewrite2 : Ξ-inst =ₛ
             ap (λ p → ! (p ∙  fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
               (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
             ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
               fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙      
               ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙                                            
             ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
               fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙      
               ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (!-! (snd (comp K j) a)) ◃∙                                                                                                    
             long-path-red (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (fun (F # i) a)) idp ◃∙                                                                    
             ap-cp-revR (fst (recCosCoc K)) (fst (comp ColCoC j)) (snd (F <#> g) a)  (fst (comTri ColCoC g) (fun (F # i) a)) ◃∙                                                                         
             ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (E₁ (snd (F <#> g) a) (! (glue (cin j a))))) ◃∙                                                                          
               ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K)))                                                                                                                        
             (! (ap (λ p → ! (ap right (! (ap (cin j) (snd (F <#> g) a)) ∙ cglue g (fun (F # i) a))) ∙ ! (glue (cin j a)) ∙ p) (ap (ap left) (id-βr g a))))) ◃∙                                         
             ap (λ p → p ∙ idp) (ap (ap (fst (recCosCoc K))) (E₃ {f = left} {h = [id]} {u = right} (λ z → ! (glue z)) (cglue g a) (ψ-βr g a) (λ z → idp))) ◃∙                                           
             ∙-unit-r (ap (fst (recCosCoc K)) (! (glue (cin i a)) ∙ idp)) ◃∙                                                                                                                            
             ap-∙-cmp2 (fst (recCosCoc K)) left (! (glue (cin i a))) idp ◃∙                                                                                                                             
             ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙                                                                                                                
             ap (transport (λ z → reccForg K (ψ z) == fun T ([id] z)) (cglue g a)) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙                                  
             tranp-inv-comm (fun T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙                                                                                                       
             ap ! (H₁ (cglue g a) (! (snd (comp K j) a)) (ψ-βr g a)) ◃∙                                                                                                                                 
             ap ! (H₂ (snd (F <#> g) a) (snd (comp K j) a) (cglue g (fun (F # i) a)) (recc-βr K g (fun (F # i) a))) ◃∙                                                                                  
             ap ! (ap (λ p → p ∙ ! (! (fst (comTri K g) (fun (F # i) a)) ∙ ap (recc (comp K) (comTri K) ∘ cin j) (snd (F <#> g) a) ∙ (snd (comp K j) a)))
               (ap (λ p → ! (ap (fun T) p)) (id-βr g a))) ◃∙ 
             ap ! (ap ! (snd (comTri K g) a)) ◃∙                                                                                                                                                        
             !-! (snd (comp K i) a) ◃∎
      Ξ-rewrite2 = Ξ-inst
          =ₛ⟨ Ξ-rewrite ⟩
        ap (λ p → ! (p ∙  fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a)
          (snd (comp LRfun j) a)) ◃∙
        ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a))) ◃∙
        ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap ! (FPrecc-βr K (cin j a))) ◃∙
        ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (!-! (snd (comp K j) a)) ◃∙
        long-path-red (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (fun (F # i) a)) idp ◃∙
        ap-cp-revR (fst (recCosCoc K)) (fst (comp ColCoC j)) (snd (F <#> g) a)  (fst (comTri ColCoC g) (fun (F # i) a)) ◃∙
        ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (E₁ (snd (F <#> g) a) (! (glue (cin j a))))) ◃∙
        ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K)))
          (! (ap (λ p → ! (ap right (! (ap (cin j) (snd (F <#> g) a)) ∙ cglue g (fun (F # i) a))) ∙ ! (glue (cin j a)) ∙ p) (ap (ap left) (id-βr g a))))) ◃∙
        ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (E₃ (λ z → ! (glue z)) (cglue g a) (ψ-βr g a) (λ z → idp))) ◃∙
        ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (∙-unit-r (! (glue (cin i a))))) ◃∙
        ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
        ap (transport (λ z → reccForg K (ψ z) == fun T ([id] z)) (cglue g a)) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
        tranp-inv-comm (fun T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
        ap ! (H₁ (cglue g a) (! (snd (comp K j) a)) (ψ-βr g a)) ◃∙
        ap ! (H₂ (snd (F <#> g) a) (snd (comp K j) a) (cglue g (fun (F # i) a)) (recc-βr K g (fun (F # i) a))) ◃∙
        ap ! (ap (λ p → p ∙ ! (! (fst (comTri K g) (fun (F # i) a)) ∙ ap (recc (comp K) (comTri K) ∘ cin j) (snd (F <#> g) a) ∙ (snd (comp K j) a)))
          (ap (λ p → ! (ap (fun T) p)) (id-βr g a))) ◃∙
        ap ! (ap ! (snd (comTri K g) a)) ◃∙
        !-! (snd (comp K i) a) ◃∎
          =ₛ⟨ 8 & 3 & Ξ-rewrite-refine (cglue g a) (ψ-βr g a) ⟩
        ap (λ p → ! (p ∙  fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a)
          (snd (comp LRfun j) a)) ◃∙
        ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a))) ◃∙
        ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap ! (FPrecc-βr K (cin j a))) ◃∙
        ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (!-! (snd (comp K j) a)) ◃∙
        long-path-red (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (fun (F # i) a)) idp ◃∙
        ap-cp-revR (fst (recCosCoc K)) (fst (comp ColCoC j)) (snd (F <#> g) a)  (fst (comTri ColCoC g) (fun (F # i) a)) ◃∙
        ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (E₁ (snd (F <#> g) a) (! (glue (cin j a))))) ◃∙
        ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K)))
          (! (ap (λ p → ! (ap right (! (ap (cin j) (snd (F <#> g) a)) ∙ cglue g (fun (F # i) a))) ∙ ! (glue (cin j a)) ∙ p) (ap (ap left) (id-βr g a))))) ◃∙
        ap (λ p → p ∙ idp) (ap (ap (fst (recCosCoc K))) (E₃ {f = left} {h = [id]} {u = right} (λ z → ! (glue z)) (cglue g a) (ψ-βr g a) (λ z → idp))) ◃∙
        ∙-unit-r (ap (fst (recCosCoc K)) (! (glue (cin i a)) ∙ idp)) ◃∙
        ap-∙-cmp2 (fst (recCosCoc K)) left (! (glue (cin i a))) idp ◃∙
        ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
        ap (transport (λ z → reccForg K (ψ z) == fun T ([id] z)) (cglue g a)) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
        tranp-inv-comm (fun T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
        ap ! (H₁ (cglue g a) (! (snd (comp K j) a)) (ψ-βr g a)) ◃∙
        ap ! (H₂ (snd (F <#> g) a) (snd (comp K j) a) (cglue g (fun (F # i) a)) (recc-βr K g (fun (F # i) a))) ◃∙
        ap ! (ap (λ p → p ∙ ! (! (fst (comTri K g) (fun (F # i) a)) ∙ ap (recc (comp K) (comTri K) ∘ cin j) (snd (F <#> g) a) ∙ (snd (comp K j) a)))
          (ap (λ p → ! (ap (fun T) p)) (id-βr g a))) ◃∙
        ap ! (ap ! (snd (comTri K g) a)) ◃∙
        !-! (snd (comp K i) a) ◃∎
          =ₛ₁⟨ 1 & 2 & ∙-ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
              fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap-inv-rid (fst (recCosCoc K))
              (glue (cin j a))) (ap ! (FPrecc-βr K (cin j a))) ⟩
        ap (λ p → ! (p ∙  fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a)       
               (snd (comp LRfun j) a)) ◃∙                                                                                                                                                               
             ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
               fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙      
               ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙                                            
             ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
               fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙      
               ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (!-! (snd (comp K j) a)) ◃∙                                                                                                    
             long-path-red (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (fun (F # i) a)) idp ◃∙                                                                    
             ap-cp-revR (fst (recCosCoc K)) (fst (comp ColCoC j)) (snd (F <#> g) a)  (fst (comTri ColCoC g) (fun (F # i) a)) ◃∙                                                                         
             ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (E₁ (snd (F <#> g) a) (! (glue (cin j a))))) ◃∙                                                                          
               ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K)))                                                                                                                        
             (! (ap (λ p → ! (ap right (! (ap (cin j) (snd (F <#> g) a)) ∙ cglue g (fun (F # i) a))) ∙ ! (glue (cin j a)) ∙ p) (ap (ap left) (id-βr g a))))) ◃∙                                         
             ap (λ p → p ∙ idp) (ap (ap (fst (recCosCoc K))) (E₃ {f = left} {h = [id]} {u = right} (λ z → ! (glue z)) (cglue g a) (ψ-βr g a) (λ z → idp))) ◃∙                                           
             ∙-unit-r (ap (fst (recCosCoc K)) (! (glue (cin i a)) ∙ idp)) ◃∙                                                                                                                            
             ap-∙-cmp2 (fst (recCosCoc K)) left (! (glue (cin i a))) idp ◃∙                                                                                                                             
             ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙                                                                                                                
             ap (transport (λ z → reccForg K (ψ z) == fun T ([id] z)) (cglue g a)) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙                                  
             tranp-inv-comm (fun T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙                                                                                                       
             ap ! (H₁ (cglue g a) (! (snd (comp K j) a)) (ψ-βr g a)) ◃∙                                                                                                                                 
             ap ! (H₂ (snd (F <#> g) a) (snd (comp K j) a) (cglue g (fun (F # i) a)) (recc-βr K g (fun (F # i) a))) ◃∙                                                                                  
             ap ! (ap (λ p → p ∙ ! (! (fst (comTri K g) (fun (F # i) a)) ∙ ap (recc (comp K) (comTri K) ∘ cin j) (snd (F <#> g) a) ∙ (snd (comp K j) a)))
               (ap (λ p → ! (ap (fun T) p)) (id-βr g a))) ◃∙ 
             ap ! (ap ! (snd (comTri K g) a)) ◃∙                                                                                                                                                        
             !-! (snd (comp K i) a) ◃∎ ∎ₛ


    Ξ-Red0 : {x : Colim (ConsDiag Γ A)} (q : cin j a == x) (Q : a == [id] x) (U : ψ (cin j a) == ψ x) (R : fst (comp K j) (fun (F # j) a) == fun T a) (L : a == a)
      (M : left a == right (ψ (cin j a)))  (t : ap (fst (recCosCoc K)) (! M) ∙ ap (fun T) L == ! (! R))
      → ap (fst (recCosCoc K)) (! (ap right U) ∙ (! M) ∙ ap left L ∙ ap left Q) ∙ idp =-= ! (! (ap (fun T) Q) ∙ ! R ∙ ap (recc (comp K) (comTri K)) U)
    Ξ-Red0 q Q U R L M t = ap (fst (recCosCoc K)) (! (ap right U) ∙ (! M) ∙ ap left L ∙ ap left Q) ∙ idp
                         =⟪  Ξ-helper1-delay right (fst (recCosCoc K)) left U M Q L  ⟫
                       ap (fst (recCosCoc K)) (! (ap right U)) ∙ (ap (fst (recCosCoc K)) (! M) ∙ ap (fun T) L) ∙ ap (fun T) Q
                         =⟪ ap (λ p → ap (fst (recCosCoc K)) (! (ap right U)) ∙ p ∙ ap (fun T) Q) t  ⟫
                       ap (fst (recCosCoc K)) (! (ap right U)) ∙ ! (! R) ∙ ap (fun T) Q
                         =⟪ Ξ-helper2-delay right (fst (recCosCoc K)) left U Q R  ⟫
                       ! (! (ap (fun T) Q) ∙ ! R ∙ ap (recc (comp K) (comTri K)) U) ∎∎ 

    abstract

      Ξ-RedEq0 : {x : Colim (ConsDiag Γ A)} (q : cin j a == x) (U : ψ (cin j a) == ψ x) (E : ap ψ q == U) (R : fst (comp K j) (fun (F # j) a) == fun T a)
        (L : (z : Colim (ConsDiag Γ A)) → [id] z == [id] z) (t : ap (fst (recCosCoc K)) (! (glue (cin j a))) ∙ ap (fun T) (L (cin j a)) == ! (! R))
        → ap (λ p → p ∙ idp) (ap (ap (fst (recCosCoc K))) (E₃ {f = left} {h = [id]} (λ z → ! (glue z)) q E (λ z → ap left (L z)))) ◃∙
        ∙-unit-r (ap (fst (recCosCoc K)) (! (glue x) ∙ ap left (L x))) ◃∙
        ap-∙-cmp2 (fst (recCosCoc K)) left (! (glue x)) (L x) ◃∙
        ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ ap (fun T) (L z)) q) ◃∙
        ap (transport (λ z → reccForg K (ψ z) == fun T ([id] z)) q) t ◃∙
        tranp-inv-comm (fun T ∘ [id]) (reccForg K ∘ ψ) q (! R) ◃∙
        ap ! (H₁ q (! R) E) ◃∎
          =ₛ
        Ξ-Red0 q (ap [id] q) U R (L (cin j a)) (glue (cin j a)) t
      Ξ-RedEq0 idp U idp R L t = =ₛ-in (lemma (glue (cin j a)) (L (cin j a)) R t)
        where
          lemma : {y : P} (G : left a == y) {z : A} (Λ : a == z) 
            (r : fst (recCosCoc K) y == fun T z) (τ : ap (fst (recCosCoc K)) (! G) ∙ ap (fun T) Λ == ! (! r)) 
            → ap (λ p → p ∙ idp) (ap (ap (fst (recCosCoc K))) (ap (_∙_ (! G)) (∙-unit-r (ap left Λ)))) ∙
              ∙-unit-r (ap (fst (recCosCoc K)) ((! G) ∙ (ap left Λ))) ∙
              ap-∙-cmp2 (fst (recCosCoc K)) left (! G) Λ ∙
              ap (λ z → z) τ ∙
              ap ! (! (∙-unit-r (! r))) ==
            Ξ-coher1-trip (fst (recCosCoc K)) left Λ G idp ∙
            ap (λ p → p ∙ idp) τ ∙
            Ξ-coher2 r idp
          lemma idp idp r τ = lemma2 r τ ∙ ap (λ p → p ∙ Ξ-coher2 r idp) (ap-rid-transf τ)
            where
              lemma2 : {c₁ c₂ : ty T} (r' : c₁ == c₂) {p : c₁ == c₂} (τ' : p == ! (! r'))
                → ap (λ z → z) τ' ∙ ap ! (! (∙-unit-r (! r'))) == (τ' ∙ ! (∙-unit-r (! (! r')))) ∙ Ξ-coher2 r' idp
              lemma2 idp idp = idp

    Ξ-Red1 : (Q : a == a) (R : fst (comp K j) (fun (F # j) a) == fun T a) (t : ap (fst (recCosCoc K)) (! (glue (cin j a))) ∙ ap (fun T) Q == ! (! R))
      (C : fst (comp K j) (fst (F <#> g) (fun (F # i) a)) == fst (comp K i) (fun (F # i) a)) (c : ap (recc (comp K) (comTri K)) (cglue g (fun (F # i) a)) == C)
      (W : fst (comp K i) (fun (F # i) a) == fun T a) (s : ! C ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ R == W)
      → ap (fst (recCosCoc K)) (! (ap right (! (ap (cin j) (snd (F <#> g) a)) ∙ (cglue g (fun (F # i) a)))) ∙ ! (glue (cin j a)) ∙ ap left Q ∙ ap left Q) ∙ idp
        =-= ! (! (ap (fun T) Q) ∙ ! W)
    Ξ-Red1 Q R t C c W s =
      ap (fst (recCosCoc K)) (! (ap right (! (ap (cin j) (snd (F <#> g) a)) ∙ (cglue g (fun (F # i) a)))) ∙ ! (glue (cin j a)) ∙ ap left Q ∙ ap left Q) ∙ idp
        =⟪ long-path-red2 right (fst (recCosCoc K)) (cin j) left (snd (F <#> g) a) (cglue g (fun (F # i) a)) (glue (cin j a)) Q  ⟫
      (! (ap (recc (comp K) (comTri K)) (cglue g (fun (F # i) a))) ∙ ap (recc (comp K) (comTri K) ∘ cin j) (snd (F <#> g) a) ∙
        (ap (fst (recCosCoc K)) (! (glue (cin j a))) ∙ ap (fun T) Q)) ∙
        ap (fun T) Q
        =⟪ ap (λ p → (! p ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ (ap (fst (recCosCoc K)) (! (glue (cin j a))) ∙ ap (fun T) Q)) ∙ ap (fun T) Q) c ⟫   
      (! C ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ (ap (fst (recCosCoc K)) (! (glue (cin j a))) ∙ ap (fun T) Q)) ∙ ap (fun T) Q
        =⟪ ap (λ p → (! C ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ p) ∙ ap (fun T) Q) t ⟫           
      (! C ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ ! (! R)) ∙ ap (fun T) Q 
        =⟪ ap (λ p → (! C ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ p) ∙ ap (fun T) Q) (!-! R) ⟫
      (! C ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ R) ∙ ap (fun T) Q
        =⟪ ap (λ p → p ∙ ap (fun T) Q) s ⟫
      W ∙ ap (fun T) Q
        =⟪ ap-dbl-inv-∙-del (fun T) Q W  ⟫
      ! (! (ap (fun T) Q) ∙ ! W)
      ∎∎

    abstract

      Ξ-RedEq1 : (Q : a == a) (I : ap [id] (cglue g a) == Q) (R : fst (comp K j) (fun (F # j) a) == fun T a) (t : ap (fst (recCosCoc K)) (! (glue (cin j a))) ∙ ap (fun T) Q == ! (! R))
        (C : fst (comp K j) (fst (F <#> g) (fun (F # i) a)) == fst (comp K i) (fun (F # i) a)) (c : ap (recc (comp K) (comTri K)) (cglue g (fun (F # i) a)) == C)
        (W : fst (comp K i) (fun (F # i) a) == fun T a) (s : ! C ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ R == W)
        →
        ap (λ p → p ∙ idp) (ap (ap (fst (recCosCoc K))) (! (ap (λ p → ! (ap right (! (ap (cin j) (snd (F <#> g) a)) ∙ cglue g (fun (F # i) a))) ∙ ! (glue (cin j a)) ∙ ap left Q ∙ p)
          (ap (ap left) I)))) ◃∙
        ↯ (Ξ-Red0 (cglue g a) (ap [id] (cglue g a)) (! (ap (cin j) (snd (F <#> g) a)) ∙ (cglue g (fun (F # i) a))) R Q (glue (cin j a)) t) ◃∙
        ap ! (H₂ (snd (F <#> g) a) R (cglue g (fun (F # i) a)) c) ◃∙
        ap ! (ap (λ p → p ∙ ! (! C ∙ ap (recc (comp K) (comTri K) ∘ cin j) (snd (F <#> g) a) ∙ R)) (ap (λ p → ! (ap (fun T) p)) I)) ◃∙
        ap ! (ap (λ p → ! (ap (fun T) Q) ∙ p) (ap ! s)) ◃∎
          =ₛ
        Ξ-Red1 Q R t C c W s
      Ξ-RedEq1 Q idp R t C idp W idp = =ₛ-in (lemma (cglue g (fun (F # i) a)))
        where
          lemma : {y : Colim (DiagForg A Γ F)} (κ : cin j (fst (F <#> g) (fun (F # i) a)) == y)
            → (Ξ-helper1-delay right (fst (recCosCoc K)) left (! (ap (cin j) (snd (F <#> g) a)) ∙ κ) (glue (cin j a)) (ap [id] (cglue g a)) (ap [id] (cglue g a)) ∙
            ap (λ p →  ap (fst (recCosCoc K)) (! (ap right (! (ap (cin j) (snd (F <#> g) a)) ∙ κ))) ∙ p ∙ ap (fun T) (ap [id] (cglue g a))) t ∙
            Ξ-helper2-delay right (fst (recCosCoc K)) left (! (ap (cin j) (snd (F <#> g) a)) ∙ κ) (ap [id] (cglue g a)) R) ∙
            ap ! (H₂ {u = recc (comp K) (comTri K)} {g = cin j} (snd (F <#> g) a) R κ idp) ∙
            idp
              ==
            long-path-red2 right (fst (recCosCoc K)) (cin j) left (snd (F <#> g) a) κ (glue (cin j a)) (ap [id] (cglue g a)) ∙
            ap (λ p → (! (ap (recc (comp K) (comTri K)) κ) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ p) ∙ ap (fun T) (ap [id] (cglue g a))) t ∙
            ap (λ p → (! (ap (recc (comp K) (comTri K)) κ) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ p) ∙ ap (fun T) (ap [id] (cglue g a))) (!-! R) ∙
            ap-dbl-inv-∙-del (fun T) (ap [id] (cglue g a)) (! (ap (recc (comp K) (comTri K)) κ) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ R) 
          lemma idp = lemma2 (snd (F <#> g) a)
            where
              lemma2 : {w : ty (F # j)} (Z : w == fun (F # j) a)
                → (Ξ-helper1-delay right (fst (recCosCoc K)) left (! (ap (cin j) Z) ∙ idp) (glue (cin j a)) (ap [id] (cglue g a)) (ap [id] (cglue g a)) ∙
                ap (λ p →  ap (fst (recCosCoc K)) (! (ap right (! (ap (cin j) Z) ∙ idp))) ∙ p ∙ ap (fun T) (ap [id] (cglue g a))) t ∙
                Ξ-helper2-delay right (fst (recCosCoc K)) left (! (ap (cin j) Z) ∙ idp) (ap [id] (cglue g a)) R) ∙
                ap ! (H₂ Z R idp idp) ∙ idp
                  ==
                long-path-red2 right (fst (recCosCoc K)) (cin j) left Z idp (glue (cin j a)) (ap [id] (cglue g a)) ∙
                ap (λ p → (ap (fst (comp K j)) Z ∙ p) ∙ ap (fun T) (ap [id] (cglue g a))) t ∙ ap (λ p → (ap (fst (comp K j)) Z ∙ p) ∙
                  ap (fun T) (ap [id] (cglue g a))) (!-! R) ∙
                ap-dbl-inv-∙-del (fun T) (ap [id] (cglue g a)) (ap (fst (comp K j)) Z ∙ R)
              lemma2 idp = lemma3 (glue (cin j a)) R t
                where
                  lemma3 : {y : P} (G : left a == y) (r : fst (recCosCoc K) y == fun T a) (τ : ap (fst (recCosCoc K)) (! G) ∙ ap (fun T) (ap [id] (cglue g a)) == ! (! r))
                    → (Ξ-coher1-trip (fst (recCosCoc K)) left (ap [id] (cglue g a)) G (ap [id] (cglue g a)) ∙ -- Ξ-coher1-trip e k p₃ p₂ p₄
                    ap (λ p → p ∙ ap (fun T) (ap [id] (cglue g a))) τ ∙
                    Ξ-coher2 r (ap (fun T) (ap [id] (cglue g a)))) ∙
                    ap ! (ap (λ p → ! (ap (fun T) (ap [id] (cglue g a))) ∙ p) (∙-unit-r (! r))) ∙ idp
                      ==
                    ap-cmp-inv-loop (fst (recCosCoc K)) left (! G) (ap [id] (cglue g a)) ∙
                    ap (λ p → p ∙ ap (fun T) (ap [id] (cglue g a))) τ ∙
                    ap (λ p → p ∙ ap (fun T) (ap [id] (cglue g a))) (!-! r) ∙
                    ap-dbl-inv-∙-del (fun T) (ap [id] (cglue g a)) r 
                  lemma3 idp r τ = lemma4 (ap [id] (cglue g a)) r τ (ap [id] (cglue g a))
                    where
                      lemma4 : {y : A} (Q₁ : a == y) (r' : fun T a == fun T y) (τ' : ap (fun T) Q₁ == ! (! r')) {z : A} (Q₂ : y == z)
                        → (Ξ-coher1-trip (fst (recCosCoc K)) left Q₁ idp Q₂ ∙
                        ap (λ p → p ∙ ap (fun T) Q₂) τ' ∙
                        Ξ-coher2 r' (ap (fun T) Q₂)) ∙
                        ap ! (ap (_∙_ (! (ap (fun T) Q₂))) (∙-unit-r (! r'))) ∙
                        idp
                          ==
                        ap-inv-cmp-rid2 left (fst (recCosCoc K)) Q₁ Q₂ ∙
                        ap (λ p → p ∙ ap (fun T) Q₂) τ' ∙
                        ap (λ p → p ∙ ap (fun T) Q₂) (!-! r') ∙
                        ap-dbl-inv-∙-del (fun T) Q₂ r'
                      lemma4 idp r' τ' idp = lemma5 r' τ'
                        where
                          lemma5 : {y : ty T} (𝕣 : y == fun T a) {c : y == fun T a} (u : c == ! (! 𝕣))
                            → (ap (λ p → p ∙ idp) u ∙ Ξ-coher2 𝕣 idp) ∙
                            ap ! (ap (λ q → q) (∙-unit-r (! 𝕣))) ∙ idp
                              ==
                            ap (λ p → p ∙ idp) u ∙
                            ap (λ p → p ∙ idp) (!-! 𝕣) ∙ ap-dbl-inv-∙-del (fun T) idp 𝕣
                          lemma5 idp idp = idp

