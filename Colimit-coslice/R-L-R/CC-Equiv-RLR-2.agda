{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Colim
open import Coslice
open import Diagram-Cos
open import SIP-CosCoc
open import Cocone-po
open import AuxPaths
open import Helper-paths
open import CC-Equiv-RLR-1

module CC-Equiv-RLR-2 where

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} (f : A → B) where

  ap-cmp-inv-loop-red : {x y : A} (p : x == y) → ap f (p ∙ idp) ∙ idp == (ap f p ∙ idp) ∙ idp
  ap-cmp-inv-loop-red idp = idp

  ap-cmp-inv-loop-eq : ∀ {ℓ} {E : Type ℓ} (k : E → A) {x : E} {y : A} (q : y == k x)
    → ap-cmp-inv-loop f k q idp == ap-cmp-inv-loop-red q
  ap-cmp-inv-loop-eq k idp = idp

module _ {ℓ} {A : Type ℓ} where

  helper-coher-rid : {x : A} (r : x == x) (δ : idp == r)
    → ap (λ p → ! (((p ∙ idp) ∙ idp) ∙ idp) ∙ r) δ ◃∙ db-neg-rid-db r idp ◃∙ ap (λ p → p ∙ idp) δ ◃∎ =ₛ ! (∙-unit-r r) ◃∎
  helper-coher-rid r idp = =ₛ-in idp 

  coher-rid-trip : {x : A} (r : x == x) (τ : idp == ! (! r)) →
    ap (λ p → ! (((p ∙ idp) ∙ idp) ∙ idp) ∙ r) τ ◃∙
    ap (λ p → ! (((p ∙ idp) ∙ idp) ∙ idp) ∙ r) (!-! r) ◃∙
    db-neg-rid-db r idp ◃∙
    ap (λ p → p ∙ idp) τ ◃∙ ap (λ p → p ∙ idp) (!-! r) ◃∎
      =ₛ
    ! (∙-unit-r r) ◃∎
  coher-rid-trip r τ =
    ap (λ p → ! (((p ∙ idp) ∙ idp) ∙ idp) ∙ r) τ ◃∙
    ap (λ p → ! (((p ∙ idp) ∙ idp) ∙ idp) ∙ r) (!-! r) ◃∙
    db-neg-rid-db r idp ◃∙
    ap (λ p → p ∙ idp) τ ◃∙
    ap (λ p → p ∙ idp) (!-! r) ◃∎
      =ₛ₁⟨ 0 & 2 & ∙-ap (λ p → ! (((p ∙ idp) ∙ idp) ∙ idp) ∙ r) τ (!-! r) ⟩
    ap (λ p → ! (((p ∙ idp) ∙ idp) ∙ idp) ∙ r) (τ ∙ !-! r) ◃∙
    db-neg-rid-db r idp ◃∙
    ap (λ p → p ∙ idp) τ ◃∙
    ap (λ p → p ∙ idp) (!-! r) ◃∎
      =ₛ₁⟨ 2 & 2 & ∙-ap (λ p → p ∙ idp) τ (!-! r) ⟩
    ap (λ p → ! (((p ∙ idp) ∙ idp) ∙ idp) ∙ r) (τ ∙ !-! r) ◃∙
    db-neg-rid-db r idp ◃∙
    ap (λ p → p ∙ idp) (τ ∙ !-! r) ◃∎
      =ₛ⟨  helper-coher-rid r (τ ∙ !-! r) ⟩
    ! (∙-unit-r r) ◃∎ ∎ₛ

module ConstrE2Cont2 {ℓv ℓe ℓ ℓd ℓc} {Γ : Graph ℓv ℓe} {A : Type ℓ} (F : CosDiag ℓd ℓ A Γ) (T : Coslice ℓc ℓ A) (K : CosCocone A F T) where

  open ConstrE2Cont F T K public

  module Equiv2c (i j : Obj Γ) (g : Hom Γ i j) (a : A) where

    open Equiv2b i j g a

    Ξ-Red2 : {R : fst (comp K j) (str (F # j) a) == str T a}
      {C : fst (comp K j) (fst (F <#> g) (str (F # i) a)) == fst (comp K i) (str (F # i) a)}
      (W : fst (comp K i) (str (F # i) a) == str T a) (s : ! C ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ R == W)
      → ! C ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ R =-= ! (! W)
    Ξ-Red2 W s = s ◃∙ ! (!-! W) ◃∎

    abstract
      Ξ-Red2Eq : (R : fst (comp K j) (str (F # j) a) == str T a) (t : ap (fst (recCosCoc K)) (! (glue (cin j a))) ∙ idp == ! (! R))
        {C : fst (comp K j) (fst (F <#> g) (str (F # i) a)) == fst (comp K i) (str (F # i) a)}
        (c : ap (recc (comp K) (comTri K)) (cglue g (str (F # i) a)) == C)
        {W : fst (comp K i) (str (F # i) a) == str T a} (s : ! C ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ R == W) →
        ! (ap (λ p → ! p ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ R) (∘-ap (fst (recCosCoc K)) right (cglue g (str (F # i) a)) ∙ c)) ◃∙
        ap (λ p → ! (p ∙ fst (comTri LRfun g) (str (F # i) a)) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ R)
          (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
        ap (λ p →
             ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙
               ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙ fst (comTri LRfun g) (str (F # i) a)) ∙
             ap (fst (comp K j)) (snd (F <#> g) a) ∙ R)
           t ◃∙
        ap (λ p →
             ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
               fst (comTri LRfun g) (str (F # i) a)) ∙
             ap (fst (comp K j)) (snd (F <#> g) a) ∙ R)
           (!-! R) ◃∙
        CCeq-coh-path (snd (F <#> g) a) R (snd (comp LRfun j) a) (fst (comTri LRfun g) (str (F # i) a)) idp ◃∙
        !-ap-ap-∘-ap-∙ (fst (recCosCoc K)) (fst (comp ColCoC-cos j)) (snd (F <#> g) a) (fst (comTri ColCoC-cos g) (str (F # i) a)) ◃∙
        ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (E₁ (snd (F <#> g) a) (! (glue (cin j a))))) ◃∙
        Ξ-Red1 idp R t C c W s
          =ₛ
        Ξ-Red2 {R = R} {C = C} W s
      Ξ-Red2Eq R t idp idp = =ₛ-in (lemma (cglue g (str (F # i) a)))
        where
          lemma : {y : Colim (DiagForg A Γ F)} (κ : cin j (fst (F <#> g) (str (F # i) a)) == y) →
            ! (ap (λ p → ! p ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ R) (∘-ap (fst (recCosCoc K)) right κ ∙ idp)) ∙
            ap (λ p → ! (p ∙ ap (fst (recCosCoc K)) (ap right κ)) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ R)
              (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ∙
            ap (λ p →
                 ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
                   ap (fst (recCosCoc K)) (ap right κ)) ∙
                 ap (fst (comp K j)) (snd (F <#> g) a) ∙ R)
               t ∙
            ap (λ p →
                 ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
                   ap (fst (recCosCoc K)) (ap right κ)) ∙
                 ap (fst (comp K j)) (snd (F <#> g) a) ∙ R)
               (!-! R) ∙
            CCeq-coh-path (snd (F <#> g) a) R (ap (fst (recCosCoc K)) (! (glue (cin j a))) ∙ idp) (ap (fst (recCosCoc K)) (ap right κ)) idp ∙
            !-ap-ap-∘-ap-∙ (fst (recCosCoc K)) (fst (comp ColCoC-cos j)) (snd (F <#> g) a) (ap right κ) ∙
            ap (λ p → p ∙ snd (recCosCoc K) a) (ap (ap (fst (recCosCoc K))) (E₁ (snd (F <#> g) a) (! (glue (cin j a))))) ∙
            CCeq-coh-path2 right (fst (recCosCoc K)) (cin j) left (snd (F <#> g) a) κ (glue (cin j a)) idp ∙
            ap (λ p → (! (ap (recc (comp K) (comTri K)) κ) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ p) ∙ idp) t ∙
            ap (λ p → (! (ap (recc (comp K) (comTri K)) κ) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ p) ∙ idp) (!-! R) ∙ 
            ap-dbl-inv-∙-del (str T) idp (! (ap (recc (comp K) (comTri K)) κ) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ R)
              ==
            ! (!-! (! (ap (recc (comp K) (comTri K)) κ) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ R))
          lemma idp = lemma2 (snd (F <#> g) a)
            where
              lemma2 : {w : ty (F # j)} (Z : w == str (F # j) a) →
                ap (λ p → ! (p ∙ idp) ∙ ap (fst (comp K j)) Z ∙ R) (hmtpy-nat-rev (λ z → idp) Z (snd (comp LRfun j) a)) ∙
                ap (λ p →
                     ! ((ap (fst (comp K j)) Z ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) Z)) ∙ idp) ∙
                     ap (fst (comp K j)) Z ∙ R) t ∙
                     ap (λ p → ! ((ap (fst (comp K j)) Z ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) Z)) ∙ idp) ∙ ap (fst (comp K j)) Z ∙ R)
                   (!-! R) ∙
                CCeq-coh-path Z R (ap (fst (recCosCoc K)) (! (glue (cin j a))) ∙ idp) idp idp ∙
                !-ap-ap-∘-ap-∙ (fst (recCosCoc K)) (fst (comp ColCoC-cos j)) Z idp ∙
                ap (λ p → p ∙ snd (recCosCoc K) a) (ap (ap (fst (recCosCoc K))) (E₁ Z (! (glue (cin j a))))) ∙
                CCeq-coh-path2 right (fst (recCosCoc K)) (cin j) left Z idp (glue (cin j a)) idp ∙
                ap (λ p → (ap (fst (comp K j)) Z ∙ p) ∙ idp) t ∙
                ap (λ p → (ap (fst (comp K j)) Z ∙ p) ∙ idp) (!-! R) ∙ 
                ap-dbl-inv-∙-del (str T) idp (ap (fst (comp K j)) Z ∙ R)
                  ==
                ! (!-! (ap (fst (comp K j)) Z ∙ R))
              lemma2 idp = =ₛ-out (lemma3a ∙ₛ lemma3b (glue (cin j a)) R t)
                where
                  lemma3a :
                    ap (λ p → ! (p ∙ idp) ∙ R) (hmtpy-nat-rev {f = fst (comp K j)} (λ z → idp) idp (ap (fst (recCosCoc K)) (! (glue (cin j a))) ∙ idp)) ◃∙
                    ap (λ p → ! (((p ∙ ! (ap (fst (recCosCoc K)) (! (glue (cin j a))) ∙ idp)) ∙ idp) ∙ idp) ∙ R) t ◃∙
                    ap (λ p → ! (((p ∙ ! (ap (fst (recCosCoc K)) (! (glue (cin j a))) ∙ idp)) ∙ idp) ∙ idp) ∙ R) (!-! R) ◃∙
                    CCeq-coh-path {f = fst (comp K j)} {g = fst (comp K j)} idp R (ap (fst (recCosCoc K)) (! (glue (cin j a))) ∙ idp) idp idp ◃∙
                    ap (λ p → p ∙ idp) (ap (ap (fst (recCosCoc K))) (E₁ {f = right} {g = cin j} idp (! (glue (cin j a))))) ◃∙
                    ap-cmp-inv-loop (fst (recCosCoc K)) left (! (glue (cin j a))) idp ◃∙
                    ap (λ p → p ∙ idp) t ◃∙
                    ap (λ p → p ∙ idp) (!-! R) ◃∙
                    ap-dbl-inv-∙-del (str T) idp R ◃∎
                      =ₛ
                    ap (λ p → ! (p ∙ idp) ∙ R) (hmtpy-nat-rev {f = fst (comp K j)} (λ z → idp) idp (ap (fst (recCosCoc K)) (! (glue (cin j a))) ∙ idp)) ◃∙
                    ap (λ p → ! (((p ∙ ! (ap (fst (recCosCoc K)) (! (glue (cin j a))) ∙ idp)) ∙ idp) ∙ idp) ∙ R) t ◃∙
                    ap (λ p → ! (((p ∙ ! (ap (fst (recCosCoc K)) (! (glue (cin j a))) ∙ idp)) ∙ idp) ∙ idp) ∙ R) (!-! R) ◃∙
                    CCeq-coh-path {f = fst (comp K j)} {g = fst (comp K j)} idp R (ap (fst (recCosCoc K)) (! (glue (cin j a))) ∙ idp) idp idp ◃∙
                    ap (λ p → p ∙ idp) (ap (ap (fst (recCosCoc K))) (E₁ {f = right} {g = cin j} idp (! (glue (cin j a))))) ◃∙
                    ap-cmp-inv-loop-red (fst (recCosCoc K)) (! (glue (cin j a))) ◃∙
                    ap (λ p → p ∙ idp) t ◃∙
                    ap (λ p → p ∙ idp) (!-! R) ◃∙
                    ap-dbl-inv-∙-del (str T) idp R ◃∎
                  lemma3a = ap (λ p → ! (p ∙ idp) ∙ R) (hmtpy-nat-rev {f = fst (comp K j)} (λ z → idp) idp (ap (fst (recCosCoc K)) (! (glue (cin j a))) ∙ idp)) ◃∙
                    ap (λ p → ! (((p ∙ ! (ap (fst (recCosCoc K)) (! (glue (cin j a))) ∙ idp)) ∙ idp) ∙ idp) ∙ R) t ◃∙
                    ap (λ p → ! (((p ∙ ! (ap (fst (recCosCoc K)) (! (glue (cin j a))) ∙ idp)) ∙ idp) ∙ idp) ∙ R) (!-! R) ◃∙
                    CCeq-coh-path {f = fst (comp K j)} {g = fst (comp K j)} idp R (ap (fst (recCosCoc K)) (! (glue (cin j a))) ∙ idp) idp idp ◃∙
                    ap (λ p → p ∙ idp) (ap (ap (fst (recCosCoc K))) (E₁ {f = right} {g = cin j} idp (! (glue (cin j a))))) ◃∙
                    ap-cmp-inv-loop (fst (recCosCoc K)) left (! (glue (cin j a))) idp ◃∙
                    ap (λ p → p ∙ idp) t ◃∙
                    ap (λ p → p ∙ idp) (!-! R) ◃∙
                    ap-dbl-inv-∙-del (str T) idp R ◃∎
                      =ₛ₁⟨ 5 & 1 & ap-cmp-inv-loop-eq (fst (recCosCoc K)) left (! (glue (cin j a))) ⟩
                    ap (λ p → ! (p ∙ idp) ∙ R) (hmtpy-nat-rev {f = fst (comp K j)} (λ z → idp) idp (ap (fst (recCosCoc K)) (! (glue (cin j a))) ∙ idp)) ◃∙
                    ap (λ p → ! (((p ∙ ! (ap (fst (recCosCoc K)) (! (glue (cin j a))) ∙ idp)) ∙ idp) ∙ idp) ∙ R) t ◃∙
                    ap (λ p → ! (((p ∙ ! (ap (fst (recCosCoc K)) (! (glue (cin j a))) ∙ idp)) ∙ idp) ∙ idp) ∙ R) (!-! R) ◃∙
                    CCeq-coh-path {f = fst (comp K j)} {g = fst (comp K j)} idp R (ap (fst (recCosCoc K)) (! (glue (cin j a))) ∙ idp) idp idp ◃∙
                    ap (λ p → p ∙ idp) (ap (ap (fst (recCosCoc K))) (E₁ {f = right} {g = cin j} idp (! (glue (cin j a))))) ◃∙
                    ap-cmp-inv-loop-red (fst (recCosCoc K)) (! (glue (cin j a))) ◃∙
                    ap (λ p → p ∙ idp) t ◃∙
                    ap (λ p → p ∙ idp) (!-! R) ◃∙
                    ap-dbl-inv-∙-del (str T) idp R ◃∎ ∎ₛ

                  lemma3b : {y : po-coscol-tip} (G : y == right (ψ (cin j a))) (r : fst (comp K j) (str (F # j) a) == (fst (recCosCoc K)) y)
                    (τ : ap (fst (recCosCoc K)) (! G) ∙ idp == ! (! r)) →
                    ap (λ p → ! (p ∙ idp) ∙ r) (hmtpy-nat-rev {f = fst (comp K j)} (λ z → idp) idp (ap (fst (recCosCoc K)) (! G) ∙ idp)) ◃∙
                    ap (λ p → ! (((p ∙ ! (ap (fst (recCosCoc K)) (! G) ∙ idp)) ∙ idp) ∙ idp) ∙ r) τ ◃∙
                    ap (λ p → ! (((p ∙ ! (ap (fst (recCosCoc K)) (! G) ∙ idp)) ∙ idp) ∙ idp) ∙ r) (!-! r) ◃∙
                    CCeq-coh-path {f = fst (comp K j)} {g = fst (comp K j)} idp r (ap (fst (recCosCoc K)) (! G) ∙ idp) idp idp ◃∙
                    ap (λ p → p ∙ idp) (ap (ap (fst (recCosCoc K))) (E₁ {f = right} {g = cin j} idp (! G))) ◃∙
                    ap-cmp-inv-loop-red (fst (recCosCoc K)) (! G) ◃∙
                    ap (λ p → p ∙ idp) τ ◃∙
                    ap (λ p → p ∙ idp) (!-! r) ◃∙
                    (∙-unit-r r ∙ ! (!-! r)) ◃∎
                      =ₛ
                    ! (!-! r) ◃∎
                  lemma3b idp r τ = =ₛ-in (=ₛ-out (lemma4a ∙ₛ lemma4b r))
                    where
                      lemma4a :
                        ap (λ p → ! (((p ∙ idp) ∙ idp) ∙ idp) ∙ r) τ ◃∙
                        ap (λ p → ! (((p ∙ idp) ∙ idp) ∙ idp) ∙ r) (!-! r) ◃∙
                        db-neg-rid-db r idp ◃∙
                        ap (λ p → p ∙ idp) τ ◃∙
                        ap (λ p → p ∙ idp) (!-! r) ◃∙
                        (∙-unit-r r ∙ ! (!-! r)) ◃∎
                          =ₛ
                        ! (∙-unit-r r) ◃∙
                        (∙-unit-r r ∙ ! (!-! r)) ◃∎
                      lemma4a =
                        ap (λ p → ! (((p ∙ idp) ∙ idp) ∙ idp) ∙ r) τ ◃∙
                        ap (λ p → ! (((p ∙ idp) ∙ idp) ∙ idp) ∙ r) (!-! r) ◃∙
                        db-neg-rid-db r idp ◃∙
                        ap (λ p → p ∙ idp) τ ◃∙
                        ap (λ p → p ∙ idp) (!-! r) ◃∙
                        (∙-unit-r r ∙ ! (!-! r)) ◃∎
                          =ₛ⟨ 0 & 5 & coher-rid-trip r τ ⟩
                        ! (∙-unit-r r) ◃∙
                        (∙-unit-r r ∙ ! (!-! r)) ◃∎ ∎ₛ
                      
                      lemma4b : {y : ty T} (r' : y == fst (comp K j) (str (F # j) a)) →
                        ! (∙-unit-r r') ◃∙
                        (∙-unit-r r' ∙ ! (!-! r')) ◃∎
                          =ₛ
                        ! (!-! r') ◃∎
                      lemma4b idp = =ₛ-in idp

    Λ-eq0 =
      ! (ap (λ p → ! p ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (↯ (FunHomEq g (str (F # i) a)))) ◃∙ Ξ-RW.Ξ-inst g a
        =ₑ⟨ 1 & 7 &
          (ap (λ p → ! (p ∙  fst (comTri LRfun g) (str (F # i) a)) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
            (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
          ap (λ p →
               ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
               fst (comTri LRfun g) (str (F # i) a)) ∙
               ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
             (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
          ap (λ p →
               ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
               fst (comTri LRfun g) (str (F # i) a)) ∙
               ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
             (!-! (snd (comp K j) a)) ◃∙
          CCeq-coh-path (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (str (F # i) a)) idp ◃∙
          !-ap-ap-∘-ap-∙ (fst (recCosCoc K)) (fst (comp ColCoC-cos j)) (snd (F <#> g) a)  (fst (comTri ColCoC-cos g) (str (F # i) a)) ◃∙
          ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (E₁ (snd (F <#> g) a) (! (glue (cin j a))))) ◃∙
          ap (λ p → p ∙ (snd (recCosCoc K) a))
            (ap (ap (fst (recCosCoc K)))
              (! (ap (λ p → ! (ap right (! (ap (cin j) (snd (F <#> g) a)) ∙ cglue g (str (F # i) a))) ∙ ! (glue (cin j a)) ∙ p) (ap (ap left) (id-βr g a))))) ◃∙
          ap (λ p → p ∙ idp) (ap (ap (fst (recCosCoc K))) (E₃ {f = left} {h = [id]} {u = right} (λ z → ! (glue z)) (cglue g a) (ψ-βr g a) (λ z → idp))) ◃∙
          ∙-unit-r (ap (fst (recCosCoc K)) (! (glue (cin i a)) ∙ idp)) ◃∙
          ap-∙-cmp2 (fst (recCosCoc K)) left (! (glue (cin i a))) idp ◃∙
          ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
          ap (transport (λ z → reccForg K (ψ z) == str T ([id] z)) (cglue g a)) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
          transp-inv-comm (str T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
          ap ! (H₁ (cglue g a) (! (snd (comp K j) a)) (ψ-βr g a)) ◃∙
          ap ! (H₂ (snd (F <#> g) a) (snd (comp K j) a) (cglue g (str (F # i) a)) (recc-βr K g (str (F # i) a))) ◃∙
          ap !
            (ap (λ p → p ∙ ! (! (fst (comTri K g) (str (F # i) a)) ∙ ap (recc (comp K) (comTri K) ∘ cin j) (snd (F <#> g) a) ∙ (snd (comp K j) a)))
              (ap (λ p → ! (ap (str T) p)) (id-βr g a))) ◃∙
          ap ! (ap ! (snd (comTri K g) a)) ◃∙
          !-! (snd (comp K i) a) ◃∎)
          % Ξ-rewrite2 ⟩
      ! (ap (λ p → ! p ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (↯ (FunHomEq g (str (F # i) a)))) ◃∙
      ap (λ p → ! (p ∙ fst (comTri LRfun g) (str (F # i) a)) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p →
           ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
           fst (comTri LRfun g) (str (F # i) a)) ∙
           ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
         (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p →
           ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
           fst (comTri LRfun g) (str (F # i) a)) ∙
           ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
         (!-! (snd (comp K j) a)) ◃∙
      CCeq-coh-path (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (str (F # i) a)) idp ◃∙
      !-ap-ap-∘-ap-∙ (fst (recCosCoc K)) (fst (comp ColCoC-cos j)) (snd (F <#> g) a)  (fst (comTri ColCoC-cos g) (str (F # i) a)) ◃∙
      ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (E₁ (snd (F <#> g) a) (! (glue (cin j a))))) ◃∙
      ap (λ p → p ∙ (snd (recCosCoc K) a))
        (ap (ap (fst (recCosCoc K)))
          (! (ap (λ p → ! (ap right (! (ap (cin j) (snd (F <#> g) a)) ∙ cglue g (str (F # i) a))) ∙ ! (glue (cin j a)) ∙ p) (ap (ap left) (id-βr g a))))) ◃∙
      ap (λ p → p ∙ idp) (ap (ap (fst (recCosCoc K))) (E₃ {f = left} {h = [id]} {u = right} (λ z → ! (glue z)) (cglue g a) (ψ-βr g a) (λ z → idp))) ◃∙
      ∙-unit-r (ap (fst (recCosCoc K)) (! (glue (cin i a)) ∙ idp)) ◃∙
      ap-∙-cmp2 (fst (recCosCoc K)) left (! (glue (cin i a))) idp ◃∙
      ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
      ap (transport (λ z → reccForg K (ψ z) == str T ([id] z)) (cglue g a)) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      transp-inv-comm (str T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
      ap ! (H₁ (cglue g a) (! (snd (comp K j) a)) (ψ-βr g a)) ◃∙
      ap ! (H₂ (snd (F <#> g) a) (snd (comp K j) a) (cglue g (str (F # i) a)) (recc-βr K g (str (F # i) a))) ◃∙
      ap !
        (ap (λ p → p ∙ ! (! (fst (comTri K g) (str (F # i) a)) ∙ ap (recc (comp K) (comTri K) ∘ cin j) (snd (F <#> g) a) ∙ (snd (comp K j) a)))
          (ap (λ p → ! (ap (str T) p)) (id-βr g a))) ◃∙
      ap ! (ap ! (snd (comTri K g) a)) ◃∙
      !-! (snd (comp K i) a) ◃∎ ∎ₛ

    Λ-eq1 =
      ! (ap (λ p → ! p ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (↯ (FunHomEq g (str (F # i) a)))) ◃∙
      ap (λ p → ! (p ∙  fst (comTri LRfun g) (str (F # i) a)) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p →
           ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
             fst (comTri LRfun g) (str (F # i) a)) ∙
           ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
         (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p →
           ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
             fst (comTri LRfun g) (str (F # i) a)) ∙
           ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
         (!-! (snd (comp K j) a)) ◃∙
      CCeq-coh-path (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (str (F # i) a)) idp ◃∙
      !-ap-ap-∘-ap-∙ (fst (recCosCoc K)) (fst (comp ColCoC-cos j)) (snd (F <#> g) a)  (fst (comTri ColCoC-cos g) (str (F # i) a)) ◃∙
      ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (E₁ (snd (F <#> g) a) (! (glue (cin j a))))) ◃∙
      ap (λ p → p ∙ (snd (recCosCoc K) a))
        (ap (ap (fst (recCosCoc K)))
          (! (ap (λ p → ! (ap right (! (ap (cin j) (snd (F <#> g) a)) ∙ cglue g (str (F # i) a))) ∙ ! (glue (cin j a)) ∙ p) (ap (ap left) (id-βr g a))))) ◃∙
      ap (λ p → p ∙ idp) (ap (ap (fst (recCosCoc K))) (E₃ {f = left} {h = [id]} {u = right} (λ z → ! (glue z)) (cglue g a) (ψ-βr g a) (λ z → idp))) ◃∙
      ∙-unit-r (ap (fst (recCosCoc K)) (! (glue (cin i a)) ∙ idp)) ◃∙
      ap-∙-cmp2 (fst (recCosCoc K)) left (! (glue (cin i a))) idp ◃∙
      ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
      ap (transport (λ z → reccForg K (ψ z) == str T ([id] z)) (cglue g a)) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      transp-inv-comm (str T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
      ap ! (H₁ (cglue g a) (! (snd (comp K j) a)) (ψ-βr g a)) ◃∙
      ap ! (H₂ (snd (F <#> g) a) (snd (comp K j) a) (cglue g (str (F # i) a)) (recc-βr K g (str (F # i) a))) ◃∙
      ap !
        (ap (λ p → p ∙ ! (! (fst (comTri K g) (str (F # i) a)) ∙ ap (recc (comp K) (comTri K) ∘ cin j) (snd (F <#> g) a) ∙ (snd (comp K j) a)))
          (ap (λ p → ! (ap (str T) p)) (id-βr g a))) ◃∙
      ap ! (ap ! (snd (comTri K g) a)) ◃∙
      !-! (snd (comp K i) a) ◃∎
        =ₑ⟨ 8 & 7 &
          (↯ (Ξ-Red0 (cglue g a) (ap [id] (cglue g a)) (! (ap (cin j) (snd (F <#> g) a)) ∙ (cglue g (str (F # i) a)))
               (snd (comp K j) a) idp (glue (cin j a)) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))))) ◃∎
          % =ₛ-in
              (=ₛ-out
                (Ξ-RedEq0 (cglue g a) (! (ap (cin j) (snd (F <#> g) a)) ∙ cglue g (str (F # i) a)) (ψ-βr g a) (snd (comp K j) a) (λ z → idp)
                  (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))))) ⟩
      ! (ap (λ p → ! p ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (↯ (FunHomEq g (str (F # i) a)))) ◃∙
      ap (λ p → ! (p ∙  fst (comTri LRfun g) (str (F # i) a)) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p →
           ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
             fst (comTri LRfun g) (str (F # i) a)) ∙
           ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
         (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p →
           ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
             fst (comTri LRfun g) (str (F # i) a)) ∙
           ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
         (!-! (snd (comp K j) a)) ◃∙
      CCeq-coh-path (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (str (F # i) a)) idp ◃∙
      !-ap-ap-∘-ap-∙ (fst (recCosCoc K)) (fst (comp ColCoC-cos j)) (snd (F <#> g) a)  (fst (comTri ColCoC-cos g) (str (F # i) a)) ◃∙
      ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (E₁ (snd (F <#> g) a) (! (glue (cin j a))))) ◃∙
      ap (λ p → p ∙ (snd (recCosCoc K) a))
        (ap (ap (fst (recCosCoc K)))
          (! (ap (λ p → ! (ap right (! (ap (cin j) (snd (F <#> g) a)) ∙ cglue g (str (F # i) a))) ∙ ! (glue (cin j a)) ∙ p) (ap (ap left) (id-βr g a))))) ◃∙
      ↯ (Ξ-Red0 (cglue g a) (ap [id] (cglue g a)) (! (ap (cin j) (snd (F <#> g) a)) ∙ (cglue g (str (F # i) a)))
          (snd (comp K j) a) idp (glue (cin j a)) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a)))) ◃∙
      ap ! (H₂ (snd (F <#> g) a) (snd (comp K j) a) (cglue g (str (F # i) a)) (recc-βr K g (str (F # i) a))) ◃∙
      ap !
        (ap (λ p → p ∙ ! (! (fst (comTri K g) (str (F # i) a)) ∙ ap (recc (comp K) (comTri K) ∘ cin j) (snd (F <#> g) a) ∙ (snd (comp K j) a)))
          (ap (λ p → ! (ap (str T) p)) (id-βr g a))) ◃∙
      ap ! (ap ! (snd (comTri K g) a)) ◃∙
      !-! (snd (comp K i) a) ◃∎ ∎ₛ

