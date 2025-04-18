{-# OPTIONS --without-K --rewriting #-}

-- Coordinate description of A-cocone identity

open import lib.Basics
open import lib.types.Sigma
open import lib.types.Pi
open import Helper-paths
open import FTID
open import Coslice
open import Diagram

module FTID-Cos where

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f g : A → B} where

  long-path-red : {x y : A} (p : x == y) {z : B} (q₁ : g y == z) (q₂ : f y  == z)
    {w : B} (P : f x == w) {v : B} (C : w == v)
    → ! ((ap g p ∙ (q₁ ∙ ! q₂) ∙ ! (ap f p)) ∙ P ∙ C) ∙ ap g p ∙ q₁ == ! C ∙ ! P ∙ ap f p ∙ q₂
  long-path-red idp q₁ q₂ P idp = !-∙-!-rid-∙-rid P q₁ q₂ 

module _ {ℓv ℓe ℓ ℓd ℓc} {Γ : Graph ℓv ℓe} {A : Type ℓ} (F : CosDiag ℓd ℓ A Γ) (T : Coslice ℓc ℓ A) (K₁ : CosCocone A F T) where

  record CosCocEq (K₂ : CosCocone A F T) : Type (lmax ℓc (lmax (lmax ℓv ℓe) (lmax ℓd ℓ))) where
    constructor CocEq
    field W : (i : Obj Γ) → fst (comp K₁ i) ∼ fst (comp K₂ i)
    field u : (i : Obj Γ) (a : A) → ! (W i (fun (F # i) a)) ∙ snd (comp K₁ i) a == snd (comp K₂ i) a    
    Ξ : (i j : Obj Γ) (g : Hom Γ i j) (a : A) → ! (! (W j (fst (F <#> g) (fun (F # i) a))) ∙ fst (comTri K₁ g) (fun (F # i) a) ∙ W i (fun (F # i) a)) ∙
      ap (fst (comp K₂ j)) (snd (F <#> g) a) ∙ snd (comp K₂ j) a =-= snd (comp K₂ i) a
    Ξ i j g a =
      ! (! (W j (fst (F <#> g) (fun (F # i) a))) ∙ fst (comTri K₁ g) (fun (F # i) a) ∙ W i (fun (F # i) a)) ∙
      ap (fst (comp K₂ j)) (snd (F <#> g) a) ∙
      snd (comp K₂ j) a
        =⟪ ap (λ p → ! (p ∙ fst (comTri K₁ g) (fun (F # i) a) ∙ W i (fun (F # i) a)) ∙ ap (fst (comp K₂ j)) (snd (F <#> g) a) ∙ snd (comp K₂ j) a)
             (hmtpy-nat-rev (W j) (snd (F <#> g) a) (snd (comp K₁ j) a)) ⟫
      ! ((ap (fst (comp K₂ j)) (snd (F <#> g) a) ∙ ((! (W j (fun (F # j) a)) ∙ snd (comp K₁ j) a) ∙ ! (snd (comp K₁ j) a)) ∙ ! (ap (fst (comp K₁ j)) (snd (F <#> g) a))) ∙
        fst (comTri K₁ g) (fun (F # i) a) ∙ W i (fun (F # i) a)) ∙
      ap (fst (comp K₂ j)) (snd (F <#> g) a) ∙ snd (comp K₂ j) a
        =⟪ ap (λ p → ! ((ap (fst (comp K₂ j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp K₁ j) a)) ∙ ! (ap (fst (comp K₁ j)) (snd (F <#> g) a))) ∙
             fst (comTri K₁ g) (fun (F # i) a) ∙ W i (fun (F # i) a)) ∙ ap (fst (comp K₂ j)) (snd (F <#> g) a) ∙ snd (comp K₂ j) a)
           (u j a) ⟫
      ! ((ap (fst (comp K₂ j)) (snd (F <#> g) a) ∙ (snd (comp K₂ j) a ∙ ! (snd (comp K₁ j) a)) ∙ ! (ap (fst (comp K₁ j)) (snd (F <#> g) a))) ∙
        fst (comTri K₁ g) (fun (F # i) a) ∙ W i (fun (F # i) a)) ∙
      ap (fst (comp K₂ j)) (snd (F <#> g) a) ∙ snd (comp K₂ j) a
        =⟪ long-path-red (snd (F <#> g) a) (snd (comp K₂ j) a) (snd (comp K₁ j) a) (fst (comTri K₁ g) (fun (F # i) a)) (W i (fun (F # i) a)) ⟫
      ! (W i (fun (F # i) a)) ∙ ! (fst (comTri K₁ g) (fun (F # i) a)) ∙ ap (fst (comp K₁ j)) (snd (F <#> g) a) ∙ snd (comp K₁ j) a
        =⟪ ap (λ p → ! (W i (fun (F # i) a)) ∙ p) (snd (comTri K₁ g) a) ⟫
      ! (W i (fun (F # i) a)) ∙ snd (comp K₁ i) a
        =⟪ u i a ⟫
      snd (comp K₂ i) a ∎∎
    field
      Λ : {i j : Obj Γ} (g : Hom Γ i j) →
        Σ ((x : ty (F # i)) → ! (W j (fst (F <#> g) x)) ∙ fst (comTri K₁ g) x ∙ W i x == fst (comTri K₂ g) x)
          (λ R → ((a : A) →
            ! (ap (λ p → ! p ∙ ap (fst (comp K₂ j)) (snd (F <#> g) a) ∙ snd (comp K₂ j) a) (R (fun (F # i) a))) ◃∙
            Ξ i j g a =ₛ snd (comTri K₂ g) a ◃∎))
        
  open CosCocEq public

  center-CCEq : CosCocEq K₁
  W center-CCEq = λ i x → idp
  u center-CCEq = λ i a → idp
  Λ center-CCEq {i} {j} g =
    (λ x → ∙-unit-r (fst (comTri K₁ g) x)) , (λ a → =ₛ-in (lemma a (snd (F <#> g) a) (snd (comp K₁ j) a) (snd (comTri K₁ g) a)))
    where
      lemma : (a : A) → {w : ty (F # j)} (σ₁ : fst (F <#> g) (fun (F # i) a) == w) {z : ty T} (σ₂ : fst (comp K₁ j) w == z)
        {v : fst (comp K₁ i) (fun (F # i) a) == z} (τ : ! (fst (comTri K₁ g) (fun (F # i) a)) ∙ ap (fst (comp K₁ j)) σ₁ ∙ σ₂ == v) →
        ! (ap (λ p → ! p ∙ ap (fst (comp K₁ j)) σ₁ ∙ σ₂) (∙-unit-r (fst (comTri K₁ g) (fun (F # i) a)))) ∙
        ap (λ p → ! (p ∙ fst (comTri K₁ g) (fun (F # i) a) ∙ idp) ∙ ap (fst (comp K₁ j)) σ₁ ∙ σ₂)
        (hmtpy-nat-rev (λ x → idp) σ₁ σ₂) ∙
        long-path-red σ₁ σ₂ σ₂ (fst (comTri K₁ g) (fun (F # i) a)) idp ∙
        ap (λ q → q) τ ∙ idp
        == τ
      lemma a idp idp idp = lemma2 (fst (comTri K₁ g) (fun (F # i) a))
        where
          lemma2 : {t : ty T} (U : fst (< A > comp K₁ j ∘ F <#> g) (fun (F # i) a) == t)
            → ! (ap (λ p → ! p ∙ idp) (∙-unit-r U)) ∙ long-path-red {f = fst (comp K₁ j)} {g = fst (comp K₁ j)} idp idp idp U idp ∙ idp == idp
          lemma2 idp = idp

  open MapsCos A

  CosCocEq-tot : Type (lmax ℓc (lmax (lmax ℓv ℓe) (lmax ℓd ℓ)))
  CosCocEq-tot =
    Σ ((i : Obj Γ) → (Σ (F # i *→  T) (λ g →  < F # i > comp K₁ i ∼ g)))
      (λ H → ((i j : Obj Γ) (g : Hom Γ i j) →
        Σ (Σ (fst (fst (H j)) ∘ fst (F <#> g) ∼ fst (fst (H i)))
            (λ K → (x : ty (F # i)) → ! (fst (snd (H j)) (fst (F <#> g) x)) ∙ fst (comTri K₁ g) x ∙ fst (snd (H i)) x == K x))
          (λ (K , R) →
            Σ ((a : A) → ! (K (fun (F # i) a)) ∙ ap (fst (fst (H j))) (snd (F <#> g) a) ∙ snd (fst (H j)) a  == snd (fst (H i)) a)
              (λ J →
                ((a : A) →
                  ! (ap (λ p → ! p ∙ ap (fst (fst (H j))) (snd (F <#> g) a) ∙ snd (fst (H j)) a) (R (fun (F # i) a))) ∙
                  ↯ (ϕ H i j g a) == J a)))))
    module CCEq-Σ where
      ϕ : (H : _) (i j : Obj Γ) (g : Hom Γ i j) (a : A) →
        ! (! (fst (snd (H j)) (fst (F <#> g) (fun (F # i) a))) ∙ fst (comTri K₁ g) (fun (F # i) a) ∙ fst (snd (H i)) (fun (F # i) a)) ∙
          ap (fst (fst (H j))) (snd (F <#> g) a) ∙ snd (fst (H j)) a
        =-=  snd (fst (H i)) a
      ϕ H i j g a =
        ! (! (fst (snd (H j)) (fst (F <#> g) (fun (F # i) a))) ∙ fst (comTri K₁ g) (fun (F # i) a) ∙ fst (snd (H i)) (fun (F # i) a)) ∙
        ap (fst (fst (H j))) (snd (F <#> g) a) ∙ snd (fst (H j)) a
          =⟪ ap (λ p → ! (p ∙  fst (comTri K₁ g) (fun (F # i) a) ∙ fst (snd (H i)) (fun (F # i) a)) ∙ ap (fst (fst (H j))) (snd (F <#> g) a) ∙ snd (fst (H j)) a)
               (hmtpy-nat-rev (fst (snd (H j))) (snd (F <#> g) a) (snd (comp K₁ j) a)) ⟫
        ! ((ap (fst (fst (H j))) (snd (F <#> g) a) ∙ ((! (fst (snd (H j)) (fun (F # j) a)) ∙ snd (comp K₁ j) a) ∙ ! (snd (comp K₁ j) a)) ∙ ! (ap (fst (comp K₁ j)) (snd (F <#> g) a))) ∙
          fst (comTri K₁ g) (fun (F # i) a) ∙ fst (snd (H i)) (fun (F # i) a)) ∙
          ap (fst (fst (H j))) (snd (F <#> g) a) ∙ snd (fst (H j)) a
          =⟪ ap
               (λ p →
                 ! ((ap (fst (fst (H j))) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp K₁ j) a)) ∙ ! (ap (fst (comp K₁ j)) (snd (F <#> g) a))) ∙
                   fst (comTri K₁ g) (fun (F # i) a) ∙ fst (snd (H i)) (fun (F # i) a)) ∙
                 ap (fst (fst (H j))) (snd (F <#> g) a) ∙ snd (fst (H j)) a) (snd (snd (H j)) a) ⟫
        ! ((ap (fst (fst (H j))) (snd (F <#> g) a) ∙ (snd (fst (H j)) a ∙ ! (snd (comp K₁ j) a)) ∙ ! (ap (fst (comp K₁ j)) (snd (F <#> g) a))) ∙
          fst (comTri K₁ g) (fun (F # i) a) ∙ fst (snd (H i)) (fun (F # i) a)) ∙ ap (fst (fst (H j))) (snd (F <#> g) a) ∙ snd (fst (H j)) a
          =⟪ long-path-red (snd (F <#> g) a) (snd (fst (H j)) a) (snd (comp K₁ j) a) (fst (comTri K₁ g) (fun (F # i) a)) (fst (snd (H i)) (fun (F # i) a)) ⟫
        ! (fst (snd (H i)) (fun (F # i) a)) ∙ ! (fst (comTri K₁ g) (fun (F # i) a)) ∙ ap (fst (comp K₁ j)) (snd (F <#> g) a) ∙ snd (comp K₁ j) a
          =⟪ ap (λ p → ! (fst (snd (H i)) (fun (F # i) a)) ∙ p) (snd (comTri K₁ g) a) ⟫
        ! (fst (snd (H i)) (fun (F # i) a)) ∙ snd (comp K₁ i) a
          =⟪ snd (snd (H i)) a ⟫
        snd (fst (H i)) a ∎∎

  CosCocEq-tot-contr : is-contr (CosCocEq-tot)
  CosCocEq-tot-contr =
    equiv-preserves-level ((Σ-contr-red (Π-level (λ i → PtFunHomContr (comp K₁ i))))⁻¹)
      {{Π-level
        (λ i → (Π-level (λ j →
          (Π-level (λ g →
            equiv-preserves-level ((Σ-contr-red (FunHomContr {f = λ z → (fst (comTri K₁ g) z) ∙ idp}))⁻¹)
            {{FunHomContr {f = λ a → ↯ (CCEq-Σ.ϕ (λ i → (comp K₁ i , (λ x → idp) , (λ a → idp))) i j g a)}}})))))}}

  CosCocEq-eq : CosCocEq-tot ≃ Σ (CosCocone A F T) (λ K₂ → CosCocEq K₂)
  CosCocEq-eq =
    equiv
      (λ x →
        ((λ i → fst (fst x i)) & (λ {j} {i} g → (fst (fst (snd x i j g))) , (fst (snd (snd x i j g))))) ,
        CocEq (λ i x₁ → fst (snd (fst x i)) x₁) (λ i a → snd (snd (fst x i)) a)
          (λ {i} {j} g → (λ x₁ → snd (fst (snd x i j g)) x₁ ) , λ a → =ₛ-in (snd (snd (snd x i j g)) a)))
      (λ ((r & K) , e) →
        (λ i → r i , (CosCocEq.W e i) , (CosCocEq.u e i)) ,
        λ i j g → (fst (K g) , fst (CosCocEq.Λ e g)) , (snd (K g)) , (λ a → =ₛ-out (snd (CosCocEq.Λ e g) a)))
      (λ b → idp)
      λ a → idp

  CosCocEq-IDsys : ID-sys (CosCocone A F T) (λ K → CosCocEq K) K₁ center-CCEq
  CosCocEq-IDsys p = contr-has-all-paths {{(equiv-preserves-level CosCocEq-eq {{CosCocEq-tot-contr}}) }} (K₁ , center-CCEq) p 

  CosCocEq-ind : {K₂ : CosCocone A F T} → CosCocEq K₂ → K₁ == K₂
  CosCocEq-ind {K₂} e = ind (ID-ind {P = λ K s → K₁ == K} CosCocEq-IDsys) idp K₂ e
