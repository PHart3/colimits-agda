{-# OPTIONS --without-K --confluence-check --rewriting #-}

open import lib.Basics
open import lib.Equivalence2
open import lib.types.Sigma
open import lib.types.Graph
open import lib.types.Diagram
open import lib.types.Diagram-SIP

-- definition of colimit HIT and its basic theory

module lib.types.Colim where 

module _ {ℓv ℓe}  where

  postulate  -- HIT
    Colim : ∀ {ℓd} → {Γ : Graph ℓv ℓe} (D : Diag ℓd Γ) → Type ℓd

  module _ {ℓd} {Γ : Graph ℓv ℓe} {D : Diag ℓd Γ} where

    postulate  -- HIT
      cin : (i : Obj Γ) → D # i → Colim D
      cglue : {i j : Obj Γ} (g : Hom Γ i j) (x : D # i) → cin j ((D <#> g) x) == cin i x

  module ColimElim {ℓd ℓ} {Γ : Graph ℓv ℓe} {D : Diag ℓd Γ} {P : Colim {ℓd = ℓd} {Γ = Γ} D → Type ℓ}
    (cin* : (i : Obj Γ) (x : D # i) → P (cin i x))
    (cglue* : (i j : Obj Γ) (g : Hom Γ i j) (x : D # i)
      → cin* j ((D <#> g) x) == cin* i x [ P ↓ cglue {i = i} {j = j} g x ]) where

    postulate  -- HIT
      colimE : Π (Colim {Γ = Γ} D) P
      cin-β : ∀ i x → colimE (cin i x) ↦ cin* i x
    {-# REWRITE cin-β #-}

    postulate  -- HIT
      cglue-β : ∀ {i j} g x → apd colimE (cglue {i = i} {j = j} g x) == cglue* i j g x

  open ColimElim public

  -- trees
  is-tree : Graph ℓv ℓe → Type lzero
  is-tree Γ = is-contr (Colim (ConsDiag Γ Unit))

  module _ {Γ : Graph ℓv ℓe} where

    ColimMapEq : ∀ {ℓd ℓ} {D : Diag ℓd Γ} {V : Type ℓ} (h₁ h₂ : Colim D → V)
      (H : (i : Obj Γ) → h₁ ∘ cin i ∼ h₂ ∘ cin i)
      → ((i j : Obj Γ) (g : Hom Γ i j) (x : D # i)
        → ! (ap h₁ (cglue g x)) ∙ H j ((D <#> g) x) ∙ ap h₂ (cglue g x)  == H i x )
      → h₁ ∼ h₂
    ColimMapEq {D = D} h₁ h₂ H = λ S → colimE H
      (λ i j g x → from-transp (λ x → h₁ x == h₂ x) (cglue g x) (transp-pth (cglue g x) (H j ((D <#> g) x)) ∙ (S i j g x))) 

    module ColimRec {ℓd ℓ} {D : Diag ℓd Γ} {V : Type ℓ}
      (cin* : (i : Obj Γ) → (D # i) → V)
      (cglue* :  (i j : Obj Γ) (g : Hom Γ i j) (x : D # i)
        → cin* j ((D <#> g) x) == cin* i x) where

      private
        module M = ColimElim cin* (λ i j g x → ↓-cst-in (cglue* i j g x))

      colimR : Colim D → V
      colimR = M.colimE

      cglue-βr : {i j : Obj Γ} (g : Hom Γ i j) (x : D # i) → ap colimR (cglue {i = i} {j = j} g x) == cglue* i j g x
      cglue-βr g x = apd=cst-in {f = colimR} (M.cglue-β g x)

    open ColimRec public 

  colimR-coc : ∀ {ℓ} {Γ : Graph ℓv ℓe} {ℓd} {D : Diag ℓd Γ} {V : Type ℓ} (J : Cocone D V) → Colim D → V
  colimR-coc J = colimR (comp J) (λ i j g x → comTri J g x)

  module ColimitMap {Γ : Graph ℓv ℓe} {ℓd₁ ℓd₂} {F : Diag ℓd₁ Γ} {G : Diag ℓd₂ Γ} (M : DiagMor F G) where

    private
      module M = ColimRec {D = F} {V = Colim G} (λ i → cin i ∘ nat M i)
        (λ i j g x →  ! (ap (cin j) (comSq M g x)) ∙ (cglue {i = i} {j = j} g (nat M i x)))

    ColMap : Colim F → Colim G
    ColMap = M.colimR

    MapComp : {i j : Obj Γ} (g : Hom Γ i j) (x : F # i) →
      ap ColMap (cglue {i = i} {j = j} g x) == ! (ap (cin j) (comSq M g x)) ∙ (cglue {i = i} {j = j} g (nat M i x))
    MapComp g x = M.cglue-βr g x

  open ColimitMap public

  module _ {Γ : Graph ℓv ℓe} {ℓd : ULevel} where

    can-coc : (F : Diag ℓd Γ) → Cocone F (Colim F)
    comp (can-coc F) = cin
    comTri (can-coc F) = cglue

    module _ {ℓ₁ ℓ₂} {F : Diag ℓd Γ} {D : Type ℓ₁} {E : Type ℓ₂} {J : Cocone F E} (ζ : is-colim J) where

      abstract
        can-coc-is-eqv : is-equiv (PostComp (can-coc F) D)
        can-coc-is-eqv = is-eq (PostComp (can-coc F) D) (λ K → colimR (comp K) λ _ _ g → comTri K g)
          (λ K → CocEq-to-== (coceq (λ _ _ → idp) (λ g x → cglue-βr (comp K) (λ _ _ g → comTri K g) g x)))
          λ f → λ= $
            ColimMapEq _ f (λ _ _ → idp) (λ i j g x → ap (λ p → ! p ∙ ap f (cglue g x)) (cglue-βr _ _ g x) ∙ !-inv-l (ap f (cglue g x)))

      can-coc-is-contr : (K : Cocone F D) → is-contr (Σ (E → D) (λ f → PostComp J D f == K))
      can-coc-is-contr K = equiv-is-contr-map (ζ D) K

      pstcomp-coc-mor-≃-aux : (K : Cocone F D) (f : E → D) → (CocEq (PostComp J D f) K) ≃ Cocone-mor-str J K f
      pstcomp-coc-mor-≃-aux _ f = equiv ==-to-mor mor-to-== rtrip1 rtrip2

        where
          ==-to-mor : {L : Cocone F D} → CocEq (PostComp J D f) L → Cocone-mor-str J L f
          comp-∼ (==-to-mor e) = comp-== e
          comTri-∼ (==-to-mor e) = tri-== e

          mor-to-== : {L : Cocone F D} → Cocone-mor-str J L f →  CocEq (PostComp J D f) L
          mor-to-== m = coceq (comp-∼ m) (comTri-∼ m)

          abstract
          
            rtrip1 : {L : Cocone F D} (b : Cocone-mor-str J L f) → ==-to-mor (mor-to-== b) == b
            rtrip1 {L} b = idp
            
            rtrip2 : {L : Cocone F D} (a : CocEq (PostComp J D f) L) → mor-to-== (==-to-mor a) == a
            rtrip2 = CocEq-ind (λ L a → mor-to-== (==-to-mor a) == a) idp

      pstcomp-coc-mor-≃ : (K : Cocone F D) (f : E → D) → (PostComp J D f == K) ≃ Cocone-mor-str J K f
      pstcomp-coc-mor-≃ K f = pstcomp-coc-mor-≃-aux K f ∘e CocEq-==-≃ ⁻¹

      can-coc-mor-contr : (K : Cocone F D) → is-contr (Σ (E → D) (λ f → Cocone-mor-str J K f))
      can-coc-mor-contr K = equiv-preserves-level (Σ-emap-r (pstcomp-coc-mor-≃ K)) {{can-coc-is-contr K}}

      abstract
        can-coc-mor-paths : {K : Cocone F D} {f₁ f₂ : E → D}
          (σ₁ : Cocone-mor-str J K f₁) (σ₂ : Cocone-mor-str J K f₂)
          → (f₁ , σ₁) == (f₂ , σ₂)
        can-coc-mor-paths {K} {f₁} {f₂} σ₁ σ₂ = contr-has-all-paths {{can-coc-mor-contr K}} (f₁ , σ₁) (f₂ , σ₂)
