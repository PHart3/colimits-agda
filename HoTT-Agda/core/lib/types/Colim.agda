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

  module ColimitMap {Γ : Graph ℓv ℓe} {ℓd₁ ℓd₂} {F : Diag ℓd₁ Γ} {G : Diag ℓd₂ Γ} (M : DiagMor F G) where

    private
      module M = ColimRec {D = F} {V = Colim G} (λ i → (cin i) ∘ (nat M i))
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

    module _ {ℓ} {F : Diag ℓd Γ} {D : Type ℓ} where

      can-coc-is-eqv : is-equiv (PostComp (can-coc F) D)
      can-coc-is-eqv = is-eq (PostComp (can-coc F) D) (λ K → colimR (comp K) λ _ _ g → comTri K g)
        (λ K → CocEq-to-== (coceq (λ _ _ → idp) (λ g x → cglue-βr (comp K) (λ _ _ g → comTri K g) g x)))
        λ f → λ= $
          ColimMapEq _ f (λ _ _ → idp) (λ i j g x → ap (λ p → ! p ∙ ap f (cglue g x)) (cglue-βr _ _ g x) ∙ !-inv-l (ap f (cglue g x)))

      can-coc-is-contr : (K : Cocone F D) → is-contr (Σ (Colim F → D) (λ f → PostComp (can-coc F) D f == K))
      can-coc-is-contr K = equiv-is-contr-map can-coc-is-eqv K

      pstcomp-coc-mor-≃ : (K : Cocone F D) (f : Colim F → D) → (PostComp (can-coc F) D f == K) ≃ Cocone-mor-str (can-coc F) K f
      pstcomp-coc-mor-≃ _ f = equiv ==-to-mor mor-to-== rtrip1 rtrip2

        where
          ==-to-mor : {L : Cocone F D} → PostComp (can-coc F) D f == L → Cocone-mor-str (can-coc F) L f
          comp-∼ (==-to-mor e) = comp-== (==-to-CocEq e)
          comTri-∼ (==-to-mor e) = tri-== (==-to-CocEq e) 

          mor-to-== : {L : Cocone F D} → Cocone-mor-str (can-coc F) L f →  PostComp (can-coc F) D f == L
          mor-to-== m = CocEq-to-== (coceq (comp-∼ m) (comTri-∼ m))

          rtrip1 : {L : Cocone F D} (b : Cocone-mor-str (can-coc F) L f) → ==-to-mor (mor-to-== b) == b
          rtrip1 {L} b = CocMorEq-to-==
            (cocmoreq
              (λ i x → ap (λ p → comp-== p i x) (CocEq-≃.rtrip2 {K₂ = L} (coceq (comp-∼ b) (comTri-∼ b))))
              λ {i} {j} g x → =ₛ-out $
                ap (λ p → ! p ∙ ap f (cglue g x) ∙' comp-∼ b i x)
                  (! (ap (λ p → comp-== p j ((F <#> g) x)) (CocEq-≃.rtrip2 {K₂ = L} (coceq (comp-∼ b) (comTri-∼ b))))) ◃∙
                ap (λ p → ! (comp-== (==-to-CocEq (mor-to-== b)) j ((F <#> g) x)) ∙ ap f (cglue g x) ∙' p)
                  (! (ap (λ p → comp-== p i x) (CocEq-≃.rtrip2 {K₂ = L} (coceq (comp-∼ b) (comTri-∼ b))))) ◃∙
                tri-== (==-to-CocEq (mor-to-== b)) g x ◃∎
                  =ₛ⟨ 2 & 1 & apCommSq2◃' (λ ce → tri-== ce g x) (CocEq-≃.rtrip2 {K₂ = L} (coceq (comp-∼ b) (comTri-∼ b))) ⟩
                ap (λ p → ! p ∙ ap f (cglue g x) ∙' comp-∼ b i x)
                  (! (ap (λ p → comp-== p j ((F <#> g) x)) (CocEq-≃.rtrip2 {K₂ = L} (coceq (comp-∼ b) (comTri-∼ b))))) ◃∙
                ap (λ p → ! (comp-== (==-to-CocEq (mor-to-== b)) j ((F <#> g) x)) ∙ ap f (cglue g x) ∙' p)
                  (! (ap (λ p → comp-== p i x) (CocEq-≃.rtrip2 {K₂ = L} (coceq (comp-∼ b) (comTri-∼ b))))) ◃∙
                ap (λ p → ! (comp-== p j ((F <#> g) x)) ∙ ap f (cglue g x) ∙' comp-== p i x)
                  (CocEq-≃.rtrip2 {K₂ = L} (coceq (comp-∼ b) (comTri-∼ b))) ◃∙
                comTri-∼ b g x ◃∙
                ! (ap (λ _ → comTri L g x) (CocEq-≃.rtrip2 {K₂ = L} (coceq (comp-∼ b) (comTri-∼ b)))) ◃∎
                  =ₛ₁⟨ 0 & 3 & aux g x (CocEq-≃.rtrip2 {K₂ = L} (coceq (comp-∼ b) (comTri-∼ b))) ⟩
                idp ◃∙
                comTri-∼ b g x ◃∙
                ! (ap (λ _ → comTri L g x) (CocEq-≃.rtrip2 {K₂ = L} (coceq (comp-∼ b) (comTri-∼ b)))) ◃∎
                  =ₛ₁⟨ ap (λ p → comTri-∼ b g x ∙ ! p) (ap-cst (comTri L g x) _) ∙ ∙-unit-r (comTri-∼ b g x) ⟩
                comTri-∼ b g x ◃∎ ∎ₛ)
                where abstract
                  aux : ∀ {i} {j} g x {t : _}
                    (r : t == coceq (comp-∼ b) (comTri-∼ b)) → 
                    ap (λ p → ! p ∙ ap f (cglue g x) ∙' comp-∼ b i x)
                      (! (ap (λ p → comp-== p j ((F <#> g) x)) r)) ∙
                    ap (λ p → ! (comp-== t j ((F <#> g) x)) ∙  ap f (cglue g x) ∙' p)
                      (! (ap (λ p → comp-== p i x) r)) ∙
                    ap (λ p → ! (comp-== p j ((F <#> g) x)) ∙ ap f (cglue g x) ∙' comp-== p i x) r
                      ==
                    idp
                  aux {i} {j} g x idp = idp

          rtrip2 : {L : Cocone F D} (a : PostComp (can-coc F) D f == L) → mor-to-== (==-to-mor a) == a
          rtrip2 idp = CocEq-β

      can-coc-mor-contr : (K : Cocone F D) → is-contr (Σ (Colim F → D) (λ f → Cocone-mor-str (can-coc F) K f))
      can-coc-mor-contr K = equiv-preserves-level (Σ-emap-r (pstcomp-coc-mor-≃ K)) {{can-coc-is-contr K}}

      can-coc-mor-paths : {K : Cocone F D} {f₁ f₂ : Colim F → D}
        (σ₁ : Cocone-mor-str (can-coc F) K f₁) (σ₂ : Cocone-mor-str (can-coc F) K f₂)
        → (f₁ , σ₁) == (f₂ , σ₂)
      can-coc-mor-paths {K} {f₁} {f₂} σ₁ σ₂ = contr-has-all-paths {{can-coc-mor-contr K}} (f₁ , σ₁) (f₂ , σ₂)
