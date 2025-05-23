{-# OPTIONS --without-K --confluence-check --rewriting #-}

open import lib.Basics
open import lib.types.Graph
open import lib.types.Diagram

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

  module ColimitMap {d₁ d₂} {Γ : Graph ℓv ℓe} {F : Diag d₁ Γ} {G : Diag d₂ Γ} (M : DiagMor F G) where

    private
      module M = ColimRec {D = F} {V = Colim G} (λ i → (cin i) ∘ (nat M i))
        (λ i j g x →  ! (ap (cin j) (comSq M g x)) ∙ (cglue {i = i} {j = j} g (nat M i x) ) )

    ColMap : Colim F → Colim G
    ColMap = M.colimR

    MapComp : {i j : Obj Γ} (g : Hom Γ i j) (x : F # i)  →
      ap ColMap (cglue {i = i} {j = j} g x) == ! (ap (cin j) (comSq M g x)) ∙ (cglue {i = i} {j = j} g (nat M i x))
    MapComp g x = M.cglue-βr g x

  open ColimitMap public

