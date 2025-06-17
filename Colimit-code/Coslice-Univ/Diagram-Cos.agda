{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import Helper-paths
open import Coslice

module Diagram-Cos where 

open import lib.types.Graph public
open import lib.types.Diagram public

private variable ℓv ℓv' ℓv'' ℓe ℓe' ℓe'' ℓd ℓd' : ULevel 

CosGr : ∀ i j (A : Type j) → Graph (lmax (lsucc i) j) (lmax i j)
Obj (CosGr i j A) = Coslice i j A
Hom (CosGr i j A) X Y = < A > X *→ Y

-- coslice-valued diagram
CosDiag : ∀ i j (A : Type j) (Γ : Graph ℓv ℓe) → Type (lmax (lmax (lmax ℓv ℓe) (lsucc i)) j)
CosDiag i j A Γ = GraphHom Γ (CosGr i j A)

-- forgetful functor
DiagForg : ∀ {i j} (A : Type j) (Γ : Graph ℓv ℓe) → CosDiag i j A Γ → Diag i Γ
(DiagForg A Γ D) # x = ty (D # x)
(DiagForg A Γ D) <#> f = fst (D <#> f) 

record CosDiagMor {Γ : Graph ℓv ℓe} {ℓ₁ ℓ₂ ℓ₃} (A : Type ℓ₁) (F : CosDiag ℓ₂ ℓ₁ A Γ) (F' : CosDiag ℓ₃ ℓ₁ A Γ)
  : Type (lmax (lmax (lmax ℓv ℓe) (lmax (lsucc ℓ₂) ℓ₁)) (lmax (lmax ℓv ℓe) (lmax ℓ₃ ℓ₁))) where
  field
    nat : ∀ (i : Obj Γ) → < A > F # i *→ F' # i
    comSq : ∀ {i j : Obj Γ} (g : Hom Γ i j) (z : ty (F # i)) → fst (F' <#> g) (fst (nat i) z) == fst (nat j) (fst (F <#> g) z)
    comSq-coher : {i j : Obj Γ} (g : Hom Γ i j) (a : A) →
      comSq g (str (F # i) a)
        ==
      ap (fst (F' <#> g)) (snd (nat i) a) ∙ snd (F' <#> g) a ∙ ! (snd (nat j) a) ∙ ! (ap (fst (nat j)) (snd (F <#> g) a))
open CosDiagMor public

-- coslice cocone
record CosCocone {i j k} (A : Type j) {Γ : Graph ℓv ℓe} (F : CosDiag i j A Γ) (C : Coslice k j A)
  : Type (lmax k (lmax (lmax ℓv ℓe) (lmax i j))) where
  constructor _&_
  field
    comp : (x : Obj Γ) → < A > (F # x) *→ C
    comTri : ∀ {y x : Obj Γ} (f : Hom Γ x y) → [ A , F # x ] (< A > comp y ∘ F <#> f) ∼ comp x
open CosCocone public

module _ {ℓ₁ ℓ₂} {A : Type ℓ₂} {Γ : Graph ℓv ℓe} {F : CosDiag ℓ₁ ℓ₂ A Γ} where

  open MapsCos A

  -- forgetful map
  CocForg : ∀ {k} {C : Coslice k ℓ₂ A} → CosCocone A F C → Cocone (DiagForg A Γ F) (ty C)
  comp (CocForg (K & _)) i = fst (K i)
  comTri (CocForg (_ & r)) {y = j} {x = i} g = fst (r g)

  -- canonical post-composition function on cocones
  PostComp-cos : ∀ {k k'} {C : Coslice k ℓ₂ A} {D : Coslice k' ℓ₂ A} → CosCocone A F C → (C *→ D) → CosCocone A F D
  comp (PostComp-cos K (f , fₚ)) i = f ∘ (fst (comp K i)) , λ a → ap f (snd (comp K i) a) ∙ fₚ a 
  comTri (PostComp-cos K (f , fₚ)) {y = j} {x = i} g =
    (λ x → ap f (fst (comTri K g) x)) , λ a →
      !-ap-ap-∘-ap-∙ f (fst (comp K j)) (snd (F <#> g) a) (fst (comTri K g) (str (F # i) a)) ∙
      ap (λ p → p ∙ fₚ a) (ap (ap f) (snd (comTri K g) a))

  -- another form of post-comp on cocones
  RWhisk-coscoc : ∀ {k k'} {C : Coslice k ℓ₂ A} {D : Coslice k' ℓ₂ A} → CosCocone A F C → (C *→ D) → CosCocone A F D
  comp (RWhisk-coscoc K f) i = f ∘* comp K i
  comTri (RWhisk-coscoc K f) {y = j} {x = i} g = *→-assoc f (comp K j) (F <#> g) ∼∘-cos (post-∘*-∼ f (comTri K g))

  -- small lemma for proof of pullback stability in coslice of Type
  pstcomp-coscoc-mor-ord : ∀ {k₁ k₂} {C₁ : Coslice k₁ ℓ₂ A} {C₂ : Coslice k₂ ℓ₂ A} {K₁ : CosCocone A F C₁} {K₂ : CosCocone A F C₂}
    (f : C₁ *→ C₂) → RWhisk-coscoc K₁ f == K₂ → Cocone-mor-str (CocForg K₁) (CocForg K₂) (fst f)
  comp-∼ (pstcomp-coscoc-mor-ord f idp) _ _ = idp
  comTri-∼ (pstcomp-coscoc-mor-ord f idp) _ _ = idp
