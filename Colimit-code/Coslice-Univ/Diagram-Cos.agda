{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import Coslice

module Diagram-Cos where 

open import lib.types.Graph public
open import lib.types.Diagram public

private variable ℓv ℓv' ℓv'' ℓe ℓe' ℓe'' ℓd ℓd' : ULevel 

ConsDiag : ∀ {ℓd} (G : Graph ℓv ℓe) (A : Type ℓd) → Diag ℓd G
(ConsDiag G A) # _ = A
(ConsDiag G A) <#> _ = idf A

-- coslice-valued diagram

CosGr : ∀ i j (A : Type j) → Graph (lmax (lsucc i) j) (lmax i j)
Obj (CosGr i j A) = Coslice i j A
Hom (CosGr i j A) X Y = < A > X *→ Y

CosDiag : ∀ i j (A : Type j) (G : Graph ℓv ℓe) → Type (lmax (lmax (lmax ℓv ℓe) (lsucc i)) j)
CosDiag i j A G = GraphHom G (CosGr i j A)

-- forgetful functor
DiagForg : ∀ {i j} (A : Type j) (G : Graph ℓv ℓe) → CosDiag i j A G → Diag i G
(DiagForg A G D) # x = ty (D # x)
(DiagForg A G D) <#> f = fst (D <#> f) 

record CosDiagMor {G : Graph ℓv ℓe} {ℓ₁ ℓ₂ ℓ₃} (A : Type ℓ₁) (F : CosDiag ℓ₂ ℓ₁ A G) (F' : CosDiag ℓ₃ ℓ₁ A G)
  : Type (lmax (lmax (lmax ℓv ℓe) (lmax (lsucc ℓ₂) ℓ₁)) (lmax (lmax ℓv ℓe) (lmax ℓ₃ ℓ₁))) where
  field
    nat : ∀ (i : Obj G) → < A > F # i *→ F' # i
    comSq : ∀ {i j : Obj G} (g : Hom G i j) (z : ty (F # i)) → fst (F' <#> g) (fst (nat i) z) == fst (nat j) (fst (F <#> g) z)
    comSq-coher : {i j : Obj G} (g : Hom G i j) (a : A) →
      comSq g (fun (F # i) a)
        ==
      ap (fst (F' <#> g)) (snd (nat i) a) ∙ snd (F' <#> g) a ∙ ! (snd (nat j) a) ∙ ! (ap (fst (nat j)) (snd (F <#> g) a))
open CosDiagMor public

-- coslice cocone
record CosCocone {i j k} (A : Type j) {G : Graph ℓv ℓe} (F : CosDiag i j A G) (C : Coslice k j A)
  : Type (lmax k (lmax (lmax ℓv ℓe) (lmax i j))) where
  constructor _&_
  field
    comp : (x : Obj G) → < A > (F # x) *→ C
    comTri : ∀ {y x : Obj G} (f : Hom G x y) → [ A , F # x ] (< A > comp y ∘ F <#> f) ∼ comp x
open CosCocone public

module _ {ℓ₁ ℓ₂ k} {A : Type ℓ₂} {Γ : Graph ℓv ℓe} {F : CosDiag ℓ₁ ℓ₂ A Γ} {C : Coslice k ℓ₂ A} where

  -- forgetful map
  CocForg : CosCocone A F C → Cocone (DiagForg A Γ F) (ty C)
  comp (CocForg (K & _)) i = fst (K i)
  comTri (CocForg (_ & r)) {y = j} {x = i} g = fst (r g)

  -- canonical post-composition function on cocones
  PostComp-cos : ∀ {k'} {D : Coslice k' ℓ₂ A} → CosCocone A F C → (< A > C *→ D) → CosCocone A F D
  comp (PostComp-cos K (f , fₚ)) i = f ∘ (fst (comp K i)) , λ a → ap f (snd (comp K i) a) ∙ fₚ a 
  comTri (PostComp-cos K (f , fₚ)) {y = j} {x = i} g =
    (λ x → ap f (fst (comTri K g) x)) , λ a →
      !-ap-ap-∘-ap-∙ f (fst (comp K j)) (snd (F <#> g) a) (fst (comTri K g) (fun (F # i) a)) ∙
      ap (λ p → p ∙ fₚ a) (ap (ap f) (snd (comTri K g) a))
