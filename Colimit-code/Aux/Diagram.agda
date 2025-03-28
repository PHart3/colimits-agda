{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import Coslice

module Diagram where 

-- The type of directed multigraphs (with loops)

private variable ℓv ℓv' ℓv'' ℓe ℓe' ℓe'' ℓd ℓd' : ULevel 

record Graph ℓv ℓe : Type (lsucc (lmax ℓv ℓe)) where
  field
    Obj : Type ℓv
    Hom : Obj → Obj → Type ℓe

open Graph public

TypeGr : ∀ i → Graph (lsucc i) i
Obj (TypeGr i) = Type i
Hom (TypeGr i) A B = A → B

CosGr : ∀ i j (A : Type j) → Graph (lmax (lsucc i) j) (lmax i j)
Obj (CosGr i j A) = Coslice i j A
Hom (CosGr i j A) X Y = < A > X *→ Y

-- Graph homomorphisms

record GraphHom (G  : Graph ℓv  ℓe) (G' : Graph ℓv' ℓe') : Type (lmax (lmax ℓv ℓe) (lmax ℓv' ℓe')) where
  field
    _#_ : Obj G → Obj G'
    _<#>_ : ∀ {x y : Obj G} → Hom G x y → Hom G' (_#_ x) (_#_ y)
  infix 90 _<#>_
  infix 91 _#_

open GraphHom public

-- Diagrams are graph homomorphisms with codomain Type

Diag : ∀ ℓd (G : Graph ℓv ℓe) → Type (lmax (lmax ℓv ℓe) (lsucc ℓd))
Diag ℓd G = GraphHom G (TypeGr ℓd)

ConsDiag : ∀ {ℓd} (G : Graph ℓv ℓe) (A : Type ℓd) → Diag ℓd G
(ConsDiag G A) # _ = A
(ConsDiag G A) <#> _ = idf A

CosDiag : ∀ i j (A : Type j) (G : Graph ℓv ℓe) → Type (lmax (lmax ℓv ℓe) (lmax (lsucc i) j))
CosDiag i j A G = GraphHom G (CosGr i j A)

-- Forgetful functor

DiagForg : ∀ {i j} (A : Type j) (G : Graph ℓv ℓe) → CosDiag i j A G → Diag i G
(DiagForg A G D) # x = ty (D # x)
(DiagForg A G D) <#> f = fst (D <#> f) 

-- Maps of diagrams

record DiagMor {G : Graph ℓv ℓe} (F : Diag ℓd G) (F' : Diag ℓd' G)
  : Type (lmax (lmax ℓv ℓe) (lmax ℓd ℓd')) where
  constructor Δ
  field
    nat : ∀ (x : Obj G) → F # x → F' # x
    comSq : ∀ {x y : Obj G} (f : Hom G x y) (z : F # x) → (F' <#> f) (nat x z) == nat y ((F <#> f) z)

open DiagMor public

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

-- Cocones under diagrams

record Cocone {i k} {G : Graph ℓv ℓe} (F : Diag i G) (C : Type k)
  : Type (lmax k (lmax (lmax ℓv ℓe) i)) where
  constructor _&_
  field
    comp : (x : Obj G) → F # x → C
    comTri : ∀ {y x : Obj G} (f : Hom G x y) → comp y ∘ F <#> f ∼ comp x

open Cocone public

record CosCocone {i j k} (A : Type j) {G : Graph ℓv ℓe} (F : CosDiag i j A G) (C : Coslice k j A)
  : Type (lmax k (lmax (lmax ℓv ℓe) (lmax i j))) where
  constructor _&_
  field
    comp : (x : Obj G) → < A > (F # x) *→ C
    comTri : ∀ {y x : Obj G} (f : Hom G x y) → [ A , F # x ] (< A > comp y ∘ F <#> f) ∼ comp x
 
open CosCocone public

-- Some operations on coslice cocones

module _ {ℓi ℓj k} {A : Type ℓj} {Γ : Graph ℓv ℓe} {F : CosDiag ℓi ℓj A Γ} {C : Coslice k ℓj A} where

  ForgCoc : (CosCocone A F C) → Cocone (DiagForg A Γ F) (ty C)
  comp (ForgCoc (K & _)) i = fst (K i)
  comTri (ForgCoc (_ & r)) {y = j} {x = i} g = fst (r g)

  PostComp : ∀ {k'} {D : Coslice k' ℓj A} → CosCocone A F C → (< A > C *→ D) → CosCocone A F D
  comp (PostComp K (f , fₚ)) i = f ∘ (fst (comp K i)) , λ a → ap f (snd (comp K i) a) ∙ fₚ a 
  comTri (PostComp K (f , fₚ)) {y = j} {x = i} g =
    (λ x → ap f (fst (comTri K g) x)) ,
    λ a →
      ap-cp-revR f (fst (comp K j)) (snd (F <#> g) a) (fst (comTri K g) (fun (F # i) a)) ∙
      ap (λ p → p ∙ fₚ a) (ap (ap f) (snd (comTri K g) a))
