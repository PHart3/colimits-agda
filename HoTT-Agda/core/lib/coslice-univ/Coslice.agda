{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics

{- coslices of the universe -}

module Coslice where

infix 60 *[_,_]
record Coslice (i j : ULevel) (A : Type j) : Type (lmax (lsucc i) j) where
  constructor *[_,_]
  field
    ty : Type i
    str : A → ty
open Coslice public

Cos : ∀ {i j} {A : Type j} (X : Type i) → (A → X) → Coslice i j A
Cos = *[_,_]

infixr 30 <_>_*→_
<_>_*→_ : ∀ {i j k} (A : Type j) → Coslice i j A → Coslice k j A → Type (lmax (lmax i k) j)
< A > *[ X , f ] *→ *[ Y , g ] = Σ (X → Y) (λ h → (a : A) → h (f a) == g a)

infixr 40 <_>_∘_
<_>_∘_ : ∀ {j i k l} (A : Type j) {X : Coslice i j A} {Y : Coslice k j A} {Z : Coslice l j A}
  → < A > Y *→ Z → < A > X *→ Y → < A > X *→ Z
< A > (g , q) ∘ (f , p) = g ∘ f , λ a → ap g (p a) ∙ q a

infixr 30 [_,_]_∼_
[_,_]_∼_ :  ∀ {i j k} (A : Type j) (X : Coslice i j A) {Y : Coslice k j A} →
  < A > X *→ Y → < A > X *→ Y → Type (lmax (lmax i k) j)    
[ A , *[ X , f ] ] ( h₁ , p₁ ) ∼ ( h₂ , p₂ ) =
  Σ (h₁ ∼ h₂) (λ H → (a : A) →  ! (H (f a)) ∙ p₁ a == p₂ a)

module MapsCos {j} (A : Type j) where

  infixr 30 _*→_
  _*→_ : ∀ {i k} → Coslice i j A → Coslice k j A → Type (lmax (lmax i k) j)
  *[ X , f ] *→ *[ Y , g ] = < A > *[ X , f ] *→ *[ Y , g ] 

  infixr 40 _∘*_
  _∘*_ : ∀ {i k l} {X : Coslice i j A} {Y : Coslice k j A} {Z : Coslice l j A}
    → < A > Y *→ Z → < A > X *→ Y → < A > X *→ Z
  g ∘* f = < A > g ∘ f 

  -- homotopy of A-maps
  infixr 30 <_>_∼_
  <_>_∼_ : ∀ {i k} (X : Coslice i j A) {Y : Coslice k j A} →
    X *→ Y →  X *→ Y → Type (lmax (lmax i k) j)    
  < X > h ∼ g = [ A , X ] h ∼ g 

  id-cos : ∀ {i} {X : Coslice i j A} → X *→ X
  id-cos {X = X} = idf (ty X) , (λ _ → idp)

  *→-assoc : ∀ {i k l ℓ} {X : Coslice i j A} {Y : Coslice k j A} {Z : Coslice l j A}
    {W : Coslice ℓ j A} (h₃ : Z *→ W) (h₂ : Y *→ Z) (h₁ : X *→ Y) →
    < X > (h₃ ∘* h₂) ∘* h₁ ∼ h₃ ∘* (h₂ ∘* h₁)
  fst (*→-assoc h₃ h₂ h₁) x = idp
  snd (*→-assoc h₃ h₂ h₁) a =
    ap (λ p → p ∙ ap (fst h₃) (snd h₂ a) ∙ snd h₃ a) (ap-∘ (fst h₃) (fst h₂) (snd h₁ a)) ∙
    ! (ap-ap-∙-∙ (fst h₃) (fst h₂) (snd h₁ a) (snd h₂ a) (snd h₃ a))

  lunit-∘* : ∀ {i k} {X : Coslice i j A} {Y : Coslice k j A} (f : X *→ Y) → < X > f ∼ id-cos ∘* f
  lunit-∘* f = (λ _ → idp) , λ a → ! (∙-unit-r (snd f a)) ∙ ap (λ p → p ∙ idp) (! (ap-idf (snd f a)))

  -- right whiskering
  post-∘*-∼ : ∀ {i k l} {X : Coslice i j A} {Y : Coslice k j A} {Z : Coslice l j A}
    {h₁ h₂ : X *→ Y} (f : Y *→ Z) → < X > h₁ ∼ h₂ → < X > f ∘* h₁ ∼ f ∘* h₂ 
  fst (post-∘*-∼ f H) x = ap (fst f) (fst H x)
  snd (post-∘*-∼ {X = X} {h₁ = h₁} f H) a = 
    ap (λ p → p ∙ ap (fst f) (snd h₁ a) ∙ snd f a) (!-ap (fst f) (fst H (str X a))) ∙ 
    ! (∙-assoc (ap (fst f) (! (fst H (str X a)))) (ap (fst f) (snd h₁ a)) (snd f a)) ∙
    ap (λ p → p ∙ snd f a) (∙-ap (fst f) (! (fst H (str X a))) (snd h₁ a)) ∙
    ap (λ p → ap (fst f) p ∙ snd f a) (snd H a)

  -- left whiskering
  pre-∘*-∼ : ∀ {i k l} {X : Coslice i j A} {Y : Coslice k j A} {Z : Coslice l j A}
    {h₁ h₂ : X *→ Y} (f : Z *→ X) → < X > h₁ ∼ h₂ → < Z > h₁ ∘* f ∼ h₂ ∘* f
  fst (pre-∘*-∼ f H) x = fst H (fst f x)
  snd (pre-∘*-∼ {X = X} {Z = Z} {h₁ = h₁} {h₂} f H) a =
    (! (∙-assoc (! (fst H (fst f (str Z a)))) (ap (fst h₁) (snd f a)) (snd h₁ a)) ∙
    ap (λ p → p ∙ snd h₁ a) (hmtpy-nat-!-sq (fst H) (snd f a)) ∙
    ∙-assoc (ap (fst h₂) (snd f a)) (! (fst H (str X a))) (snd h₁ a)) ∙
    ap (λ p → ap (fst h₂) (snd f a) ∙ p) (snd H a)

  -- inversion
  ∼!-cos : ∀ {i k} {X : Coslice i j A} {Y : Coslice k j A} {h₁ h₂ : X *→ Y}
    → < X > h₁ ∼ h₂ → < X > h₂ ∼ h₁
  fst (∼!-cos H) x = ! (fst H x)
  snd (∼!-cos {X = X} {h₁ = h₁} H) a =
    ap (λ p → ! (! (fst H (str X a))) ∙ p) (! (snd H a)) ∙
    ap (λ p → p ∙ ! (fst H (str X a)) ∙ snd h₁ a) (!-! (fst H (str X a))) ∙
    ! (∙-assoc (fst H (str X a)) (! (fst H (str X a))) (snd h₁ a)) ∙
    ap (λ p → p ∙ snd h₁ a) (!-inv-r (fst H (str X a))) 

  -- composition
  infixr 40 _∼∘-cos_
  _∼∘-cos_ : ∀ {i k} {X : Coslice i j A} {Y : Coslice k j A} {h₁ h₂ h₃ : X *→ Y}
    → < X > h₁ ∼ h₂ → < X > h₂ ∼ h₃ → < X > h₁ ∼ h₃
  _∼∘-cos_ {X = X} {h₁ = h₁} (H₁ , H₂) (K₁ , K₂) =
    (λ x → H₁ x ∙ K₁ x) ,
    (λ a →
      (ap (λ p → p ∙ snd h₁ a) (!-∙ (H₁ (str X a)) (K₁ (str X a))) ∙
      ∙-assoc (! (K₁ (str X a))) (! (H₁ (str X a))) (snd h₁ a)) ∙
      ap (λ p → ! (K₁ (str X a)) ∙ p) (H₂ a) ∙ K₂ a)

  -- identity homotopy
  cos∼id : ∀ {i k} {X : Coslice i j A} {Y : Coslice k j A} (h : X *→ Y) → < X > h ∼ h
  fst (cos∼id h) _ = idp
  snd (cos∼id h) _ = idp

  -- homotopy of homotopies of A-maps
  infixr 30 <_>_∼∼_
  <_>_∼∼_ : ∀ {i k} (X : Coslice i j A) {Y : Coslice k j A} {h₁ h₂ : X *→ Y} →
    < X > h₁ ∼ h₂ → < X > h₁ ∼ h₂ → Type (lmax k (lmax i j))
  <_>_∼∼_ X {h₁ = h₁} H₁ H₂ =
    Σ (fst H₁ ∼ fst H₂) (λ K →
      (a : A) → ap (λ p → ! p ∙ snd h₁ a) (! (K (str X a))) ∙ snd H₁ a == snd H₂ a)
