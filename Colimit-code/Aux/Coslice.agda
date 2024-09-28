{-# OPTIONS --without-K --rewriting #-}

{- Coslice categories of the universe -}

open import lib.Basics
open import lib.types.Sigma

module Coslice where

infix 60 *[_,_]

record Coslice (i j : ULevel) (A : Type j) : Type (lmax (lsucc i) j) where
  constructor *[_,_]
  field
    ty : Type i
    fun : A → ty
open Coslice public

Cos : ∀ {i j} {A : Type j} (X : Type i) →  (A → X) →  Coslice i j A
Cos = *[_,_]

infixr 30 <_>_*→_
<_>_*→_ : ∀ {i j k} (A : Type j) → Coslice i j A → Coslice k j A → Type (lmax (lmax i k) j)
< A > *[ X , f ] *→ *[ Y , g ] = Σ (X → Y) (λ h → ((a : A) → h (f a) == g a))

infixr 40 <_>_∘_
<_>_∘_ : ∀ {j i k l} (A : Type j) {X : Coslice i j A} {Y : Coslice k j A} {Z : Coslice l j A} →
  < A > Y *→ Z → < A > X *→ Y → < A > X *→ Z
< A > (g , q) ∘ (f , p) = (g ∘ f , λ a → ap g (p a) ∙ q a) 

infixr 30 [_,_]_∼_
[_,_]_∼_ :  ∀ {i j k} (A : Type j) (X : Coslice i j A) {Y : Coslice k j A} →
  < A >  X *→ Y  →  < A >  X *→ Y →  Type (lmax (lmax i k) j)    
[ A , *[ X , f ] ] ( h₁ , p₁ )∼( h₂ , p₂ ) = Σ ((x : X) → h₁ x == h₂ x)
  (λ H → ((a : A) →  (! (H (f a)) ∙ (p₁ a) == p₂ a) ))

module MapsCos {j : ULevel} (A : Type j) where

  infixr 30 _*→_
  _*→_ : ∀ {i k} → Coslice i j A → Coslice k j A → Type (lmax (lmax i k) j)
  *[ X , f ] *→ *[ Y , g ] = < A > *[ X , f ] *→ *[ Y , g ] 

  infixr 40 _∘*_
  _∘*_ : ∀ {i k l} {X : Coslice i j A} {Y : Coslice k j A} {Z : Coslice l j A} →
    < A > Y *→ Z → < A > X *→ Y → < A > X *→ Z
  g ∘* f = < A > g ∘ f 

  infixr 30 <_>_∼_
  <_>_∼_ : ∀ {i k} (X : Coslice i j A) {Y : Coslice k j A} →
    < A >  X *→ Y  →  < A >  X *→ Y →  Type (lmax (lmax i k) j)    
  < X > h ∼ g = [ A , X ] h ∼ g 
