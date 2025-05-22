{-# OPTIONS --without-K --rewriting #-}

open import lib.Base

module lib.types.Graph where

-- Our notion of graph is a quiver.
record Graph (ℓv ℓe : ULevel) : Type (lsucc (lmax ℓv ℓe)) where
  field
    Obj : Type ℓv
    Hom : Obj → Obj → Type ℓe
open Graph public

Graph-op : ∀ {ℓv ℓe} → Graph ℓv ℓe → Graph ℓv ℓe
Obj (Graph-op G) = Obj G
Hom (Graph-op G) j i  = Hom G i j

TypeGr : ∀ i → Graph (lsucc i) i
Obj (TypeGr i) = Type i
Hom (TypeGr i) A B = A → B

-- graph homomorphisms
record GraphHom {ℓv ℓe ℓv' ℓe'} (G : Graph ℓv ℓe) (G' : Graph ℓv' ℓe') : Type (lmax (lmax ℓv ℓe) (lmax ℓv' ℓe')) where
  field
    _#_ : Obj G → Obj G'
    _<#>_ : ∀ {x y : Obj G} → Hom G x y → Hom G' (_#_ x) (_#_ y)
  infix 90 _<#>_
  infix 91 _#_
open GraphHom public
