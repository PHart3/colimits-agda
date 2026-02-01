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

-- the discrete graph over a type
discrete-graph : ∀ {ℓv} → Type ℓv → Graph ℓv lzero
Obj (discrete-graph G₀) = G₀
Hom (discrete-graph G₀) _ _ = Empty

TypeGr : ∀ i → Graph (lsucc i) i
Obj (TypeGr i) = Type i
Hom (TypeGr i) A B = A → B

-- graph homomorphisms
record GraphHom {ℓv ℓe ℓv' ℓe'} (G : Graph ℓv ℓe) (G' : Graph ℓv' ℓe') : Type (lmax (lmax ℓv ℓe) (lmax ℓv' ℓe')) where
  field
    _#_ : Obj G → Obj G'
    _<#>_ : ∀ {x y : Obj G} → Hom G x y → Hom G' (_#_ x) (_#_ y)
  infix 90 _<#>_
  infix 90 _#_
open GraphHom public

-- graphs underlying span and cospan

data Triple : Type₀ where
  lft mid rght : Triple

Graph-span : Graph lzero lzero 
Obj Graph-span = Triple
Hom Graph-span lft lft = Empty
Hom Graph-span lft mid = Empty
Hom Graph-span lft rght = Empty
Hom Graph-span mid lft = Unit
Hom Graph-span mid mid = Empty
Hom Graph-span mid rght = Unit
Hom Graph-span rght lft = Empty
Hom Graph-span rght mid = Empty
Hom Graph-span rght rght = Empty

Graph-cspan : Graph lzero lzero 
Obj Graph-cspan = Triple
Hom Graph-cspan lft lft = Empty
Hom Graph-cspan lft mid = Unit
Hom Graph-cspan lft rght = Empty
Hom Graph-cspan mid lft = Empty
Hom Graph-cspan mid mid = Empty
Hom Graph-cspan mid rght = Empty
Hom Graph-cspan rght lft = Empty
Hom Graph-cspan rght mid = Unit
Hom Graph-cspan rght rght = Empty
