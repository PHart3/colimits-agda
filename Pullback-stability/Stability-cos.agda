{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Cospan
open import lib.types.Pullback
open import lib.types.Colim
open import lib.types.Graph
open import lib.types.Diagram
open import lib.wild-cats.WildCats
open import SIP-Cos
open import Cos-wc
open import Stability-ord
open import Lim-pres
open import CosColim-Iso
open import Diagram-Cos
open import Cocone-po
open import Tree-create

-- pullback stability for coslice colimits

module Stability-cos where

module _ {ℓ} {A : Type ℓ}  where

  open MapsCos A

  StPb-forg-iso : ∀ {ℓd} {Δ : Diag-cspan (Coslice-wc A (lmax ℓd ℓ))}
    {X : Coslice (lmax ℓd ℓ) ℓ A} {K : Cone-wc Δ X} (pb : is-pb-wc K) →
    Cone-csp-iso (diag-to-csp (F-diag (Forg-funct-cos A {ℓd}) Δ))
      (Pb-con (diag-to-csp (F-diag (Forg-funct-cos A {ℓd}) Δ)))
      (con-to-csp (F-diag (Forg-funct-cos A {i = ℓd}) Δ)
        (cone (λ v z → fst (Cone-wc.leg K v) z) (λ f → ap fst (Cone-wc.tri K f))))
  StPb-forg-iso {ℓd} pb = StdPb-Lim-≃ (Forg-cos-lim-pres A {ℓd} pb)

  module _ {ℓv ℓe ℓd} {Γ : Graph ℓv ℓe} {Δ-wc : Diagram Γ (Coslice-wc A (lmax ℓd ℓ))}
    {Y Z : Coslice (lmax ℓd ℓ) ℓ A} (f : po-CosCol (Diag-to-grhom Δ-wc) *→ Z) (h : Y *→ Z) where

    private
      Δ = Diag-to-grhom (Δ-wc)

    open Id.Maps Γ A

    pb-comp-cos : (i : Obj Γ) → Diag-cspan (Coslice-wc A (lmax ℓd ℓ))
    D₀ (pb-comp-cos i) lft = Δ # i
    D₀ (pb-comp-cos i) mid = Z
    D₀ (pb-comp-cos i) rght = Y
    D₁ (pb-comp-cos i) {lft} {mid} g = f ∘* comp (ColCoC-cos Δ) i
    D₁ (pb-comp-cos i) {rght} {mid} g = h
    D₁ (pb-comp-cos i) {lft} {rght} ()
    D₁ (pb-comp-cos i) {lft} {lft} ()

    pb-csp-cos : Diag-cspan (Coslice-wc A (lmax ℓd ℓ))
    D₀ pb-csp-cos lft = po-CosCol Δ
    D₀ pb-csp-cos mid = Z
    D₀ pb-csp-cos rght = Y
    D₁ pb-csp-cos {lft} {mid} g = f
    D₁ pb-csp-cos {rght} {mid} g = h
    D₁ pb-csp-cos {lft} {rght} ()
    D₁ pb-csp-cos {lft} {lft} ()

    {-
      We just assume the existence of the relevant pullbacks in the
      coslice universe. It is possible, however, to explicitly construct
      all pullbacks. See Note 6.0.4 of the technical report for the
      details of such a construction.
    -}
    
    module _
      (T : (i : Obj Γ) → Σ (Coslice (lmax ℓ ℓd) ℓ A) (λ T₀ → Cone-wc (pb-comp-cos i) T₀))
      (pb-comp : (i : Obj Γ) → is-pb-wc (snd (T i))) 
      (τ : Coslice (lmax ℓ ℓd) ℓ A) (PbStb-cos-con : Cone-wc pb-csp-cos τ)
      (pb : is-pb-wc PbStb-cos-con) where

      open Cone-wc

      private
        assoc = α (Coslice-wc A (lmax ℓ ℓd))

      map-to-pb-con : ∀ {x y} (g : Hom Γ x y) → Cone-wc (pb-comp-cos y) (fst (T x))
      leg (map-to-pb-con {x} g) lft = Δ <#> g ∘* leg (snd (T x)) lft
      leg (map-to-pb-con {x} g) mid = leg (snd (T x)) mid
      leg (map-to-pb-con {x} g) rght = leg (snd (T x)) rght
      tri (map-to-pb-con {x} {y} g) {lft} {mid} unit = 
        ! (assoc (f ∘* comp (ColCoC-cos Δ) y) (Δ <#> g) (leg (snd (T x)) lft)) ∙
        ap (λ m → m ∘* leg (snd (T x)) lft) (assoc f (comp (ColCoC-cos Δ) y) (Δ <#> g)) ∙
        ap (λ m → (f ∘* m) ∘* leg (snd (T x)) lft) (UndFun∼-to-== (comTri (ColCoC-cos Δ) g)) ∙
        tri (snd (T x)) {y = mid} unit
      tri (map-to-pb-con {x} {y} g) {rght} {mid} unit = tri (snd (T x)) {y = mid} unit
      tri (map-to-pb-con {x} {y} g) {mid} {lft} ()
      
      diag-pbs-cos : CosDiag (lmax ℓ ℓd) ℓ A Γ
      diag-pbs-cos # x = fst (T x)
      _<#>_ diag-pbs-cos {y = y} g = gap-map-wc (snd (T y)) (pb-comp y) (map-to-pb-con g)

      canmap-cos-pbs-comp : (i : Obj Γ) → Cone-wc pb-csp-cos (fst (T i))
      leg (canmap-cos-pbs-comp i) lft = comp (ColCoC-cos Δ) i ∘* leg (snd (T i)) lft
      leg (canmap-cos-pbs-comp i) mid = f ∘* comp (ColCoC-cos Δ) i ∘* leg (snd (T i)) lft
      leg (canmap-cos-pbs-comp i) rght = leg (snd (T i)) rght 
      tri (canmap-cos-pbs-comp i) {lft} {mid} unit = idp
      tri (canmap-cos-pbs-comp i) {rght} {mid} unit =
        tri (snd (T i)) {x = rght} {y = mid} unit ∙
        ! (tri (snd (T i)) {x = lft} {y = mid} unit) ∙
        assoc f (comp (ColCoC-cos Δ) i) (leg (snd (T i)) lft)
      tri (canmap-cos-pbs-comp i) {mid} {lft} ()

      canmap-cos-pbs-coc : CosCocone A diag-pbs-cos τ
      comp canmap-cos-pbs-coc i = gap-map-wc PbStb-cos-con pb (canmap-cos-pbs-comp i)
      comTri canmap-cos-pbs-coc {j} {i} g = UndFun∼-from-== (lim-wc-homeq _ pb pbs-coc-leg pbs-coc-tri)
        where
        
          pbs-coc-leg : (t : Triple) →
            leg PbStb-cos-con t ∘*
            gap-map-wc PbStb-cos-con pb (canmap-cos-pbs-comp j) ∘* gap-map-wc (snd (T j)) (pb-comp j) (map-to-pb-con g) 
              ==
            leg PbStb-cos-con t ∘* gap-map-wc PbStb-cos-con pb (canmap-cos-pbs-comp i)
          pbs-coc-leg t = 
            ! (assoc
                (leg PbStb-cos-con t)
                (gap-map-wc PbStb-cos-con pb (canmap-cos-pbs-comp j))
                (gap-map-wc (snd (T j)) (pb-comp j) (map-to-pb-con g))) ∙
            ap (λ m → m ∘* gap-map-wc (snd (T j)) (pb-comp j) (map-to-pb-con g)) (gap-map-ind-leg PbStb-cos-con pb t) ∙
            pbs-coc-leg-aux t ∙
            ! (gap-map-ind-leg PbStb-cos-con pb t)
              where
                pbs-coc-leg-aux : (t' : Triple) →
                  leg (canmap-cos-pbs-comp j) t' ∘* gap-map-wc (snd (T j)) (pb-comp j) (map-to-pb-con g)
                    ==
                  leg (canmap-cos-pbs-comp i) t'
                pbs-coc-leg-aux lft = 
                  assoc (comp (ColCoC-cos Δ) j) (leg (snd (T j)) lft) (gap-map-wc (snd (T j)) (pb-comp j) (map-to-pb-con g)) ∙
                  ap (λ m → comp (ColCoC-cos Δ) j ∘* m) (gap-map-ind-leg (snd (T j)) (pb-comp j) lft) ∙
                  ! (assoc (comp (ColCoC-cos Δ) j) (Δ <#> g) (leg (snd (T i)) lft)) ∙
                  ap (λ m → m ∘* leg (snd (T i)) lft) (UndFun∼-to-== (comTri (ColCoC-cos Δ) g))
                pbs-coc-leg-aux mid = 
                  assoc f (comp (ColCoC-cos Δ) j ∘* leg (snd (T j)) lft) (gap-map-wc (snd (T j)) (pb-comp j) (map-to-pb-con g)) ∙
                  ap (λ m → f ∘* m)
                    (assoc (comp (ColCoC-cos Δ) j) (leg (snd (T j)) lft) (gap-map-wc (snd (T j)) (pb-comp j) (map-to-pb-con g))) ∙
                  ap (λ m → f ∘* comp (ColCoC-cos Δ) j ∘* m) (gap-map-ind-leg (snd (T j)) (pb-comp j) lft) ∙
                  ap (λ m → f ∘* m) (! (assoc (comp (ColCoC-cos Δ) j) (Δ <#> g) (leg (snd (T i)) lft))) ∙
                  ap (λ m → f ∘* m ∘* leg (snd (T i)) lft) (UndFun∼-to-== (comTri (ColCoC-cos Δ) g))
                pbs-coc-leg-aux rght = gap-map-ind-leg (snd (T j)) (pb-comp j) rght
          
          pbs-coc-tri :
            {x y : Triple} (γ : Hom Graph-cspan x y) →
              (! (assoc (D₁ pb-csp-cos γ) (leg PbStb-cos-con x)
                   (gap-map-wc PbStb-cos-con pb (canmap-cos-pbs-comp j) ∘* gap-map-wc (snd (T j)) (pb-comp j) (map-to-pb-con g))) ∙
              ap (λ m → m ∘*
                  gap-map-wc PbStb-cos-con pb (canmap-cos-pbs-comp j) ∘* gap-map-wc (snd (T j)) (pb-comp j) (map-to-pb-con g))
                (tri PbStb-cos-con γ)) ∙'
              pbs-coc-leg y
                ==
              ap (λ m → D₁ pb-csp-cos γ ∘* m) (pbs-coc-leg x) ∙
              ! (assoc (D₁ pb-csp-cos γ) (leg PbStb-cos-con x) (gap-map-wc PbStb-cos-con pb (canmap-cos-pbs-comp i))) ∙
              ap (λ m →  m ∘* gap-map-wc PbStb-cos-con pb (canmap-cos-pbs-comp i))
                (tri PbStb-cos-con γ)
          pbs-coc-tri {lft} {lft} ()
          pbs-coc-tri {lft} {mid} unit = {!!}
          pbs-coc-tri {lft} {rght} ()
          pbs-coc-tri {mid} {lft} ()
          pbs-coc-tri {mid} {mid} ()
          pbs-coc-tri {mid} {rght} ()
          pbs-coc-tri {rght} {lft} ()
          pbs-coc-tri {rght} {mid} unit = {!!}
          pbs-coc-tri {rght} {rght} ()

      canmap-cos-pbs : po-CosCol diag-pbs-cos *→ τ
      canmap-cos-pbs = cogap-cos canmap-cos-pbs-coc

-- can-map-equiv (F-diag (Forg-funct-cos A {ℓd}) Δ) (fst h) (fst f)

{-

(!
 (assoc f (leg PbStb-cos-con lft)
  (gap-map-wc PbStb-cos-con pb (canmap-cos-pbs-comp j) ∘*
   gap-map-wc (snd (T j)) (pb-comp j) (map-to-pb-con g)))
 ∙
 ap
 (λ m →
    m ∘*
    gap-map-wc PbStb-cos-con pb (canmap-cos-pbs-comp j) ∘*
    gap-map-wc (snd (T j)) (pb-comp j) (map-to-pb-con g))
 (tri PbStb-cos-con unit))
∙' pbs-coc-leg mid
==
ap (_∘*_ f) (pbs-coc-leg lft) ∙
!
(assoc f (leg PbStb-cos-con lft)
 (gap-map-wc PbStb-cos-con pb (canmap-cos-pbs-comp i)))
∙
ap (λ m → m ∘* gap-map-wc PbStb-cos-con pb (canmap-cos-pbs-comp i))
(tri PbStb-cos-con unit)

-}
