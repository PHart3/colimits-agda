{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Graph
open import lib.types.Colim
open import lib.types.Diagram
open import lib.types.Pushout
open import lib.types.Span
open import lib.wild-cats.WildCats
open import lib.wild-cats.Diag-ty-OFS
open import lib.wild-cats.Adj-OFS-wc
import homotopy.ColimAdjointConst
open import homotopy.ColimAdjoint-hex

-- the wild colimit functor on Type preserves the left class of an OFS

module homotopy.Colim-OFSLeftClass where

module _ {ℓ k₁ k₂ : ULevel} (fs : ofs-wc k₁ k₂ (Type-wc ℓ)) where

  module _  {ℓv ℓe} {Γ : Graph ℓv ℓe} where

    open homotopy.ColimAdjointConst {ℓ} Γ

    abstract
      ColimMap-lc-OFS : {a b : Diagram Γ (Type-wc ℓ)} {f : Map-diag-ty a b} →
        fst (Diag-ty-lw-lclass fs f) → fst (lclass fs (ColMap (diagmor-from-wc f)))
      ColimMap-lc-OFS fl = OFS-Rprv-Lpsv ColimConst-ty-Adj ColimConst-ty-adj-hex
        is-univ-Diag-ty-wc triangle-wc-Dty pentagon-wc-Dty
        Type-wc-is-univ triangle-wc-ty pentagon-wc-ty
        (Diag-ty-lwOFS fs) fs
        (λ {_} {_} {m} mr → λ _ → mr) fl

  -- deducing the version for pushout maps:

  open import lib.types.PO-Colim-conv

  module _ {σ₁ σ₂ : Span {ℓ} {ℓ} {ℓ}} (sm : SpanMap-Rev σ₁ σ₂) where

    private
      module PM = PushoutMap sm

    abstract
      PushoutMap-lc-OFS :
        fst (lclass fs (SpanMap-Rev.hA sm)) →
        fst (lclass fs (SpanMap-Rev.hB sm)) →
        fst (lclass fs (SpanMap-Rev.hC sm)) →
        fst (lclass fs (PM.f))
      PushoutMap-lc-OFS hAl hBl hCl = transport (λ m → fst (lclass fs m)) (! (Colim-PO-ty-≃-nat-== sm))
        (∘-lc fs (ofcs-wc-eqv-lc {fs = fs} Type-wc-is-univ (_ , (eqv-to-biinv-wc-ty (snd ((Colim-PO-ty-≃  σ₁)⁻¹)))))
        (∘-lc fs (ColimMap-lc-OFS (λ { lft → hAl ; rght → hBl ; mid → hCl }))
        (ofcs-wc-eqv-lc {fs = fs} Type-wc-is-univ (_ , (eqv-to-biinv-wc-ty (snd (Colim-PO-ty-≃  σ₂)))))))

