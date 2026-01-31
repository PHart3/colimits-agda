{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.types.Paths
open import lib.types.Sigma hiding (diag)
open import lib.wild-cats.WildCat
open import lib.wild-cats.Adjoint
open import lib.wild-cats.Filler-wc

{- A left adjoint between univalent wild bicategories preserves the left class of an OFS
   as soon as its right adjoint preserves the right class, under a reasonable hexagon
   coherence condition on the adjunction. -}

module lib.wild-cats.Adj-OFS-wc where

open import lib.wild-cats.Adj-hexagon public  -- statement of the hexagon identity for a wild adjunction

module _ {i₁ i₂ j₁ j₂} {C : WildCat {i₁} {j₁}} {D : WildCat {i₂} {j₂}} {L : Functor-wc C D} {R : Functor-wc D C} (adj : Adjunction L R)
  (hex : adj-wc-hexagon adj) where  -- assumption of hexagon coherence condition

  module _ {a b : ob C} {x y : ob D} {f : hom C a b} {g : hom D x y} (u : hom D (obj L a) x) (v : hom D (obj L b) y)
    (S : ⟦ D ⟧ v ◻ arr L f == ⟦ D ⟧ g ◻ u) where

    private
      ζ : ⟦ C ⟧ –> (iso adj) v ◻ f == ⟦ C ⟧ arr R g ◻ –> (iso adj) u
      ζ = nat-dom adj f v ∙ ap (–> (iso adj)) S ∙ ! (nat-cod adj g u)

    module coh-adjust (diag : hom D (obj L b) x) (tri-top : ⟦ D ⟧ diag ◻ arr L f == u) (tri-bottom : ⟦ D ⟧ g ◻ diag == v) where

      abstract
        ==-fib-≃ :  
          (ap (–> (iso adj)) (α D g diag (arr L f) ∙ ap (λ m → ⟦ D ⟧ g ◻ m) tri-top)
            ==
          ap (–> (iso adj)) (ap (λ m → ⟦ D ⟧ m ◻ arr L f) tri-bottom ∙ S))
            ≃
          (α C (arr R g) (–> (iso adj) diag) f ∙ ap (λ m → ⟦ C ⟧ arr R g ◻ m) (nat-dom adj f diag ∙ ap (–> (iso adj)) tri-top)
            ==
          ap (λ m → ⟦ C ⟧ m ◻ f) (nat-cod adj g diag ∙ ap (–> (iso adj)) tri-bottom) ∙ ζ)
        ==-fib-≃ = 
          (ap (–> (iso adj)) (α D g diag (arr L f) ∙ ap (λ m → ⟦ D ⟧ g ◻ m) tri-top)
            ==
          ap (–> (iso adj)) (ap (λ m → ⟦ D ⟧ m ◻ arr L f) tri-bottom ∙ S))
            ≃⟨ path-eqlends-≃ lemma1 lemma2 ⟩
          (! (nat-dom adj f (⟦ D ⟧ g ◻ diag)) ∙
          ! (ap (λ m → ⟦ C ⟧ m ◻ f) (nat-cod adj g diag)) ∙
          α C (arr R g) (–> (iso adj) diag) f ∙
          ap (λ m → ⟦ C ⟧ arr R g ◻ m) (nat-dom adj f diag ∙ ap (–> (iso adj)) tri-top) ∙
          nat-cod adj g u
            ==
          ! (nat-dom adj f (⟦ D ⟧ g ◻ diag)) ∙
          ap (λ m → ⟦ C ⟧ –> (iso adj) m ◻ f) tri-bottom ∙
          nat-dom adj f v ∙
          ap (–> (iso adj)) S)
            ≃⟨ lemma3 (! (nat-dom adj f (⟦ D ⟧ g ◻ diag))) (nat-cod adj g u) (nat-cod adj g diag) ⟩
          (α C (arr R g) (–> (iso adj) diag) f ∙ ap (λ m → ⟦ C ⟧ arr R g ◻ m) (nat-dom adj f diag ∙ ap (–> (iso adj)) tri-top)
            ==
          ap (λ m → ⟦ C ⟧ m ◻ f) (nat-cod adj g diag ∙ ap (–> (iso adj)) tri-bottom) ∙ ζ) ≃∎
          where abstract

            lemma1 :
              ap (–> (iso adj)) (α D g diag (arr L f) ∙ ap (λ m → ⟦ D ⟧ g ◻ m) tri-top)
                ==
              ! (nat-dom adj f (⟦ D ⟧ g ◻ diag)) ∙
              ! (ap (λ m → ⟦ C ⟧ m ◻ f) (nat-cod adj g diag)) ∙
              α C (arr R g) (–> (iso adj) diag) f ∙
              ap (λ m → ⟦ C ⟧ arr R g ◻ m) (nat-dom adj f diag ∙ ap (–> (iso adj)) tri-top) ∙
              nat-cod adj g u
            lemma1 = =ₛ-out $
              ap (–> (iso adj)) (α D g diag (arr L f) ∙ ap (λ m → ⟦ D ⟧ g ◻ m) tri-top) ◃∎
                =ₛ⟨ ap-∙-∘◃ (–> (iso adj)) (λ m → ⟦ D ⟧ g ◻ m) (α D g diag (arr L f)) tri-top ⟩
              ap (–> (iso adj)) (α D g diag (arr L f)) ◃∙ ap (λ m → –> (iso adj) (⟦ D ⟧ g ◻ m)) tri-top ◃∎
                =ₛ⟨ 1 & 1 & apCommSq◃ (λ m → nat-cod adj g m) tri-top ⟩
              ap (–> (iso adj)) (α D g diag (arr L f)) ◃∙
              ! (nat-cod adj g (⟦ D ⟧ diag ◻ arr L f)) ◃∙
              ap (λ m → ⟦ C ⟧ arr R g ◻ –> (iso adj) m) tri-top ◃∙
              nat-cod adj g u ◃∎
                =ₛ⟨ 0 & 1 & adj-wc-hexagon-rot1 adj hex ⟩
              ! (nat-dom adj f (⟦ D ⟧ g ◻ diag)) ◃∙
              ! (ap (λ m → ⟦ C ⟧ m ◻ f) (nat-cod adj g diag)) ◃∙
              α C (arr R g) (–> (iso adj) diag) f ◃∙
              ap (λ m → ⟦ C ⟧ arr R g ◻ m) (nat-dom adj f diag) ◃∙
              nat-cod adj g (⟦ D ⟧ diag ◻ arr L f) ◃∙
              ! (nat-cod adj g (⟦ D ⟧ diag ◻ arr L f)) ◃∙
              ap (λ m → ⟦ C ⟧ arr R g ◻ –> (iso adj) m) tri-top ◃∙
              nat-cod adj g u ◃∎
                =ₛ⟨ 4 & 2 & !-inv-r◃ (nat-cod adj g (⟦ D ⟧ diag ◻ arr L f)) ⟩
              ! (nat-dom adj f (⟦ D ⟧ g ◻ diag)) ◃∙
              ! (ap (λ m → ⟦ C ⟧ m ◻ f) (nat-cod adj g diag)) ◃∙
              α C (arr R g) (–> (iso adj) diag) f ◃∙
              ap (λ m → ⟦ C ⟧ arr R g ◻ m) (nat-dom adj f diag) ◃∙
              ap (λ m → ⟦ C ⟧ arr R g ◻ –> (iso adj) m) tri-top ◃∙
              nat-cod adj g u ◃∎
                =ₛ₁⟨ 4 & 1 & ap-∘ (λ m → ⟦ C ⟧ arr R g ◻ m) (–> (iso adj)) tri-top ⟩
              ! (nat-dom adj f (⟦ D ⟧ g ◻ diag)) ◃∙
              ! (ap (λ m → ⟦ C ⟧ m ◻ f) (nat-cod adj g diag)) ◃∙
              α C (arr R g) (–> (iso adj) diag) f ◃∙
              ap (λ m → ⟦ C ⟧ arr R g ◻ m) (nat-dom adj f diag) ◃∙
              ap (λ m → ⟦ C ⟧ arr R g ◻ m) (ap (–> (iso adj)) tri-top) ◃∙
              nat-cod adj g u ◃∎
                =ₛ⟨ 3 & 2 & !ₛ (ap-seq-∙ (λ m → ⟦ C ⟧ arr R g ◻ m) (nat-dom adj f diag ◃∙ ap (–> (iso adj)) tri-top ◃∎)) ⟩
              ! (nat-dom adj f (⟦ D ⟧ g ◻ diag)) ◃∙
              ! (ap (λ m → ⟦ C ⟧ m ◻ f) (nat-cod adj g diag)) ◃∙
              α C (arr R g) (–> (iso adj) diag) f ◃∙
              ap (λ m → ⟦ C ⟧ arr R g ◻ m) (nat-dom adj f diag ∙ ap (–> (iso adj)) tri-top) ◃∙
              nat-cod adj g u ◃∎ ∎ₛ

            lemma2 :
              ap (–> (iso adj)) (ap (λ m → ⟦ D ⟧ m ◻ arr L f) tri-bottom ∙ S)
                ==
              ! (nat-dom adj f (⟦ D ⟧ g ◻ diag)) ∙
              ap (λ m → ⟦ C ⟧ –> (iso adj) m ◻ f) tri-bottom ∙
              nat-dom adj f v ∙
              ap (–> (iso adj)) S
            lemma2 = =ₛ-out $
              ap (–> (iso adj)) (ap (λ m → ⟦ D ⟧ m ◻ arr L f) tri-bottom ∙ S) ◃∎
                =ₛ⟨ ap-∘-∙◃ (–> (iso adj)) (λ m → ⟦ D ⟧ m ◻ arr L f) tri-bottom S ⟩
              ap (λ m → –> (iso adj) (⟦ D ⟧ m ◻ arr L f)) tri-bottom ◃∙ ap (–> (iso adj)) S ◃∎
                =ₛ⟨ 0 & 1 & apCommSq◃ (λ m → nat-dom adj f m) tri-bottom ⟩
              ! (nat-dom adj f (⟦ D ⟧ g ◻ diag)) ◃∙
              ap (λ m → ⟦ C ⟧ –> (iso adj) m ◻ f) tri-bottom ◃∙
              nat-dom adj f v ◃∙
              ap (–> (iso adj)) S ◃∎ ∎ₛ

            lemma3 : {m₁ m₂ : hom C a (obj R y)} {m₃ : hom C b (obj R y)} {c₁ : _ == _} {c₂ : _ == m₂}
              (p : m₁ == _) (q : _ == m₂) (r : m₃ == _) → 
              (p ∙
              ! (ap (λ m → ⟦ C ⟧ m ◻ f) r) ∙ 
              c₁ ∙
              ap (λ m → ⟦ C ⟧ arr R g ◻ m) (nat-dom adj f diag ∙ ap (–> (iso adj)) tri-top) ∙
              q
                ==
              p ∙
              ap (λ m → ⟦ C ⟧ –> (iso adj) m ◻ f) tri-bottom ∙
              nat-dom adj f v ∙
              c₂)
                ≃
              (c₁ ∙ ap (λ m → ⟦ C ⟧ arr R g ◻ m) (nat-dom adj f diag ∙ ap (–> (iso adj)) tri-top)
                ==
              ap (λ m → ⟦ C ⟧ m ◻ f) (r ∙ ap (–> (iso adj)) tri-bottom) ∙ nat-dom adj f v ∙ c₂ ∙ ! q)
            lemma3 {c₁ = c₁} {C₂} idp idp idp = path-eqlends-≃
              (ap (λ p → c₁ ∙ _ ∙ p) (∙-unit-r (ap (λ m → ⟦ C ⟧ arr R g ◻ m) (nat-dom adj f diag ∙ ap (–> (iso adj)) tri-top))))
              (! (ap2 (λ p₁ p₂ → p₁ ∙ nat-dom adj f v ∙ p₂)
                (∘-ap (λ m → ⟦ C ⟧ m ◻ f) (–> (iso adj)) tri-bottom)
                (∙-unit-r C₂)))

    open coh-adjust

    fill-adj-transf : Fill-wc {C = D} u v S ≃ Fill-wc {C = C} (–> (iso adj) u) (–> (iso adj) v) ζ
    fill-adj-transf = 
      Fill-wc u v S
        ≃⟨ Fill-wc-Σ u v S ⟩
      [ diag ∈ hom D (obj L b) x ] × [ (tri-top , tri-bottom) ∈ (⟦ D ⟧ diag ◻ arr L f == u) × (⟦ D ⟧ g ◻ diag == v) ] ×
        (α D g diag (arr L f) ∙ ap (λ m → ⟦ D ⟧ g ◻ m) tri-top == ap (λ m → ⟦ D ⟧ m ◻ arr L f) tri-bottom ∙ S)
        ≃⟨ Σ-emap-r (λ diag → Σ-emap-r (λ (tri-top , tri-bottom) →
          ap-equiv (ap-equiv (iso adj) _ _)
            (α D g diag (arr L f) ∙ ap (λ m → ⟦ D ⟧ g ◻ m) tri-top)
            (ap (λ m → ⟦ D ⟧ m ◻ arr L f) tri-bottom ∙ S))) ⟩
      [ diag ∈ hom D (obj L b) x ] × [ (tri-top , tri-bottom) ∈ (⟦ D ⟧ diag ◻ arr L f == u) × (⟦ D ⟧ g ◻ diag == v) ] ×
        (ap (–> (iso adj)) (α D g diag (arr L f) ∙ ap (λ m → ⟦ D ⟧ g ◻ m) tri-top)
          ==
        ap (–> (iso adj)) (ap (λ m → ⟦ D ⟧ m ◻ arr L f) tri-bottom ∙ S))
        ≃⟨ Σ-emap-r (λ diag → Σ-emap-r (λ (tri-top , tri-bottom) → ==-fib-≃ diag tri-top tri-bottom)) ⟩
      [ diag ∈ hom D (obj L b) x ] × [ (tri-top , tri-bottom) ∈ (⟦ D ⟧ diag ◻ arr L f == u) × (⟦ D ⟧ g ◻ diag == v) ] ×
        (α C (arr R g) (–> (iso adj) diag) f ∙ ap (λ m → ⟦ C ⟧ arr R g ◻ m) (nat-dom adj f diag ∙ ap (–> (iso adj)) tri-top)
          ==
        ap (λ m → ⟦ C ⟧ m ◻ f) (nat-cod adj g diag ∙ ap (–> (iso adj)) tri-bottom) ∙ ζ)
        ≃⟨ Σ-emap-r (λ diag → Σ-emap-l _ (×-emap (ap-equiv (iso adj) _ _) (ap-equiv (iso adj) _ _))) ⟩
      [ diag ∈ hom D (obj L b) x ] ×
        [ (tri-top , tri-bottom) ∈
          (–> (iso adj) (⟦ D ⟧ diag ◻ arr L f) == –> (iso adj) u) × (–> (iso adj) (⟦ D ⟧ g ◻ diag) == –> (iso adj) v) ] ×
        (α C (arr R g) (–> (iso adj) diag) f ∙ ap (λ m → ⟦ C ⟧ arr R g ◻ m) (nat-dom adj f diag ∙ tri-top)
          ==
        ap (λ m → ⟦ C ⟧ m ◻ f) (nat-cod adj g diag ∙ tri-bottom) ∙ ζ)
        ≃⟨ Σ-emap-r (λ diag → Σ-emap-l _ (×-emap (pre∙-equiv (nat-dom adj f diag)) (pre∙-equiv (nat-cod adj g diag)))) ⟩
      [ diag ∈ hom D (obj L b) x ] ×
        [ (tri-top , tri-bottom) ∈
          (⟦ C ⟧ –> (iso adj) diag ◻ f == –> (iso adj) u) × (⟦ C ⟧ arr R g ◻ –> (iso adj) diag == –> (iso adj) v) ] ×
        (α C (arr R g) (–> (iso adj) diag) f ∙ ap (λ m → ⟦ C ⟧ arr R g ◻ m) tri-top
          ==
        ap (λ m → ⟦ C ⟧ m ◻ f) tri-bottom ∙ ζ)
        ≃⟨ Σ-emap-l _ (iso adj) ⟩
      [ diag ∈ hom C b (obj R x) ] ×
        [ (tri-top , tri-bottom) ∈
          (⟦ C ⟧ diag ◻ f == –> (iso adj) u) × (⟦ C ⟧ arr R g ◻ diag == –> (iso adj) v) ] ×
        (α C (arr R g) diag f ∙ ap (λ m → ⟦ C ⟧ arr R g ◻ m) tri-top
          ==
        ap (λ m → ⟦ C ⟧ m ◻ f) tri-bottom ∙ ζ)
        ≃⟨ (Fill-wc-Σ (–> (iso adj) u) (–> (iso adj) v) ζ)⁻¹ ⟩
      Fill-wc (–> (iso adj) u) (–> (iso adj) v) ζ ≃∎

  open import lib.wild-cats.OFS-filler-wc

  -- main theorem
  module _ {k₁ k₂ k₃ k₄}
    (uC : is-univ-wc C) (tC : triangle-wc C) (pC : pentagon-wc C)
    (uD : is-univ-wc D) (tD : triangle-wc D) (pD : pentagon-wc D)
    (fsC : ofs-wc k₁ k₂ C) (fsD : ofs-wc k₃ k₄ D) where

    OFS-Rprv-Lpsv : ({x y : ob D} {f : hom D x y} → fst (rclass fsD f) → fst (rclass fsC (arr R f))) →
      ({x y : ob C} {f : hom C x y} → fst (lclass fsC f) → fst (lclass fsD (arr L f)))
    OFS-Rprv-Lpsv prsv-R {f = f} fl = llp-ofs-lc fsD uD tD pD (arr L f) lemma
      where abstract
        lemma : llp-wc {C = D} (rclass fsD) (arr L f)
        lemma {r = g} g-H u v T = equiv-preserves-level ((fill-adj-transf u v T)⁻¹)
          {{lc-ofs-llp fsC uC tC pC fl (prsv-R g-H) (–> (iso adj) u) (–> (iso adj) v) _}}
