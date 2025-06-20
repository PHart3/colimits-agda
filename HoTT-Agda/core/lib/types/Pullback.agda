{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.Equivalence2
open import lib.types.Graph
open import lib.types.Cospan
open import lib.types.Pointed
open import lib.types.Sigma
open import lib.wild-cats.WildCats

module lib.types.Pullback where

module _ {i j k} (D : Cospan {i} {j} {k}) where

  open Cospan D

  -- standard pullback
  record Pullback : Type (lmax i (lmax j k)) where
    constructor pullback
    field
      a : A
      b : B
      h : f a == g b

  Pb-con : Cone-csp D Pullback
  Cone-csp.left Pb-con = Pullback.a
  Cone-csp.right Pb-con = Pullback.b
  Cone-csp.sq Pb-con = Pullback.h

  pullback= : {a a' : A} (p : a == a') {b b' : B} (q : b == b')
    {h : f a == g b} {h' : f a' == g b'} (r : h ∙ ap g q == ap f p ∙ h')
    → pullback a b h == pullback a' b' h'
  pullback= idp idp r =
    ap (pullback _ _) (! (∙-unit-r _) ∙ r) 

  pullback-aβ : {a a' : A} (p : a == a') {b b' : B} (q : b == b')
    {h : f a == g b} {h' : f a' == g b'} (r : h ∙ ap g q == ap f p ∙ h')
    → ap Pullback.a (pullback= p q {h = h} {h' = h'} r) == p
  pullback-aβ idp idp r =
    ap Pullback.a (ap (pullback _ _) (! (∙-unit-r _) ∙ r))
      =⟨ ∘-ap Pullback.a (pullback _ _) _ ⟩
    ap (λ _ → _) (! (∙-unit-r _) ∙ r)
      =⟨ ap-cst _ _ ⟩
    idp =∎

  pullback-bβ : {a a' : A} (p : a == a') {b b' : B} (q : b == b')
    {h : f a == g b} {h' : f a' == g b'} (r : h ∙ ap g q == ap f p ∙ h')
    → ap Pullback.b (pullback= p q {h = h} {h' = h'} r) == q
  pullback-bβ idp idp r =
    ap Pullback.b (ap (pullback _ _) (! (∙-unit-r _) ∙ r))
      =⟨ ∘-ap Pullback.b (pullback _ _) _ ⟩
    ap (λ _ → _) (! (∙-unit-r _) ∙ r)
      =⟨ ap-cst _ _ ⟩
    idp =∎

-- pullbacks are invariant under equivalence
module _ {i j k : ULevel} where

  cspm-to-pb : {C₁ C₂ : Cospan {i} {j} {k}} → Cospan-mor C₁ C₂ → Pullback C₁ → Pullback C₂
  Pullback.a (cspm-to-pb μ (pullback a b h)) = cspm-A μ a
  Pullback.b (cspm-to-pb μ (pullback a b h)) = cspm-B μ b
  Pullback.h (cspm-to-pb μ (pullback a b h)) = cspm-nat-f μ a ∙ ap (cspm-C μ) h ∙ cspm-nat-g μ b 

  csp-to-pb-eqv : {C₁ C₂ : Cospan {i} {j} {k}} → Cospan-eqv C₁ C₂ → Pullback C₁ ≃ Pullback C₂
  csp-to-pb-eqv {C₁} {C₂} ε@(E , eA , eB , eC) = equiv (cspm-to-pb E) (cspm-to-pb (fst (csp-eqv-rev ε)))
    rtrip1 rtrip2
    where abstract
    
      rtrip1 : (x : Pullback C₂) → cspm-to-pb E (cspm-to-pb (fst (csp-eqv-rev ε)) x) == x
      rtrip1 (pullback a b h) = pullback= C₂ (is-equiv.f-g eA a) (is-equiv.f-g eB b) $
        ap (λ p → (cspm-nat-f E (is-equiv.g eA a) ∙ p ∙ cspm-nat-g E (is-equiv.g eB b)) ∙ ap (Cospan.g C₂) (is-equiv.f-g eB b))
          (ap2 (λ p₁ p₂ →
            ap (cspm-C E)
              ((! (is-equiv.g-f eC (Cospan.f C₁ (is-equiv.g eA a))) ∙
                ap (is-equiv.g eC) (! (cspm-nat-f E (is-equiv.g eA a))) ∙ p₁) ∙
              ap (is-equiv.g eC) h ∙ ! p₂ ∙ ap (is-equiv.g eC) (! (cspm-nat-g E (is-equiv.g eB b))) ∙
              is-equiv.g-f eC (Cospan.g C₁ (is-equiv.g eB b))))
            (ap-∘ (is-equiv.g eC) (Cospan.f C₂) (is-equiv.f-g eA a))
            (ap-∘ (is-equiv.g eC) (Cospan.g C₂) (is-equiv.f-g eB b)) ∙
          aux1 (cspm-C E) (is-equiv.g eC) (is-equiv.f-g eC)
            (is-equiv.g-f eC (Cospan.f C₁ (is-equiv.g eA a)))
            (cspm-nat-f E (is-equiv.g eA a))
            (ap (Cospan.f C₂) (is-equiv.f-g eA a))
            h
            (ap (Cospan.g C₂) (is-equiv.f-g eB b))
            (cspm-nat-g E (is-equiv.g eB b))
            (is-equiv.g-f eC (Cospan.g C₁ (is-equiv.g eB b)))) ∙
        ap2 (λ p₁ p₂ →
            (cspm-nat-f E (is-equiv.g eA a) ∙
            (! p₁ ∙
            is-equiv.f-g eC (cspm-C E (Cospan.f C₁ (is-equiv.g eA a))) ∙
            ! (cspm-nat-f E (is-equiv.g eA a)) ∙
            ap (Cospan.f C₂) (is-equiv.f-g eA a) ∙ h ∙
            ! (ap (Cospan.g C₂) (is-equiv.f-g eB b)) ∙
            ! (cspm-nat-g E (is-equiv.g eB b)) ∙
            ! p₂ ∙'
            ap (cspm-C E) (is-equiv.g-f eC (Cospan.g C₁ (is-equiv.g eB b)))) ∙
            cspm-nat-g E (is-equiv.g eB b)) ∙
            ap (Cospan.g C₂) (is-equiv.f-g eB b))
          (is-equiv.adj eC (Cospan.f C₁ (is-equiv.g eA a)))
          (! (is-equiv.adj eC (Cospan.g C₁ (is-equiv.g eB b)))) ∙
        aux2
          (cspm-nat-f E (is-equiv.g eA a))
          (is-equiv.f-g eC (cspm-C E (Cospan.f C₁ (is-equiv.g eA a))))
          (ap (Cospan.f C₂) (is-equiv.f-g eA a))
          h
          (ap (Cospan.g C₂) (is-equiv.f-g eB b))
          (cspm-nat-g E (is-equiv.g eB b))
          (ap (cspm-C E) (is-equiv.g-f eC (Cospan.g C₁ (is-equiv.g eB b))))
        where
        
          aux1 : ∀ {ℓ₁ ℓ₂} {T₁ : Type ℓ₁} {T₂ : Type ℓ₂} (f₁ : T₁ → T₂) (f₂ : T₂ → T₁) (H : f₁ ∘ f₂ ∼ idf T₂)
            {x₁ x₂ : T₁} {y₁ y₂ y₃ y₄ y₅ y₆ : T₂}
            (p₁ : f₂ y₂ == x₁) (p₂ : y₁ == y₂)
            (p₃ : y₁ == y₃) (p₄ : y₃ == y₄)
            (p₅ : y₅ == y₄) (p₆ : y₆ == y₅) (p₇ : f₂ y₆ == x₂) →
            ap f₁ (((! p₁ ∙ ap f₂ (! p₂) ∙ ap f₂ p₃) ∙ ap f₂ p₄ ∙ ! (ap f₂ p₅) ∙ ap f₂ (! p₆) ∙ p₇))
              ==
            ! (ap f₁ p₁) ∙ H y₂ ∙ ! p₂ ∙ p₃ ∙ p₄ ∙ ! p₅ ∙ ! p₆ ∙ ! (H y₆) ∙' ap f₁ p₇
          aux1 _ _ H {y₁ = y₁} idp idp idp idp idp idp idp = ! (!-inv-r (H y₁))

          aux2 : ∀ {ℓ} {T : Type ℓ} {y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : T}
            (p₁ : y₁ == y₂) (p₂ : y₃ == y₂)
            (p₃ : y₁ == y₄) (p₄ : y₄ == y₅)
            (p₅ : y₆ == y₅) (p₆ : y₇ == y₆) (p₇ : y₈ == y₇) → 
            (p₁ ∙ (! p₂ ∙ p₂ ∙ ! p₁ ∙ p₃ ∙ p₄ ∙ ! p₅ ∙ ! p₆ ∙ ! p₇ ∙' p₇) ∙ p₆) ∙ p₅
              ==
            p₃ ∙ p₄
          aux2 idp idp idp idp idp idp idp = idp
          
      rtrip2 : (x : Pullback C₁) → cspm-to-pb (fst (csp-eqv-rev ε)) (cspm-to-pb E x) == x
      rtrip2 (pullback a b h) = pullback= C₁ (is-equiv.g-f eA a) (is-equiv.g-f eB b) $
        ap5 (λ p₁ p₂ q r₁ r₂ →
            ((r₁ ∙
              ap (is-equiv.g eC) p₁ ∙
              ap (is-equiv.g eC ∘ Cospan.f C₂) (is-equiv.f-g eA (cspm-A E a))) ∙
            q ∙
            ! (ap (is-equiv.g eC ∘ Cospan.g C₂) (is-equiv.f-g eB (cspm-B E b))) ∙
            ap (is-equiv.g eC) p₂ ∙
            r₂) ∙
            ap (Cospan.g C₁) (is-equiv.g-f eB b))
          (hmtpy-nat-!-∙' (cspm-nat-f E) (is-equiv.g-f eA a))
          (hmtpy-nat-!-∙' (cspm-nat-g E) (is-equiv.g-f eB b))
          (ap-∙∙ (is-equiv.g eC) (cspm-nat-f E a) (ap (cspm-C E) h) (cspm-nat-g E b) ∙
          ap (λ p → ap (is-equiv.g eC) (cspm-nat-f E a) ∙ p ∙ ap (is-equiv.g eC) (cspm-nat-g E b))
            (∘-ap (is-equiv.g eC) (cspm-C E) h ∙
            apeq-rev (is-equiv.g-f eC) h))
          (hmtpy-nat-!-∙' (is-equiv.g-f eC) (ap (Cospan.f C₁) (is-equiv.g-f eA a)))
          (apCommSq2' (is-equiv.g-f eC) (ap (Cospan.g C₁) (is-equiv.g-f eB b))) ∙        
        ap2 (λ p₁ p₂ →
            (((ap (λ z → z) (ap (Cospan.f C₁) (is-equiv.g-f eA a)) ∙
            ! (is-equiv.g-f eC (Cospan.f C₁ a)) ∙'
            ! (ap (λ z → is-equiv.g eC (cspm-C E z)) (ap (Cospan.f C₁) (is-equiv.g-f eA a)))) ∙
            ap (is-equiv.g eC)
              (ap (cspm-C E ∘ Cospan.f C₁) (is-equiv.g-f eA a) ∙
              ! (cspm-nat-f E a) ∙'
              ! (ap (Cospan.f C₂ ∘ cspm-A E) (is-equiv.g-f eA a))) ∙
            ap (is-equiv.g eC ∘ Cospan.f C₂) p₁) ∙
            (ap (is-equiv.g eC) (cspm-nat-f E a) ∙
            (is-equiv.g-f eC (Cospan.f C₁ a) ∙ ap (λ z → z) h ∙ ! (is-equiv.g-f eC (Cospan.g C₁ b))) ∙
            ap (is-equiv.g eC) (cspm-nat-g E b)) ∙
            ! (ap (is-equiv.g eC ∘ Cospan.g C₂) p₂) ∙
            ap (is-equiv.g eC)
              (ap (Cospan.g C₂ ∘ cspm-B E) (is-equiv.g-f eB b) ∙
              ! (cspm-nat-g E b) ∙'
              ! (ap (cspm-C E ∘ Cospan.g C₁) (is-equiv.g-f eB b))) ∙
            ap (λ z → is-equiv.g eC (cspm-C E z)) (ap (Cospan.g C₁) (is-equiv.g-f eB b)) ∙
            is-equiv.g-f eC (Cospan.g C₁ b) ∙'
            ! (ap (λ z → z) (ap (Cospan.g C₁) (is-equiv.g-f eB b)))) ∙
            ap (Cospan.g C₁) (is-equiv.g-f eB b))
          (! (is-equiv.adj eA a) )
          (! (is-equiv.adj eB b)) ∙
        aux
          (is-equiv.g-f eA a)
          h
          (is-equiv.g-f eC (Cospan.f C₁ a))
          (cspm-nat-f E a)
          (is-equiv.g-f eC (Cospan.g C₁ b))
          (cspm-nat-g E b)
          (is-equiv.g-f eB b)
        where
          aux : {x₁ x₂ : Cospan.A C₁} {w₁ w₂ : Cospan.B C₁}
            (p₁ : x₁ == x₂) (p₂ : Cospan.f C₁ x₂ == Cospan.g C₁ w₂) (p₃ : _ == Cospan.f C₁ x₂)
            (p₄ : Cospan.f C₂ (cspm-A E x₂) == (cspm-C E ∘ Cospan.f C₁) x₂)
            (p₅ : is-equiv.g eC (cspm-C E (Cospan.g C₁ _)) == Cospan.g C₁ _)
            (p₆ : cspm-C E (Cospan.g C₁ _) == Cospan.g C₂ (cspm-B E _))
            (p₇ : w₁ == w₂) → 
            (((ap (λ z → z) (ap (Cospan.f C₁) p₁) ∙
            ! p₃ ∙'
            ! (ap (λ z → is-equiv.g eC (cspm-C E z)) (ap (Cospan.f C₁) p₁))) ∙
            ap (is-equiv.g eC)
              (ap (cspm-C E ∘ Cospan.f C₁) p₁ ∙
              ! p₄ ∙'
              ! (ap (Cospan.f C₂ ∘ cspm-A E) p₁)) ∙
            ap (is-equiv.g eC ∘ Cospan.f C₂) (ap (cspm-A E) p₁)) ∙
            (ap (is-equiv.g eC) p₄ ∙
            (p₃ ∙
            ap (λ z → z) p₂ ∙ ! p₅) ∙
            ap (is-equiv.g eC) p₆) ∙
            ! (ap (is-equiv.g eC ∘ Cospan.g C₂) (ap (cspm-B E) p₇)) ∙
            ap (is-equiv.g eC)
              (ap (Cospan.g C₂ ∘ cspm-B E) p₇ ∙
              ! p₆ ∙'
              ! (ap (cspm-C E ∘ Cospan.g C₁) p₇)) ∙
            ap (λ z → is-equiv.g eC (cspm-C E z)) (ap (Cospan.g C₁) p₇) ∙
            p₅ ∙'
            ! (ap (λ z → z) (ap (Cospan.g C₁) p₇))) ∙
            ap (Cospan.g C₁) p₇
              ==
            ap (Cospan.f C₁) p₁ ∙ p₂
          aux idp p₂ p₃ p₄ p₅ p₆ idp = lemma (is-equiv.g eC) p₂ p₃ p₄ p₅ p₆
            where
              lemma : ∀ {ℓ₁ ℓ₂} {T₁ : Type ℓ₁} {T₂ : Type ℓ₂} (f : T₁ → T₂)
                {x₁ x₂ x₃ x₄ : T₁} {y₁ y₂ : T₂}
                (r₁ : y₁ == y₂) (r₂ : f x₂ == y₁) (r₃ : x₁ == x₂) (r₄ : f x₃ == y₂) (r₅ : x₃ == x₄) →
                ((! r₂ ∙ ap f (! r₃) ∙ idp) ∙
                (ap f r₃ ∙ (r₂ ∙ ap (λ z → z) r₁ ∙ ! r₄) ∙ ap f r₅) ∙
                ap f (! r₅) ∙ r₄) ∙ idp
                  ==
                r₁
              lemma {T₂ = T₂} _ idp r₂ idp r₄ idp = lemma-aux r₂ r₄
                where
                  lemma-aux : {x y z : T₂} (s : x == y) (q : z == y)
                    → ((! s ∙ idp) ∙ ((s ∙ ! q) ∙ idp) ∙ q) ∙ idp == idp
                  lemma-aux idp idp = idp

  lw-to-pb-csp : {D : Cospan {i} {j} {k}} {T₁ : Type i} {T₃ : Type j} {T₂ : Type k}
    (E₁ : Cospan.A D ≃ T₁) (E₂ : Cospan.C D ≃ T₂) (E₃ : Cospan.B D ≃ T₃)
    → Pullback D ≃ Pullback (cospan T₁ T₃ T₂ (–> E₂ ∘ Cospan.f D ∘ <– E₁) (–> E₂ ∘ Cospan.g D ∘ <– E₃))
  lw-to-pb-csp {D} ε₁@(e₁ , eqv₁) (e₂ , eqv₂) ε₃@(e₃ , eqv₃) = csp-to-pb-eqv ((cospanmor e₁ e₃ e₂
    (λ x → ap (e₂ ∘ Cospan.f D) (<–-inv-l ε₁ x))
    λ x → ! (ap (e₂ ∘ Cospan.g D) (<–-inv-l ε₃ x))) ,
    (eqv₁ , eqv₃ , eqv₂))

module _ {i j k} (D : ⊙Cospan {i} {j} {k}) where

  ⊙Pullback : Ptd (lmax i (lmax j k))
  ⊙Pullback =
    ⊙[ Pullback (⊙cospan-out D) ,
       pullback (pt X) (pt Y) (snd f ∙ ! (snd g)) ]
    where open ⊙Cospan D

module _ {i j k} (D : Cospan {i} {j} {k}) where
  open Cospan D

  pullback-decomp-equiv : Pullback D ≃ Σ (A × B) (λ {(a , b) → f a == g b})
  pullback-decomp-equiv = equiv
    (λ {(pullback a b h) → ((a , b) , h)})
    (λ {((a , b) , h) → pullback a b h})
    (λ _ → idp)
    (λ _ → idp)

module _ {i j k} (n : ℕ₋₂) {D : Cospan {i} {j} {k}} where

  open Cospan D

  pullback-level : has-level n A → has-level n B → has-level n C
    → has-level n (Pullback D)
  pullback-level pA pB pC =
    equiv-preserves-level ((pullback-decomp-equiv D)⁻¹) where instance _ = pA; _ = pB; _ = pC

instance
  pullback-level-instance : {i j k : ULevel} {n : ℕ₋₂} {D : Cospan {i} {j} {k}} →
    {{has-level n (Cospan.A D)}} → {{has-level n (Cospan.B D)}} → {{has-level n (Cospan.C D)}}
      → has-level n (Pullback D)
  pullback-level-instance {n = n} {{pA}} {{pB}} {{pC}} = pullback-level n pA pB pC

-- abstract pullbacks

module _ {i j k ℓ₁ ℓ₂} {D : Cospan {i} {j} {k}} {T : Type ℓ₁} where

  open Cospan D

  module _ (K : Cone-csp D T) where

    open Cone-csp K

    pre-cmp-csp : (S : Type ℓ₂) → (S → T) → Cone-csp D S
    pre-cmp-csp = λ S m → cone-csp (left ∘ m) (right ∘ m) λ x → sq (m x) 

    is-pb-abs : Type (lmax (lmax (lmax (lmax i j) k) ℓ₁) (lsucc ℓ₂))
    is-pb-abs = (S : Type ℓ₂) → is-equiv (pre-cmp-csp S)

    is-pb-abs-≃ : (p : is-pb-abs) (S : Type ℓ₂) → (S → T) ≃ Cone-csp D S
    is-pb-abs-≃ p = λ S → (pre-cmp-csp S) , (p S)

  module _ {K : Cone-csp D T} (ζ : is-pb-abs K) {S : Type ℓ₂} where

    limcsp-is-contr : (J : Cone-csp D S) → is-contr (Σ (S → T) (λ f → pre-cmp-csp K S f == J))
    limcsp-is-contr J = equiv-is-contr-map (ζ S) J

    precmp-csp-mor-≃-aux : (J : Cone-csp D S) (f : S → T) → (ConCspEq (pre-cmp-csp K S f) J) ≃ Cone-csp-mor-str D K J f
    precmp-csp-mor-≃-aux _ f = equiv ==-to-mor mor-to-== rtrip1 rtrip2

      where
        open Cone-csp-mor-str 

        ==-to-mor : {L : Cone-csp D S} → ConCspEq (pre-cmp-csp K S f) L → Cone-csp-mor-str D K L f
        map-left (==-to-mor e) = left-== e
        map-right (==-to-mor e) = right-== e
        map-sq (==-to-mor e) = sq-== e

        mor-to-== : {L : Cone-csp D S} → Cone-csp-mor-str D K L f →  ConCspEq (pre-cmp-csp K S f) L
        left-== (mor-to-== m) = map-left m
        right-== (mor-to-== m) = map-right m
        sq-== (mor-to-== m) = map-sq m

        abstract

          rtrip1 : {L : Cone-csp D S} (b : Cone-csp-mor-str D K L f) → ==-to-mor (mor-to-== b) == b
          rtrip1 {L} b = idp

          rtrip2 : {L : Cone-csp D S} (a : ConCspEq (pre-cmp-csp K S f) L) → mor-to-== (==-to-mor a) == a
          rtrip2 = ConCspEq-ind (λ L a → mor-to-== (==-to-mor a) == a) idp

    precmp-csp-mor-≃ : (J : Cone-csp D S) (f : S → T) → (pre-cmp-csp K S f == J) ≃ Cone-csp-mor-str D K J f
    precmp-csp-mor-≃ J f = precmp-csp-mor-≃-aux J f ∘e ConCspEq-==-≃ ⁻¹

    limcsp-mor-contr : (J : Cone-csp D S) → is-contr (Σ (S → T) (λ f → Cone-csp-mor-str D K J f))
    limcsp-mor-contr J = equiv-preserves-level (Σ-emap-r (precmp-csp-mor-≃ J)) {{limcsp-is-contr J}}

    abstract
      limcsp-mor-paths : {J : Cone-csp D S} {f₁ f₂ : S → T}
        (σ₁ : Cone-csp-mor-str D K J f₁) (σ₂ : Cone-csp-mor-str D K J f₂)
        → (f₁ , σ₁) == (f₂ , σ₂)
      limcsp-mor-paths {J} {f₁} {f₂} σ₁ σ₂ = contr-has-all-paths {{limcsp-mor-contr J}} (f₁ , σ₁) (f₂ , σ₂)

module _ {i j k ℓ} {D : Cospan {i} {j} {k}} {T₁ : Type ℓ} {T₂ : Type ℓ} {K₁ : Cone-csp D T₁} {K₂ : Cone-csp D T₂}
  (ζ₁ : is-pb-abs {ℓ₂ = ℓ} K₁) (ζ₂ : is-pb-abs {ℓ₂ = ℓ} K₂) where

  private

    can-map₁ : Cone-csp-mor K₂ K₁
    can-map₁ = contr-center (limcsp-mor-contr ζ₂ K₁) 

    can-map₂ : Cone-csp-mor K₁ K₂
    can-map₂ = contr-center (limcsp-mor-contr ζ₁ K₂)

    can-map-rtrip₁ : can-map₁ Cone-csp-mor-∘ can-map₂ == Cone-csp-mor-id
    can-map-rtrip₁ = limcsp-mor-paths ζ₁ _ _

    can-map-rtrip₂ : can-map₂ Cone-csp-mor-∘ can-map₁ == Cone-csp-mor-id
    can-map-rtrip₂ = limcsp-mor-paths ζ₂ _ _

  -- uniqueness of pullback squares
  pb-unique : Cone-csp-iso D K₁ K₂
  fst pb-unique = equiv (fst can-map₂) (fst can-map₁) (app= (fst= can-map-rtrip₁)) (app= (fst= can-map-rtrip₂))
  snd pb-unique = snd can-map₂

  pb-unique-mor : Cone-csp-mor K₁ K₂
  pb-unique-mor = Cone-csp-iso-mor pb-unique

module pb-qinv {i j k ℓ} {D : Cospan {i} {j} {k}} {T₁ : Type ℓ} {T₂ : Type ℓ} {K₁ : Cone-csp D T₁} {K₂ : Cone-csp D T₂}
  (ζ₁ : is-pb-abs {ℓ₂ = ℓ} K₁) (ζ₂ : is-pb-abs {ℓ₂ = ℓ} K₂) where

  abstract
    pb-unique-qinv : cospan-is-qinv (pb-unique-mor {K₁ = K₁} {K₂ = K₂} ζ₁ ζ₂) (pb-unique-mor {D = D} ζ₂ ζ₁)
    fst pb-unique-qinv = limcsp-mor-paths ζ₂ _ _
    snd pb-unique-qinv = limcsp-mor-paths ζ₁ _ _

module _ {ℓ} {Δ : Diag-cspan (Type-wc ℓ)} {X : Type ℓ} {K : Cone-wc Δ X} where

  open Cone-wc

  -- limiting cone is pullback
  lim-to-pb : is-pb-wc K → is-pb-abs {ℓ₂ = ℓ} (con-to-csp Δ K)
  lim-to-pb pb = λ S → ∼-preserves-equiv {f₀ = –> (con-csp-diag-≃ Δ) ∘ pre-cmp-con {G = Graph-cspan} K S} {f₁ = pre-cmp-csp (con-to-csp Δ K) S}
    (λ f → ConCspEq-to-== (concspeq (λ _ → idp) (λ _ → idp)
      (λ x → ! (ap (ap (λ u → u x)) (!r-ap-∙ (λ m z → m (f z)) (tri K unit) (tri K unit)) ∙ ∘-ap (λ u → u x) (λ m z → m (f z)) (tri K unit ∙ ! (tri K unit))))))
    (snd (con-csp-diag-≃ Δ ∘e is-lim-≃ {G = Graph-cspan} K pb S))

-- standard pullback is abstract pullback
module _ {i j k} (D : Cospan {i} {j} {k}) where

  open Cospan D
  open Cone-csp

  stdpb-is-abspb : ∀ {ℓ} → is-pb-abs {ℓ₂ = ℓ} (Pb-con D)
  stdpb-is-abspb = λ S →
    is-eq (pre-cmp-csp (Pb-con D) S) (λ K x → pullback (left K x) (right K x) (sq K x)) (λ _ → idp) λ f → λ= (λ _ → idp)

-- conversion between pullback squares and limiting cones
module _ {ℓ} {Δ : Diag-cspan (Type-wc ℓ)} {X : Type ℓ} {K : Cone-wc Δ X} (ζ : is-pb-wc K) where

  StdPb-Lim-≃ : Cone-csp-iso _ (Pb-con (diag-to-csp Δ)) (con-to-csp Δ K)
  StdPb-Lim-≃ = pb-unique (stdpb-is-abspb (diag-to-csp Δ)) (lim-to-pb ζ)

  Lim-StdPb-≃ : Cone-csp-iso _ (con-to-csp Δ K) (Pb-con (diag-to-csp Δ))
  Lim-StdPb-≃ = pb-unique (lim-to-pb ζ) (stdpb-is-abspb (diag-to-csp Δ))
