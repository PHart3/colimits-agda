{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import lib.PathSeq
open import Coslice
open import Diagram
open import Cocone
open import Cocone-switch
open import AuxPaths-v2
open import FTID
open import Colim
open import CC-Equiv-LRL-2

module CC-Equiv-LRL-3 where

module Constr4 {ℓv ℓe ℓ ℓd ℓc} {Γ : Graph ℓv ℓe} {A : Type ℓ} (F : CosDiag ℓd ℓ A Γ) (T : Coslice ℓc ℓ A) where

  open Id Γ A public

  open Maps F public

  open Recc T public

  open CC-switch F T

  module DiagCoher4 (i j : Obj Γ) (f : P → ty T) (fₚ : (a : A) → f (left a)  == fun T a) (g : Hom Γ i j) (a : A) where

    open Constr3.DiagCoher3 F T i j f fₚ g a public

    ω : transport (λ x → (fun T) ([id] x) == reccForg K (ψ x)) (cglue g a) (! (ap f (! (glue (cin j a))) ∙ fₚ a)) =-= ! (ap f (! (glue (cin i a))) ∙ fₚ a)
    ω = η (comp K) (comTri K) i j g a

    ω-ap-inv : (! (ap f (glue (cin i a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin i a))) ∙ fₚ a) =-=
      (! (ap f (glue (cin i a))) ∙ fₚ a) ∙ transport (λ x → (fun T) ([id] x) == reccForg K (ψ x)) (cglue g a) (! (ap f (! (glue (cin j a))) ∙ fₚ a))
    ω-ap-inv = seq-! (ap-seq (λ p → (! (ap f (glue (cin i a))) ∙ fₚ a) ∙ p) ω)

    ω-switch = κ-switch K g a
    
    ω-ap-inv-switch = seq-! (ap-seq (λ p → (! (ap f (glue (cin i a))) ∙ fₚ a) ∙ p) ω-switch)

    ω=ω-switch : ω-switch =ₛ ω  
    ω=ω-switch = κ=κ-switch K g a

    abstract

      ω=ω-switch-ap-inv : ω-ap-inv-switch =ₛ ω-ap-inv
      ω=ω-switch-ap-inv = !-=ₛ (ap-seq-=ₛ (λ p → (! (ap f (glue (cin i a))) ∙ fₚ a) ∙ p) ω=ω-switch) 


    PathSeq1 : (! (ap f (glue (cin i a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin i a))) ∙ fₚ a) =-=
        transport (λ x → f (right (ψ x)) == f (right (ψ x))) (cglue g a) ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a))
    PathSeq1 =  ω-ap-inv ∙∙ (! (apd-concat-pres {F = λ x → ! (ap f (glue x)) ∙ fₚ ([id] x)} {G = σ (comp K) (comTri K)} (cglue g a)) ◃∙
        transpEq-s ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a)))

    abstract

      Reduce1 : {x : Colim (ConsDiag Γ A)} (p : cin j a == x) {Q : ψ (cin j a) == ψ x}
          → (! (ap f (glue x)) ∙ fₚ ([id] x)) ∙ ! (ap (fun T) (ap [id] p)) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a) ∙
            ap (reccForg K) Q ==
            ! (ap (f ∘ right) (ap ψ p)) ∙ ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a)) ∙
              ap (reccForg K) Q
      Reduce1 idp {Q = Q} = ! (∙-assoc (! (ap f (glue (cin j a))) ∙ fₚ a) (! (ap f (! (glue (cin j a))) ∙ fₚ a)) (ap (reccForg K) Q))
    
      CommSq1 : {x : Colim (ConsDiag Γ A)} (p : cin j a == x) {Q : ψ (cin j a) == ψ x} (R : ap ψ p == Q)
          → ! (ap (λ p → (! (ap f (glue x)) ∙ fₚ ([id] x)) ∙ p) (H₁ p (! (ap f (! (glue (cin j a))) ∙ fₚ a)) R)) ◃∙
            ! (apd-concat-pres {F = λ x → ! (ap f (glue x)) ∙ fₚ ([id] x)} {G = σ (comp K) (comTri K)} p)  ◃∙
              O₁ (((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a))) p R ◃∎
          =ₛ Reduce1 p {Q = Q} ◃∎
      CommSq1 idp idp = =ₛ-in ( lemma (glue (cin j a)) (fₚ a) )
          where
            lemma : {x : P} (r : left a == x) {y : ty T} (s : f (left a) == y) 
              → ! (ap (_∙_ (! (ap f r) ∙ s)) (! (∙-unit-r (! (ap f (! r) ∙ s)))))
                ∙ ! (∙-unit-r ((! (ap f r) ∙ s) ∙ ! (ap f (! r) ∙ s)))
              == ! (∙-assoc (! (ap f r) ∙ s) (! (ap f (! r) ∙ s)) idp)
            lemma idp idp = idp 

      Reduce2 : {x : Colim (ConsDiag Γ A)} (p : cin j a == x) {R : (reccForg K) (cin j (fst (F <#> g) (fun (F # i) a))) == (reccForg K) (ψ x)}
            → (! (ap f (glue x)) ∙ fₚ ([id] x)) ∙ ! (ap (fun T) (ap [id] p)) ∙
                ! (! R ∙ ap (f ∘ right ∘ cin j) (snd (F <#> g) a) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a)) ==
              ! (ap (f ∘ right) (ap ψ p)) ∙ ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a)) ∙
                (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ ! (! R ∙ ap (f ∘ right ∘ cin j) (snd (F <#> g) a) ∙ ap f (! (glue (cin j a))) ∙ fₚ a)
      Reduce2 idp {R = R} = R2lemma (ap f (! (glue (cin j a))) ∙ fₚ a) (! (ap f (glue (cin j a))) ∙ fₚ a) (! (! R ∙ ap (f ∘ right ∘ cin j) (snd (F <#> g) a) ∙
        ap f (! (glue (cin j a))) ∙ fₚ a))
          module _ where R2lemma : ∀ {x z w y : ty T} (q : x == z) (u : w == z) (r : z == y) → u ∙ r == (u ∙ ! q) ∙ q ∙ r
                         R2lemma idp u r = ap (λ p → p ∙ r) (! (∙-unit-r u))

      CommSq2 : {x : Colim (ConsDiag Γ A)} (p : cin j a == x) {s : cin j (fst (F <#> g) (fun (F # i) a))  == ψ x}
          {R : (reccForg K) (cin j (fst (F <#> g) (fun (F # i) a))) == (reccForg K) (ψ x)} (V : ap (reccForg K) s == R)
          → ! (ap (λ q → (! (ap f (glue x)) ∙ fₚ ([id] x)) ∙ q) (H₂ (snd (F <#> g) a) (ap f (! (glue (cin j a))) ∙ fₚ a) {p = ! (ap (fun T) (ap [id] p))} s V)) ◃∙
            Reduce1 p ◃∙ O₂ {p = ! (ap (f ∘ right) (ap ψ p))} {g = cin j} {q = ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a))}
            (snd (F <#> g) a) (ap f (! (glue (cin j a))) ∙ fₚ a) s V ◃∎
          =ₛ Reduce2 p {R = R} ◃∎
      CommSq2 idp {s = s} {R = R} idp = lemma (fₚ a) (snd (F <#> g) a) (glue (cin j a)) 
          where
            lemma : {y : ty T} (w : f (left a) == y) {z : ty (F # j)} (t : fst (F <#> g) (fun (F # i) a) == z) (r : left a == right (cin j z))
              → (! (ap (_∙_ (! (ap f r) ∙ w)) (H₂ {u = reccForg K} {g = cin j} t (ap f (! r) ∙ w) {p = idp} s idp)) ◃∙ ! (∙-assoc (! (ap f r) ∙ w) (! (ap f (! r) ∙ w))
              (ap (reccForg K) (! (ap (cin j) t) ∙ s))) ◃∙ O₂ {p = idp} {g = cin j} t (ap f (! r) ∙ w) s idp ◃∎)
              =ₛ R2lemma {R = ap (reccForg K) s} (ap f (! r) ∙ w) (! (ap f r) ∙ w) (! (! R ∙ ap (f ∘ right ∘ cin j) t ∙ ap f (! r) ∙ w)) ◃∎
            lemma idp idp r = lemma2 r
              where
                lemma2 : {x : P} (e : x == right (cin j (fst (F <#> g) (fun (F # i) a))))
                  → ! (ap (_∙_ (! (ap f e) ∙ idp)) (H₂ {u = reccForg K} {g = cin j} idp (ap f (! e) ∙ idp) s idp)) ◃∙ ! (∙-assoc (! (ap f e) ∙ idp) (! (ap f (! e) ∙ idp))
                    (ap (reccForg K) s)) ◃∙ O₂ {p = idp} {g = cin j} {q = ((! (ap f e) ∙ idp) ∙ ! (ap f (! e) ∙ idp))} idp (ap f (! e) ∙ idp) s idp ◃∎
                  =ₛ R2lemma {R = ap (reccForg K) s} (ap f (! e) ∙ idp) (! (ap f e) ∙ idp) (! (! (ap (reccForg K) s) ∙ ap f (! e) ∙ idp)) ◃∎
                lemma2 idp = lemma3 s
                  where
                    lemma3 : {c : Colim (DiagForg A Γ F)} (S : cin j (fst (F <#> g) (fun (F # i) a)) == c)
                      → (! (ap (λ q → q) (H₂ {g = cin j} idp idp S idp)) ◃∙ idp ◃∙ O₂ {p = idp} {g = cin j} {q = idp} idp idp S idp ◃∎) =ₛ R2lemma {R = ap (reccForg K) s} idp idp
                        (! (! (ap (reccForg K) S) ∙ idp)) ◃∎
                    lemma3 idp = =ₛ-in idp

      Reduce3 : {x : Colim (ConsDiag Γ A)} (p : cin j a == x) {t : ty T} (V : fun T a == t) 
            → (! (ap f (glue x)) ∙ fₚ ([id] x)) ∙ ! (ap (fun T) (ap [id] p)) ∙ V ==
              ! (ap (f ∘ right) (ap ψ p)) ∙ ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a)) ∙
                (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ V
      Reduce3 idp V = R3lemma (glue (cin j a)) (fₚ a) V 
          module _ where
            R3lemma : {x : P} (r : left a == x) {y : ty T} (s : f (left a) == y) {z : ty T} (w : y == z)
              → (! (ap f r) ∙ s) ∙ w
              == ((! (ap f r) ∙ s) ∙ ! ((ap f (! r)) ∙ s)) ∙ (ap f (! r) ∙ s) ∙ w
            R3lemma idp idp w = idp

      CommSq3 : {x : Colim (ConsDiag Γ A)} (p : cin j a == x) {R : (reccForg K) (cin j (fst (F <#> g) (fun (F # i) a))) == (reccForg K) (ψ x)}
          {S : fun T a  == (reccForg K) (ψ x)} (E : ! (! R ∙ ap (f ∘ right ∘ cin j) (snd (F <#> g) a) ∙ ap f (! (glue (cin j a))) ∙ fₚ a) == S)
          → ! (ap (λ q →  (! (ap f (glue x)) ∙ fₚ ([id] x)) ∙ q) (ap (λ q → ! (ap (fun T) (ap [id] p)) ∙ q) E)) ◃∙ Reduce2 p {R = R} ◃∙
            ap (λ q → ! (ap (f ∘ right) (ap ψ p)) ∙ ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a)) ∙
              (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q) E ◃∎
          =ₛ Reduce3 p S ◃∎
      CommSq3 idp {R = R} idp = lemma (glue (cin j a)) (fₚ a) (! (! R ∙ ap (f ∘ right ∘ cin j) (snd (F <#> g) a) ∙ ap f (! (glue (cin j a))) ∙ fₚ a))
          where
            lemma : {x : P} (r : left a == x) {y : ty T} (s : f (left a) == y) {z : ty T} (w : y == z)
              → idp ◃∙ R2lemma {R = R} (ap f (! r) ∙ s) (! (ap f r) ∙ s) w ◃∙ idp ◃∎ =ₛ R3lemma (! (! R ∙ ap (f ∘ right ∘ cin j) (snd (F <#> g) a) ∙
                ap f (! (glue (cin j a))) ∙ fₚ a)) r s w ◃∎
            lemma idp idp w = =ₛ-in idp

      Reduce4 : {x : Colim (ConsDiag Γ A)} (p : cin j a == x) {z : A} (e : z == [id] x) {w : ty T} (u : w == fun T z) → (! (ap f (glue x)) ∙ fₚ ([id] x)) ∙ ! (ap (fun T) e) ∙ ! u
          == ! (ap (f ∘ right) (ap ψ p)) ∙ ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a)) ∙
            (ap (f ∘ right) (ap ψ p) ∙ (ap f (! (glue x)) ∙ fₚ ([id] x)) ∙ ! (ap (fun T) e)) ∙ ! u
      Reduce4 idp {z = z} e u = R4lemma (glue (cin j a)) (fₚ a) (! (ap (fun T) e)) (! u)
          module _ where
            R4lemma : {x n : P} (r : n == x) {y d c : ty T} (s : f n == y) (q : y == d) (U : d == c)
              → (! (ap f r) ∙ s) ∙ q ∙ U == ((! (ap f r) ∙ s) ∙
              ! (ap f (! r) ∙ s)) ∙ ((ap f (! r) ∙ s) ∙ q) ∙ U
            R4lemma idp idp q U = idp

      CommSq4 : {x : Colim (ConsDiag Γ A)} (p : cin j a == x) {e : a == [id] x} (K : ap [id] p == e) (u : f (right (ψ x)) == fun T a)
          → ! (ap (λ q →  (! (ap f (glue x)) ∙ fₚ ([id] x)) ∙ q) (ap (λ q → q ∙ ! u) (ap (λ q → ! (ap (fun T) q)) K))) ◃∙ (Reduce3 p (! u) ◃∙
            (ap (λ q → ! (ap (f ∘ right) (ap ψ p)) ∙ ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a)) ∙ q ∙ ! u)
              (O₄ {u = fun T} (λ x → ap f (! (glue x)) ∙ fₚ ([id] x)) p K) ◃∎))
          =ₛ Reduce4 p e u ◃∎
      CommSq4 idp idp u = lemma (glue (cin j a)) (fₚ a)
          where
            lemma : {x : P} (r : left a == x) (s : f (left a) == fun T a) 
              → (idp ◃∙ R3lemma (! u) r s (! u) ◃∙ ap (λ q →  ((! (ap f r) ∙ s) ∙ ! (ap f (! r) ∙ s)) ∙ q ∙ ! u)
                (! (∙-unit-r (ap f (! r) ∙ s))) ◃∎)
              =ₛ R4lemma idp u r s idp (! u) ◃∎
            lemma idp s = subLemma s (! u)
              where subLemma : {z : ty T} (S : f (left a) == z) (U : z == f (right (ψ (cin j a))))
                      → idp ◃∙ R3lemma (! u) idp S U ◃∙ ap (λ q → (S ∙ ! S) ∙ q ∙ U) (! (∙-unit-r S)) ◃∎ =ₛ R4lemma idp u idp S idp U ◃∎
                    subLemma idp U = =ₛ-in idp

      CommSq5 : {x : Colim (ConsDiag Γ A)} (p : cin j a == x)
          → Reduce4 p idp (ap f (! (glue x)) ∙ fₚ ([id] x)) ◃∙ O₅ {f = f ∘ right} ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙
            ! (ap f (! (glue (cin j a))) ∙ fₚ a)) p (ap f (! (glue x)) ∙ fₚ ([id] x)) ◃∎
          =ₛ ! (apd-tr (λ x → (! (ap f (glue x)) ∙ fₚ ([id] x)) ∙ ! (ap f (! (glue x)) ∙ fₚ ([id] x))) p) ◃∎
      CommSq5 idp =  lemma (glue (cin j a)) (fₚ a)
          where
            lemma : {n : P} (r : n == right (ψ (cin j a))) {t : ty T} (s : f n == t)
              → (R4lemma idp (ap f (! (glue (cin j a))) ∙ fₚ a) r s idp (! (ap f (! r) ∙ s))
                ◃∙ O₅ {f = f ∘ right} {h = ψ} {b = cin j a} ((! (ap f r) ∙ s) ∙ ! (ap f (! r) ∙ s)) idp (ap f (! r) ∙ s) ◃∎)
              =ₛ (idp ◃∎)
            lemma idp idp = =ₛ-in idp

      BigReduct1 : PathSeq1 =ₛ ! (apd-tr (λ x → (! (ap f (glue x)) ∙ fₚ ([id] x)) ∙ ! (ap f (! (glue x)) ∙ fₚ ([id] x))) (cglue g a)) ◃∎
      BigReduct1 = PathSeq1
                     =ₛ⟨ 0 & 4 & !ₛ ω=ω-switch-ap-inv ⟩
                   ω-ap-inv-switch ∙∙ (! (apd-concat-pres {F = λ x → ! (ap f (glue x)) ∙ fₚ ([id] x)} {G = σ (comp K) (comTri K)} (cglue g a)) ◃∙
                     transpEq-s ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a)))
                     =ₛ⟨ 3 & 3 &  CommSq1 (cglue g a) (ψ-βr g a) ⟩
                   (range 0 3 ω-ap-inv-switch) ∙∙ (Reduce1 (cglue g a) ◃∙ (range 1 4 (transpEq-s ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a)))))
                     =ₛ⟨ 2 & 3 & CommSq2 (cglue g a) (recc-βr K g (fun (F # i) a))  ⟩ 
                   (range 0 2 ω-ap-inv-switch) ∙∙ (Reduce2 (cglue g a) {R = ap f (ap right (cglue g (fun (F # i) a)))} ◃∙
                   (range 2 3 (transpEq-s ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a)))))
                     =ₛ⟨ 1 & 3 & CommSq3 (cglue g a) (ap ! (snd (comTri K g) a)) ⟩ 
                   (range 0 1 ω-ap-inv-switch) ∙∙ (Reduce3 (cglue g a) (! (ap f (! (glue (cin i a))) ∙ fₚ a)) ◃∙
                   (range 3 2 (transpEq-s ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a)))))
                     =ₛ⟨ 0  & 3  & CommSq4 (cglue g a) (id-βr g a) (ap f (! (glue (cin i a))) ∙ fₚ a) ⟩ 
                   Reduce4 (cglue g a) idp (ap f (! (glue (cin i a))) ∙ fₚ a) ◃∙ O₅ ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a))
                   (cglue g a) (ap f (! (glue (cin i a))) ∙ fₚ a) ◃∎
                     =ₛ⟨ CommSq5 (cglue g a) ⟩ 
                   ! (apd-tr (λ x → (! (ap f (glue x)) ∙ fₚ ([id] x)) ∙ ! (ap f (! (glue x)) ∙ fₚ ([id] x))) (cglue g a)) ◃∎ ∎ₛ

      abstract

        apdRW1 : apd-tr (λ x → (! (ap f (glue x)) ∙ fₚ ([id] x)) ∙ σ (comp K) (comTri K) x) (cglue g a) ◃∎ =ₛ
          apd-concat-pres {F = λ x → ! (ap f (glue x)) ∙ fₚ ([id] x)} {G = σ (comp K) (comTri K)} (cglue g a) ◃∙
          ap (λ p → (! (ap f (glue (cin i a))) ∙ fₚ a) ∙ p) (↯ ω) ◃∎
        apdRW1 = apd-tr (λ x → (! (ap f (glue x)) ∙ fₚ ([id] x)) ∙ σ (comp K) (comTri K) x) (cglue g a) ◃∎
                   =ₛ⟨ apd-concat-fun-s (cglue g a) ⟩
                 apd-concat-pres (cglue g a) ◃∙ ap (λ p → (! (ap f (glue (cin i a))) ∙ fₚ a) ∙ p)
                 (apd-tr (σ (comp K) (comTri K)) (cglue g a)) ◃∎
                   =ₛ⟨ 1 & 1 & =ₛ-in (ap (ap (λ p → (! (ap f (glue (cin i a))) ∙ fₚ a) ∙ p)) (σ-β K g a)) ⟩
                 apd-concat-pres (cglue g a) ◃∙ ap (λ p → (! (ap f (glue (cin i a))) ∙ fₚ a) ∙ p) (↯ ω) ◃∎ ∎ₛ
