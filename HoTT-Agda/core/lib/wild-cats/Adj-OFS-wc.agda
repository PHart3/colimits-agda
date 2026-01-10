{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.Equivalence2
open import lib.SIP
open import lib.types.Sigma
open import lib.wild-cats.WildCat
open import lib.wild-cats.Adjoint
open import lib.wild-cats.OFS-filler-wc

-- Left adjoint preserves left class as soon as right adjoint preserves right class.

module lib.wild-cats.Adj-OFS-wc where

module _ {i₁ i₂ j₁ j₂} {C : WildCat {i₁} {j₁}} {D : WildCat {i₂} {j₂}}
  {L : Functor-wc C D} {R : Functor-wc D C} {a b : ob C} {x y : ob D} {f : hom C a b} {g : hom D x y} where

  private
    trips : Type j₁
    trips = [ r ∈ hom C a (obj R x) ] × [ s ∈ hom C b (obj R y) ] × (⟦ C ⟧ s ◻ f == ⟦ C ⟧ arr R g ◻ r)

  module SIP-trip where

    infixr 70 _=-fact-wc_
    _=-trip_ : trips → trips → Type j₁
    (r , s , H) =-trip (r' , s' , H') = [ (e₁ , e₂) ∈ (r == r') × (s == s') ] ×
      (ap (λ m → ⟦ C ⟧ m ◻ f) e₂ ∙ H' == H ∙' ap (λ m → ⟦ C ⟧ arr R g ◻ m) e₁)

    =-trip-id : {c : trips} → c =-trip c
    fst (=-trip-id {r , s , H}) = idp , idp
    snd (=-trip-id {r , s , H}) = idp

    module _ {c₁@(r , s , H) : trips} where

      trip-contr-aux :
        is-contr $
          [ (r' , e₁) ∈ Σ (hom C a (obj R x)) (λ r' → r == r') ] ×
            [ (s' , e₂) ∈ Σ (hom C b (obj R y)) (λ s' → s == s') ] ×
              (Σ (⟦ C ⟧ s' ◻ f == ⟦ C ⟧ arr R g ◻ r') (λ H' →
                ap (λ m → ⟦ C ⟧ m ◻ f) e₂ ∙ H' == H ∙' ap (λ m → ⟦ C ⟧ arr R g ◻ m) e₁))
      trip-contr-aux = equiv-preserves-level ((Σ-contr-red ⟨⟩)⁻¹) {{equiv-preserves-level ((Σ-contr-red ⟨⟩)⁻¹)}} 

      abstract
        trip-contr : is-contr ([ c₂ ∈ trips ] × (c₁ =-trip c₂))
        trip-contr = equiv-preserves-level lemma {{trip-contr-aux}}
          where
            lemma :
              ([ (r' , e₁) ∈ Σ (hom C a (obj R x)) (λ r' → r == r') ] ×
                [ (s' , e₂) ∈ Σ (hom C b (obj R y)) (λ s' → s == s') ] ×
                  (Σ (⟦ C ⟧ s' ◻ f == ⟦ C ⟧ arr R g ◻ r') (λ H' →
                    ap (λ m → ⟦ C ⟧ m ◻ f) e₂ ∙ H' == H ∙' ap (λ m → ⟦ C ⟧ arr R g ◻ m) e₁)))
                ≃
              [ c₂ ∈ trips ] × (c₁ =-trip c₂)
            lemma =
              equiv
               (λ ((r' , e₁) , (s' , e₂) , (H' , c)) → (r' , (s' , H')) , ((e₁ , e₂) , c))
               (λ ((r' , (s' , H')) , ((e₁ , e₂) , c)) → ((r' , e₁) , (s' , e₂) , (H' , c)))
               (λ _ → idp)
               λ _ → idp

      trip-ind : ∀ {k} (P : (c₂ : trips) → (c₁ =-trip c₂ → Type k))
        → P c₁ =-trip-id → {c₂ : trips} (e : c₁ =-trip c₂) → P c₂ e
      trip-ind P = ID-ind-map P trip-contr

      trip-to-== : {c₂ : trips} → c₁ =-trip c₂ → c₁ == c₂
      trip-to-== = trip-ind (λ c₂ _ → c₁ == c₂) idp

      trip-to-==-β : trip-to-== (=-trip-id {c₁}) == idp
      trip-to-==-β = ID-ind-map-β (λ c₂ _ → c₁ == c₂) trip-contr idp

      trip-from-== : {c₂ : trips} → c₁ == c₂ → c₁ =-trip c₂
      trip-from-== idp = =-trip-id

      trip-==-≃ : {c₂ : trips} → (c₁ == c₂) ≃ (c₁ =-trip c₂)
      trip-==-≃ = equiv trip-from-== trip-to-== aux1 aux2
        where abstract

          aux1 : {c₂ : trips} (e : c₁ =-trip c₂) → trip-from-== (trip-to-== e) == e
          aux1 = trip-ind (λ c₂ e → trip-from-== (trip-to-== e) == e) (ap trip-from-== trip-to-==-β)

          aux2 : {c₂ : trips} (e : c₁ == c₂) → trip-to-== (trip-from-== e) == e
          aux2 idp = trip-to-==-β 


  -- equivalence of commuting sqaures across an adjunction
  adj-sq-transfer-≃ : (α : Adjunction L R) →
    [ u ∈ hom D (obj L a) x ] × [ v ∈ hom D (obj L b) y ] × (⟦ D ⟧ v ◻ arr L f == ⟦ D ⟧ g ◻ u)
      ≃
    [ r ∈ hom C a (obj R x) ] × [ s ∈ hom C b (obj R y) ] × (⟦ C ⟧ s ◻ f == ⟦ C ⟧ arr R g ◻ r)
  fst (adj-sq-transfer-≃ α) (u , v , G) =
    –> (iso α) u  , (–> (iso α) v) , (nat-dom α f v ∙ ap (–> (iso α)) G ∙ ! (nat-cod α g u))
  snd (adj-sq-transfer-≃ α) = contr-map-is-equiv aux
    where abstract
      open SIP-trip
      aux : (c : [ r ∈ hom C a (obj R x) ] × [ s ∈ hom C b (obj R y) ] × (⟦ C ⟧ s ◻ f == ⟦ C ⟧ arr R g ◻ r)) →
        is-contr ([ (u , v , G) ∈
          [ u ∈ hom D (obj L a) x ] × [ v ∈ hom D (obj L b) y ] × (⟦ D ⟧ v ◻ arr L f == ⟦ D ⟧ g ◻ u)] ×
             (–> (iso α) u  , (–> (iso α) v) , (nat-dom α f v ∙ ap (–> (iso α)) G ∙ ! (nat-cod α g u))
               ==
             c))
      aux (r , s , H) = equiv-preserves-level (Σ-emap-r (λ (u , v , c) → trip-==-≃ ⁻¹)) {{aux2}}
        where abstract
        
          fib-sp : Type (lmax j₁ j₂)
          fib-sp =
            Σ (Σ (hom D (obj L a) x) (λ u →
              Σ (hom D (obj L b) y) (λ v → ⟦ D ⟧ v ◻ arr L f == ⟦ D ⟧ g ◻ u))) (λ (u , v , G) →
                (–> (iso α) u , –> (iso α) v , nat-dom α f v ∙ ap (–> (iso α)) G ∙ ! (nat-cod α g u))
                  =-trip
                (r , s , H))

          fib-sp-rearrange :
            [ (u , e₁) ∈ Σ (hom D (obj L a) x) (λ u → –> (iso α) u == r) ] ×
            [ (v , e₂) ∈ Σ (hom D (obj L b) y) (λ v → –> (iso α) v == s) ] ×
              (Σ (⟦ D ⟧ v ◻ arr L f == ⟦ D ⟧ g ◻ u) (λ G →
                ap (λ m → ⟦ C ⟧ m ◻ f) e₂ ∙ H
                  ==
                (nat-dom α f v ∙ ap (–> (iso α)) G ∙ ! (nat-cod α g u)) ∙' ap (λ m → ⟦ C ⟧ arr R g ◻ m) e₁))
              ≃
            fib-sp
          fib-sp-rearrange = equiv
            (λ ((u , e₁) , (v , e₂) , (G , c)) → (u , (v , G)) , ((e₁ , e₂) , c))
            (λ ((u , (v , G)) , ((e₁ , e₂) , c)) → ((u , e₁) , (v , e₂) , (G , c)))
            (λ _ → idp)
            λ _ → idp
            
          aux2 : is-contr fib-sp
          aux2 = equiv-preserves-level fib-sp-rearrange {{{!!}}}

  module _ (uC : is-univ-wc C) (tC : triangle-wc C) (pC : pentagon-wc C) where
