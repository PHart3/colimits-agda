{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import Coslice

-- preservation of groupoid structure by UndFun∼-to-==

module CosMap-conv {j} {A : Type j} where

open import SIP-CosMap public

open MapsCos A

module _ {ℓ₁ ℓ₂} {X : Coslice ℓ₁ j A} {Y : Coslice ℓ₂ j A} where

  abstract

    !cos-conv : {f₁ f₂ : X *→ Y} (h : < X > f₁ ∼ f₂) →
      ! (UndFun∼-to-== h) == UndFun∼-to-== (∼!-cos h)
    !cos-conv {f₁} = 
      UndFun-ind {f = f₁}
        (λ f₂ h → ! (UndFun∼-to-== h) == UndFun∼-to-== (∼!-cos h))
        (! (UndFun∼-β ∙ ap ! (! UndFun∼-β)))

    cos∘-conv : {f₁ f₃ f₂ : X *→ Y} (h₁ : < X > f₁ ∼ f₂) (h₂ : < X > f₂ ∼ f₃) →
      UndFun∼-to-== (h₁ ∼∘-cos h₂) ◃∎ =ₛ UndFun∼-to-== h₁ ◃∙ UndFun∼-to-== h₂ ◃∎
    cos∘-conv {f₁} {f₃} =
      UndFun-ind {f = f₁}
        (λ f₂ h₁ →
          ((h₂ : < X > f₂ ∼ f₃) →
            UndFun∼-to-== (h₁ ∼∘-cos h₂) ◃∎ =ₛ UndFun∼-to-== h₁ ◃∙ UndFun∼-to-== h₂ ◃∎))
        λ h₂ → 
          UndFun∼-to-== (cos∼id f₁ ∼∘-cos h₂) ◃∎
            =ₛ₁⟨ ap UndFun∼-to-== (∼∼-cos∼-to-== ((λ _ → idp) , (λ a → ap (λ p → p ∙ snd h₂ a) (aux (fst h₂ (str X a)))))) ⟩
          UndFun∼-to-== h₂ ◃∎
            =ₛ⟨ =ₛ-in (idp {a = UndFun∼-to-== h₂}) ⟩
          idp {a = f₁} ◃∙ UndFun∼-to-== h₂ ◃∎
            =ₛ₁⟨ 0 & 1 & ! UndFun∼-β ⟩
          UndFun∼-to-== (cos∼id f₁) ◃∙ UndFun∼-to-== h₂ ◃∎ ∎ₛ
          where
            aux : {a : A} {x : ty Y} (q : fst f₁ (str X a) == x) →
              ap (λ p → p ∙ snd f₁ a) (!-∙ idp q) ∙
              ∙-assoc (! q) idp (snd f₁ a)
                ==
              idp
            aux idp = idp
    
    cos∘-conv-tri : {f₁ f₂ f₃ f₄ : X *→ Y}
      {h₁ : < X > f₁ ∼ f₂} {h₂ : < X > f₂ ∼ f₃} {h₃ : < X > f₃ ∼ f₄} →
      UndFun∼-to-== h₁ ◃∙ UndFun∼-to-== h₂ ◃∙ UndFun∼-to-== h₃ ◃∎ =ₛ UndFun∼-to-== (h₁ ∼∘-cos h₂ ∼∘-cos h₃) ◃∎
    cos∘-conv-tri {h₁ = h₁} {h₂} {h₃} = 
      UndFun∼-to-== h₁ ◃∙ UndFun∼-to-== h₂ ◃∙ UndFun∼-to-== h₃ ◃∎
        =ₛ⟨ 1 & 2 & !ₛ (cos∘-conv h₂ h₃) ⟩
      UndFun∼-to-== h₁ ◃∙
      UndFun∼-to-== (h₂ ∼∘-cos h₃) ◃∎
        =ₛ⟨ !ₛ (cos∘-conv h₁ (h₂ ∼∘-cos h₃)) ⟩
      UndFun∼-to-== (h₁ ∼∘-cos h₂ ∼∘-cos h₃) ◃∎ ∎ₛ

    cos∘-conv-pent : {f₁ f₂ f₃ f₄ f₅ f₆ : X *→ Y}
      {h₁ : < X > f₁ ∼ f₂} {h₂ : < X > f₂ ∼ f₃} {h₃ : < X > f₃ ∼ f₄}
      {h₄ : < X > f₄ ∼ f₅} {h₅ : < X > f₅ ∼ f₆}  →
      UndFun∼-to-== h₁ ◃∙ UndFun∼-to-== h₂ ◃∙ UndFun∼-to-== h₃ ◃∙ UndFun∼-to-== h₄ ◃∙ UndFun∼-to-== h₅ ◃∎
        =ₛ
      UndFun∼-to-== (h₁ ∼∘-cos h₂ ∼∘-cos h₃ ∼∘-cos h₄ ∼∘-cos h₅) ◃∎
    cos∘-conv-pent {h₁ = h₁} {h₂} {h₃} {h₄} {h₅} = 
      UndFun∼-to-== h₁ ◃∙ UndFun∼-to-== h₂ ◃∙ UndFun∼-to-== h₃ ◃∙ UndFun∼-to-== h₄ ◃∙ UndFun∼-to-== h₅ ◃∎
        =ₛ⟨ 2 & 3 & cos∘-conv-tri ⟩
      UndFun∼-to-== h₁ ◃∙ UndFun∼-to-== h₂ ◃∙ UndFun∼-to-== (h₃ ∼∘-cos h₄ ∼∘-cos h₅) ◃∎
        =ₛ⟨ cos∘-conv-tri ⟩
      UndFun∼-to-== (h₁ ∼∘-cos h₂ ∼∘-cos h₃ ∼∘-cos h₄ ∼∘-cos h₅) ◃∎ ∎ₛ

    cos∘-conv-sept : {f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ : X *→ Y}
      {h₁ : < X > f₁ ∼ f₂} {h₂ : < X > f₂ ∼ f₃} {h₃ : < X > f₃ ∼ f₄} {h₄ : < X > f₄ ∼ f₅}
      {h₅ : < X > f₅ ∼ f₆} {h₆ : < X > f₆ ∼ f₇} {h₇ : < X > f₇ ∼ f₈} →
      UndFun∼-to-== h₁ ◃∙ UndFun∼-to-== h₂ ◃∙ UndFun∼-to-== h₃ ◃∙
      UndFun∼-to-== h₄ ◃∙ UndFun∼-to-== h₅ ◃∙ UndFun∼-to-== h₆ ◃∙ UndFun∼-to-== h₇ ◃∎
        =ₛ
      UndFun∼-to-== (h₁ ∼∘-cos h₂ ∼∘-cos h₃ ∼∘-cos h₄ ∼∘-cos h₅ ∼∘-cos h₆ ∼∘-cos h₇) ◃∎
    cos∘-conv-sept {h₁ = h₁} {h₂} {h₃} {h₄} {h₅} {h₆} {h₇} = 
      UndFun∼-to-== h₁ ◃∙ UndFun∼-to-== h₂ ◃∙ UndFun∼-to-== h₃ ◃∙ UndFun∼-to-== h₄ ◃∙
      UndFun∼-to-== h₅ ◃∙ UndFun∼-to-== h₆ ◃∙ UndFun∼-to-== h₇ ◃∎
        =ₛ⟨ 2 & 5 & cos∘-conv-pent ⟩
      UndFun∼-to-== h₁ ◃∙ UndFun∼-to-== h₂ ◃∙ UndFun∼-to-== (h₃ ∼∘-cos h₄ ∼∘-cos h₅ ∼∘-cos h₆ ∼∘-cos h₇) ◃∎
        =ₛ⟨ cos∘-conv-tri ⟩
      UndFun∼-to-== (h₁ ∼∘-cos h₂ ∼∘-cos h₃ ∼∘-cos h₄ ∼∘-cos h₅ ∼∘-cos h₆ ∼∘-cos h₇) ◃∎ ∎ₛ

module _ {ℓ₁ ℓ₂ ℓ₃} {X : Coslice ℓ₁ j A} {Y : Coslice ℓ₂ j A} {Z : Coslice ℓ₃ j A} where

  abstract

    whisk-cos-conv-r : {f₁ : X *→ Y} {f₂ f₂' : Y *→ Z} (h : < Y > f₂ ∼ f₂') →
      ap (λ m → m ∘* f₁) (UndFun∼-to-== h) == UndFun∼-to-== (pre-∘*-∼ f₁ h)
    whisk-cos-conv-r {f₁} {f₂} =
      UndFun-ind {f = f₂}
        (λ f₂' h → ap (λ m → m ∘* f₁) (UndFun∼-to-== h) == UndFun∼-to-== (pre-∘*-∼ f₁ h))
        (ap (ap (λ m → m ∘* f₁)) UndFun∼-β ∙
        ! (UndFun∼-β) ∙
        ap UndFun∼-to-== (∼∼-cos∼-to-== ((λ _ → idp) , (λ a → aux (snd f₁ a)))))
        where
          aux : {a : A} {x : ty Y} (q : x == str Y a) →
            idp
              ==
            (ap (λ p → p ∙ snd f₂ a) (hmtpy-nat-!-sq (λ _ → idp) q) ∙
            ∙-assoc (ap (λ z → fst f₂ z) q) idp (snd f₂ a)) ∙ idp
          aux idp = idp

    whisk-cos-conv-l : {f₁ : Y *→ Z} {f₂ f₂' : X *→ Y} (h : < X > f₂ ∼ f₂') →
      ap (λ m → f₁ ∘* m) (UndFun∼-to-== h) == UndFun∼-to-== (post-∘*-∼ f₁ h)
    whisk-cos-conv-l {f₁} {f₂} = 
      UndFun-ind {f = f₂}
        (λ f₂' h → ap (λ m → f₁ ∘* m) (UndFun∼-to-== h) == UndFun∼-to-== (post-∘*-∼ f₁ h))
        (ap (ap (λ m → f₁ ∘* m)) UndFun∼-β ∙ ! UndFun∼-β)

