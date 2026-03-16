{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import Coslice

-- preservation of groupoid structure by UndHom∼-to-==

module CosMap-conv {j} {A : Type j} where

open import SIP-CosMap public

open MapsCos A

module _ {ℓ₁ ℓ₂} {X : Coslice ℓ₁ j A} {Y : Coslice ℓ₂ j A} where

  abstract

    !cos-conv : {f₁ f₂ : X *→ Y} (h : < X > f₁ ∼ f₂) →
      ! (UndHom∼-to-== h) == UndHom∼-to-== (∼!-cos h)
    !cos-conv {f₁} = 
      UndHom-ind {f = f₁}
        (λ f₂ h → ! (UndHom∼-to-== h) == UndHom∼-to-== (∼!-cos h))
        (! (UndHom∼-β ∙ ap ! (! UndHom∼-β)))

    cos∘-conv : {f₁ f₃ f₂ : X *→ Y} (h₁ : < X > f₁ ∼ f₂) (h₂ : < X > f₂ ∼ f₃) →
      UndHom∼-to-== (h₁ ∼∘-cos h₂) ◃∎ =ₛ UndHom∼-to-== h₁ ◃∙ UndHom∼-to-== h₂ ◃∎
    cos∘-conv {f₁} {f₃} =
      UndHom-ind {f = f₁}
        (λ f₂ h₁ →
          ((h₂ : < X > f₂ ∼ f₃) →
            UndHom∼-to-== (h₁ ∼∘-cos h₂) ◃∎ =ₛ UndHom∼-to-== h₁ ◃∙ UndHom∼-to-== h₂ ◃∎))
        λ h₂ → 
          UndHom∼-to-== (cos∼id f₁ ∼∘-cos h₂) ◃∎
            =ₛ₁⟨ ap UndHom∼-to-== (∼∼-cos∼-to-== ((λ _ → idp) , (λ a → ap (λ p → p ∙ snd h₂ a) (aux (fst h₂ (str X a)))))) ⟩
          UndHom∼-to-== h₂ ◃∎
            =ₛ⟨ =ₛ-in (idp {a = UndHom∼-to-== h₂}) ⟩
          idp {a = f₁} ◃∙ UndHom∼-to-== h₂ ◃∎
            =ₛ₁⟨ 0 & 1 & ! UndHom∼-β ⟩
          UndHom∼-to-== (cos∼id f₁) ◃∙ UndHom∼-to-== h₂ ◃∎ ∎ₛ
          where
            aux : {a : A} {x : ty Y} (q : fst f₁ (str X a) == x) →
              ap (λ p → p ∙ snd f₁ a) (!-∙ idp q) ∙
              ∙-assoc (! q) idp (snd f₁ a)
                ==
              idp
            aux idp = idp
    
    cos∘-conv-tri : {f₁ f₂ f₃ f₄ : X *→ Y}
      {h₁ : < X > f₁ ∼ f₂} {h₂ : < X > f₂ ∼ f₃} {h₃ : < X > f₃ ∼ f₄} →
      UndHom∼-to-== h₁ ◃∙ UndHom∼-to-== h₂ ◃∙ UndHom∼-to-== h₃ ◃∎ =ₛ UndHom∼-to-== (h₁ ∼∘-cos h₂ ∼∘-cos h₃) ◃∎
    cos∘-conv-tri {h₁ = h₁} {h₂} {h₃} = 
      UndHom∼-to-== h₁ ◃∙ UndHom∼-to-== h₂ ◃∙ UndHom∼-to-== h₃ ◃∎
        =ₛ⟨ 1 & 2 & !ₛ (cos∘-conv h₂ h₃) ⟩
      UndHom∼-to-== h₁ ◃∙
      UndHom∼-to-== (h₂ ∼∘-cos h₃) ◃∎
        =ₛ⟨ !ₛ (cos∘-conv h₁ (h₂ ∼∘-cos h₃)) ⟩
      UndHom∼-to-== (h₁ ∼∘-cos h₂ ∼∘-cos h₃) ◃∎ ∎ₛ

    cos∘-conv-pent : {f₁ f₂ f₃ f₄ f₅ f₆ : X *→ Y}
      {h₁ : < X > f₁ ∼ f₂} {h₂ : < X > f₂ ∼ f₃} {h₃ : < X > f₃ ∼ f₄}
      {h₄ : < X > f₄ ∼ f₅} {h₅ : < X > f₅ ∼ f₆}  →
      UndHom∼-to-== h₁ ◃∙ UndHom∼-to-== h₂ ◃∙ UndHom∼-to-== h₃ ◃∙ UndHom∼-to-== h₄ ◃∙ UndHom∼-to-== h₅ ◃∎
        =ₛ
      UndHom∼-to-== (h₁ ∼∘-cos h₂ ∼∘-cos h₃ ∼∘-cos h₄ ∼∘-cos h₅) ◃∎
    cos∘-conv-pent {h₁ = h₁} {h₂} {h₃} {h₄} {h₅} = 
      UndHom∼-to-== h₁ ◃∙ UndHom∼-to-== h₂ ◃∙ UndHom∼-to-== h₃ ◃∙ UndHom∼-to-== h₄ ◃∙ UndHom∼-to-== h₅ ◃∎
        =ₛ⟨ 2 & 3 & cos∘-conv-tri ⟩
      UndHom∼-to-== h₁ ◃∙ UndHom∼-to-== h₂ ◃∙ UndHom∼-to-== (h₃ ∼∘-cos h₄ ∼∘-cos h₅) ◃∎
        =ₛ⟨ cos∘-conv-tri ⟩
      UndHom∼-to-== (h₁ ∼∘-cos h₂ ∼∘-cos h₃ ∼∘-cos h₄ ∼∘-cos h₅) ◃∎ ∎ₛ

    cos∘-conv-sept : {f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ : X *→ Y}
      {h₁ : < X > f₁ ∼ f₂} {h₂ : < X > f₂ ∼ f₃} {h₃ : < X > f₃ ∼ f₄} {h₄ : < X > f₄ ∼ f₅}
      {h₅ : < X > f₅ ∼ f₆} {h₆ : < X > f₆ ∼ f₇} {h₇ : < X > f₇ ∼ f₈} →
      UndHom∼-to-== h₁ ◃∙ UndHom∼-to-== h₂ ◃∙ UndHom∼-to-== h₃ ◃∙
      UndHom∼-to-== h₄ ◃∙ UndHom∼-to-== h₅ ◃∙ UndHom∼-to-== h₆ ◃∙ UndHom∼-to-== h₇ ◃∎
        =ₛ
      UndHom∼-to-== (h₁ ∼∘-cos h₂ ∼∘-cos h₃ ∼∘-cos h₄ ∼∘-cos h₅ ∼∘-cos h₆ ∼∘-cos h₇) ◃∎
    cos∘-conv-sept {h₁ = h₁} {h₂} {h₃} {h₄} {h₅} {h₆} {h₇} = 
      UndHom∼-to-== h₁ ◃∙ UndHom∼-to-== h₂ ◃∙ UndHom∼-to-== h₃ ◃∙ UndHom∼-to-== h₄ ◃∙
      UndHom∼-to-== h₅ ◃∙ UndHom∼-to-== h₆ ◃∙ UndHom∼-to-== h₇ ◃∎
        =ₛ⟨ 2 & 5 & cos∘-conv-pent ⟩
      UndHom∼-to-== h₁ ◃∙ UndHom∼-to-== h₂ ◃∙ UndHom∼-to-== (h₃ ∼∘-cos h₄ ∼∘-cos h₅ ∼∘-cos h₆ ∼∘-cos h₇) ◃∎
        =ₛ⟨ cos∘-conv-tri ⟩
      UndHom∼-to-== (h₁ ∼∘-cos h₂ ∼∘-cos h₃ ∼∘-cos h₄ ∼∘-cos h₅ ∼∘-cos h₆ ∼∘-cos h₇) ◃∎ ∎ₛ

module _ {ℓ₁ ℓ₂ ℓ₃} {X : Coslice ℓ₁ j A} {Y : Coslice ℓ₂ j A} {Z : Coslice ℓ₃ j A} where

  abstract

    whisk-cos-conv-r : {f₁ : X *→ Y} {f₂ f₂' : Y *→ Z} (h : < Y > f₂ ∼ f₂') →
      ap (λ m → m ∘* f₁) (UndHom∼-to-== h) == UndHom∼-to-== (pre-∘*-∼ f₁ h)
    whisk-cos-conv-r {f₁} {f₂} =
      UndHom-ind {f = f₂}
        (λ f₂' h → ap (λ m → m ∘* f₁) (UndHom∼-to-== h) == UndHom∼-to-== (pre-∘*-∼ f₁ h))
        (ap (ap (λ m → m ∘* f₁)) UndHom∼-β ∙
        ! (UndHom∼-β) ∙
        ap UndHom∼-to-== (∼∼-cos∼-to-== ((λ _ → idp) , (λ a → aux (snd f₁ a)))))
        where
          aux : {a : A} {x : ty Y} (q : x == str Y a) →
            idp
              ==
            (ap (λ p → p ∙ snd f₂ a) (hmtpy-nat-!-sq (λ _ → idp) q) ∙
            ∙-assoc (ap (λ z → fst f₂ z) q) idp (snd f₂ a)) ∙ idp
          aux idp = idp

    whisk-cos-conv-l : {f₁ : Y *→ Z} {f₂ f₂' : X *→ Y} (h : < X > f₂ ∼ f₂') →
      ap (λ m → f₁ ∘* m) (UndHom∼-to-== h) == UndHom∼-to-== (post-∘*-∼ f₁ h)
    whisk-cos-conv-l {f₁} {f₂} = 
      UndHom-ind {f = f₂}
        (λ f₂' h → ap (λ m → f₁ ∘* m) (UndHom∼-to-== h) == UndHom∼-to-== (post-∘*-∼ f₁ h))
        (ap (ap (λ m → f₁ ∘* m)) UndHom∼-β ∙ ! UndHom∼-β)

