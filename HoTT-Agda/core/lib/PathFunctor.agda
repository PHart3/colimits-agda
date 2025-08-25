{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.PathGroupoid

module lib.PathFunctor where

{- Nondependent stuff -}
module _ {i j} {A : Type i} {B : Type j} (f : A → B) where

  !-ap : {x y : A} (p : x == y)
    → ! (ap f p) == ap f (! p)
  !-ap idp = idp

  ap-! : {x y : A} (p : x == y)
    → ap f (! p) == ! (ap f p)
  ap-! idp = idp

  ap-!-inv : {x y : A} (p : x == y)
    → ap f p ∙ ap f (! p) == idp
  ap-!-inv idp = idp

  !-ap-inv : {x y : A} (p : x == y)
    → ap f p ∙ ! (ap f p) == idp
  !-ap-inv idp = idp
  
  ap-!-inv-l : {x y : A} (p : x == y)
    → ap f (! p) ∙ ap f p == idp
  ap-!-inv-l idp = idp
  
  ∙-ap : {x y z : A} (p : x == y) (q : y == z)
    → ap f p ∙ ap f q == ap f (p ∙ q)
  ∙-ap idp q = idp

  ap-∙ : {x y z : A} (p : x == y) (q : y == z)
    → ap f (p ∙ q) == ap f p ∙ ap f q
  ap-∙ idp q = idp

  ap-∙◃ : {x y z : A} (p : x == y) (q : y == z)
    → ap f (p ∙ q) ◃∎ =ₛ ap f p ◃∙ ap f q ◃∎
  ap-∙◃ idp q = =ₛ-in idp

  ap-!-!-∙◃ : {x y z : A} (p : x == y) (q : x == z)
    → ap f (! (! p ∙ q)) ◃∎ =ₛ ! (ap f q) ◃∙ ap f p ◃∎
  ap-!-!-∙◃ idp idp = =ₛ-in idp

  !-ap-∙-!∙ : {x y z w : A} (p₁ : x == y) (p₂ : y == z) (p₃ : w == z)
    → ! (ap f (p₁ ∙ p₂ ∙ ! p₃)) ◃∎ =ₛ ap f p₃ ◃∙ ! (ap f p₂) ◃∙ ! (ap f p₁) ◃∎ 
  !-ap-∙-!∙ idp idp idp = =ₛ-in idp

  !ap-∙=∙-ap : {x y z : A} (p : x == y) (q : y == z)
    → ! (ap-∙ p q) == ∙-ap p q
  !ap-∙=∙-ap idp q = idp

  ∙∙-ap : {x y z w : A} (p : x == y) (q : y == z) (r : z == w)
    → ap f p ∙ ap f q ∙ ap f r == ap f (p ∙ q ∙ r)
  ∙∙-ap idp idp r = idp

  ap-∙∙ : {x y z w : A} (p : x == y) (q : y == z) (r : z == w)
    → ap f (p ∙ q ∙ r) == ap f p ∙ ap f q ∙ ap f r
  ap-∙∙ idp idp r = idp

  ap-!∙∙ : {x y z w : A} (p : y == x) (q : y == z) (r : z == w)
    → ap f (! p ∙ q ∙ r) == ! (ap f p) ∙ ap f q ∙ ap f r
  ap-!∙∙ idp idp r = idp

  ap-∙∙∙ : {x y z w t : A} (p : x == y) (q : y == z) (r : z == w) (s : w == t)
    → ap f (p ∙ q ∙ r ∙ s) == ap f p ∙ ap f q ∙ ap f r ∙ ap f s
  ap-∙∙∙ idp idp idp s = idp

  ∙'-ap : {x y z : A} (p : x == y) (q : y == z)
    → ap f p ∙' ap f q == ap f (p ∙' q)
  ∙'-ap p idp = idp

  ap3-!-ap-!-rid : ∀ {k} {C : Type k} (g : B → C) {x y : A} (p₁ : x == y)
    {e : f x == f y} (p₂ : ap f p₁ == e) →
    ap (ap g) (ap (λ p → p) (! (ap-! p₁ ∙ ap ! (p₂ ∙ idp))))
    ==
    ap (λ p → ap g (! p)) (! p₂) ∙ ap (ap g) (!-ap p₁)
  ap3-!-ap-!-rid _ idp idp = idp
  
{- Dependent stuff -}
module _ {i j} {A : Type i} {B : A → Type j} (f : Π A B) where

  apd-∙ : {x y z : A} (p : x == y) (q : y == z)
    → apd f (p ∙ q) == apd f p ∙ᵈ apd f q
  apd-∙ idp idp = idp

  apd-∙' : {x y z : A} (p : x == y) (q : y == z)
    → apd f (p ∙' q) == apd f p ∙'ᵈ apd f q
  apd-∙' idp idp = idp

  apd-! : {x y : A} (p : x == y)
    → apd f (! p) == !ᵈ (apd f p)
  apd-! idp = idp

{- Over stuff -}
module _ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
  (f : {a : A} → B a → C a) where

  ap↓-◃ : {x y z : A} {u : B x} {v : B y} {w : B z}
    {p : x == y} {p' : y == z} (q : u == v [ B ↓ p ]) (r : v == w [ B ↓ p' ])
    → ap↓ f (q ◃ r) == ap↓ f q ◃ ap↓ f r
  ap↓-◃ {p = idp} {p' = idp} idp idp = idp

  ap↓-▹! : {x y z : A} {u : B x} {v : B y} {w : B z}
    {p : x == y} {p' : z == y} (q : u == v [ B ↓ p ]) (r : w == v [ B ↓ p' ])
    → ap↓ f (q ▹! r) == ap↓ f q ▹! ap↓ f r
  ap↓-▹! {p = idp} {p' = idp} idp idp = idp

{- Fuse and unfuse -}

module _ {i j} {A : Type i} {B : Type j} (g : A → B) where

  !-ap-∙ : {x y : A} (p : x == y) {z : A} (r : x == z) → ! (ap g p) ∙ ap g r == ap g (! p ∙ r)
  !-ap-∙ idp r = idp

  ap-∙! : {x y : A} (p : x == y) {z : A} (r : x == z) → ap g (! p ∙ r) == ! (ap g p) ∙ ap g r
  ap-∙! idp r = idp

  !r-ap-∙ : {x y z : A} (p₁ : x == y) (p₂ : z == y)
    → ap g p₁ ∙ ! (ap g p₂) == ap g (p₁ ∙ ! p₂)
  !r-ap-∙ idp idp = idp

  ap-!-∙-ap : ∀ {k} {C : Type k} (h : C → A) {y z : C} {x : A} (q : y == z) (p : x == h y) 
    → ap g (! p) ∙ ap g (p ∙ ap h q) == ap g (ap h q)
  ap-!-∙-ap h q idp = idp 

  !-ap-∙-s : {x y : A} (p : x == y) {z : A} {r : x == z} {w : B} {s : g z == w}
    → ! (ap g p) ∙ ap g r ∙ s == ap g (! p ∙ r) ∙ s
  !-ap-∙-s idp = idp

  !-∙-ap-∙'-! : {x w : B} {y z : A} (p : x == g y) (q : y == z) (r : w == g z)
    → ! (p ∙ ap g q ∙' ! r) == r ∙ ap g (! q) ∙' ! p
  !-∙-ap-∙'-! idp q idp = !-ap g q

  !-∙-ap-∙'-!-coher : {y : A} {x : B} (p : x == g y) →
    ! (!-inv-r p) ∙ ap (_∙_ p) (! (∙'-unit-l (! p)))
      ==
    ap ! (! (!-inv-r p) ∙ ap (_∙_ p) (! (∙'-unit-l (! p)))) ∙
    !-∙-ap-∙'-! p idp p
  !-∙-ap-∙'-!-coher idp = idp

  idp-ap-!-!-∙-∙' : {x y : A} (p : x == y)
    → idp == ap g (! p) ∙ ap g (p ∙ idp ∙' ! p) ∙' ! (ap g (! p))
  idp-ap-!-!-∙-∙' idp = idp  

  idp-ap-!-!-∙-∙'-coher : {x y : A} (p : x == y) →
    ! (!-inv-r (ap g (! p))) ∙
    ap (_∙_ (ap g (! p))) (! (∙'-unit-l (! (ap g (! p)))))
      ==
    idp-ap-!-!-∙-∙' p ∙
    ! (ap (λ q → ap g (! p) ∙ ap g q ∙' ! (ap g (! p)))
      (! (!-inv-r p) ∙ ap (_∙_ p) (! (∙'-unit-l (! p))))) ∙ idp
  idp-ap-!-!-∙-∙'-coher idp = idp

module _ {i j k} {A : Type i} {B : Type j} {C : Type k} (g : B → C) (f : A → B) where

  ∘-ap : {x y : A} (p : x == y) → ap g (ap f p) == ap (g ∘ f) p
  ∘-ap idp = idp

  ap-∘ : {x y : A} (p : x == y) → ap (g ∘ f) p == ap g (ap f p)
  ap-∘ idp = idp

  ap-∘-∙ : {x y : A} (p : x == y) {b : B} (q : f y == b)
    → ap g (ap f p ∙ q) == ap (g ∘ f) p ∙ ap g q
  ap-∘-∙ idp q = idp

  ∘-ap-! : {x y : A} (p : x == y) → ap g (! (ap f p)) == ! (ap (g ∘ f) p)
  ∘-ap-! idp = idp

  ap-∘-! : {x y : A} (p : x == y) → ap g (ap f (! p)) == ! (ap g (ap f p))
  ap-∘-! idp = idp

  ap-∘-∘ : ∀ {l} {D : Type l} (h : D → A) {x y : D} (p : x == y)
    → ap (g ∘ f ∘ h) p == ap g (ap f (ap h p))
  ap-∘-∘ h idp = idp

  ap-ap-∙-∙ : {x y : A} (p₁ : x == y) {b : B} (p₂ : f y == b) {c : C} (p₃ : g b == c)
    → ap g (ap f p₁ ∙ p₂) ∙ p₃ == ap g (ap f p₁) ∙ ap g p₂ ∙ p₃
  ap-ap-∙-∙ idp p₂ p₃ = idp

  !ap-∘=∘-ap : {x y : A} (p : x == y) → ! (ap-∘ p) == ∘-ap p
  !ap-∘=∘-ap idp = idp

  ap-∘2-ap-! : {x y : A} (v : x == y)
    {c : g (f (y)) == g (f x)} (e : ap g (! (ap f v)) == c) 
    → (! (ap (λ q → q) (ap-∘ (! v) ∙
      ap (ap g) (ap-! f v))) ∙ idp) ∙
      ap-∘ (! v) ∙
      ap (ap g) (ap (λ p → p) (ap-! f v)) ∙ e
      == e
  ap-∘2-ap-! idp e = idp 

  ap-∘2-ap-∙ : {x y : A} (v : x == y) → 
    ! (ap (ap g) (ap-∙ f v idp ∙ idp)) ∙
    ! (ap (λ q → q) (ap-∘ (v ∙ idp))) ∙
    ! (! (ap (λ p → p ∙ idp) (ap-∘ v)) ∙ ! (ap-∙ (g ∘ f) v idp))
      ==
    ap-∙ g (ap f v) idp ∙ idp
  ap-∘2-ap-∙ idp = idp

  ap-∘-rev : {w : C} {z : B} {x y : A} (p : x == y) (q : f x == z) (r : g (f y) == w) →
    ! (ap g q) ∙ ap (g ∘ f) p ∙ r == ! (ap g (! (ap f p) ∙ q)) ∙ r
  ap-∘-rev idp q r = idp

  !-ap-ap-∘-ap-∙ : {x y : A} (q : x == y) {w : B} {z : C} {r : f y == w} {s : g w == z} {b : B} (p : f x == b) 
    → ! (ap g p) ∙ (ap (g ∘ f) q) ∙ (ap g r) ∙ s == ap g (! p ∙ ap f q ∙ r) ∙ s
  !-ap-ap-∘-ap-∙ idp {r = r} {s = s} p = !-ap-∙-s g p {r = r} {s = s}

  ap-cmp-rev-◃ : {x y : A} (q : x == y) {z : B} {p : f x == z}
    → ap g ((! (ap f q)) ∙ p) ◃∎ =ₛ ! (ap (g ∘ f) q) ◃∙ ap g p ◃∎
  ap-cmp-rev-◃ idp = =ₛ-in idp

  ap-cmp-rev-◃2 : {x y : A} (q : x == y) {z : B} (p : f x == z)
    → ap g (ap f (! q) ∙ p) ◃∎ =ₛ ! (ap (g ∘ f) q) ◃∙ ap g p ◃∎
  ap-cmp-rev-◃2 idp p = =ₛ-in idp

  inv-canc-cmp : {a b : A} (p : a == b) {z : B} (S : f a == z) {w : C} (gₚ : g z == w)
    → ! (ap (g ∘ f) p) ∙ (ap g S ∙ gₚ) ∙ ! (ap g (! (ap f p) ∙ S ∙ idp) ∙ gₚ) == idp
  inv-canc-cmp idp idp idp = idp

  ap-!-∘-rid-coher : {x y : A} (p : x == y) →
    ! (ap (λ q → ap g (ap f p) ∙ q) (ap-∘ (! p) ∙ ap (ap g) (ap-! f p))) ∙ idp
      ==
    ap-!-inv g (ap f p) ∙ ! (cmp-inv-r p)
  ap-!-∘-rid-coher idp = idp

  ap-!-∘-∙-rid-coher : {x y : A} (p : x == y) →
    ! (! (cmp-inv-r p) ∙ ! (ap (λ q → q ∙ ap (g ∘ f) (! p)) (ap-∘ p)) ∙ ! (ap-∙ (g ∘ f) p (! p))) ∙ idp
      ==
    ap (ap (g ∘ f)) (!-inv-r p) ∙ idp
  ap-!-∘-∙-rid-coher idp = idp

{- ap of idf -}
ap-idf : ∀ {i} {A : Type i} {u v : A} (p : u == v) → ap (idf A) p == p
ap-idf idp = idp

ap-idf-inv-l : ∀ {i} {A : Type i} {u v : A} (p : u == v) → ap (λ v → v) (! p) ∙ p == idp
ap-idf-inv-l idp = idp

inv-l-ap-idf : ∀ {i} {A : Type i} {u v : A} (p : u == v) → ! p ∙ ap (λ v → v) p == idp
inv-l-ap-idf idp = idp

ap-idf-inv-r : ∀ {i} {A : Type i} {u v : A} (p : u == v) → ap (λ v → v) p ∙ ! p == idp
ap-idf-inv-r idp = idp

ap-idf-inv-r' : ∀ {i} {A : Type i} {u v : A} (p : u == v) → ap (λ v → v) p ∙' ! p == idp
ap-idf-inv-r' idp = idp

{- Functoriality of [coe] -}
coe-∙ : ∀ {i} {A B C : Type i} (p : A == B) (q : B == C) (a : A)
  → coe (p ∙ q) a == coe q (coe p a)
coe-∙ idp q a = idp

coe-! : ∀ {i} {A B : Type i} (p : A == B) (b : B) → coe (! p) b == coe! p b
coe-! idp b = idp

coe!-inv-r : ∀ {i} {A B : Type i} (p : A == B) (b : B)
  → coe p (coe! p b) == b
coe!-inv-r idp b = idp

coe!-inv-l : ∀ {i} {A B : Type i} (p : A == B) (a : A)
  → coe! p (coe p a) == a
coe!-inv-l idp a = idp

coe-inv-adj : ∀ {i} {A B : Type i} (p : A == B) (a : A) →
  ap (coe p) (coe!-inv-l p a) == coe!-inv-r p (coe p a)
coe-inv-adj idp a = idp

coe!-inv-adj : ∀ {i} {A B : Type i} (p : A == B) (b : B) →
  ap (coe! p) (coe!-inv-r p b) == coe!-inv-l p (coe! p b)
coe!-inv-adj idp b = idp

coe-ap-! : ∀ {i j} {A : Type i} (P : A → Type j) {a b : A} (p : a == b) (x : P b)
  → coe (ap P (! p)) x == coe! (ap P p) x
coe-ap-! P idp x = idp

{- Functoriality of transport -}
transp-∙ : ∀ {i j} {A : Type i} {B : A → Type j} {x y z : A}
  (p : x == y) (q : y == z) (b : B x)
  → transport B (p ∙ q) b == transport B q (transport B p b)
transp-∙ idp _ _ = idp

transp-∙' : ∀ {i j} {A : Type i} {B : A → Type j} {x y z : A}
  (p : x == y) (q : y == z) (b : B x)
  → transport B (p ∙' q) b == transport B q (transport B p b)
transp-∙' _ idp _ = idp

{- Naturality of transport -}
transp-naturality : ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
  (u : {a : A} → B a → C a)
  {a₀ a₁ : A} (p : a₀ == a₁)
  → u ∘ transport B p == transport C p ∘ u
transp-naturality f idp = idp

transp-idp : ∀ {i j} {A : Type i} {B : Type j}
  (f : A → B) {x y : A} (p : x == y)
  → transport (λ a → f a == f a) p idp == idp
transp-idp f idp = idp

module _ {i j} {A : Type i} {B : Type j} where

  ap-transp : (f g : A → B) {a₀ a₁ : A} (p : a₀ == a₁) (h : f a₀ == g a₀)
    → h ∙ ap g p == ap f p ∙ transport (λ a → f a == g a) p h
  ap-transp f g p@idp h = ∙-unit-r h

  ap-transp-idp : (f : A → B) {a₀ a₁ : A} (p : a₀ == a₁) →
    ap-transp f f p idp ◃∙
    ap (ap f p ∙_) (transp-idp f p) ◃∙
    ∙-unit-r (ap f p) ◃∎
      =ₛ
    []
  ap-transp-idp f p@idp = =ₛ-in idp

{- for functions with two arguments -}
module _ {i j k} {A : Type i} {B : Type j} {C : Type k} (f : A → B → C) where

  ap2 : {x y : A} {w z : B}
    → (x == y) → (w == z) → f x w == f y z
  ap2 idp idp = idp

  ap2-out : {x y : A} {w z : B} (p : x == y) (q : w == z)
    → ap2 p q ◃∎ =ₛ ap (λ u → f u w) p ◃∙ ap (λ v → f y v) q ◃∎
  ap2-out idp idp = =ₛ-in idp

  ap2-out' : {x y : A} {w z : B} (p : x == y) (q : w == z)
    → ap2 p q ◃∎ =ₛ ap (λ u → f x u) q ◃∙ ap (λ v → f v z) p ◃∎
  ap2-out' idp idp = =ₛ-in idp

  ap2-idp-l : {x : A} {w z : B} (q : w == z)
    → ap2 (idp {a = x}) q == ap (f x) q
  ap2-idp-l idp = idp

  ap2-idp-r : {x y : A} {w : B} (p : x == y)
    → ap2 p (idp {a = w}) == ap (λ z → f z w) p
  ap2-idp-r idp = idp

  ap2-! : {a a' : A} {b b' : B} (p : a == a') (q : b == b')
    → ap2 (! p) (! q) == ! (ap2 p q)
  ap2-! idp idp = idp

  !-ap2 : {a a' : A} {b b' : B} (p : a == a') (q : b == b')
    → ! (ap2 p q) == ap2 (! p) (! q)
  !-ap2 idp idp = idp

  ap2-∙ : {a a' a'' : A} {b b' b'' : B}
    (p : a == a') (p' : a' == a'')
    (q : b == b') (q' : b' == b'')
    → ap2 (p ∙ p') (q ∙ q') == ap2 p q ∙ ap2 p' q'
  ap2-∙ idp p' idp q' = idp

  ∙-ap2 : {a a' a'' : A} {b b' b'' : B}
    (p : a == a') (p' : a' == a'')
    (q : b == b') (q' : b' == b'')
    → ap2 p q ∙ ap2 p' q' == ap2 (p ∙ p') (q ∙ q')
  ∙-ap2 idp p' idp q' = idp

{- ap2 lemmas -}
module _ {i j} {A : Type i} {B : Type j} where

  ap2-fst : {x y : A} {w z : B} (p : x == y) (q : w == z)
    → ap2 (curry fst) p q == p
  ap2-fst idp idp = idp

  ap2-snd : {x y : A} {w z : B} (p : x == y) (q : w == z)
    → ap2 (curry snd) p q == q
  ap2-snd idp idp = idp

  ap-ap2 : ∀ {k l} {C : Type k} {D : Type l}
    (g : C → D) (f : A → B → C) {x y : A} {w z : B}
    (p : x == y) (q : w == z)
    → ap g (ap2 f p q) == ap2 (λ a b → g (f a b)) p q
  ap-ap2 g f idp idp = idp

  ap2-ap-l : ∀ {k l} {C : Type k} {D : Type l}
    (g : B → C → D) (f : A → B) {x y : A} {w z : C}
    (p : x == y) (q : w == z)
    → ap2 g (ap f p) q == ap2 (λ a c → g (f a) c) p q
  ap2-ap-l g f idp idp = idp

  ap2-ap-r : ∀ {k l} {C : Type k} {D : Type l}
    (g : A → C → D) (f : B → C) {x y : A} {w z : B}
    (p : x == y) (q : w == z)
    → ap2 g p (ap f q) == ap2 (λ a b → g a (f b)) p q
  ap2-ap-r g f idp idp = idp

  ap2-ap-lr : ∀ {k l m} {C : Type k} {D : Type l} {E : Type m}
    (g : C → D → E) (f : A → C) (h : B → D)
    {x y : A} {w z : B}
    (p : x == y) (q : w == z)
    → ap2 g (ap f p) (ap h q) == ap2 (λ a b → g (f a) (h b)) p q
  ap2-ap-lr g f h idp idp = idp

  ap2-diag : (f : A → A → B)
    {x y : A} (p : x == y)
    → ap2 f p p == ap (λ x → f x x) p
  ap2-diag f idp = idp

module _ {i j k} {A : Type i} {B : Type j} {C : Type k} (g : B → C) (f : A → B) where

  module _ {a a' a'' : A} (p : a == a') (p' : a' == a'') where
    ap-∘-∙-coh-seq₁ :
      ap (g ∘ f) (p ∙ p') =-= ap g (ap f p) ∙ ap g (ap f p')
    ap-∘-∙-coh-seq₁ =
      ap (g ∘ f) (p ∙ p')
        =⟪ ap-∙ (g ∘ f) p p' ⟫
      ap (g ∘ f) p ∙ ap (g ∘ f) p'
        =⟪ ap2 _∙_ (ap-∘ g f p) (ap-∘ g f p') ⟫
      ap g (ap f p) ∙ ap g (ap f p') ∎∎

    ap-∘-∙-coh-seq₂ :
      ap (g ∘ f) (p ∙ p') =-= ap g (ap f p) ∙ ap g (ap f p')
    ap-∘-∙-coh-seq₂ =
      ap (g ∘ f) (p ∙ p')
        =⟪ ap-∘ g f (p ∙ p') ⟫
      ap g (ap f (p ∙ p'))
        =⟪ ap (ap g) (ap-∙ f p p') ⟫
      ap g (ap f p ∙ ap f p')
        =⟪ ap-∙ g (ap f p) (ap f p') ⟫
      ap g (ap f p) ∙ ap g (ap f p') ∎∎

  ap-∘-∙-coh :  {a a' a'' : A} (p : a == a') (p' : a' == a'')
    → ap-∘-∙-coh-seq₁ p p' =ₛ ap-∘-∙-coh-seq₂ p p'
  ap-∘-∙-coh idp idp = =ₛ-in idp

  ap-∘-long : (h : A → B) (K : (z : A) → h z == f z) {x y : A} (p : x == y) →
    ap (g ∘ f) p
      ==
    ap g (! (K x)) ∙ ap g (K x ∙ ap f p ∙' ! (K y)) ∙' ! (ap g (! (K y)))
  ap-∘-long h K {x} idp = idp-ap-!-!-∙-∙' g (K x)

module _ {i j} {A : Type i} {B : Type j} (b : B) where

  ap-cst : {x y : A} (p : x == y) → ap (cst b) p == idp
  ap-cst idp = idp

  ap-cst-coh : {x y z : A} (p : x == y) (q : y == z) →
    ap-cst (p ∙ q) ◃∎
      =ₛ
    ap-∙ (cst b) p q ◃∙
    ap2 _∙_ (ap-cst p) (ap-cst q) ◃∎
  ap-cst-coh idp idp = =ₛ-in idp

{- Naturality of homotopies -}
module _ {i} {A : Type i} where

  homotopy-naturality : ∀ {k} {B : Type k} (f g : A → B)
    (h : (x : A) → f x == g x) {x y : A} (p : x == y)
    → ap f p ◃∙ h y ◃∎ =ₛ h x ◃∙ ap g p ◃∎
  homotopy-naturality f g h {x} idp =
    =ₛ-in (! (∙-unit-r (h x)))

  homotopy-naturality-to-idf : (f : A → A)
    (h : (x : A) → f x == x) {x y : A} (p : x == y)
    → ap f p ◃∙ h y ◃∎ =ₛ h x ◃∙ p ◃∎
  homotopy-naturality-to-idf f h {x} p = =ₛ-in $
    =ₛ-out (homotopy-naturality f (λ a → a) h p) ∙ ap (λ w → h x ∙ w) (ap-idf p)

  homotopy-naturality-from-idf : (g : A → A)
    (h : (x : A) → x == g x) {x y : A} (p : x == y)
    → p ◃∙ h y ◃∎ =ₛ h x ◃∙ ap g p ◃∎
  homotopy-naturality-from-idf g h {y = y} p = =ₛ-in $
    ap (λ w → w ∙ h y) (! (ap-idf p)) ∙ =ₛ-out (homotopy-naturality (λ a → a) g h p)

  homotopy-naturality-to-cst : ∀ {k} {B : Type k} (f : A → B) (b : B)
    (h : (x : A) → f x == b) {x y : A} (p : x == y)
    → ap f p == h x ∙ ! (h y)
  homotopy-naturality-to-cst f b h {x} p@idp = ! (!-inv-r (h x))

  homotopy-naturality-cst-to-cst : ∀ {k} {B : Type k}
    (b : B) {x y : A} (p : x == y)
    → homotopy-naturality-to-cst (cst b) b (λ a → idp) p ==
      ap-cst b p
  homotopy-naturality-cst-to-cst b p@idp = idp

  homotopy-naturality-cst-to-cst' : ∀ {k} {B : Type k}
    (b₀ b₁ : B) (h : A → b₀ == b₁) {x y : A} (p : x == y)
    → homotopy-naturality-to-cst (cst b₀) b₁ h p ◃∙
      ap (λ v → h v ∙ ! (h y)) p ◃∙
      !-inv-r (h y) ◃∎
      =ₛ
      ap-cst b₀ p ◃∎
  homotopy-naturality-cst-to-cst' b₀ b₁ h {x} p@idp =
    =ₛ-in (!-inv-l (!-inv-r (h x)))

  homotopy-naturality-cst-to-cst-comp : ∀ {k} {B : Type k}
    (b₀ b₁ : B) (h : A → b₀ == b₁) {x y z : A} (p : x == y) (q : y == z)
    → homotopy-naturality-to-cst (cst b₀) b₁ h (p ∙ q) ◃∙
      ap (λ v → h v ∙ ! (h z)) p ◃∎
      =ₛ
      ap-∙ (cst b₀) p q ◃∙
      ap (_∙ ap (cst b₀) q) (ap-cst b₀ p) ◃∙
      homotopy-naturality-to-cst (cst b₀) b₁ h q ◃∎
  homotopy-naturality-cst-to-cst-comp b₀ b₁ h {x} p@idp q@idp =
    =ₛ-in (∙-unit-r (! (!-inv-r (h x))))

  homotopy-naturality-cst-to-cst-comp' : ∀ {k} {B : Type k}
    (b₀ b₁ : B) (h : A → b₀ == b₁) {x y z : A} (p : x == z) (q : x == y)
    → homotopy-naturality-to-cst (cst b₀) b₁ h p ◃∙
      ap (λ v → h v ∙ ! (h z)) q ◃∎
      =ₛ
      ap-cst b₀ p ◃∙
      ! (ap-cst b₀ (! q ∙ p)) ◃∙
      homotopy-naturality-to-cst (cst b₀) b₁ h (! q ∙ p) ◃∎
  homotopy-naturality-cst-to-cst-comp' b₀ b₁ h {x} p@idp q@idp =
    =ₛ-in (∙-unit-r (! (!-inv-r (h x))))

module _ {i j k} {A : Type i} {B : Type j} {C : Type k}
         (f g : A → B → C) (h : ∀ a b → f a b == g a b) where
         
  homotopy-naturality2 : {a₀ a₁ : A} {b₀ b₁ : B} (p : a₀ == a₁) (q : b₀ == b₁)
    → ap2 f p q ◃∙ h a₁ b₁ ◃∎ =ₛ h a₀ b₀ ◃∙ ap2 g p q ◃∎
  homotopy-naturality2 {a₀ = a} {b₀ = b} idp idp =  =ₛ-in (! (∙-unit-r (h a b)))

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} (f g : A → B) (H : (x : A) → f x == g x) where

  apCommSq : {x y : A} (p : x == y) → ! (H x) ∙ ap f p ∙ H y == ap g p
  apCommSq {x = x} idp = !-inv-l (H x)

  apCommSq2 : {x y : A} (p : x == y) → H x == ap f p ∙ H y ∙ ! (ap g p)
  apCommSq2 {x = x} idp = ! (∙-unit-r (H x))

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f g : A → B} (H : (x : A) → f x == g x) where

  homotopy-naturality-rot : {x y : A} (p : x == y)
    → ! (H x) ◃∙ ap f p ◃∎ =ₛ ap g p ◃∙ ! (H y) ◃∎
  homotopy-naturality-rot {x} idp =
    =ₛ-in (∙-unit-r (! (H x)))

  apeq : {x y : A} (p : x == y) → ap g p == ! (H x) ∙ ap f p ∙ H y
  apeq {x = x} idp = ! (!-inv-l (H x))

  apeq-rev : {x y : A} (p : x == y) → ap f p == H x ∙ ap g p ∙ ! (H y)
  apeq-rev {x = x} idp = ! (!-inv-r (H x))

  apeq-rev-!◃ : {x y : A} (p : x == y) → ! (ap f p) ◃∎ =ₛ H y ◃∙ ! (ap g p) ◃∙ ! (H x) ◃∎
  apeq-rev-!◃ {x = x} idp = =ₛ-in (! (!-inv-r (H x)))

  apCommSq◃ : {x y : A} (p : x == y) → ap g p ◃∎ =ₛ ! (H x) ◃∙ ap f p ◃∙ H y ◃∎
  apCommSq◃ {x} idp = =ₛ-in (! (!-inv-l (H x)))

  apCommSq2' : {x y : A} (p : x == y) → H x == ap f p ∙ H y ∙' ! (ap g p)
  apCommSq2' idp = idp

  apCommSq2◃ : {x y : A} (p : x == y) → H x ◃∎ =ₛ ap f p ◃∙ H y ◃∙ ! (ap g p) ◃∎
  apCommSq2◃ {x} idp = =ₛ-in (! (∙-unit-r (H x)))

  apCommSq2◃-rev : {x y : A} (p : x == y) → H y ◃∎ =ₛ ! (ap f p) ◃∙ H x ◃∙ ap g p ◃∎
  apCommSq2◃-rev {x = x} idp = =ₛ-in (! (∙-unit-r (H x)))

  hmtpy-nat-! : {x y : A} (p : x == y) → ! (H x) == ap g p ∙ ! (H y) ∙ ! (ap f p)
  hmtpy-nat-! {x} idp = ! (∙-unit-r (! (H x)))

  hmtpy-nat-!-∙' : {x y : A} (p : x == y) → ! (H x) == ap g p ∙ ! (H y) ∙' ! (ap f p)
  hmtpy-nat-!-∙' idp = idp

  hmtpy-nat-!◃ : {x y : A} (p : x == y) → ! (H x) ◃∎ =ₛ ap g p ◃∙ ! (H y) ◃∙ ! (ap f p) ◃∎
  hmtpy-nat-!◃ {x} idp = =ₛ-in (! (∙-unit-r (! (H x))))

  hmtpy-nat-!-sq : {x y : A} (p : x == y) → ! (H x) ∙ ap f p == ap g p ∙ ! (H y)
  hmtpy-nat-!-sq {x} idp = ∙-unit-r (! (H x))

  hnat-sq-! : {x y : A} (p : x == y) → ! (H y) == ! (ap g p) ∙ ! (H x) ∙ ap f p
  hnat-sq-! {x} idp = ! (∙-unit-r (! (H x)))

  hnat-sq-!◃ : {x y : A} (p : x == y) → ! (H y) ◃∎ =ₛ ! (ap g p) ◃∙ ! (H x) ◃∙ ap f p ◃∎
  hnat-sq-!◃ {x} idp = =ₛ-in (! (∙-unit-r (! (H x))))

  hmtpy-nat-∙' : {x y : A} (p : x == y) → ap f p == H x ∙ ap g p ∙' ! (H y)
  hmtpy-nat-∙' {x} idp = ! (!-inv-r (H x)) ∙ ap (λ p → H x ∙ p) (! (∙'-unit-l (! (H x))))

  hmtpy-nat-∙◃ : {x y : A} (p : x == y) → ap f p ◃∎ =ₛ H x ◃∙ ap g p ◃∙ ! (H y) ◃∎
  hmtpy-nat-∙◃ {x} idp = =ₛ-in (! (!-inv-r (H x)))

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B} where

  hnat-!-β : {x y : A} (p : x == y) → hmtpy-nat-! {f = f} (λ _ → idp) p == ! (!-ap-inv f p)
  hnat-!-β idp = idp

  hmtpy-nat-∙'-idp : {x y : A} (p : x == y) → hmtpy-nat-∙' {f = f} (λ _ → idp) p == idp
  hmtpy-nat-∙'-idp idp = idp

  hmtpy-nat-!-∼ : {g : A → B} {H₁ H₂ : (a : A) → f a == g a} (K : (a : A) → H₂ a == H₁ a) {x y : A} (p : x == y)
    → hmtpy-nat-! H₁ p == ap ! (! (K x)) ∙ hmtpy-nat-! H₂ p ∙ ap (λ q → ap g p ∙ ! q ∙ ! (ap f p)) (K y)
  hmtpy-nat-!-∼ {H₁ = H₁} {H₂} K {x} idp =
    hmtpy-nat-! ∙-unit-r (ap ! (! (K x))) ∙
    ap (λ q → q ∙ ! (∙-unit-r (! (H₂ x))) ∙ ! (ap (λ z → z ∙ idp) (ap ! (! (K x))))) (ap-idf (ap ! (!(K x)))) ∙
    ap (λ q → ap ! (! (K x)) ∙ ! (∙-unit-r (! (H₂ x))) ∙ q) (aux (K x))
    where
      aux : {p₁ p₂ : _} (t : p₁ == p₂) → ! (ap (λ z → z ∙ idp) (ap ! (! t))) == ap (λ q → ! q ∙ idp) t
      aux idp = idp

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄} {f : A → B} {g : A → C} where

  apCommSq-cmp : (v : B → D) (u : C → D) (H : (x : A) → v (f x) == u (g x))
    {x y : A} (p : x == y) → ap v (ap f p) == H x ∙ ap u (ap g p) ∙ ! (H y)
  apCommSq-cmp _ _ H {x} idp = ! (!-inv-r (H x)) 

module _ {i j k} {A : Type i} {B : Type j} {C : Type k} (f : A → B → C) where

  ap-comm : {a₀ a₁ : A} (p : a₀ == a₁) {b₀ b₁ : B} (q : b₀ == b₁)
    → ap (λ a → f a b₀) p ∙ ap (λ z → f a₁ z) q ==
      ap (λ z → f a₀ z) q ∙ ap (λ a → f a b₁) p
  ap-comm p q = ! (=ₛ-out (ap2-out f p q)) ∙ =ₛ-out (ap2-out' f p q)

  ap-comm-=ₛ : {a₀ a₁ : A} (p : a₀ == a₁) {b₀ b₁ : B} (q : b₀ == b₁)
    → ap (λ a → f a b₀) p ◃∙ ap (λ z → f a₁ z) q ◃∎ =ₛ
      ap (λ z → f a₀ z) q ◃∙ ap (λ a → f a b₁) p ◃∎
  ap-comm-=ₛ p q = =ₛ-in (ap-comm p q)

  ap-comm' : {a₀ a₁ : A} (p : a₀ == a₁) {b₀ b₁ : B} (q : b₀ == b₁)
    → ap (λ a → f a b₀) p ∙' ap (λ z → f a₁ z) q ==
      ap (λ z → f a₀ z) q ∙ ap (λ a → f a b₁) p
  ap-comm' p idp = idp

  ap-comm-cst-seq : {a₀ a₁ : A} (p : a₀ == a₁) {b₀ b₁ : B} (q : b₀ == b₁)
    (c : C) (h₀ : ∀ b → f a₀ b == c)
    → ap (λ a → f a b₀) p ∙ ap (λ b → f a₁ b) q =-=
      ap (λ z → f a₀ z) q ∙ ap (λ a → f a b₁) p
  ap-comm-cst-seq {a₀} {a₁} p {b₀} {b₁} q c h₀ =
    ap (λ a → f a b₀) p ∙ ap (λ b → f a₁ b) q
      =⟪ ap (ap (λ a → f a b₀) p ∙_) $
        homotopy-naturality-to-cst (λ b → f a₁ b) c h₁ q ⟫
    ap (λ a → f a b₀) p ∙ h₁ b₀ ∙ ! (h₁ b₁)
      =⟪ ap (ap (λ a → f a b₀) p ∙_) $ ap (λ k → k h₀) $
        transp-naturality {B = λ a → ∀ b → f a b == c} (λ h → h b₀ ∙ ! (h b₁)) p ⟫
    ap (λ a → f a b₀) p ∙ transport (λ a → f a b₀ == f a b₁) p (h₀ b₀ ∙ ! (h₀ b₁))
      =⟪ ! (ap-transp (λ a → f a b₀) (λ a → f a b₁) p (h₀ b₀ ∙ ! (h₀ b₁))) ⟫
    (h₀ b₀ ∙ ! (h₀ b₁)) ∙ ap (λ a → f a b₁) p
      =⟪ ! (ap (_∙ ap (λ a → f a b₁) p) $
              (homotopy-naturality-to-cst (λ b → f a₀ b) c h₀ q)) ⟫
    ap (λ z → f a₀ z) q ∙ ap (λ a → f a b₁) p ∎∎
    where
      h₁ : ∀ b → f a₁ b == c
      h₁ = transport (λ a → ∀ b → f a b == c) p h₀

  ap-comm-cst-coh : {a₀ a₁ : A} (p : a₀ == a₁) {b₀ b₁ : B} (q : b₀ == b₁)
    (c : C) (h₀ : ∀ b → f a₀ b == c)
    → ap-comm p q ◃∎ =ₛ
      ap-comm-cst-seq p q c h₀
  ap-comm-cst-coh p@idp {b₀} q@idp c h₀ = =ₛ-in $ ! $
    ap (idp ∙_) (! (!-inv-r (h₀ b₀))) ∙
    ! (∙-unit-r (h₀ b₀ ∙ ! (h₀ b₀))) ∙
    ! (ap (_∙ idp) (! (!-inv-r (h₀ b₀))))
      =⟨ ap (_∙ ! (∙-unit-r (h₀ b₀ ∙ ! (h₀ b₀))) ∙ ! (ap (_∙ idp) (! (!-inv-r (h₀ b₀)))))
            (ap-idf (! (!-inv-r (h₀ b₀)))) ⟩
    ! (!-inv-r (h₀ b₀)) ∙
    ! (∙-unit-r (h₀ b₀ ∙ ! (h₀ b₀))) ∙
    ! (ap (_∙ idp) (! (!-inv-r (h₀ b₀))))
      =⟨ ap (λ v → ! (!-inv-r (h₀ b₀)) ∙ ! (∙-unit-r (h₀ b₀ ∙ ! (h₀ b₀))) ∙ v)
            (!-ap (_∙ idp) (! (!-inv-r (h₀ b₀)))) ⟩
    ! (!-inv-r (h₀ b₀)) ∙
    ! (∙-unit-r (h₀ b₀ ∙ ! (h₀ b₀))) ∙
    ap (_∙ idp) (! (! (!-inv-r (h₀ b₀))))
      =⟨ ap (! (!-inv-r (h₀ b₀)) ∙_) $ ! $ =ₛ-out $
         homotopy-naturality-from-idf (_∙ idp)
                                      (λ p → ! (∙-unit-r p))
                                      (! (! (!-inv-r (h₀ b₀)))) ⟩
    ! (!-inv-r (h₀ b₀)) ∙ ! (! (!-inv-r (h₀ b₀))) ∙ idp
      =⟨ ap (! (!-inv-r (h₀ b₀)) ∙_) (∙-unit-r (! (! (!-inv-r (h₀ b₀))))) ⟩
    ! (!-inv-r (h₀ b₀)) ∙ ! (! (!-inv-r (h₀ b₀)))
      =⟨ !-inv-r (! (!-inv-r (h₀ b₀))) ⟩
    idp =∎

module _ {i j k} {A : Type i} {B : Type j} {C : Type k} where

  ap-comm-comm : (f : A → B → C) {a₀ a₁ : A} (p : a₀ == a₁) {b₀ b₁ : B} (q : b₀ == b₁)
    → ap-comm f p q == ! (ap-comm (λ x y → f y x) q p)
  ap-comm-comm f p@idp q@idp = idp

module _ {i} {A : Type i} where

  transp-cst=idf : {a x y : A} (p : x == y) (q : a == x)
    → transport (λ x → a == x) p q == q ∙ p
  transp-cst=idf idp q = ! (∙-unit-r q)

  transp-cst=idf-l : {a x y : A} (p : x == y) (q : x == a)
    → transport (λ x → x == a) p q == ! p ∙ q
  transp-cst=idf-l idp q = idp

  transp-cst=idf-pentagon : {a x y z : A}
    (p : x == y) (q : y == z) (r : a == x)
    → transp-cst=idf (p ∙ q) r ◃∎ =ₛ
      transp-∙ p q r ◃∙
      ap (transport (λ x → a == x) q) (transp-cst=idf p r) ◃∙
      transp-cst=idf q (r ∙ p) ◃∙
      ∙-assoc r p q ◃∎
  transp-cst=idf-pentagon idp q idp =
    =ₛ-in (! (∙-unit-r (transp-cst=idf q idp)))

{- Various lemmas on transporting identities -}

module _ {i j} {A : Type i} {B : Type j} {f : A → B} where

  transp-pth : {x y : A} {g : A → B} (p : x == y) (q : f x == g x)
    → transport (λ x → f x == g x) p q == (! (ap f p)) ∙ q ∙ (ap g p)
  transp-pth idp q = ! (∙-unit-r q)

  transp-pth-◃ : {x y : A} {g : A → B} (p : x == y) (q : f x == g x)
    → transport (λ x → f x == g x) p q ◃∎ =ₛ (! (ap f p)) ◃∙ q ◃∙ (ap g p) ◃∎
  transp-pth-◃ idp q = =ₛ-in (! (∙-unit-r q))

  transp-path-cmp-idf : (g : B → A) {x y : A} (p : x == y) (q : g (f x) == x)
    → transport (λ z → g (f z) == z) p q ◃∎ =ₛ ! (ap g (ap f p)) ◃∙ q ◃∙ p ◃∎
  transp-path-cmp-idf g idp q = =ₛ-in (! (∙-unit-r q))

  transp-pth-Rcmp : ∀ {k l} {C : Type k} {D : Type l} {h : C → A} {v : C → D} {u : D → B}
    {x y : C} (p : x == y) (q : u (v x) == f (h x))
    → transport (λ x → u (v x) == f (h x)) p q == ! (ap u (ap v p)) ∙ q ∙ (ap (f ∘ h) p)
  transp-pth-Rcmp idp q = ! (∙-unit-r q)

  transp-pth-cmp-◃ : ∀ {k l} {C : Type k} {D : Type l} {h : C → A} {v : C → D} {u : D → B}
    {x y : C} (p : x == y) (q : u (v x) == f (h x))
    → transport (λ x → u (v x) == f (h x)) p q ◃∎ =ₛ (! (ap u (ap v p))) ◃∙ q ◃∙ (ap f (ap h p)) ◃∎
  transp-pth-cmp-◃ idp q = =ₛ-in (! (∙-unit-r q))

  transp-pth-l : {x y : A} {g : A → B} (p : x == y) (q : f x == g x)
    → transport (λ x → f x == g x) p q == ((! (ap f p)) ∙ q) ∙ (ap g p)
  transp-pth-l idp q = ! (∙-unit-r q)

  transp-pth-l-◃ : {x y : A} {g : A → B} (p : x == y) (q : f x == g x)
    → transport (λ x → f x == g x) p q ◃∎ =ₛ ((! (ap f p)) ∙ q) ◃∙ (ap g p) ◃∎
  transp-pth-l-◃ idp q = =ₛ-in (! (∙-unit-r q))

  transp-pth-cmpR : ∀ {k l m} {C : Type k} {D : Type l} {Z : Type m} {t : C → Z} {h : Z → A} {v : C → D} {u : D → B}
    {x y : C} (p : x == y) (q : u (v x) == f (h (t x)))
    → transport (λ x → u (v x) == f (h (t x))) p q == (! (ap u (ap v p))) ∙ q ∙ (ap f (ap h (ap t p)))
  transp-pth-cmpR idp q = ! (∙-unit-r q)

  transp-pth-cmp : ∀ {k l} {C : Type k} {D : Type l} {h : C → A} {v : C → D} {u : D → B}
    {x y : C} (p : x == y) (q : u (v x) == f (h x))
    → transport (λ x → u (v x) == f (h x)) p q == (! (ap u (ap v p))) ∙ q ∙ (ap f (ap h p))
  transp-pth-cmp idp q = ! (∙-unit-r q)
  
  transp-pth-cmp-l : ∀ {k l} {C : Type k} {D : Type l} {h : C → A} {v : C → D} {u : D → B}
    {x y : C} (p : x == y) (q : u (v x) == f (h x))
    → transport (λ x → u (v x) == f (h x)) p q == ((! (ap u (ap v p))) ∙ q) ∙ (ap f (ap h p))
  transp-pth-cmp-l idp q = ! (∙-unit-r q)

  transpRev : {x y : A} {g : A → B} (p : x == y) {q : f x == g x} {r : f y == g y}
    → (transport (λ x → f x == g x) p q == r) → transport (λ x → g x == f x) p (! q) == ! r
  transpRev idp t = ap ! t

module _ {i j k} {A : Type i} {B : Type j} {C : Type k} (f : A → B) (h : C → A) (g : C → B) where

  transp-pth-cmpL : {x y : C} (p : x == y) (q : f (h x) == g x)
    → transport (λ z → f (h z) == g z) p q == ! (ap f (ap h p)) ∙ q ∙ ap g p
  transp-pth-cmpL idp q = ! (∙-unit-r q)

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {f : C → A} {h : B → C} where

  apd-tr-refl : {x y : B} (p : x == y) → transport (λ z → f (h z) == f (h z)) p idp == idp
  apd-tr-refl idp = idp

module _ {i j k l} {A : Type i} {B : Type j} {f : A → B} {C : Type k} {D : Type l} {h : C → A} {v : C → D} {u : D → B} where 

  transpRevSlice : {x y : C} (p : x == y) (q : u (v x) == f (h x)) {r : u (v y) == f (h y)}
    → (((! (ap u (ap v p))) ∙ q) ∙ (ap f (ap h p)) == r) → (! (ap f (ap h p))) ∙ ! q ∙ (ap u (ap v p)) == ! r
  transpRevSlice idp q idp = ∙-unit-r (! q) ∙ ap (λ p → ! p) (! (∙-unit-r q))

  DecompTrRev : {x y : C} (p : x == y) (q : u (v x) == f (h x)) {r : u (v y) == f (h y)}
    (e : ((! (ap u (ap v p))) ∙ q) ∙ (ap f (ap h p)) == r)
    → transp-pth-cmp p (! q) ◃∙ transpRevSlice p q e ◃∎ =ₛ transpRev p ((transp-pth-cmp-l p q) ∙ e) ◃∎
  DecompTrRev idp q idp = =ₛ-in (RUnCoh q)

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂} where

  transp-id-concat : (f g : (x : A) → B x) {x y : A} (p : x == y) {c : B x} (q₁ : f x == c) (q₂ : c == g x)
    {r : f y == transport B p (f x)} (R : ! (apd-tr f p) == r)
    → transport (λ z → f z == g z) p (q₁ ∙ q₂) ◃∎ =ₛ r ◃∙ ap (transport B p) q₁ ◃∙ ap (transport B p) q₂ ◃∙ apd-tr g p ◃∎
  transp-id-concat f g {x = x} idp idp q₂ idp = =ₛ-in (lemma q₂)
    where lemma : {a b : B x} (q : a == b) → q == ap (transport B idp) q ∙ idp
          lemma idp = idp

module _ {i j} {A : Type i} {B : A → Type j} (f g : (a : A) → B a) where

  dtransp-pth-◃ : {x y : A} (p : x == y) (q : f x == g x)
    → transport (λ x → f x == g x) p q ◃∎ =ₛ ! (apd-tr f p) ◃∙ ap (transport B p) q ◃∙ apd-tr g p ◃∎
  dtransp-pth-◃ idp q = =ₛ-in (! (ap (λ r → r ∙ idp) (ap-idf q) ∙ ∙-unit-r q))

  dtransp-pth : {x y : A} (p : x == y) (q : f x == g x)
    → transport (λ x → f x == g x) p q == ! (apd-tr f p) ∙ ap (transport B p) q ∙ apd-tr g p
  dtransp-pth idp q = ! (ap (λ r → r ∙ idp) (ap-idf q) ∙ ∙-unit-r q)

  dtransp-nat : (H : (z : A) → f z == g z) {x y : A} (p : x == y)
    → ! (apd-tr f p) == H y ∙ ! (apd-tr g p) ∙ ! (ap (transport B p) (H x))
  dtransp-nat H {x = x} idp = lemma (H x)
    where lemma : {a : B x} (r : a == g x) → idp == r ∙ ! (ap (transport B idp) r)
          lemma idp = idp

  dtransp-nat-rev-◃ : (H : (z : A) → f z ==  g z) {x y : A} (p : x == y)
    → ! (apd-tr f p) ◃∎ =ₛ H y ◃∙ ! (apd-tr g p) ◃∙ ! (ap (transport B p) (H x)) ◃∎
  dtransp-nat-rev-◃ H p = =ₛ-in (dtransp-nat H p)

  dtransp-nat-◃ : (H : (z : A) → f z ==  g z) {x y : A} (p : x == y)
    → apd-tr f p ◃∎ =ₛ ap (transport B p) (H x) ◃∙ apd-tr g p ◃∙ ! (H y) ◃∎
  dtransp-nat-◃ H {x = x} idp = =ₛ-in (lemma (H x))
    where lemma : {a : B x} (r : a == g x) → idp == ap (transport B idp) r ∙ ! r
          lemma idp = idp 

module _ {i j} {A : Type i} {B : A → Type j} {f g : (a : A) → B a}  where

  apd-tr-∼ : {H₁ H₂ : (a : A) → f a == g a} (K : (a : A) → H₂ a == H₁ a) {x y : A} (p : x == y)
    → apd-tr H₁ p == ap (transport (λ z → f z == g z) p) (! (K x)) ∙ apd-tr H₂ p ∙ K y
  apd-tr-∼ K {x} idp = ! (ap-idf-inv-l (K x))

  dp-hnat-! : (H : (a : A) → f a == g a) {x y : A} (p : x == y)
    → ! (H x) == ! (apd-tr g (! p)) ∙ ap (transport B (! p)) (! (H y)) ∙' apd-tr f (! p) 
  dp-hnat-! H {x} idp = ! (ap-idf (! (H x)))

module _ {i j} {A : Type i} {B : A → Type j} where

  transpFunEq : {x y : A} {p q : x == y} (r : p == q) → (z : B x) → transport B p z == transport B q z
  transpFunEq idp z = idp

module _ {i j} {A : Type i} {x y : A} {B : Type j} {f g h : A → B} {F : (x : A) → f x == g x} {G : (x : A) → g x == h x} where

  apd-concat-pres : (κ : x == y) → transport (λ x → f x == h x) κ (F x ∙ G x) == F y ∙ (transport (λ x → g x == h x) κ (G x))
  apd-concat-pres idp = idp

  apd-concat-fun-◃ : (κ : x == y) → apd-tr (λ x → F x ∙ G x) κ ◃∎ =ₛ apd-concat-pres κ ◃∙ ap (λ p → F y ∙ p) (apd-tr G κ) ◃∎ 
  apd-concat-fun-◃ idp = =ₛ-in idp

module _ {i j k} {A : Type i} {x y : A} {B : Type j} {ψ : A → B} {F : (x : B) → Type k} {γ : (x : B) → F x} where

  apd-comp-ap : (κ : x == y) → transport (λ x → F (ψ x)) κ (γ (ψ x)) == transport F (ap ψ κ) (γ (ψ x))
  apd-comp-ap idp = idp

  apd-comp-◃ : (κ : x == y) → apd-tr (λ x → γ (ψ x)) κ ◃∎ =ₛ apd-comp-ap κ ◃∙ apd-tr γ (ap ψ κ) ◃∎
  apd-comp-◃ idp = =ₛ-in idp

  apd-comp-eq-◃ : (κ : x == y) {p : ψ x == ψ y} (τ : ap ψ κ == p)
    → apd-tr γ (ap ψ κ) ◃∎ =ₛ ap (λ p → transport F p (γ (ψ x))) τ ◃∙ apd-tr γ p ◃∎
  apd-comp-eq-◃ idp idp = =ₛ-in idp

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂} {x y : A} where

  transp-inv : (p : x == y) (v : B y) → transport B p (transport B (! p) v) == v
  transp-inv idp v = idp

module _ {i j} {A : Type i} {F : A → Type j} {γ : (x : A) → F x} {x y z : A} where

  transp-over-∙ : {q : y == z} (p : x == y) → transport F (p ∙ q) (γ x) == transport F q (γ y)
  transp-over-∙ idp = idp

  apd-concat-arg : (p : x == y) (q : y == z) → apd-tr γ (p ∙ q) ◃∎ =ₛ transp-over-∙ p ◃∙ apd-tr γ q ◃∎
  apd-concat-arg idp idp = =ₛ-in idp

{- for functions with more arguments -}
module _ {i₀ i₁ i₂ j} {A₀ : Type i₀} {A₁ : Type i₁} {A₂ : Type i₂}
  {B : Type j} (f : A₀ → A₁ → A₂ → B) where

  ap3 : {x₀ y₀ : A₀} {x₁ y₁ : A₁} {x₂ y₂ : A₂}
    → (x₀ == y₀) → (x₁ == y₁) → (x₂ == y₂) → f x₀ x₁ x₂ == f y₀ y₁ y₂
  ap3 idp idp idp = idp

module _ {i₀ i₁ i₂ i₃ j} {A₀ : Type i₀} {A₁ : Type i₁} {A₂ : Type i₂} {A₃ : Type i₃}
  {B : Type j} (f : A₀ → A₁ → A₂ → A₃ → B) where

  ap4 : {x₀ y₀ : A₀} {x₁ y₁ : A₁} {x₂ y₂ : A₂} {x₃ y₃ : A₃}
    → (x₀ == y₀) → (x₁ == y₁) → (x₂ == y₂) → (x₃ == y₃) → f x₀ x₁ x₂ x₃ == f y₀ y₁ y₂ y₃
  ap4 idp idp idp idp = idp

module _ {i₀ i₁ i₂ i₃ i₄ j} {A₀ : Type i₀} {A₁ : Type i₁} {A₂ : Type i₂} {A₃ : Type i₃}
  {A₄ : Type i₄} {B : Type j} (f : A₀ → A₁ → A₂ → A₃ → A₄ → B) where

  ap5 : {x₀ y₀ : A₀} {x₁ y₁ : A₁} {x₂ y₂ : A₂} {x₃ y₃ : A₃} {x₄ y₄ : A₄}
    → (x₀ == y₀) → (x₁ == y₁) → (x₂ == y₂) → (x₃ == y₃) → (x₄ == y₄)
    → f x₀ x₁ x₂ x₃ x₄ == f y₀ y₁ y₂ y₃ y₄
  ap5 idp idp idp idp idp = idp

module _ {i₀ i₁ i₂ i₃ i₄ i₅ j} {A₀ : Type i₀} {A₁ : Type i₁} {A₂ : Type i₂} {A₃ : Type i₃}
  {A₄ : Type i₄} {A₅ : Type i₅} {B : Type j} (f : A₀ → A₁ → A₂ → A₃ → A₄ → A₅ → B) where

  ap6 : {x₀ y₀ : A₀} {x₁ y₁ : A₁} {x₂ y₂ : A₂} {x₃ y₃ : A₃} {x₄ y₄ : A₄} {x₅ y₅ : A₅}
    → (x₀ == y₀) → (x₁ == y₁) → (x₂ == y₂) → (x₃ == y₃) → (x₄ == y₄) → (x₅ == y₅)
    → f x₀ x₁ x₂ x₃ x₄ x₅ == f y₀ y₁ y₂ y₃ y₄ y₅
  ap6 idp idp idp idp idp idp = idp
