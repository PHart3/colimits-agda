{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics

module lib.types.Paths where

{- ! is an equivalence and works on ≠ -}
module _ {i} {A : Type i} {x y : A} where

  !-equiv : (x == y) ≃ (y == x)
  !-equiv = equiv ! ! !-! !-!

  ≠-inv : (x ≠ y) → (y ≠ x)
  ≠-inv x≠y y=x = x≠y (! y=x)

{- Pre- and post- concatenation are equivalences -}
module _ {i} {A : Type i} {x y z : A} where

  pre∙-is-equiv : (p : x == y) → is-equiv (λ (q : y == z) → p ∙ q)
  pre∙-is-equiv p = is-eq (λ q → p ∙ q) (λ r → ! p ∙ r) f-g g-f
    where f-g : ∀ r → p ∙ ! p ∙ r == r
          f-g r = ! (∙-assoc p (! p) r) ∙ ap (λ s → s ∙ r) (!-inv-r p)

          g-f : ∀ q → ! p ∙ p ∙ q == q
          g-f q = ! (∙-assoc (! p) p q) ∙ ap (λ s → s ∙ q) (!-inv-l p)

  pre∙-equiv : (p : x == y) → (y == z) ≃ (x == z)
  pre∙-equiv p = ((λ q → p ∙ q) , pre∙-is-equiv p)

  post∙-is-equiv : (p : y == z) → is-equiv (λ (q : x == y) → q ∙ p)
  post∙-is-equiv p = is-eq (λ q → q ∙ p) (λ r → r ∙ ! p) f-g g-f
    where f-g : ∀ r → (r ∙ ! p) ∙ p == r
          f-g r = ∙-assoc r (! p) p ∙ ap (λ s → r ∙ s) (!-inv-l p) ∙ ∙-unit-r r

          g-f : ∀ q → (q ∙ p) ∙ ! p == q
          g-f q = ∙-assoc q p (! p) ∙ ap (λ s → q ∙ s) (!-inv-r p) ∙ ∙-unit-r q

  post∙-equiv : (p : y == z) → (x == y) ≃ (x == z)
  post∙-equiv p = ((λ q → q ∙ p) , post∙-is-equiv p)

  pre∙'-is-equiv : (p : x == y) → is-equiv (λ (q : y == z) → p ∙' q)
  pre∙'-is-equiv p = is-eq (λ q → p ∙' q) (λ r → ! p ∙' r) f-g g-f
    where f-g : ∀ r → p ∙' ! p ∙' r == r
          f-g r = ! (∙'-assoc p (! p) r) ∙ ap (λ s → s ∙' r) (!-inv'-r p)
                  ∙ ∙'-unit-l r

          g-f : ∀ q → ! p ∙' p ∙' q == q
          g-f q = ! (∙'-assoc (! p) p q) ∙ ap (λ s → s ∙' q) (!-inv'-l p)
                  ∙ ∙'-unit-l q

  pre∙'-equiv : (p : x == y) → (y == z) ≃ (x == z)
  pre∙'-equiv p = ((λ q → p ∙' q) , pre∙'-is-equiv p)

  post∙'-is-equiv : (p : y == z) → is-equiv (λ (q : x == y) → q ∙' p)
  post∙'-is-equiv p = is-eq (λ q → q ∙' p) (λ r → r ∙' ! p) f-g g-f
    where f-g : ∀ r → (r ∙' ! p) ∙' p == r
          f-g r = ∙'-assoc r (! p) p ∙ ap (λ s → r ∙' s) (!-inv'-l p)

          g-f : ∀ q → (q ∙' p) ∙' ! p == q
          g-f q = ∙'-assoc q p (! p) ∙ ap (λ s → q ∙' s) (!-inv'-r p)

  post∙'-equiv : (p : y == z) → (x == y) ≃ (x == z)
  post∙'-equiv p = ((λ q → q ∙' p) , post∙'-is-equiv p)

  path-eqlends-≃ : ∀ {w} → (p : x == y) (q : z == w) → (x == z) ≃ (y == w)
  path-eqlends-≃ idp idp = ide _

module _ {i} {A : Type i} {x y : A} where

  post∙idp∘!-is-equiv : (x == y) ≃ (y == x) 
  post∙idp∘!-is-equiv = (post∙-equiv idp) ∘e (!-equiv)

  ap-post∙idp∘!-inv : {p₁ p₂ : x == y}
    → ! p₁ ∙ idp == ! p₂ ∙ idp → p₁ == p₂
  ap-post∙idp∘!-inv {p₁} {p₂} = <– (ap-equiv (post∙idp∘!-is-equiv) p₁ p₂)

  path-rot-in-≃ : {z : A} (p₁ : x == y) (p₂ : z == x) {p₃ : z == y} →
    (p₁ == ! p₂ ∙ p₃) ≃ (p₂ ∙ p₁ == p₃)
  path-rot-in-≃ idp idp = ide _

module _ {i j} {A : Type i} {B : Type j} {f g : A → B} where

  ap-app= : {a : A} (p : f == g) → ap (λ u → u a) p == app= p a
  ap-app= idp = idp

  funext-nat : (a : A) {H₁ H₂ : f ∼ g} (K : H₁ == H₂)
    → ap (λ H → H a) K == app= K a
  funext-nat a idp = idp

  funext-nat-∼ : (a : A) {H₁ H₂ : f ∼ g} (K : H₁ ∼ H₂)
    → ap (λ H → H a) (λ= K) == K a
  funext-nat-∼ a K = funext-nat a (λ= K) ∙ app=-β K a

module _ {i} {A : Type i} {a : A} where

  λ=-ap-idf : ap (λ H → H (idp :> (a == a))) (λ= (ap-idf {A = A})) == idp
  λ=-ap-idf = funext-nat-∼ idp ap-idf

module _ {i j} {A : Type i} {B : Type j}
  {f : A → B} {x y : A} {b : B} where

  ↓-app=cst-in : {p : x == y} {u : f x == b} {v : f y == b}
    → u == (ap f p ∙ v)
    → (u == v [ (λ x → f x == b) ↓ p ])
  ↓-app=cst-in {p = idp} q = q

  ↓-app=cst-out : {p : x == y} {u : f x == b} {v : f y == b}
    → (u == v [ (λ x → f x == b) ↓ p ])
    → u == (ap f p ∙ v)
  ↓-app=cst-out {p = idp} r = r

  ↓-app=cst-β : {p : x == y} {u : f x == b} {v : f y == b}
    → (q : u == (ap f p ∙ v))
    → ↓-app=cst-out {p = p} (↓-app=cst-in q) == q
  ↓-app=cst-β {p = idp} q = idp

  ↓-app=cst-η : {p : x == y} {u : f x == b} {v : f y == b}
    → (q : u == v [ (λ x → f x == b) ↓ p ])
    → ↓-app=cst-in (↓-app=cst-out q) == q
  ↓-app=cst-η {p = idp} q = idp

  ↓-app=cst-econv : {p : x == y} {u : f x == b} {v : f y == b}
    → (u == (ap f p ∙ v)) ≃ (u == v [ (λ x → f x == b) ↓ p ])
  ↓-app=cst-econv {p = p} = equiv ↓-app=cst-in ↓-app=cst-out
    (↓-app=cst-η {p = p}) (↓-app=cst-β {p = p})

  ↓-cst=app-in : {p : x == y} {u : b == f x} {v : b == f y}
    → (u ∙' ap f p) == v
    → (u == v [ (λ x → b == f x) ↓ p ])
  ↓-cst=app-in {p = idp} q = q

  ↓-cst=app-out : {p : x == y} {u : b == f x} {v : b == f y}
    → (u == v [ (λ x → b == f x) ↓ p ])
    → (u ∙' ap f p) == v
  ↓-cst=app-out {p = idp} r = r

  ↓-cst=app-econv : {p : x == y} {u : b == f x} {v : b == f y}
    → ((u ∙' ap f p) == v) ≃ (u == v [ (λ x → b == f x) ↓ p ])
  ↓-cst=app-econv {p = idp} = equiv ↓-cst=app-in ↓-cst=app-out
     (λ _ → idp) (λ _ → idp)

{- alternative versions -}

module _ {i j} {A : Type i} {B : Type j}
  {f : A → B} {x y : A} {b : B} where

  ↓-app=cst-in' : {p : x == y} {u : f x == b} {v : f y == b}
    → u == (ap f p ∙' v)
    → (u == v [ (λ x → f x == b) ↓ p ])
  ↓-app=cst-in' {p = idp} {v = idp} q = q

  ↓-app=cst-out' : {p : x == y} {u : f x == b} {v : f y == b}
    → (u == v [ (λ x → f x == b) ↓ p ])
    → u == (ap f p ∙' v)
  ↓-app=cst-out' {p = idp} {v = idp} r = r

  ↓-app=cst-β' : {p : x == y} {u : f x == b} {v : f y == b}
    → (q : u == (ap f p ∙' v))
    → ↓-app=cst-out' {p = p} {v = v} (↓-app=cst-in' q) == q
  ↓-app=cst-β' {p = idp} {v = idp} q = idp

  ↓-app=cst-η' : {p : x == y} {u : f x == b} {v : f y == b}
    → (q : u == v [ (λ x → f x == b) ↓ p ])
    → ↓-app=cst-in' (↓-app=cst-out' q) == q
  ↓-app=cst-η' {p = idp} {v = idp} q = idp

  ↓-cst=app-in' : {p : x == y} {u : b == f x} {v : b == f y}
    → (u ∙ ap f p) == v
    → (u == v [ (λ x → b == f x) ↓ p ])
  ↓-cst=app-in' {p = idp} {u = idp} q = q

  ↓-cst=app-out' : {p : x == y} {u : b == f x} {v : b == f y}
    → (u == v [ (λ x → b == f x) ↓ p ])
    → (u ∙ ap f p) == v
  ↓-cst=app-out' {p = idp} {u = idp} r = r

module _ {i} {A : Type i} where

  ↓-app=idf-in : {f : A → A} {x y : A} {p : x == y}
    {u : f x == x} {v : f y == y}
    → u ∙' p == ap f p ∙ v
    → u == v [ (λ z → f z == z) ↓ p ]
  ↓-app=idf-in {p = idp} q = q

  ↓-app=idf-out : {f : A → A} {x y : A} {p : x == y}
    {u : f x == x} {v : f y == y}
    → u == v [ (λ z → f z == z) ↓ p ]
    → u ∙' p == ap f p ∙ v
  ↓-app=idf-out {p = idp} q = q

  ↓-cst=idf-in : {a : A} {x y : A} {p : x == y} {u : a == x} {v : a == y}
    → (u ∙' p) == v
    → (u == v [ (λ x → a == x) ↓ p ])
  ↓-cst=idf-in {p = idp} q = q

  ↓-cst=idf-in' : {a : A} {x y : A} {p : x == y} {u : a == x} {v : a == y}
    → (u ∙ p) == v
    → (u == v [ (λ x → a == x) ↓ p ])
  ↓-cst=idf-in' {p = idp} q = ! (∙-unit-r _) ∙ q

  ↓-idf=cst-in : {a : A} {x y : A} {p : x == y} {u : x == a} {v : y == a}
    → u == p ∙ v
    → (u == v [ (λ x → x == a) ↓ p ])
  ↓-idf=cst-in {p = idp} q = q

  ↓-idf=cst-out : {a : A} {x y : A} {p : x == y} {u : x == a} {v : y == a}
    → (u == v [ (λ x → x == a) ↓ p ])
    → u == p ∙ v
  ↓-idf=cst-out {p = idp} q = q

  ↓-idf=cst-in' : {a : A} {x y : A} {p : x == y} {u : x == a} {v : y == a}
    → u == p ∙' v
    → (u == v [ (λ x → x == a) ↓ p ])
  ↓-idf=cst-in' {p = idp} q = q ∙ ∙'-unit-l _

  ↓-idf=idf-in' : {x y : A} {p : x == y} {u : x == x} {v : y == y}
    → u ∙ p == p ∙' v
    → (u == v [ (λ x → x == x) ↓ p ])
  ↓-idf=idf-in' {p = idp} q = ! (∙-unit-r _) ∙ q ∙ ∙'-unit-l _

  ↓-idf=idf-out' : {x y : A} {p : x == y} {u : x == x} {v : y == y}
    → (u == v [ (λ x → x == x) ↓ p ])
    → u ∙ p == p ∙' v
  ↓-idf=idf-out' {p = idp} q = ∙-unit-r _ ∙ q ∙ ! (∙'-unit-l _)

{- Nondependent identity type -}

module _ {i j} {A : Type i} {B : Type j} {f g : A → B} where

  abstract
    ↓-='-in : ∀ {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
      → (u ∙' ap g p) == (ap f p ∙ v)
      → (u == v [ (λ x → f x == g x) ↓ p ])
    ↓-='-in {p = idp} q = q

    ↓-='-out : ∀ {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
      → (u == v [ (λ x → f x == g x) ↓ p ])
      → (u ∙' ap g p) == (ap f p ∙ v)
    ↓-='-out {p = idp} q = q

    ↓-='-in' : ∀ {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
      → (u ∙ ap g p) == (ap f p ∙' v)
      → (u == v [ (λ x → f x == g x) ↓ p ])
    ↓-='-in' {p = idp} q = ! (∙-unit-r _) ∙ q ∙ (∙'-unit-l _)

    ↓-='-out' : ∀ {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
      → (u == v [ (λ x → f x == g x) ↓ p ])
      → (u ∙ ap g p) == (ap f p ∙' v)
    ↓-='-out' {p = idp} q = (∙-unit-r _) ∙ q ∙ ! (∙'-unit-l _)

{- Identity type where the type is dependent -}

module _ {i j} {A : Type i} {B : A → Type j} {f g : Π A B} where

  abstract
    private
      ◃idp' : {x : A} {v : B x} {w = w₁ : B x} (q : _==_ {j} {B x} w₁ v) →
              _==_ {j} {_==_ {j} {B x} w₁ v}
              (_◃_ {i} {j} {A} {B} {x} {x} {x} {idp} {idp} {w₁} {v} {v} q idp) q
      ◃idp' = ◃idp {B = B}
      idp▹' : {x : A} {v : B x} {w = w₁ : B x} (q : _==_ {j} {B x} v w₁) →
              _==_ {j} {_==_ {j} {B x} v w₁}
              (_▹_ {i} {j} {A} {B} {x} {x} {x} {idp} {idp} {v} {v} {w₁} idp q) q
      idp▹' = idp▹ {B = B}

    ↓-=-in : {x y : A} {p : x == y} {u : g x == f x} {v : g y == f y}
      → u ◃ apd f p == apd g p ▹ v
      → (u == v [ (λ x → g x == f x) ↓ p ])
    ↓-=-in {p = idp} {u} {v} q = ! (◃idp' u) ∙ q ∙ idp▹' v

    ↓-=-out : {x y : A} {p : x == y} {u : g x == f x} {v : g y == f y}
      → (u == v [ (λ x → g x == f x) ↓ p ])
      → u ◃ apd f p == apd g p ▹ v
    ↓-=-out {p = idp} {u} {v} q = (◃idp' u) ∙ q ∙ ! (idp▹' v)

    ↓-=-in-β : {x y : A} {p : x == y} {u : g x == f x} {v : g y == f y}
      → (q : u == v [ (λ x → g x == f x) ↓ p ])
      → ↓-=-in (↓-=-out q) == q
    ↓-=-in-β {p = idp} {u} {v} q =
      ! (◃idp' u) ∙ (◃idp' u ∙ q ∙ ! (idp▹' v)) ∙ idp▹' v
        =⟨ ap (! (◃idp' u) ∙_) (∙-assoc (◃idp' u) (q ∙ ! (idp▹' v)) (idp▹' v)) ⟩
      ! (◃idp' u) ∙ ◃idp' u ∙ (q ∙ ! (idp▹' v)) ∙ idp▹' v
        =⟨ ap (λ w → ! (◃idp' u) ∙ ◃idp' u ∙ w) (∙-assoc q (! (idp▹' v)) (idp▹' v)) ⟩
      ! (◃idp' u) ∙ ◃idp' u ∙ (q ∙ ! (idp▹' v) ∙ idp▹' v)
        =⟨ ap (λ w → ! (◃idp' u) ∙ ◃idp' u ∙ (q ∙ w)) (!-inv-l (idp▹' v)) ⟩
      ! (◃idp' u) ∙ ◃idp' u ∙ q ∙ idp
        =⟨ ap (λ w → ! (◃idp' u) ∙ ◃idp' u ∙ w) (∙-unit-r q) ⟩
      ! (◃idp' u) ∙ ◃idp' u ∙ q
        =⟨ ! (∙-assoc (! (◃idp' u)) (◃idp' u) q) ⟩
      (! (◃idp' u) ∙ ◃idp' u) ∙ q
        =⟨ ap (_∙ q) (!-inv-l (◃idp' u)) ⟩
      q =∎

    ↓-=-out-η : {x y : A} {p : x == y} {u : g x == f x} {v : g y == f y}
      → (q : u ◃ apd f p == apd g p ▹ v)
      → q == ↓-=-out (↓-=-in q)
    ↓-=-out-η {p = idp} {u} {v} q = ! $
      ◃idp' u ∙ (! (◃idp' u) ∙ q ∙ idp▹' v) ∙ ! (idp▹' v)
        =⟨ ap (λ w → ◃idp' u ∙ w) (∙-assoc (! (◃idp' u)) (q ∙ idp▹' v) (! (idp▹' v))) ⟩
      ◃idp' u ∙ ! (◃idp' u) ∙ (q ∙ idp▹' v) ∙ ! (idp▹' v)
        =⟨ ap (λ w → ◃idp' u ∙ ! (◃idp' u) ∙ w) (∙-assoc q (idp▹' v) (! (idp▹' v))) ⟩
      ◃idp' u ∙ ! (◃idp' u) ∙ q ∙ idp▹' v ∙ ! (idp▹' v)
        =⟨ ap (λ w → ◃idp' u ∙ ! (◃idp' u) ∙ q ∙ w) (!-inv-r (idp▹' v)) ⟩
      ◃idp' u ∙ ! (◃idp' u) ∙ q ∙ idp
        =⟨ ap (λ w → ◃idp' u ∙ ! (◃idp' u) ∙ w) (∙-unit-r q) ⟩
      ◃idp' u ∙ ! (◃idp' u) ∙ q
        =⟨ ! (∙-assoc (◃idp' u) (! (◃idp' u)) q) ⟩
      (◃idp' u ∙ ! (◃idp' u)) ∙ q
        =⟨ ap (_∙ q) (!-inv-r (◃idp' u)) ⟩
      q =∎

  ↓-=-in-is-equiv : {x y : A} {p : x == y} {u : g x == f x} {v : g y == f y}
    → is-equiv (↓-=-in {p = p} {u = u} {v = v})
  ↓-=-in-is-equiv = is-eq _ ↓-=-out ↓-=-in-β λ q → ! (↓-=-out-η q)

  ↓-=-equiv : {x y : A} {p : x == y} {u : g x == f x} {v : g y == f y}
    → (u ◃ apd f p == apd g p ▹ v) ≃ (u == v [ (λ x → g x == f x) ↓ p ])
  ↓-=-equiv = ↓-=-in , ↓-=-in-is-equiv

-- Dependent path in a type of the form [λ x → g (f x) == x]
module _ {i j} {A : Type i} {B : Type j} (g : B → A) (f : A → B) where
  ↓-∘=idf-in' : {x y : A} {p : x == y} {u : g (f x) == x} {v : g (f y) == y}
    → ((ap g (ap f p) ∙' v) == (u ∙ p))
    → (u == v [ (λ x → g (f x) == x) ↓ p ])
  ↓-∘=idf-in' {p = idp} q = ! (∙-unit-r _) ∙ (! q) ∙ (∙'-unit-l _)
