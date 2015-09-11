{-# OPTIONS --without-K #-}

module Utils where

open import lib.Basics

transport-id-nondep : ∀ {i j}
    (A : Type i) (B : Type j) (f g : A → B) {a a' : A} (p : a == a') (q : f a == g a)
  → transport (λ x → f x == g x) p q == ! (ap f p) ∙ q ∙ (ap g p)
transport-id-nondep A B₁ f₁ g idp q = ! (∙-unit-r q)

triple= : ∀ {i j k} {A : Type i} {B : A → Type j} {C : Σ A B → Type k}
  {a a' : A}
  (p : a == a')
  {b : B a} {b' : B a'}
  {c : C (a , b)} {c' : C (a' , b')}
  (q : b == b' [ B ↓ p ])
  (r : c == c' [ C ↓ pair= p q ])
  → (a , b , c) == (a' , b' , c')
triple= {a = a} idp {b = b} idp r = ap (λ x → a , b , x) r

→-path-over : ∀ {i j}
  {A B : Type i}
  {C D : Type j}
  → (p : A == B)
  → (q : C == D)
  → (f : A → C)
  → (g : B → D)
  → (coe q ∘ f ∘ coe! p == g)
  → f == g [ (λ z → fst z → snd z) ↓ pair= p (↓-cst-in q) ]
→-path-over idp idp f g p = p

Im : ∀ {i j} {X : Type i} {Y : Type j} (f : X → Y) → Type (lmax i j)
Im {Y = Y} f = Σ Y (hfiber f)

-- Im f ≃ X
module _ {i j} {X : Type i} {Y : Type j} (f : X → Y) where
  private
    to : Im f → X
    to (fx , x , f-x=fx) = x
  
    from : X → Im f
    from x = f x , x , idp
  
    to-from : (x : X) → to (from x) == x
    to-from x = idp
  
    from-to : (x : Im f) → from (to x) == x
    from-to (.(f x), x , idp) = idp

  Im-f≃X : Im f ≃ X
  Im-f≃X = equiv to from to-from from-to

coe-β-λ= : ∀ {i} {A B : Type i} (e : A ≃ B)
  → coe (ua e) == –> e
coe-β-λ= e = λ= (coe-β e)

coe!-β-λ= : ∀ {i} {A B : Type i} (e : A ≃ B)
  → coe! (ua e) == <– e
coe!-β-λ= e = λ= (coe!-β e)

module _ {i} {X : Type i} where
  p=q→!p∙q=idp : {x y : X} (p q : x == y)
               → p == q → ! p ∙ q == idp
  p=q→!p∙q=idp p .p idp = !-inv-l p

module _
  {i j}
  {A : Type i} (B : A → Type j)
  {x y : A} (p q : x == y)
  (u : B x) (v : B y) where
  PathOver-transport : p == q → u == v [ B ↓ p ] → u == v [ B ↓ q ]
  PathOver-transport = transport (λ s → u == v [ B ↓ s ])

module _
  {i j}
  {A : Type i} (B B' : A → Type j)  where
  transportB→B' :
    {a a' : A}
    (p : a == a')
    (f : B a → B' a)
    (x : B a') → transport (λ x' → B x' → B' x') p f x == transport B' p (f (transport B (! p) x))
  transportB→B' idp f x = idp

