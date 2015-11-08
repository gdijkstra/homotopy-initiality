{-# OPTIONS --without-K #-}

-- Embed the category structure of paths into that of Type, which
-- gives us the category laws definitionally.

module PathList where

open import lib.Base
open import lib.PathGroupoid

module _ {A : Type0} where
  Endo : A → A → Type0
  Endo x y = (z : A) → z == x → z == y

  module _ {x y : A} where
    η : x == y → Endo x y
    η p = λ z q → q ∙ p
  
    ε : Endo x y → x == y
    ε p = p x idp
  
    ε-η : (p : x == y) → ε (η p) == p
    ε-η p = idp

  _∙-e_ : {x y z : A} → Endo x y → Endo y z → Endo x z
  f ∙-e g = λ z x → g z (f z x)

  refl : {x : A} → Endo x x 
  refl = λ z p → p

assoc :
   {A : Type0}
   {x y z w : A} →
   (p : Endo x y)
   (q : Endo y z)
   (r : Endo z w)
 → (p ∙-e (q ∙-e r)) == ((p ∙-e q) ∙-e r)
assoc p q r = idp

module _ {A : Type0} {B : A → Type0} where
  EndoOver :
    {x y : A}
    (p : Endo x y)
    (u : B x)
    (v : B y) → Type0
  EndoOver {x} {y} p u v = {z : A} {w : B z} (q : Endo z x)
    → w == u [ B ↓ ε q ] → w == v [ B ↓ ε (q ∙-e p) ]

  module _ {x y : A} (p : x == y) (u : B x) (v : B y) where
    η-Over : u == v [ B ↓ p ] → EndoOver (η p) u v
    η-Over p = λ q r → r ∙ᵈ p

    ε-Over : EndoOver (η p) u v → u == v [ B ↓ p ]
    ε-Over p = p refl idp
  
    ε-η-Over : (p : u == v [ B ↓ p ]) → ε-Over (η-Over p) == p
    ε-η-Over p = idp◃ p -- Not definitionally :(
    
  _∙ᵈ-e_ :
   {x y z : A}
   {p : Endo x y}
   {q : Endo y z}
   {u : B x}
   {v : B y}
   {w : B z}
   → (EndoOver p u v)
   → (EndoOver q v w)
   → (EndoOver (p ∙-e q) u w)
  _∙ᵈ-e_ {x} {y} {z} {p} {q} {u} {v} {w} f g = λ r wu → g (r ∙-e p) (f r wu)

  -- This sort of works, but leads to unsolved metas.
  -- assocᵈ :
  --    {a b c d : A} →
  --    (p : Endo a b)
  --    (q : Endo b c)
  --    (r : Endo c d)
  --    (u : B a)
  --    (v : B b)
  --    (w : B c)
  --    (o : B d)
  --    (f : EndoOver p u v)
  --    (g : EndoOver q v w)
  --    (h : EndoOver r w o)
  --  → (f ∙ᵈ-e (g ∙ᵈ-e h)) == ((f ∙ᵈ-e g) ∙ᵈ-e h)
  -- assocᵈ p q r u v w o f g h = idp
