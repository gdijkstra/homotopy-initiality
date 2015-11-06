{-# OPTIONS --without-K #-}

-- An alternative to PathSeq
module PathList where

open import lib.Base
open import lib.PathGroupoid

module _ {A : Type0} where
  Endo : A → A → Type0
  Endo x y = {z : A} → z == x → z == y

  module _ {x y : A} where
    η : x == y → Endo x y
    η p = λ q → q ∙ p
  
    ε : Endo x y → x == y
    ε p = p idp
  
    ε-η : (p : x == y) → ε (η p) == p
    ε-η p = idp

  _∙-e_ : {x y z : A} → Endo x y → Endo y z → Endo x z
  f ∙-e g = g ∘ f

  refl : {x x : A} → Endo x x 
  refl = λ x → x

module _ {A : Type0} {B : A → Type0} where
  EndoOver : {x y : A} (p : Endo x y) (u : B x) (v : B y) → Type0
  EndoOver {x} {y} p u v = {z : A} {w : B z} {q : Endo z x}
    → w == u [ B ↓ ε q ] → w == v [ B ↓ ε (q ∙-e p) ]

  module _ {x y : A} (p : x == y) (u : B x) (v : B y) where
    η-Over : u == v [ B ↓ p ] → EndoOver (η p) u v
    η-Over p = λ r → r ∙ᵈ p

    ε-Over : EndoOver (η p) u v → u == v [ B ↓ p ]
    ε-Over p = p {z = x} {w = u} {q = refl {A} {x} {x}} idp
  
--    ε-η-Over : (p : u == v [ B ↓ p ]) → ε-Over (η-Over p) == p
--    ε-η-Over p = idp
    
