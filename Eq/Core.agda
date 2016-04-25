{-# OPTIONS --without-K #-}

module Eq.Core where

open import lib.Basics

module _ {i} {A : Type i} where
  Eq : A → A → Type i
  Eq x y = (x' : A) → x' == x → x' == y

  Eq-natural : {x y : A}
    (p : Eq x y) (x' : A) (q : x' == x) → q ∙ p x idp == p x' q
  Eq-natural {x} {y} p .x idp = idp

module Correctness {i} {A : Type i} where
  to : {x y : A} → x == y → Eq x y
  to p x q = q ∙ p

  from : {x y : A} → Eq x y → x == y
  from {x} p = p x idp

  to-from : {x y : A} → (p : Eq x y) → to (from p) == p
  to-from p = λ= (λ= ∘ Eq-natural p)

  from-to : {x y : A} → (p : x == y) → from (to p) == p
  from-to p = idp

  correct : {x y : A} → Eq x y ≃ (x == y)
  correct = equiv from to from-to to-from

module _ {i} {A : Type i} where
  refl : {x : A} → Eq x x
  refl {x} = λ x' z → z

module _
  {i} {A : Type i}
  where

  private
    refl' : {x : A} → Eq x x
    refl' {x} = λ x' z → z ∙ idp
    
    refl=refl' : {x : A} → refl {x = x} == refl' {x = x}
    refl=refl' {x} = λ= (λ _ → λ= (λ p → ! (∙-unit-r p)))

  Eq-J : {a : A} {j : ULevel} (B : (a' : A) (p : Eq a a') → Type j) (d : B a refl)
    {a' : A} (p : Eq a a') → B a' p
  Eq-J B d p with Correctness.to-from p
  ... | q with Correctness.from p
  Eq-J B d ._ | idp | idp = transport (B _) refl=refl' d
  
  Eq-J' : {a : A} {j : ULevel} (B : (a' : A) (p : Eq a' a) → Type j) (d : B a refl)
    {a' : A} (p : Eq a' a) → B a' p
  Eq-J' B d p with Correctness.to-from p
  ... | q with Correctness.from p
  Eq-J' B d ._ | idp | idp = transport (B _) refl=refl' d

module _ {i} {A : Type i} where
  infixr 80 _*_

  _*_ : {x y z : A} → Eq x y → Eq y z → Eq x z
  p * q = λ x' z → q x' (p x' z)

  *-unit-l : {x y : A} (p : Eq x y) → (refl * p) == p
  *-unit-l p = idp

  *-unit-r : {x y : A} (p : Eq x y) → (p * refl) == p
  *-unit-r p = idp

  *-assoc : {x y z w : A} (p : Eq x y) (q : Eq y z) (r : Eq z w)
    → (p * q) * r == p * (q * r)
  *-assoc p q r = idp

  sym : {x y : A} → Eq x y → Eq y x
  sym {x} f x' p = p ∙' ! (f x idp)

  sym-refl : {x : A} → sym (refl {x = x}) == refl
  sym-refl {x} = idp

  sym-*-inv-r : {x y : A} (p : Eq x y) → Eq (p * sym p) refl
  sym-*-inv-r = Eq-J (λ a q → Eq (q * sym q) refl) refl

  sym-*-inv-l : {x y : A} (p : Eq x y) → Eq (sym p * p) refl
  sym-*-inv-l = Eq-J (λ a q → Eq (sym q * q) refl) refl

  infix  15 _∎*
  infixr 10 _*⟨_⟩_

  _*⟨_⟩_ : (x : A) {y z : A} → Eq x y → Eq y z → Eq x z
  _ *⟨ p ⟩ q = p * q

  _∎* : (x : A) → Eq x x
  x ∎* = refl
