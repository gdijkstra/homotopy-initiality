{-# OPTIONS --without-K #-}

module Eq.Funext where

open import Admit

open import lib.Basics
open import Eq.Core
open import Eq.Ap

module _ {i} {j} {A : Type i} {P : A → Type j} {f g : Π A P} where
  Funext : (r : (x : A) → Eq (f x) (g x)) → Eq f g
  Funext r = λ h q → q ∙ λ= (λ x → r x (f x) idp)

  App= : Eq f g → ((x : A) → Eq (f x) (g x))
  App= p x = Ap (λ u → u x) p

  App=-β : (r : (x : A) → Eq (f x) (g x)) (x : A) → Eq (App= (Funext r) x) (r x)
  App=-β r x = admit _

  Funext-η : (r : Eq f g) → Eq r (Funext (App= r))
  Funext-η r = admit _

module _ {i} {j} {A : Type i} {B : Type j} {f g : A → B} where
  App=-β' : 
    ∀ {j}
    {C : Type j}
    (r : (x : A) → Eq (f x) (g x))
    (h : C → A)
    → Eq (Funext (r ∘ h)) (Ap (`∘ h) (Funext r))
  App=-β' = admit _
