{-# OPTIONS --without-K #-}

open import Admit

module Eq.Product where

open import lib.Basics
open import Eq.Core

module _ {i j} {A : Type i} {B : Type j} where
  open import lib.types.Sigma

  pair-eq :
    {x y : A × B}
    → Eq (fst x) (fst y)
    → Eq (snd x) (snd y)
    → Eq x y
  pair-eq {a , b} {c , d} p q with Correctness.from p , Correctness.from q
  pair-eq {a , b} {.a , .b} p q | idp , idp = refl

  open import Eq.Funext

  pair-fun-eq :
    ∀ {k}
    {Z : Type k}
    {f g : Z → A × B}
    → Eq (fst ∘ f) (fst ∘ g)
    → Eq (snd ∘ f) (snd ∘ g)
    → Eq f g
  pair-fun-eq p q = Funext (λ x → pair-eq (App= p x) (App= q x))

  open import Eq.Ap

  pair-fun-eq-fst-β :
    ∀ {k}
    {Z : Type k}
    {f g : Z → A × B}
    (p : Eq (fst ∘ f) (fst ∘ g))
    (q : Eq (snd ∘ f) (snd ∘ g))
   → Eq (fst ∘₌ pair-fun-eq p q) p
  pair-fun-eq-fst-β p q = admit _

  pair-fun-eq-snd-β :
    ∀ {k}
    {Z : Type k}
    {f g : Z → A × B}
    (p : Eq (fst ∘ f) (fst ∘ g))
    (q : Eq (snd ∘ f) (snd ∘ g))
   → Eq (snd ∘₌ pair-fun-eq p q) q
  pair-fun-eq-snd-β p q = admit _
