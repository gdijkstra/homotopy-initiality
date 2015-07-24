{-# OPTIONS --without-K #-}

module Examples where

open import Container
open import lib.types.Unit
open import lib.Base
open import FreeMonad

module Circle where
  open import 1HIT 
    (Const ⊤)
    (Const ⊤) 
    (mk-cont-morphism (cst (c (unit , (λ ())))) (λ { _ (() , _) }))
    (mk-cont-morphism (cst (c (unit , (λ ())))) (λ { _ (() , _) }))

  S¹ : Type0
  S¹ = 1HIT

  base : S¹
  base = c₀ (unit , (λ ()))

  -- This doesn't type check the way we want it to: not all functions
  -- out of the empty type are definitionally equal.
  loop : {!!} --base == base
  loop = c₁ (unit , (λ ()))

  -- TODO: S¹ rec and ind.

module PropositionalTruncation (A : Type0) where
  open import lib.types.Bool

  open import 1HIT (Const A) (⊤ ◁ cst Bool) (mk-cont-morphism (cst {!c !}) (λ _ _ → true)) {!!}
