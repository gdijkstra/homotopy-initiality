{-# OPTIONS --without-K #-}

module Container where

open import lib.Base
open import lib.types.Sigma

infix 5 _◁_

record Container : Type1 where
  constructor _◁_
  field
    Shapes    : Type0
    Positions : Shapes → Type0

-- Functorial actions
module _ where
  -- Action on objects
  ⟦_⟧₀ : Container → Type0 → Type0
  ⟦_⟧₀ (Sh ◁ Pos) X = Σ Sh (λ s → Pos s → X)

  -- Action on morphisms
  ⟦_⟧₁ : {X Y : Type0} → (F : Container) → (X → Y) → ⟦ F ⟧₀ X → ⟦ F ⟧₀ Y
  ⟦_⟧₁ (Sh ◁ Pos) f (s , t) = (s , f ∘ t)
