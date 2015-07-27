{-# OPTIONS --without-K #-}

open import Desc

module Alg (hit : Desc) where
  open import lib.Base
  open import Container
  open import FreeMonad
  open Desc.Desc hit

  -- G₀ : Type -> Type is the identity functor.
  -- G₀₀ : Type0 → Type0
  -- G₀₀ X = X

  -- G₀₁ : {X Y : Type0} → X → Y → G₀₀ X → G₀₀ Y
  -- G₀₁ f = f

  record F₀-alg : Type1 where
    constructor mk-F₀-alg
    field
      X : Type0
      θ₀ : ⟦ F₀ ⟧₀ X → X

  record F₀-alg-morph (θ ρ : F₀-alg) : Type0 where
    constructor mk-F₀-alg-morph
    open F₀-alg θ
    open F₀-alg ρ renaming (X to Y ; θ₀ to ρ₀)
    field
      f : X → Y
      f₀ : f ∘ θ₀ == ρ₀ ∘ ⟦ F₀ ⟧₁ f

  -- G₁ : ∫ (F₀-alg) (F₁ ∘ U₀) → Type
  module _ (alg : F₀-alg) where
    open F₀-alg alg

    G₁₀ : ⟦ F₁ ⟧₀ X → Type0
    G₁₀ x = (θ₀ *¹) (l ‼ x) == (θ₀ *¹) (r ‼ x)

  module _ {θ ρ : F₀-alg} (morph : F₀-alg-morph θ ρ) where
    open F₀-alg θ
    open F₀-alg ρ renaming (X to Y; θ₀ to ρ₀)
    open F₀-alg-morph morph

    -- goal: (ρ₀ *¹) (l ‼ (⟦ F₁ ⟧₁ f x)) == (ρ₀ *¹) (r ‼ (⟦ F₁ ⟧₁ f x))
    G₁₁ : (x : ⟦ F₁ ⟧₀ X) → G₁₀ θ x → G₁₀ ρ (⟦ F₁ ⟧₁ f x)
    G₁₁ x p = {!ap p !}

  record F₁-alg : Type1 where
    constructor mk-F₁-alg
    open F₀-alg
    field
      prev₀ : F₀-alg
      θ₁ : (x : ⟦ F₁ ⟧₀ (X prev₀)) → G₁₀ prev₀ x
    open F₀-alg prev₀ public

  record F₁-alg-morph (θ ρ : F₁-alg) : Type0 where
    constructor mk-F₁-alg-morph
    open F₁-alg θ renaming (prev₀ to θ')
    open F₁-alg ρ renaming (X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁ ; prev₀ to ρ')
    open F₀-alg-morph
    field
      prev₁ : F₀-alg-morph θ' ρ'
      f₁ : (x : ⟦ F₁ ⟧₀ X) → G₁₁ prev₁ x (θ₁ x) == ρ₁ (⟦ F₁ ⟧₁ (f prev₁) x)
    open F₀-alg-morph prev₁ public 
