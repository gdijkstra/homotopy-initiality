{-# OPTIONS --without-K #-}

open import Desc

module Alg (hit : Desc) where
  open import lib.Base
  open import Container
  open import FreeMonad
  open Desc.Desc hit

  record Algebra : Type1 where
    constructor mk-algebra
    field
      X : Type0
      θ₀ : ⟦ F₀ ⟧₀ X → X
      θ₁ : (x : ⟦ F₁ ⟧₀ X) → (θ₀ *¹) (apply l X x) == (θ₀ *¹) (apply r X x)

  ap∘ : {X Y Z : Type0} (f : Y → Z) {g h : X → Y} → g == h → f ∘ g == f ∘ h
  ap∘ f = ap (λ x → f ∘ x)

  module _ (θ ρ : Algebra) where
    open Algebra θ
    open Algebra ρ renaming (X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)

    open import lib.PathGroupoid

    module Comm (f : X → Y) (f₀ : f ∘ θ₀ == ρ₀ ∘ ⟦ F₀ ⟧₁ f) where
      -- TODO: Refactor ActionMorphisms?
      open ActionMorphisms F₀ θ₀ ρ₀ f (λ x → ! (ap (λ g → g x) f₀))

      comm : (ρ₀ *¹) ∘ apply l Y ∘ ⟦ F₁ ⟧₁ f == (ρ₀ *¹) ∘ apply r Y ∘ ⟦ F₁ ⟧₁ f
           → f ∘ (θ₀ *¹) ∘ apply l X == f ∘ (θ₀ *¹) ∘ apply r X
      comm p = 
        f ∘ (θ₀ *¹) ∘ apply l X 
          =⟨ ap (λ g → g ∘ apply l X) (! comm*-ext) ⟩ 
        (ρ₀ *¹) ∘ ⟦ F₀ * ⟧₁ f ∘ apply l X
          =⟨ idp ⟩ -- naturality of l
        (ρ₀ *¹) ∘ apply l Y ∘ ⟦ F₁ ⟧₁ f
          =⟨ p ⟩
        (ρ₀ *¹) ∘ apply r Y ∘ ⟦ F₁ ⟧₁ f
          =⟨ idp ⟩ -- naturality of r
        (ρ₀ *¹) ∘ ⟦ F₀ * ⟧₁ f ∘ apply r X
          =⟨ ap (λ g → g ∘ apply r X) comm*-ext ⟩
        f ∘ (θ₀ *¹) ∘ apply r X ∎

  open import lib.Funext

  record AlgebraMorphism (θ ρ : Algebra) : Type0 where
    constructor mk-morphism
    open Algebra θ
    open Algebra ρ renaming (X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)
    open Comm θ ρ

    field
      f : X → Y
      f₀ : f ∘ θ₀ == ρ₀ ∘ ⟦ F₀ ⟧₁ f
      f₁ : ap f ∘ θ₁ == {!!} ∘ ρ₁ ∘ ⟦ F₁ ⟧₁ f
--      f₁ : (x : ⟦ F₁ ⟧₀ X) → .
