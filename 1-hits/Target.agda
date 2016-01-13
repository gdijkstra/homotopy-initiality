{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Sigma
open import Cat
open import Container
open import FreeMonad
open import 1-hits.Alg0.Alg 
open import Admit
open import 1-hits.Spec

-- Properties of target functor G.
module 1-hits.Target (s : Spec) where
  open Spec s

  G₁₁-id :
    {X : Type0}
    (θ₀ : has-alg₀ F₀ X)
    (x : ⟦ F₁ ⟧₀ X)
    (y : G₁₀ X θ₀ x)
    → G₁₁ θ₀ θ₀ (idf X) (λ x' → idp) x y == y
  G₁₁-id θ₀ x y = admit _

  G₁₁-comp :
    {X Y Z : Type0}
    (θ₀ : has-alg₀ F₀ X)
    (ρ₀ : has-alg₀ F₀ Y)
    (ζ₀ : has-alg₀ F₀ Z)
    (g : Y → Z)
    (f : X → Y)
    (g₀ : is-alg₀-hom F₀ ρ₀ ζ₀ g)
    (f₀ : is-alg₀-hom F₀ θ₀ ρ₀ f)
    (x : ⟦ F₁ ⟧₀ X)
    (y : G₁₀ X θ₀ x)
    → G₁₁ θ₀ ζ₀ (g ∘ f) (λ x' → ap g (f₀ x') ∙ g₀ (⟦ F₀ ⟧₁ f x')) x y
      == G₁₁ ρ₀ ζ₀ g g₀ (⟦ F₁ ⟧₁ f x) (G₁₁ θ₀ ρ₀ f f₀ x y)
  G₁₁-comp θ₀ ρ₀ ζ₀ g f g₀ f₀ x y = admit _
    

  -- Target functor preserves products
  module _
      {X Y : Type0}
      (θ₀ : has-alg₀ F₀ X)
      (ρ₀ : has-alg₀ F₀ Y)
      (x : ⟦ F₁ ⟧₀ (X × Y))
    where

    open import 1-hits.Alg0.Limits F₀
  
    G₁₀-prod :
      (p : G₁₀ X θ₀ (⟦ F₁ ⟧₁ fst x))
      (q : G₁₀ Y ρ₀ (⟦ F₁ ⟧₁ snd x))
      → G₁₀ (X × Y) (_×-alg₀_ θ₀ ρ₀) x
    G₁₀-prod p q = admit _
  
    G₁₀-π₁ :
      (p : G₁₀ X θ₀ (⟦ F₁ ⟧₁ fst x))
      (q : G₁₀ Y ρ₀ (⟦ F₁ ⟧₁ snd x))
      → G₁₁ (θ₀ ×-alg₀ ρ₀) θ₀ fst (λ x₁ → idp) x (G₁₀-prod p q) == p
    G₁₀-π₁ p q = admit _
  
    G₁₀-π₂ :
      (p : G₁₀ X θ₀ (⟦ F₁ ⟧₁ fst x))
      (q : G₁₀ Y ρ₀ (⟦ F₁ ⟧₁ snd x))
      → G₁₁ (θ₀ ×-alg₀ ρ₀) ρ₀ snd (λ x₁ → idp) x (G₁₀-prod p q) == q
    G₁₀-π₂ p q = admit _
