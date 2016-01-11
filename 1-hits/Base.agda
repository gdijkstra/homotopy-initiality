{-# OPTIONS --without-K #-}

module 1-hits.Base where

open import lib.Basics
open import lib.types.Sigma
open import Cat
open import Container
open import FreeMonad
open import 1-hits.Alg0 
open import Admit

record Spec : Type1 where
  constructor mk-spec
  field
    F₀ : Container
    F₁ : Container
    l r : ContHom F₁ (F₀ *)

  abstract
    G₁₀ : (X : Type0) (θ₀ : has-alg₀ F₀ X) (x : ⟦ F₁ ⟧₀ X) → Type0
    G₁₀ X θ₀ x = admit _ -- eventually something like: {!(θ₀ *¹) (l ‼ x) == (θ₀ *¹) (r ‼ x)!}
  
    G₁₁ :
      {X Y : Type0}
      (θ₀ : has-alg₀ F₀ X)
      (ρ₀ : has-alg₀ F₀ Y)
      (f : X → Y)
      (f₀ : is-alg₀-hom F₀ θ₀ ρ₀ f)
      (x : ⟦ F₁ ⟧₀ X)
      → G₁₀ X θ₀ x → G₁₀ Y ρ₀ ((⟦ F₁ ⟧₁ f) x)
    G₁₁ = admit _

-- Properties of target functor G.
module _ (s : Spec) where
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
    

  G₁₀-prod :
    {X Y : Type0}
    (θ₀ : has-alg₀ F₀ X)
    (ρ₀ : has-alg₀ F₀ Y)
    (x : ⟦ F₁ ⟧₀ (X × Y))
    (p : G₁₀ X θ₀ (⟦ F₁ ⟧₁ fst x))
    (q : G₁₀ Y ρ₀ (⟦ F₁ ⟧₁ snd x))
    → G₁₀ (X × Y) (_×-alg₀_ F₀ θ₀ ρ₀) x
  G₁₀-prod θ₀ ρ₀ x p q = admit _
