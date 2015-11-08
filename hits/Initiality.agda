{-# OPTIONS --without-K #-}

open import hits.Desc

module hits.Initiality (desc : Desc) where

open Desc desc

open import Container
open import FreeMonad
open import lib.Basics
open import Alg F₀
open import hits.Alg desc
open import hits.Target desc
open import fam.FreeMonadAlg
open import FreeMonadAlg

module _ (𝓣 : Alg₁) where
  open Alg₁ 𝓣 renaming (X to T ; θ₀ to c₀ ; θ₁ to c₁)

  -- Existence
  module Existence (𝓧 : Alg₁) where
    open Alg₁ 𝓧

    f-B : T → Type0
    f-B _ = X

    f-m₀ : (x : ⟦ F₀ ⟧₀ T) → □ F₀ f-B x → X
    f-m₀ (s , _) u = θ₀ (s , u)

    f-lᵈ : (x : ⟦ F₁ ⟧₀ T) → □ F₁ f-B x → □ (F₀ *) f-B (l ‼ x)
    f-lᵈ (s , t) u p* = u (ContainerMorphism.g l s p*)
      
    f-rᵈ : (x : ⟦ F₁ ⟧₀ T) → □ F₁ f-B x → □ (F₀ *) f-B (r ‼ x)
    f-rᵈ (s , t) u p* = u (ContainerMorphism.g r s p*)

    f-m₀*ᵈ : (x : ⟦ F₀ * ⟧₀ T) → □ (F₀ *) f-B x → f-B ((c₀ *¹) x)
    f-m₀*ᵈ = _,_*ᵈ {A = T} {B = f-B} c₀ f-m₀


    f-m₁ : (x : ⟦ F₁ ⟧₀ T) (y : □ F₁ f-B x) → f-m₀*ᵈ (l ‼ x) (f-lᵈ x y) == f-m₀*ᵈ (r ‼ x) (f-rᵈ x y) [ f-B ↓ c₁ x ]
    f-m₁ (s , _) u = ↓-cst-in {!θ₁ (s , u) !}
