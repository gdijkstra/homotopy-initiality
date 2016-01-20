{-# OPTIONS --without-K #-}

open import lib.Basics
open import Container

module 1-hits.Alg0.Alg (F : Container) where

has-alg₀ : Type0 → Type0
has-alg₀ X = ⟦ F ⟧₀ X → X

record Alg₀-obj : Type1 where
  constructor mk-alg₀
  field
    X : Type0
    θ : has-alg₀ X
    
U₀ : Alg₀-obj → Type0
U₀ (mk-alg₀ X _) = X

module _
  (𝓧 𝓨 : Alg₀-obj)
  where

  open Alg₀-obj 𝓧
  open Alg₀-obj 𝓨 renaming (X to Y ; θ to ρ)
  
  is-alg₀-hom :
    (f : X → Y)
    → Type0
  is-alg₀-hom f = (x : ⟦ F ⟧₀ X) → f (θ x) == ρ (⟦ F ⟧₁ f x)

record Alg₀-hom (𝓧 𝓨 : Alg₀-obj) : Type0 where
  constructor mk-alg₀-hom

  open Alg₀-obj 𝓧
  open Alg₀-obj 𝓨 renaming (X to Y ; θ to ρ)

  field
    f : X → Y
    f₀ : is-alg₀-hom 𝓧 𝓨 f
    
module _
  {𝓧 𝓨 𝓩 : Alg₀-obj}
  (𝓰 : Alg₀-hom 𝓨 𝓩)
  (𝓯 : Alg₀-hom 𝓧 𝓨)
  where
  
  open Alg₀-hom 𝓰 renaming (f to g ; f₀ to g₀)
  open Alg₀-hom 𝓯

  ∘₀ : is-alg₀-hom 𝓧 𝓩 (g ∘ f)
  ∘₀ = λ x → ap g (f₀ x) ∙ g₀ (⟦ F ⟧₁ f x)

  ∘-alg₀ : Alg₀-hom 𝓧 𝓩
  ∘-alg₀ = mk-alg₀-hom (g ∘ f) ∘₀

module _
  (𝓧 : Alg₀-obj)
  where

  open Alg₀-obj 𝓧

  id : X → X
  id = idf X

  id₀ : is-alg₀-hom 𝓧 𝓧 id
  id₀ = λ _ → idp

  id-alg₀ : Alg₀-hom 𝓧 𝓧
  id-alg₀ = mk-alg₀-hom id id₀
