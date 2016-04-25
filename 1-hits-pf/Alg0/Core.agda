{-# OPTIONS --without-K #-}

open import lib.Basics
open import Container
open import Eq

module 1-hits-pf.Alg0.Core (F : Container) where

open import Cat

has-alg₀ : Type0 → Type0
has-alg₀ X = ⟦ F ⟧₀ X → X

record Alg₀-obj : Type1 where
  constructor alg₀
  field
    X : Type0
    θ : has-alg₀ X
    
U₀ : Alg₀-obj → Type0
U₀ (alg₀ X _) = X

module _
  (𝓧 𝓨 : Alg₀-obj)
  where

  open Alg₀-obj 𝓧
  open Alg₀-obj 𝓨 renaming (X to Y ; θ to ρ)
  
  is-alg₀-hom :
    (f : X → Y)
    → Type0
  is-alg₀-hom f = Eq (f ∘ θ) (ρ ∘ ⟦ F ⟧₁ f)

record Alg₀-hom (𝓧 𝓨 : Alg₀-obj) : Type0 where
  constructor alg₀-hom

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
  ∘₀ = Ap (g ∘`) f₀ * Ap (`∘ ⟦ F ⟧₁ f) g₀

  ∘-alg₀ : Alg₀-hom 𝓧 𝓩
  ∘-alg₀ = alg₀-hom (g ∘ f) ∘₀

module _
  (𝓧 : Alg₀-obj)
  where

  open Alg₀-obj 𝓧

  id : X → X
  id = idf X

  id₀ : is-alg₀-hom 𝓧 𝓧 id
  id₀ = refl

  id-alg₀ : Alg₀-hom 𝓧 𝓧
  id-alg₀ = alg₀-hom id id₀
  
Alg₀ : Cat
Alg₀ = record
  { obj = Alg₀-obj
  ; hom = Alg₀-hom
  ; comp = ∘-alg₀
  ; id = id-alg₀
  }
