{-# OPTIONS --without-K #-}

open import lib.Basics
open import Container
open import 1-hits.Spec

module 1-hits.Alg1.Alg (s : Spec) where

open Spec s
open import 1-hits.Alg0.Alg F₀
open import 1-hits.Target s

has-alg₁ :
  (𝓧 : Alg₀-obj)
  → Type0
has-alg₁ 𝓧 = (x : ⟦ F₁ ⟧₀ (U₀ 𝓧)) → G₁₀ 𝓧 x

record Alg₁-obj : Type1 where
  constructor mk-alg₁

  field
   𝓧' : Alg₀-obj
   θ₁ : has-alg₁ 𝓧'

  X = Alg₀-obj.X 𝓧'
  θ₀ = Alg₀-obj.θ 𝓧'

module _
  (𝓧 𝓨 : Alg₁-obj)
  where

  open Alg₁-obj 𝓧
  open Alg₁-obj 𝓨 renaming (𝓧' to 𝓨' ; X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)
  
  module _ (𝓯' : Alg₀-hom 𝓧' 𝓨') where
    open Alg₀-hom 𝓯'
    is-alg₁-hom : Type0
    is-alg₁-hom = (x : ⟦ F₁ ⟧₀ X) → G₁₁ 𝓯' x (θ₁ x) == ρ₁ (⟦ F₁ ⟧₁ f x) 

record Alg₁-hom (𝓧 𝓨 : Alg₁-obj) : Type0 where
  constructor mk-alg₁-hom

  open Alg₁-obj 𝓧
  open Alg₁-obj 𝓨 renaming (𝓧' to 𝓨' ; X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)
  
  field
    𝓯' : Alg₀-hom 𝓧' 𝓨'
    f₁ : is-alg₁-hom 𝓧 𝓨 𝓯'

  f = Alg₀-hom.f 𝓯'
  f₀ = Alg₀-hom.f₀ 𝓯'

module _
  {𝓧 𝓨 𝓩 : Alg₁-obj}
  (𝓰 : Alg₁-hom 𝓨 𝓩)
  (𝓯 : Alg₁-hom 𝓧 𝓨)
  where
  
  open Alg₁-obj 𝓧
  open Alg₁-hom 𝓰 renaming (𝓯' to 𝓰' ; f to g ; f₀ to g₀ ; f₁ to g₁)
  open Alg₁-hom 𝓯

  ∘₁ : is-alg₁-hom 𝓧 𝓩 (∘-alg₀ 𝓰' 𝓯')
  ∘₁ = λ x → G₁₁-comp 𝓰' 𝓯' x (θ₁ x) ∙ ap (G₁₁ 𝓰' (⟦ F₁ ⟧₁ f x)) (f₁ x) ∙ g₁ (⟦ F₁ ⟧₁ f x)

  ∘-alg₁ : Alg₁-hom 𝓧 𝓩
  ∘-alg₁ = mk-alg₁-hom (∘-alg₀ 𝓰' 𝓯') ∘₁ 

module _
  (𝓧 : Alg₁-obj)
  where

  open Alg₁-obj 𝓧

  id₁ : is-alg₁-hom 𝓧 𝓧 (id-alg₀ 𝓧')
  id₁ = λ x → G₁₁-id 𝓧' x (θ₁ x)

  id-alg₁ : Alg₁-hom 𝓧 𝓧
  id-alg₁ = mk-alg₁-hom (id-alg₀ 𝓧') id₁
