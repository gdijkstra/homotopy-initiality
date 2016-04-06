{-# OPTIONS --without-K #-}

open import Admit

open import lib.Basics
open import 1-hits.Core
open import Container
open import FreeMonad
open import lib.types.PathSeq

module 1-hits.Target.AssocLaw (s : Spec) where

open Spec s
open import 1-hits.Alg0 F₀
open import 1-hits.Target.Core s
open import 1-hits.Target.Comp s
open import 1-hits.Target.Id s

module _
  {𝓧 𝓨 𝓩 𝓦 : Alg₀-obj}
  (𝓱 : Alg₀-hom 𝓩 𝓦)
  (𝓰 : Alg₀-hom 𝓨 𝓩)
  (𝓯 : Alg₀-hom 𝓧 𝓨)
  where

  open Alg₀-obj 𝓧
  open Alg₀-obj 𝓨 renaming (X to Y ; θ to ρ₀)
  open Alg₀-obj 𝓩 renaming (X to Z ; θ to ζ₀)
  open Alg₀-obj 𝓦 renaming (X to W ; θ to ω₀)
  open Alg₀-hom 𝓱 renaming (f to h ; f₀ to h₀)
  open Alg₀-hom 𝓰 renaming (f to g ; f₀ to g₀)
  open Alg₀-hom 𝓯
  
  -- Target functor preserves associativity
  module _ (x : ⟦ F₁ ⟧₀ X) (p : G₁₀ 𝓧 x) where
    G₁₁-assoc :
      G₁₁-comp (∘-alg₀ 𝓱 𝓰) 𝓯 x p
      ∙ G₁₁-comp 𝓱 𝓰 (⟦ F₁ ⟧₁ f x) (G₁₁ 𝓯 x p)
      ==
      ap (λ p₀ → G₁₁ (alg₀-hom (h ∘ g ∘ f) p₀) x p) (λ= (assoc₀ 𝓱 𝓰 𝓯))
      ∙ G₁₁-comp 𝓱 (∘-alg₀ 𝓰 𝓯) x p
      ∙ ap (G₁₁ 𝓱 (⟦ F₁ ⟧₁ (g ∘ f) x)) (G₁₁-comp 𝓰 𝓯 x p)
    G₁₁-assoc = admit _
