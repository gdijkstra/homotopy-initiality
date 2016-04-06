{-# OPTIONS --without-K #-}

open import Admit

open import lib.Basics
open import 1-hits.Core
open import Container
open import FreeMonad
open import lib.types.PathSeq

module 1-hits.Target.IdLaws (s : Spec) where

open Spec s
open import 1-hits.Alg0 F₀
open import 1-hits.Target.Core s
open import 1-hits.Target.Comp s
open import 1-hits.Target.Id s


module _
  {𝓧 𝓨 : Alg₀-obj}
  (𝓯 : Alg₀-hom 𝓧 𝓨)
  where

  open Alg₀-obj 𝓧 renaming (θ to θ₀)
  open Alg₀-obj 𝓨 renaming (X to Y ; θ to ρ₀)
  open Alg₀-hom 𝓯

  -- Target functor preserves right identity law
  module _ (x : ⟦ F₁ ⟧₀ X) (p : G₁₀ 𝓧 x) where
    G₁₁-comp-right-id :
      G₁₁-comp 𝓯 (id-alg₀ 𝓧) x p ∙ ap (G₁₁ 𝓯 x) (G₁₁-id 𝓧 x p) == idp
    G₁₁-comp-right-id = admit _

  -- Target functor preserves left identity law
  module _ (x : ⟦ F₁ ⟧₀ X) (p : G₁₀ 𝓧 x) where
    G₁₁-comp-left-id :
      G₁₁-comp (id-alg₀ 𝓨) 𝓯 x p ∙ G₁₁-id 𝓨 (⟦ F₁ ⟧₁ f x) (G₁₁ 𝓯 x p)
      == ap (λ h₀ → G₁₁ (alg₀-hom f h₀) x p) (λ= (left-id₀ 𝓯))
    G₁₁-comp-left-id = admit _
    
