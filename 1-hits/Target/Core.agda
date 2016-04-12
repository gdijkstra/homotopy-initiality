{-# OPTIONS --without-K #-}

open import lib.Basics
open import 1-hits.Core
open import Container
open import FreeMonad
open import lib.types.PathSeq

-- Definition and properties of target functor G.
module 1-hits.Target.Core (s : Spec) where
  open Spec s
  open import 1-hits.Alg0 F₀

  module _ (𝓧 : Alg₀-obj) where
    open Alg₀-obj 𝓧 renaming (θ to θ₀)

    G₁₀ : (x : ⟦ F₁ ⟧₀ X) → Type0
    G₁₀ x = ((θ₀ *¹) (l ‼ x) == (θ₀ *¹) (r ‼ x))

  module _ {𝓧 𝓨 : Alg₀-obj} (𝓯 : Alg₀-hom 𝓧 𝓨) where
    open Alg₀-obj 𝓧 renaming (θ to θ₀)
    open Alg₀-obj 𝓨 renaming (X to Y ; θ to ρ₀)
    open Alg₀-hom 𝓯

    G₁₁ : (x : ⟦ F₁ ⟧₀ X) → G₁₀ 𝓧 x → G₁₀ 𝓨 ((⟦ F₁ ⟧₁ f) x)
    G₁₁ x p = ↯
      (ρ₀ *¹) (l ‼ ⟦ F₁ ⟧₁ f x)
       =⟪idp⟫
      (ρ₀ *¹) (⟦ F₀ * ⟧₁ f (l ‼ x))
       =⟪ ! (star-hom₀ 𝓯 (l ‼ x)) ⟫
      f ((θ₀ *¹) (l ‼ x))
       =⟪ ap f p ⟫
      f ((θ₀ *¹) (r ‼ x))
       =⟪ star-hom₀ 𝓯 (r ‼ x) ⟫
      (ρ₀ *¹) (⟦ F₀ * ⟧₁ f (r ‼ x))
       =⟪idp⟫
      (ρ₀ *¹) (r ‼ ⟦ F₁ ⟧₁ f x) ∎∎
   -- i.e. proof term is: ! (star-hom₀ 𝓯 (l ‼ x)) ∙ ap f p ∙ star-hom₀ 𝓯 (r ‼ x)

