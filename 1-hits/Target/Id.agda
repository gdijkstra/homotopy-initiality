{-# OPTIONS --without-K #-}

open import lib.Basics
open import 1-hits.Core
open import Container
open import FreeMonad
open import lib.types.PathSeq

module 1-hits.Target.Id (s : Spec) where

open Spec s
open import 1-hits.Alg0 F₀
open import 1-hits.Target.Core s

module _ (𝓧 : Alg₀-obj) where
  open Alg₀-obj 𝓧 renaming (θ to θ₀)

  G₁₁-id : (x : ⟦ F₁ ⟧₀ X) (p : G₁₀ 𝓧 x) → G₁₁ (id-alg₀ 𝓧) x p == p
  G₁₁-id x p = ↯
    G₁₁ (id-alg₀ 𝓧) x p
     =⟪idp⟫
    ! ((star-hom₀ (id-alg₀ 𝓧)) (l ‼ x)) ∙ ap (idf X) p ∙ (star-hom₀ (id-alg₀ 𝓧)) (r ‼ x)
     =⟪ ap (λ h → ! h ∙ ap (idf X) p ∙ star-hom₀ (id-alg₀ 𝓧) (r ‼ x)) (star-hom-id 𝓧 (l ‼ x)) ⟫
    ap (idf X) p ∙ (star-hom₀ (id-alg₀ 𝓧)) (r ‼ x)
     =⟪ ap (λ h → ap (idf X) p ∙ h) (star-hom-id 𝓧 (r ‼ x)) ⟫
    ap (idf X) p ∙ idp
     =⟪ ∙-unit-r (ap (idf X) p) ⟫
    ap (idf X) p
     =⟪ ap-idf p ⟫
    p
    ∎∎

  G₁₁-id-λ= : (x : ⟦ F₁ ⟧₀ X) → G₁₁ (id-alg₀ 𝓧) x == (λ p → p)
  G₁₁-id-λ= x = λ= (G₁₁-id x)
