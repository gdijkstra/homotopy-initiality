{-# OPTIONS --without-K #-}

open import Container
open import FreeMonad
open import 1-hits.Core

-- Some reasoning about apd of G₁₁. This might need to be migrated to
-- something different.
module 1-hits.ApdTarget (s : Spec) where

open Spec s
open import lib.Basics
open import 1-hits.Alg0.Core F₀
open import 1-hits.Alg0.FreeMonad F₀
open import 1-hits.Alg0.Eq
open import 1-hits.Target s
open import lib.cubical.Cubical
open import 1-hits.Cube

module Prim
  (𝓧 𝓨 : Alg₀-obj)
  (θ₁ : (x : ⟦ F₁ ⟧₀ (U₀ 𝓧)) → G₁₀ 𝓧 x)
  where

  open Alg₀-obj 𝓧
  open Alg₀-obj 𝓨 renaming (X to Y ; θ to ρ)
  open Alg₀-hom

  ⊡* :
    (𝓯 𝓰 : Alg₀-hom 𝓧 𝓨)
    (p : f 𝓯 == f 𝓰)
    (p₀ : (x : ⟦ F₀ ⟧₀ X)
          → Square (f₀ 𝓯 x) (app= p (θ x)) (ap (λ h → ρ (⟦ F₀ ⟧₁ h x)) p) (f₀ 𝓰 x))
   → (x : ⟦ F₀ * ⟧₀ X)
          → Square (star-hom₀ 𝓯 x) (app= p ((θ *¹) x)) (ap (λ h → (ρ *¹) (⟦ F₀ * ⟧₁ h x)) p) (star-hom₀ 𝓰 x)
  ⊡* (alg₀-hom f f₀) (alg₀-hom .f g₀) idp p₀ x = =⊡Alg₀-hom.p₀ (F₀ *) (star-hom=⊡* F₀ 𝓯 𝓰 (=⊡alg₀-hom idp p₀)) x
    where 𝓯 = (alg₀-hom f f₀)
          𝓰 = (alg₀-hom f g₀)


  -- We hope to show that the square:
  --   square-apd (λ 𝓱 → G₁₁ 𝓱 x (θ₁ x)) (alg₀-hom=⊡ F₀ 𝓯 𝓰 (=⊡alg₀-hom p p₀))
  -- in some sense factors as three squares. Since G₁₁ 𝓱 x (θ₁ x) is defined as:
  --   h₀* (l x) ∙ ap h p ∙ h₀* (r x)
  -- one would guess that the apd square of this factors into three
  -- squares corresponding to each factor of the path
  module _ (x : ⟦ F₁ ⟧₀ X)
           (𝓯 𝓰 : Alg₀-hom 𝓧 𝓨)
           (p : f 𝓯 == f 𝓰)
           (p₀ : (x : ⟦ F₀ ⟧₀ X) → Square (f₀ 𝓯 x) (app= p (θ x)) (ap (λ h → ρ (⟦ F₀ ⟧₁ h x)) p) (f₀ 𝓰 x))
    where
    other-square : Square
      (! (star-hom₀ 𝓯 (l ‼ x)) ∙ ap (f 𝓯) (θ₁ x) ∙ star-hom₀ 𝓯 (r ‼ x))
      (ap (λ h → (ρ *¹) (⟦ F₀ * ⟧₁ h (l ‼ x))) p)
      (ap (λ h → (ρ *¹) (⟦ F₀ * ⟧₁ h (r ‼ x))) p)
      (! (star-hom₀ 𝓰 (l ‼ x)) ∙ ap (f 𝓰) (θ₁ x) ∙ star-hom₀ 𝓰 (r ‼ x))
    other-square = !□v (⊡* 𝓯 𝓰 p p₀ (l ‼ x)) ⊡v square-apd (λ h → ap h (θ₁ x)) p ⊡v ⊡* 𝓯 𝓰 p p₀ (r ‼ x)

  -- apd-G :
  --   (𝓯 𝓰 : Alg₀-hom 𝓧 𝓨)
  --   (p : f 𝓯 == f 𝓰)
  --   (p₀ : (x : ⟦ F₀ ⟧₀ X)
  --         → Square (f₀ 𝓯 x) (app= p (θ x)) (ap (λ h → ρ (⟦ F₀ ⟧₁ h x)) p) (f₀ 𝓰 x))
  --   (x : ⟦ F₁ ⟧₀ X)
  --   → square-apd (λ 𝓱 → G₁₁ 𝓱 x (θ₁ x)) (alg₀-hom=⊡ F₀ 𝓯 𝓰 (=⊡alg₀-hom p p₀))
  --      == {!!□v (⊡* 𝓯 𝓰 p p₀ (l ‼ x))!} ⊡v {!square-apd !} ⊡v {!(⊡* 𝓯 𝓰 p p₀ (r ‼ x))!}
  -- apd-G f g p p₀ = {!!}
