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

module _
  (𝓧 𝓨 : Alg₀-obj)
  (θ₁ : (x : ⟦ F₁ ⟧₀ (U₀ 𝓧)) → G₁₀ 𝓧 x)
  (ρ₁ : (x : ⟦ F₁ ⟧₀ (U₀ 𝓨)) → G₁₀ 𝓨 x)  
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

  lemma-l :
    (𝓯 𝓰 : Alg₀-hom 𝓧 𝓨)
    (p : f 𝓯 == f 𝓰)
    (p₀ : (x : ⟦ F₀ ⟧₀ X)
          → Square (f₀ 𝓯 x) (app= p (θ x)) (ap (λ h → ρ (⟦ F₀ ⟧₁ h x)) p) (f₀ 𝓰 x))
    (x : ⟦ F₁ ⟧₀ X)
    →  ap (λ h → (ρ *¹) (l ‼ (⟦ F₁ ⟧₁ h x))) p
    == ap (λ 𝓱 → (ρ *¹) (l ‼ (⟦ F₁ ⟧₁ (Alg₀-hom.f 𝓱) x))) (alg₀-hom=⊡ F₀ 𝓯 𝓰 (=⊡alg₀-hom p p₀))
  lemma-l (alg₀-hom f f₀) (alg₀-hom .f g₀) idp p₀ x with (λ= (λ x₁ → horiz-degen-path (p₀ x₁)))
  lemma-l (alg₀-hom f f₀) (alg₀-hom .f .f₀) idp p₀ x | idp = idp

  lemma-r :
    (𝓯 𝓰 : Alg₀-hom 𝓧 𝓨)
    (p : f 𝓯 == f 𝓰)
    (p₀ : (x : ⟦ F₀ ⟧₀ X)
          → Square (f₀ 𝓯 x) (app= p (θ x)) (ap (λ h → ρ (⟦ F₀ ⟧₁ h x)) p) (f₀ 𝓰 x))
    (x : ⟦ F₁ ⟧₀ X)
    →  ap (λ h → (ρ *¹) (r ‼ (⟦ F₁ ⟧₁ h x))) p
    == ap (λ 𝓱 → (ρ *¹) (r ‼ (⟦ F₁ ⟧₁ (Alg₀-hom.f 𝓱) x))) (alg₀-hom=⊡ F₀ 𝓯 𝓰 (=⊡alg₀-hom p p₀))
  lemma-r (alg₀-hom f f₀) (alg₀-hom .f g₀) idp p₀ x with (λ= (λ x₁ → horiz-degen-path (p₀ x₁)))
  lemma-r (alg₀-hom f f₀) (alg₀-hom .f .f₀) idp p₀ x | idp = idp

  apd-G-correct :
    (𝓯 𝓰 : Alg₀-hom 𝓧 𝓨)
    (p : f 𝓯 == f 𝓰)
    (p₀ : (x : ⟦ F₀ ⟧₀ X)
          → Square (f₀ 𝓯 x) (app= p (θ x)) (ap (λ h → ρ (⟦ F₀ ⟧₁ h x)) p) (f₀ 𝓰 x))
    (x : ⟦ F₁ ⟧₀ X)
    → square-apd (λ 𝓱 → G₁₁ 𝓱 x (θ₁ x)) (alg₀-hom=⊡ F₀ 𝓯 𝓰 (=⊡alg₀-hom p p₀))
       == ! (lemma-l 𝓯 𝓰 p p₀ x) ∙v⊡ other-square x 𝓯 𝓰 p p₀ ⊡v∙ lemma-r 𝓯 𝓰 p p₀ x
  apd-G-correct (alg₀-hom f f₀) (alg₀-hom .f g₀) idp p₀ x with (λ= (λ x₁ → horiz-degen-path (p₀ x₁)))
  apd-G-correct (alg₀-hom f f₀) (alg₀-hom .f .f₀) idp p₀ x | idp = lemma-stuff
    {p = star-hom₀ (alg₀-hom f f₀) (l ‼ x)}
    {q = ap f (θ₁ x)}
    {r = star-hom₀ (alg₀-hom f f₀) (r ‼ x)}

  apd-ρ₁-correct :
    (𝓯 𝓰 : Alg₀-hom 𝓧 𝓨)
    (p : f 𝓯 == f 𝓰)
    (p₀ : (x : ⟦ F₀ ⟧₀ X)
          → Square (f₀ 𝓯 x) (app= p (θ x)) (ap (λ h → ρ (⟦ F₀ ⟧₁ h x)) p) (f₀ 𝓰 x))
    (x : ⟦ F₁ ⟧₀ X)
    → square-apd (λ 𝓱 → ρ₁ (⟦ F₁ ⟧₁ (Alg₀-hom.f 𝓱) x)) (alg₀-hom=⊡ F₀ 𝓯 𝓰 (=⊡alg₀-hom p p₀))
       == ! (lemma-l 𝓯 𝓰 p p₀ x) ∙v⊡ square-apd (λ h → ρ₁ (⟦ F₁ ⟧₁ h x)) p ⊡v∙ lemma-r 𝓯 𝓰 p p₀ x
  apd-ρ₁-correct (alg₀-hom f f₀) (alg₀-hom .f g₀) idp p₀ x with (λ= (λ x₁ → horiz-degen-path (p₀ x₁)))
  apd-ρ₁-correct (alg₀-hom f f₀) (alg₀-hom .f .f₀) idp p₀ x | idp = idp
