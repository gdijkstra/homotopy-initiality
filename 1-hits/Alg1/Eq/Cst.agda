{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Sigma
open import Container
open import 1-hits.Core
open import Admit

-- Equality of algebra homomorphisms where the first component is
-- constant / definitional.
module 1-hits.Alg1.Eq.Cst (s : Spec) where

open Spec s
open import 1-hits.Target s
open import 1-hits.Alg1.Core s
open import 1-hits.Alg1.Eq.Square s
open import 1-hits.Alg0 F₀
open import lib.cubical.Cubical

module _ (𝓧 𝓨 : Alg₁-obj)
  where

  open Alg₁-obj 𝓧
  open Alg₁-obj 𝓨 renaming (𝓧' to 𝓨' ; X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)
  open Alg₁-hom

  alg₁-hom-cst2= :
    (f : X → Y)
    (f₀ : is-alg₀-hom 𝓧' 𝓨' f)
    (g₀ : is-alg₀-hom 𝓧' 𝓨' f)
    (f₁ : is-alg₁-hom 𝓧 𝓨 (alg₀-hom f f₀))
    (g₁ : is-alg₁-hom 𝓧 𝓨 (alg₀-hom f g₀))
    (p₀ : f₀ == g₀)
    (p₁ : (x : ⟦ F₁ ⟧₀ X) → Square (f₁ x) (ap (λ h₀ → G₁₁ (alg₀-hom f h₀) x (θ₁ x)) p₀) idp (g₁ x))
    → alg₁-hom {𝓧} {𝓨} (alg₀-hom f f₀) f₁ == alg₁-hom (alg₀-hom f g₀) g₁
  alg₁-hom-cst2= f f₀ .f₀ f₁ g₁ idp p₁ =
    alg₁-hom=⊡ (alg₁-hom {𝓧} {𝓨} (alg₀-hom f f₀) f₁)
               (alg₁-hom (alg₀-hom f f₀) g₁)
               idp
               p₁

  alg₁-hom-cst2=-λ :
    (f : X → Y)
    (f₀ : is-alg₀-hom 𝓧' 𝓨' f)
    (g₀ : is-alg₀-hom 𝓧' 𝓨' f)
    (f₁ : is-alg₁-hom 𝓧 𝓨 (alg₀-hom f f₀))
    (g₁ : is-alg₁-hom 𝓧 𝓨 (alg₀-hom f g₀))
    (p₀ : (x : ⟦ F₀ ⟧₀ X) → f₀ x == g₀ x)
    (p₁ : (x : ⟦ F₁ ⟧₀ X) → Square (f₁ x) (ap (λ h₀ → G₁₁ (alg₀-hom f h₀) x (θ₁ x)) (λ= p₀)) idp (g₁ x))
    → alg₁-hom {𝓧} {𝓨} (alg₀-hom f f₀) f₁ == alg₁-hom (alg₀-hom f g₀) g₁
  alg₁-hom-cst2=-λ f f₀ g₀ f₁ g₁ p₀ p₁ with (λ= p₀)
  alg₁-hom-cst2=-λ f f₀ .f₀ f₁ g₁ p₀ p₁ | idp =
    alg₁-hom=⊡ (alg₁-hom {𝓧} {𝓨} (alg₀-hom f f₀) f₁)
               (alg₁-hom (alg₀-hom f f₀) g₁)
               idp
               p₁
