{-# OPTIONS --without-K #-}

open import Admit

open import 1-hits-pf.Core
open import Container

-- Equality of algebra morphisms
module 1-hits-pf.Alg1.Eq (s : Spec) where

open import Eq
open import lib.Basics
open import 1-hits-pf.Alg1.Core s
open Spec s
open import 1-hits-pf.Alg0 F₀
open import 1-hits-pf.Alg0.FreeMonad F₀

-- Equality where only the last two fields are not definitionally equal.
module _
  {𝓧 𝓨 : Alg₁-obj}
  where
  open Alg₁-obj 𝓧
  open Alg₁-obj 𝓨 renaming (𝓧' to 𝓨' ; X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)
  
  alg₁-hom=' :
    (f : X → Y)
    (f₀ : is-alg₀-hom 𝓧' 𝓨' f)
    (g₀ : is-alg₀-hom 𝓧' 𝓨' f)
    (f₁ : is-alg₁-hom 𝓧 𝓨 (alg₀-hom f f₀))
    (g₁ : is-alg₁-hom 𝓧 𝓨 (alg₀-hom f g₀))
    (p₀ : Eq f₀ g₀)
    (p₁ : Eq (f₁ ⊡h* Ap (λ h₀ → Ap (`∘ apply r X) (star-hom₀ (alg₀-hom f h₀))) p₀)
             (Ap (λ h₀ → Ap (`∘ apply l X) (star-hom₀ (alg₀-hom f h₀))) p₀ *h⊡ g₁))
    → Eq (alg₁-hom {𝓧} {𝓨} (alg₀-hom f f₀) f₁) (alg₁-hom {𝓧} {𝓨} (alg₀-hom f g₀) g₁)
  alg₁-hom=' f f₀ g₀ f₁ g₁ p₀ p₁ = admit _
