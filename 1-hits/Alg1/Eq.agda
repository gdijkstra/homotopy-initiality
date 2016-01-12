{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Sigma
open import Cat
open import Container
open import 1-hits.Base

-- Equality of algebra homomorphisms
module 1-hits.Alg1.Eq (s : Spec) where

open Spec s
open import 1-hits.Alg1.Alg1 s
open import 1-hits.Alg0 F₀

module _
  {X Y : Type0}
  (θ₀ : has-alg₀ X)
  (ρ₀ : has-alg₀ Y)
  (θ₁ : has-alg₁ X θ₀)
  (ρ₁ : has-alg₁ Y ρ₀)
  where

  mk-alg₁-hom-eq :
     (f g : X → Y)
     (f₀ : is-alg₀-hom θ₀ ρ₀ f)
     (g₀ : is-alg₀-hom θ₀ ρ₀ g)
     (f₁ : is-alg₁-hom θ₀ ρ₀ θ₁ ρ₁ f f₀)
     (g₁ : is-alg₁-hom θ₀ ρ₀ θ₁ ρ₁ g g₀)
     (p  : f == g)
     (p₀ : f₀ == g₀ [ (λ h → (x : ⟦ F₀ ⟧₀ X) → h (θ₀ x) == ρ₀ (⟦ F₀ ⟧₁ h x)) ↓ p ])
     (p₁ : f₁ == g₁ [ (λ h → (x : ⟦ F₁ ⟧₀ X) → G₁₁ θ₀ ρ₀ (fst h) (snd h) x (θ₁ x) == ρ₁ (⟦ F₁ ⟧₁ (fst h) x)) ↓ pair= p p₀ ])
     → mk-alg₁-hom {mk-alg₁ X θ₀ θ₁} {mk-alg₁ Y ρ₀ ρ₁} f f₀ f₁ == mk-alg₁-hom g g₀ g₁
  mk-alg₁-hom-eq f .f f₀ .f₀ g₁ .g₁ idp idp idp = idp

  open import lib.cubical.Cubical

  mk-alg₁-hom-eq-sq :
     (f g : X → Y)
     (f₀ : is-alg₀-hom θ₀ ρ₀ f)
     (g₀ : is-alg₀-hom θ₀ ρ₀ g)
     (f₁ : is-alg₁-hom θ₀ ρ₀ θ₁ ρ₁ f f₀)
     (g₁ : is-alg₁-hom θ₀ ρ₀ θ₁ ρ₁ g g₀)
     (p  : f == g)
     (p₀ : f₀ == g₀ [ (λ h → (x : ⟦ F₀ ⟧₀ X) → h (θ₀ x) == ρ₀ (⟦ F₀ ⟧₁ h x)) ↓ p ])
     (p₁ : (x : ⟦ F₁ ⟧₀ X)
         → SquareOver _ vid-square
             (f₁ x)
             (apd (λ h → G₁₁ θ₀ ρ₀ (fst h) (snd h) x (θ₁ x)) (pair= p p₀))
             (apd (λ h → ρ₁ (⟦ F₁ ⟧₁ (fst h) x)) (pair= p p₀))
             (g₁ x))
     → mk-alg₁-hom {mk-alg₁ X θ₀ θ₁} {mk-alg₁ Y ρ₀ ρ₁} f f₀ f₁ == mk-alg₁-hom g g₀ g₁
  mk-alg₁-hom-eq-sq f .f f₀ .f₀ f₁ g₁ idp idp p₁ = mk-alg₁-hom-eq f f f₀ f₀ f₁ g₁ idp idp (λ= (horiz-degen-path ∘ p₁))
