{-# OPTIONS --without-K #-}

open import Container

-- Equality of algebra morphisms
module 1-hits.Alg0.Eq (F : Container) where

open import lib.Basics
open import 1-hits.Alg0.Alg F
open import lib.cubical.Cubical

-- We need to get parts of the algebra morphisms as actual arguments
-- to functions, so we can pattern match on the equality proofs
-- properly.
private
  module Prim
    {X Y : Type0}
    (θ : has-alg₀ X)
    (ρ : has-alg₀ Y)
    where
  
    mk-alg₀-hom-eq-square :
       (f g : X → Y)
       (f₀ : is-alg₀-hom θ ρ f)
       (g₀ : is-alg₀-hom θ ρ g)
       (p  : f == g)
       (p₀ : (x : ⟦ F ⟧₀ X) →
             Square (f₀ x) (app= p (θ x)) (ap (λ h → ρ (⟦ F ⟧₁ h x)) p) (g₀ x))
     → (f , f₀) == (g , g₀)
    mk-alg₀-hom-eq-square f .f f₀ g₀ idp p₀ = pair= idp (λ= (horiz-degen-path ∘ p₀)) 
  
    mk-alg₀-hom-eq-square-λ= :
       (f g : X → Y)
       (f₀ : is-alg₀-hom θ ρ f)
       (g₀ : is-alg₀-hom θ ρ g)
       (p  : (x : X) → f x == g x)
       (p₀ : (x : ⟦ F ⟧₀ X) →
             Square (f₀ x) (p (θ x)) (ap (λ h → ρ (⟦ F ⟧₁ h x)) (λ= p)) (g₀ x))
     → (f , f₀) == (g , g₀)
    mk-alg₀-hom-eq-square-λ= f g f₀ g₀ p p₀ = mk-alg₀-hom-eq-square f g f₀ g₀ (λ= p) (λ x → app=-β p (θ x) ∙v⊡ p₀ x)
  
module _
  {𝓧 𝓨 : Alg₀-obj}
  (𝓯 𝓰 : Alg₀-hom 𝓧 𝓨)
  where
  open Σ 𝓧 renaming (fst to X ; snd to θ)
  open Σ 𝓨 renaming (fst to Y ; snd to ρ)
  open Σ 𝓯 renaming (fst to f ; snd to f₀)
  open Σ 𝓰 renaming (fst to g ; snd to g₀)
  
  mk-alg₀-hom-eq :
    (p : f == g)
    (p₀ : f₀ == g₀ [ (λ h → (x : ⟦ F ⟧₀ X) → h (θ x) == ρ (⟦ F ⟧₁ h x)) ↓ p ])
    → 𝓯 == 𝓰
  mk-alg₀-hom-eq p p₀ = pair= p p₀
  
  mk-alg₀-hom-eq-square :
    (p : f == g)
    (p₀ : (x : ⟦ F ⟧₀ X) →
             Square (f₀ x) (app= p (θ x)) (ap (λ h → ρ (⟦ F ⟧₁ h x)) p) (g₀ x))
    → 𝓯 == 𝓰
  mk-alg₀-hom-eq-square p p₀ = Prim.mk-alg₀-hom-eq-square θ ρ f g f₀ g₀ p p₀

  mk-alg₀-hom-eq-square-λ= :
    (p  : (x : X) → f x == g x)
    (p₀ : (x : ⟦ F ⟧₀ X) →
           Square (f₀ x) (p (θ x)) (ap (λ h → ρ (⟦ F ⟧₁ h x)) (λ= p)) (g₀ x))
    → 𝓯 == 𝓰
  mk-alg₀-hom-eq-square-λ= p p₀ = Prim.mk-alg₀-hom-eq-square-λ= θ ρ f g f₀ g₀ p p₀
