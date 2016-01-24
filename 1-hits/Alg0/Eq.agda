{-# OPTIONS --without-K #-}

open import Container

-- Equality of algebra morphisms
module 1-hits.Alg0.Eq (F : Container) where

open import lib.Basics
open import 1-hits.Alg0.Core F
open import lib.cubical.Cubical

private
  module Prim
    (𝓧 𝓨 : Alg₀-obj)
    where

    open Alg₀-obj 𝓧
    open Alg₀-obj 𝓨 renaming (X to Y ; θ to ρ)
    open Alg₀-hom

    mk-alg₀-hom-eq :
      (𝓯 𝓰 : Alg₀-hom 𝓧 𝓨)
      (p : f 𝓯 == f 𝓰)
      (p₀ : (f₀ 𝓯) == (f₀ 𝓰) [ (λ h → (x : ⟦ F ⟧₀ X) → h (θ x) == ρ (⟦ F ⟧₁ h x)) ↓ p ])
      → 𝓯 == 𝓰
    mk-alg₀-hom-eq (mk-alg₀-hom f f₀) (mk-alg₀-hom .f g₀) idp = ap (mk-alg₀-hom f)
  
    mk-alg₀-hom-eq-square :
      (𝓯 𝓰 : Alg₀-hom 𝓧 𝓨)
      (p : f 𝓯 == f 𝓰)
      (p₀ : (x : ⟦ F ⟧₀ X)
          → Square (f₀ 𝓯 x) (app= p (θ x)) (ap (λ h → ρ (⟦ F ⟧₁ h x)) p) (f₀ 𝓰 x))
     → 𝓯 == 𝓰
    mk-alg₀-hom-eq-square (mk-alg₀-hom f f₀) (mk-alg₀-hom .f g₀) idp p₀ = ap (mk-alg₀-hom f) (λ= (horiz-degen-path ∘ p₀)) 
  
module _
  {𝓧 𝓨 : Alg₀-obj}
  (𝓯 𝓰 : Alg₀-hom 𝓧 𝓨)
  where
  open Alg₀-obj 𝓧
  open Alg₀-obj 𝓨 renaming (X to Y ; θ to ρ)
  open Alg₀-hom 𝓯
  open Alg₀-hom 𝓰 renaming (f to g ; f₀ to g₀)
  
  mk-alg₀-hom-eq :
    (p : f == g)
    (p₀ : f₀ == g₀ [ (λ h → (x : ⟦ F ⟧₀ X) → h (θ x) == ρ (⟦ F ⟧₁ h x)) ↓ p ])
    → 𝓯 == 𝓰
  mk-alg₀-hom-eq = Prim.mk-alg₀-hom-eq 𝓧 𝓨 𝓯 𝓰
  
  mk-alg₀-hom-eq-square :
    (p : f == g)
    (p₀ : (x : ⟦ F ⟧₀ X) →
             Square (f₀ x) (app= p (θ x)) (ap (λ h → ρ (⟦ F ⟧₁ h x)) p) (g₀ x))
    → 𝓯 == 𝓰
  mk-alg₀-hom-eq-square = Prim.mk-alg₀-hom-eq-square 𝓧 𝓨 𝓯 𝓰

  mk-alg₀-hom-eq-square-λ= :
    (p  : (x : X) → f x == g x)
    (p₀ : (x : ⟦ F ⟧₀ X) →
           Square (f₀ x) (p (θ x)) (ap (λ h → ρ (⟦ F ⟧₁ h x)) (λ= p)) (g₀ x))
    → 𝓯 == 𝓰
  mk-alg₀-hom-eq-square-λ= p p₀ = Prim.mk-alg₀-hom-eq-square 𝓧 𝓨 𝓯 𝓰 (λ= p) (λ x → app=-β p (θ x) ∙v⊡ p₀ x)
