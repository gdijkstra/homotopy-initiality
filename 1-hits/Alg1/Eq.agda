{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Sigma
open import Cat
open import Container
open import 1-hits.Spec
open import lib.cubical.Cubical

-- Equality of algebra homomorphisms
module 1-hits.Alg1.Eq (s : Spec) where

open Spec s
open import 1-hits.Target s
open import 1-hits.Alg1.Alg s
open import 1-hits.Alg0.Alg F₀
open import 1-hits.Alg0.Eq F₀
open import lib.cubical.Cubical

private
  module Prim
    (𝓧 𝓨 : Alg₁-obj)
    where
  
    open Alg₁-obj 𝓧
    open Alg₁-obj 𝓨 renaming (𝓧' to 𝓨' ; X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)
    open Alg₁-hom

    mk-alg₁-hom-eq :
       (𝓯 𝓰 : Alg₁-hom 𝓧 𝓨)
       (𝓹'  : 𝓯' 𝓯 == 𝓯' 𝓰)
       (p₁ : (f₁ 𝓯) == (f₁ 𝓰) [ (λ 𝓱 → (x : ⟦ F₁ ⟧₀ X) → G₁₁ 𝓱 x (θ₁ x) == ρ₁ (⟦ F₁ ⟧₁ (Alg₀-hom.f 𝓱) x)) ↓ 𝓹' ])
       → 𝓯 == 𝓰
    mk-alg₁-hom-eq (mk-alg₁-hom 𝓯' f₁) (mk-alg₁-hom .𝓯' g₁) idp = ap (mk-alg₁-hom 𝓯')

    mk-alg₁-hom-eq-λ= :
       (𝓯 𝓰 : Alg₁-hom 𝓧 𝓨)
       (𝓹'  : 𝓯' 𝓯 == 𝓯' 𝓰)
       (p₁ : (x : ⟦ F₁ ⟧₀ X) → (f₁ 𝓯) x == (f₁ 𝓰) x [ (λ 𝓱 → G₁₁ 𝓱 x (θ₁ x) == ρ₁ (⟦ F₁ ⟧₁ (Alg₀-hom.f 𝓱) x)) ↓ 𝓹' ])
       → 𝓯 == 𝓰
    mk-alg₁-hom-eq-λ= (mk-alg₁-hom 𝓯' f₁) (mk-alg₁-hom .𝓯' g₁) idp p₁ = ap (mk-alg₁-hom 𝓯') (λ= p₁)

    mk-alg₁-hom-eq-square :
       (𝓯 𝓰 : Alg₁-hom 𝓧 𝓨)
       (𝓹'  : 𝓯' 𝓯 == 𝓯' 𝓰)
       (p₁ : (x : ⟦ F₁ ⟧₀ X)
           → SquareOver _ vid-square
               (f₁ 𝓯 x)
               (apd (λ 𝓱 → G₁₁ 𝓱 x (θ₁ x)) 𝓹')
               (apd (λ 𝓱 → ρ₁ (⟦ F₁ ⟧₁ (Alg₀-hom.f 𝓱) x)) 𝓹')
               (f₁ 𝓰 x))
       → 𝓯 == 𝓰
    mk-alg₁-hom-eq-square (mk-alg₁-hom 𝓯' f₁) (mk-alg₁-hom .𝓯' g₁) idp p₁ =
      mk-alg₁-hom-eq (mk-alg₁-hom 𝓯' f₁) (mk-alg₁-hom 𝓯' g₁) idp (λ= (horiz-degen-path ∘ p₁))

module _
  {𝓧 𝓨 : Alg₁-obj}
  (𝓯 𝓰 : Alg₁-hom 𝓧 𝓨)
  where
  open Alg₁-obj 𝓧
  open Alg₁-obj 𝓨 renaming (𝓧' to 𝓨' ; X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)
  open Alg₁-hom 𝓯
  open Alg₁-hom 𝓰 renaming (𝓯' to 𝓰' ; f to g ; f₀ to g₀ ; f₁ to g₁)
  
  mk-alg₁-hom-eq :
     (𝓹'  : 𝓯' == 𝓰')
     (p₁ : f₁ == g₁ [ (λ 𝓱 → (x : ⟦ F₁ ⟧₀ X) → G₁₁ 𝓱 x (θ₁ x) == ρ₁ (⟦ F₁ ⟧₁ (Alg₀-hom.f 𝓱) x)) ↓ 𝓹' ])
     → 𝓯 == 𝓰
  mk-alg₁-hom-eq = Prim.mk-alg₁-hom-eq 𝓧 𝓨 𝓯 𝓰

  mk-alg₁-hom-eq-1 :
     (p  : f == g)
     (p₀ : f₀ == g₀ [ (λ h → (x : ⟦ F₀ ⟧₀ X) → h (θ₀ x) == ρ₀ (⟦ F₀ ⟧₁ h x)) ↓ p ])
     (p₁ : f₁ == g₁ [ (λ 𝓱 → (x : ⟦ F₁ ⟧₀ X) → G₁₁ 𝓱 x (θ₁ x) == ρ₁ (⟦ F₁ ⟧₁ (Alg₀-hom.f 𝓱) x)) ↓ mk-alg₀-hom-eq 𝓯' 𝓰' p p₀ ])
     → 𝓯 == 𝓰
  mk-alg₁-hom-eq-1 p p₀ p₁ = Prim.mk-alg₁-hom-eq 𝓧 𝓨 𝓯 𝓰 (mk-alg₀-hom-eq 𝓯' 𝓰' p p₀) p₁

  mk-alg₁-hom-eq-square :
     (𝓹'  : 𝓯' == 𝓰')
     (p₁ : (x : ⟦ F₁ ⟧₀ X)
         → SquareOver _ vid-square
             (f₁ x)
             (apd (λ 𝓱 → G₁₁ 𝓱 x (θ₁ x)) 𝓹')
             (apd (λ 𝓱 → ρ₁ (⟦ F₁ ⟧₁ (Alg₀-hom.f 𝓱) x)) 𝓹')
             (g₁ x))
     → 𝓯 == 𝓰
  mk-alg₁-hom-eq-square = Prim.mk-alg₁-hom-eq-square 𝓧 𝓨 𝓯 𝓰

  open import 1-hits.Cube

  mk-alg₁-hom-eq-cube :
     (𝓹'  : 𝓯' == 𝓰')
     (p₁ : (x : ⟦ F₁ ⟧₀ X)
         → Cube (vert-degen-square (f₁ x))
                (vert-degen-square (g₁ x))
                vid-square
                (square-apd (λ 𝓱 → G₁₁ 𝓱 x (θ₁ x)) 𝓹')
                (square-apd (λ 𝓱 → ρ₁ (⟦ F₁ ⟧₁ (Alg₀-hom.f 𝓱) x)) 𝓹')
                vid-square)
     → 𝓯 == 𝓰
  mk-alg₁-hom-eq-cube 𝓹' p₁ =
    Prim.mk-alg₁-hom-eq-λ= 𝓧 𝓨 𝓯 𝓰
      𝓹'
      (λ x → from-cube (λ 𝓱 → G₁₁ 𝓱 x (θ₁ x))
                       (λ 𝓱 → ρ₁ (⟦ F₁ ⟧₁ (Alg₀-hom.f 𝓱) x))
                       𝓹'
                       (f₁ x)
                       (g₁ x) (p₁ x))
