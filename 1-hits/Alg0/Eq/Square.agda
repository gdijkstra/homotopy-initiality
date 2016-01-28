{-# OPTIONS --without-K #-}

open import Container

-- Equality of algebra morphisms
module 1-hits.Alg0.Eq.Square (F : Container) where

open import lib.Basics
open import 1-hits.Alg0.Core F
open import 1-hits.Alg0.Eq.Core F
open import lib.cubical.Cubical

private
  module Prim
    (𝓧 𝓨 : Alg₀-obj)
    where

    open Alg₀-obj 𝓧
    open Alg₀-obj 𝓨 renaming (X to Y ; θ to ρ)
    open Alg₀-hom

    alg₀-hom=⊡ :
      (𝓯 𝓰 : Alg₀-hom 𝓧 𝓨)
      (p : f 𝓯 == f 𝓰)
      (p₀ : (x : ⟦ F ⟧₀ X)
          → Square
              (f₀ 𝓯 x)
              (app= p (θ x))
              (ap (λ h → ρ (⟦ F ⟧₁ h x)) p)
              (f₀ 𝓰 x))
     → 𝓯 == 𝓰
    alg₀-hom=⊡ (alg₀-hom f f₀) (alg₀-hom .f g₀) idp p₀ = ap (alg₀-hom f) (λ= (horiz-degen-path ∘ p₀)) 
  
module _
  {𝓧 𝓨 : Alg₀-obj}
  (𝓯 𝓰 : Alg₀-hom 𝓧 𝓨)
  where
  open Alg₀-obj 𝓧
  open Alg₀-obj 𝓨 renaming (X to Y ; θ to ρ)
  open Alg₀-hom 𝓯
  open Alg₀-hom 𝓰 renaming (f to g ; f₀ to g₀)
  
  record =⊡Alg₀-hom : Type0 where
    constructor =⊡alg₀-hom
    field
      p : f == g
      p₀ : (x : ⟦ F ⟧₀ X) →
             Square
               (f₀ x)
               (app= p (θ x))
               (ap (λ h → ρ (⟦ F ⟧₁ h x)) p)
               (g₀ x)

  alg₀-hom=⊡ : =⊡Alg₀-hom → 𝓯 == 𝓰
  alg₀-hom=⊡ (=⊡alg₀-hom p p₀) = Prim.alg₀-hom=⊡ 𝓧 𝓨 𝓯 𝓰 p p₀

  alg₀-hom=⊡-λ= :
    (p  : (x : X) → f x == g x)
    (p₀ : (x : ⟦ F ⟧₀ X) →
           Square
             (f₀ x)
             (p (θ x))
             (ap (λ h → ρ (⟦ F ⟧₁ h x)) (λ= p))
             (g₀ x))
    → 𝓯 == 𝓰
  alg₀-hom=⊡-λ= p p₀ = Prim.alg₀-hom=⊡ 𝓧 𝓨 𝓯 𝓰 (λ= p) (λ x → app=-β p (θ x) ∙v⊡ p₀ x)

-- (𝓯 == 𝓰) ≃ =⊡Alg₀-hom 𝓯 𝓰
open Alg₀-hom
open Alg₀-obj

f=⊡ :
  {𝓧 𝓨 : Alg₀-obj}
  {𝓯 𝓰 : Alg₀-hom 𝓧 𝓨}
  → 𝓯 == 𝓰 → (f 𝓯) == (f 𝓰)
f=⊡ = ap f

f₀=⊡ :
  {𝓧 𝓨 : Alg₀-obj}
  {𝓯 𝓰 : Alg₀-hom 𝓧 𝓨}
  (𝓹 : 𝓯 == 𝓰)
  (x : ⟦ F ⟧₀ (X 𝓧))
  → Square
      (f₀ 𝓯 x)
      (app= (f=⊡ 𝓹) (θ 𝓧 x))
      (ap (λ h → (θ 𝓨) (⟦ F ⟧₁ h x)) (f=⊡ 𝓹))
      (f₀ 𝓰 x)
f₀=⊡ idp x = horiz-degen-square idp

f=⊡-β :
  {𝓧 𝓨 : Alg₀-obj}
  {𝓯 𝓰 : Alg₀-hom 𝓧 𝓨}
  (p : f 𝓯 == f 𝓰)
  (p₀ : (x : ⟦ F ⟧₀ (X 𝓧)) →
        Square
          (f₀ 𝓯 x)
          (app= p (θ 𝓧 x))
          (ap (λ h → (θ 𝓨) (⟦ F ⟧₁ h x)) p)
          (f₀ 𝓰 x))
  → f=⊡ (alg₀-hom=⊡ 𝓯 𝓰 (=⊡alg₀-hom p p₀)) == p
f=⊡-β idp p₀ with λ= (λ x → horiz-degen-path (p₀ x))
f=⊡-β idp _ | idp = idp

-- f₀=⊡-β :
--   {𝓧 𝓨 : Alg₀-obj}
--   {𝓯 𝓰 : Alg₀-hom 𝓧 𝓨}
--   (p : f 𝓯 == f 𝓰)
--   (p₀ : (x : ⟦ F ⟧₀ (X 𝓧)) →
--         Square
--           (f₀ 𝓯 x)
--           (app= p (θ 𝓧 x))
--           (ap (λ h → (θ 𝓨) (⟦ F ⟧₁ h x)) p)
--           (f₀ 𝓰 x))
--   (x : ⟦ F ⟧₀ (X 𝓧))
--   → f₀=⊡ (alg₀-hom=⊡ 𝓯 𝓰 (=⊡alg₀-hom p p₀)) x == p₀ x [ (λ p' → Square (f₀ 𝓯 x) (app= p' (θ 𝓧 x)) (ap (λ h → θ 𝓨 (⟦ F ⟧₁ h x)) p') (f₀ 𝓰 x)) ↓ f=⊡-β p p₀ ]
-- f₀=⊡-β p p₀ x with p₀ x
-- f₀=⊡-β idp p₀ x | asdfp = {!asdfp!}

-- alg₀-hom=⊡-η :
--   {𝓧 𝓨 : Alg₀-obj}
--   {𝓯 𝓰 : Alg₀-hom 𝓧 𝓨}
--   (𝓹 : 𝓯 == 𝓰)
--   → 𝓹 == alg₀-hom=⊡ 𝓯 𝓰 (=⊡alg₀-hom (f=⊡ 𝓹) (f₀=⊡ 𝓹))
-- alg₀-hom=⊡-η {𝓯 = alg₀-hom f _} idp =
--   idp
--     =⟨ {!!} ⟩
--   ap (alg₀-hom f) (λ= (λ _ → idp))
--     =⟨ ap (λ p → ap (alg₀-hom f) (λ= (λ _ → p))) {!λ=idp!} ⟩
--   ap (alg₀-hom f) (λ= (λ _ → horiz-degen-path (horiz-degen-square idp))) ∎
