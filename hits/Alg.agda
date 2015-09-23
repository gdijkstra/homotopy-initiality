{-# OPTIONS --without-K #-}

open import hits.Desc

module hits.Alg (desc : Desc) where
open import lib.Basics
open import Container
open import FreeMonad
open import Alg renaming (Alg to Alg₀)
open import hits.Target desc

open Desc desc

record Alg₁ : Type1 where
  constructor mk-alg₁
  field
    X,θ : Alg₀ F₀

  X : Type0
  X = Alg.X X,θ

  θ₀ : ⟦ F₀ ⟧₀ X → X
  θ₀ = Alg.θ X,θ

  field
    θ₁ : (x : ⟦ F₁ ⟧₀ X) → G₀ X,θ x
    
record Alg₁-morph (a b : Alg₁) : Type0 where
  constructor mk-alg-morph

  open Alg₁ a
  open Alg₁ b renaming (X,θ to Y,ρ ; X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)

  field
    f,f₀ : Alg-morph F₀ X,θ Y,ρ

  f : X → Y
  f = Alg-morph.f f,f₀

  f₀ : (x : ⟦ F₀ ⟧₀ X) → f (θ₀ x) == ρ₀ (⟦ F₀ ⟧₁ f x)
  f₀ = Alg-morph.f₀ f,f₀

  field
    f₁ : (x : ⟦ F₁ ⟧₀ X) → G₁ x f,f₀ (θ₁ x) == ρ₁ (⟦ F₁ ⟧₁ f x)

-- Equality of algebra morphisms
module _ {a b : Alg₁} where
  open Alg₁ a
  open Alg₁ b renaming (X,θ to Y,ρ ; X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)
  open Alg₁-morph
  open Alg-morph renaming (f to f') hiding (f₀)

  mk-alg₁-morph-eq-orig :
     {morph-f morph-g : Alg₁-morph a b}
     (p :  f  morph-f == f  morph-g)
     (p₀ : f₀ morph-f == f₀ morph-g [ (λ f' → (x : ⟦ F₀ ⟧₀ X) → f' (θ₀ x) == ρ₀ (⟦ F₀ ⟧₁ f' x)) ↓ p ])
     (p₁ : f₁ morph-f == f₁ morph-g [ (λ f,f₀' → (x : ⟦ F₁ ⟧₀ X) → G₁ x f,f₀' (θ₁ x) == ρ₁ (⟦ F₁ ⟧₁ (f' f,f₀') x)) ↓ mk-alg-morph-eq-orig F₀ p p₀ ])
   → morph-f == morph-g
  mk-alg₁-morph-eq-orig {mk-alg-morph (mk-alg-morph f f₀) f₁} {mk-alg-morph (mk-alg-morph .f .f₀) g₁} idp idp = ap (mk-alg-morph (mk-alg-morph f f₀))

  -- TODO: Make more useful variants of this.
