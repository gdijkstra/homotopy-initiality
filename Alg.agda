{-# OPTIONS --without-K #-}

open import Desc

module Alg (hit : Desc) where
  open import lib.Basics
  open import lib.types.PathSeq
  open import Container
  open import FreeMonad
  open Desc.Desc hit

  -- G₀ : Type -> Type is the identity functor.
  -- G₁ : ∫ Type F₁ -> Type is something more involved.
  record Alg : Type1 where
    constructor mk-alg
    field
      X : Type0
      θ₀ : ⟦ F₀ ⟧₀ X → X
      θ₁ : (x : ⟦ F₁ ⟧₀ X) → (θ₀ *¹) (l ‼ x) == (θ₀ *¹) (r ‼ x)

  record Alg-morph (a b : Alg) : Type0 where
    constructor mk-alg-morph

    open Alg a 
    open Alg b renaming (X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)

    field
      f : X → Y
      f₀ : f ∘ θ₀ == ρ₀ ∘ ⟦ F₀ ⟧₁ f
      
    map : (x : ⟦ F₁ ⟧₀ X)
     → (θ₀ *¹) (l ‼ x) == (θ₀ *¹) (r ‼ x)
     → (ρ₀ *¹) (l ‼ ⟦ F₁ ⟧₁ f x) == (ρ₀ *¹) (r ‼ ⟦ F₁ ⟧₁ f x)
    map x p = ↯
      (ρ₀ *¹) (l ‼ ⟦ F₁ ⟧₁ f x)
       =⟪idp⟫ -- naturality of l
      (ρ₀ *¹) (⟦ F₀ * ⟧₁ f (l ‼ x))
       =⟪ {!!} ⟫ -- computation rule f₀ lifted to free monad
      f ((θ₀ *¹) (l ‼ x))
       =⟪ ap f (θ₁ x) ⟫ -- apply θ₁
      f ((θ₀ *¹) (r ‼ x))
       =⟪ {!!} ⟫ -- computation rule f₀ lifted to free monad
      (ρ₀ *¹) (⟦ F₀ * ⟧₁ f (r ‼ x))
       =⟪idp⟫ -- naturality of r
      (ρ₀ *¹) (r ‼ ⟦ F₁ ⟧₁ f x) ∎∎

    field
      f₁ : (x : ⟦ F₁ ⟧₀ X) → map x (θ₁ x) == ρ₁ (⟦ F₁ ⟧₁ f x)

module _ {a b : Alg} where
  open Alg a
  open Alg b renaming (X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)
  open Alg-morph

  mk-alg-morph-eq :
     {morph-f morph-g : Alg-morph a b}
     (p : f morph-f == f morph-g)
     (q : transport (λ X → X ∘ θ₀ == ρ₀ ∘ ⟦ F₀ ⟧₁ X) p (f₀ morph-f) == f₀ morph-g)
     (r : {!Alg-morph.f₁!} == f₁ morph-g)
   → morph-f == morph-g
  mk-alg-morph-eq = {!!}
