{-# OPTIONS --without-K #-}

open import Container

module NewWTypes (F : Container) where

open import lib.Base hiding (S)
open import lib.PathGroupoid
open import lib.PathFunctor
open import lib.types.PathSeq
open import lib.Funext using (λ= ; app=-β ; λ=-η ; app=)

open Container.Container F renaming (Shapes to S ; Positions to P)

record Alg : Type1 where
  constructor mk-alg
  field
    X : Type0
    θ : ⟦ F ⟧₀ X → X

record Alg-morph (a b : Alg) : Type0 where
  constructor mk-alg-morph
  open Alg a 
  open Alg b renaming (X to Y ; θ to ρ)
  field
    f : X → Y
    f₀ : ρ ∘ ⟦ F ⟧₁ f == f ∘ θ
   
-- Equality of morphisms:
module _  where
  open Alg-morph

  mk-alg-morph-eq :
     {a b : Alg} {morph-f morph-g : Alg-morph a b}
     (p : f morph-f == f morph-g)
     (q : {!!})
   → morph-f == morph-g
  mk-alg-morph-eq {mk-alg X θ} {mk-alg Y ρ} {mk-alg-morph f f₀} {mk-alg-morph .f g₀} idp q
    = {!ap !}
  
