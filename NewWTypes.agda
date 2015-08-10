{-# OPTIONS --without-K #-}

open import Container

module NewWTypes (F : Container) where

open import lib.Base hiding (S)
open import lib.PathGroupoid
open import lib.PathFunctor
open import lib.types.PathSeq
open import lib.Funext using (λ= ; app=-β ; λ=-η ; app=)

open Container.Container F renaming (Shapes to S ; Positions to P)

lemma-2-11-4' : ∀ {i j}
    (A : Type i) (B : Type j) (f g : A → B) {a a' : A} (p : a == a') (q : f a == g a)
  → transport (λ x → f x == g x) p q == ! (ap f p) ∙ q ∙ (ap g p)
lemma-2-11-4' A B₁ f₁ g idp q = ! (∙-unit-r q)

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
    f₀ : f ∘ θ == ρ ∘ ⟦ F ⟧₁ f
   
-- Equality of morphisms:
module _ {a b : Alg}  where
  open Alg a
  open Alg b renaming (X to Y ; θ to ρ)
  open Alg-morph

  mk-alg-morph-eq :
     {morph-f morph-g : Alg-morph a b}
     (p : f morph-f == f morph-g)
     (q : transport (λ X → X ∘ θ == ρ ∘ ⟦ F ⟧₁ X) p (f₀ morph-f) == f₀ morph-g)
   → morph-f == morph-g
  mk-alg-morph-eq {mk-alg-morph f f₀} {mk-alg-morph .f g₀} idp = ap (mk-alg-morph f)
  
module _ {a b : Alg} {morph-f morph-g : Alg-morph a b} where
  open Alg a
  open Alg b renaming (X to Y ; θ to ρ)
  open Alg-morph morph-f
  open Alg-morph morph-g renaming (f to g ; f₀ to g₀)
    
  mk-alg-morph-eq' :
     (p : f == g)
     (q : ! (ap (λ X₁ → X₁ ∘ θ) p) ∙ f₀ ∙ ap (λ X₁ → ρ ∘ ⟦ F ⟧₁ X₁) p == g₀)
   → morph-f == morph-g
  mk-alg-morph-eq' p q =
    mk-alg-morph-eq p ((lemma-2-11-4' (X → Y)
                                     (⟦ F ⟧₀ X → Y)
                                     (λ X₁ → X₁ ∘ θ)
                                     (λ X₁ → ρ ∘ ⟦ F ⟧₁ X₁) p f₀)
                      ∙ q)
    
