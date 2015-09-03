{-# OPTIONS --without-K #-}

open import Container

module wtypes.PointfulWTypes (F : Container) where

open import lib.Base hiding (S)
open import lib.PathGroupoid
open import lib.PathFunctor
open import lib.types.PathSeq
open import lib.Funext using (λ= ; app=-β ; λ=-η ; app=)
open Container.Container F renaming (Shapes to S ; Positions to P)
open import Utils

⟦F⟧₁= : {X Y : Type0} {f g : X → Y} (p : (x : X) → f x == g x) → (x : ⟦ F ⟧₀ X) → ⟦ F ⟧₁ f x == ⟦ F ⟧₁ g x
⟦F⟧₁= p (s , t) = ap (λ x' → s , x') (λ= (p ∘ t))

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
    f₀ : (x : ⟦ F ⟧₀ X) → f (θ x) == ρ (⟦ F ⟧₁ f x)
   
-- Equality of morphisms:
module _ {a b : Alg}  where
  open Alg a
  open Alg b renaming (X to Y ; θ to ρ)
  open Alg-morph

  mk-alg-morph-eq :
     {morph-f morph-g : Alg-morph a b}
     (p : f morph-f == f morph-g)
     (q : (x : ⟦ F ⟧₀ X)
        → transport (λ X → X (θ x) == ρ (⟦ F ⟧₁ X x)) p (f₀ morph-f x) == f₀ morph-g x)
   → morph-f == morph-g
  mk-alg-morph-eq {mk-alg-morph f f₀} {mk-alg-morph .f g₀} idp q = ap (mk-alg-morph f) (λ= q)
  
module _ {a b : Alg} {morph-f morph-g : Alg-morph a b} where
  open Alg a
  open Alg b renaming (X to Y ; θ to ρ)
  open Alg-morph morph-f
  open Alg-morph morph-g renaming (f to g ; f₀ to g₀)
    
  mk-alg-morph-eq' :
     (p : f == g)
     (q : (x : ⟦ F ⟧₀ X) → ! (ap (λ X₁ → X₁ (θ x)) p) ∙ f₀ x ∙ ap (λ X₁ → ρ (⟦ F ⟧₁ X₁ x)) p == g₀ x)
   → morph-f == morph-g
  mk-alg-morph-eq' p q =
    mk-alg-morph-eq p (λ x → lemma-2-11-4' (X → Y) Y (λ X₁ → X₁ (θ x)) (λ X₁ → ρ (⟦ F ⟧₁ X₁ x)) p (f₀ x) ∙ q x)

  mk-alg-morph-eq'' :
     (p : f == g)
     (q : (x : ⟦ F ⟧₀ X) → ! (app= p (θ x)) ∙ f₀ x ∙ ap ρ (ap (λ X₁ → ⟦ F ⟧₁ X₁ x) p) == g₀ x)
   → morph-f == morph-g
  mk-alg-morph-eq'' p q = mk-alg-morph-eq' p (λ x → ap (λ X₁ → ! (app= p (θ x)) ∙ f₀ x ∙ X₁) (ap-∘ _ _ p) ∙ q x)

  mk-alg-morph-eq''' :
     (p : f == g)
     (q : (x : ⟦ F ⟧₀ X) → ! (app= p (θ x)) ∙ f₀ x ∙ ap ρ (app= (ap ⟦ F ⟧₁ p) x) == g₀ x)
   → morph-f == morph-g
  mk-alg-morph-eq''' = {!mk-alg-morph-eq''!}

  mk-alg-morph-eq'''' :
     (p : (x : X) → f x == g x)
     (q : (x : ⟦ F ⟧₀ X) → ! (p (θ x)) ∙ f₀ x ∙ ap ρ (⟦F⟧₁= p x) == g₀ x)
   → morph-f == morph-g
  mk-alg-morph-eq'''' = {!mk-alg-morph-eq''!}
