{-# OPTIONS --without-K #-}

open import Container

module wtypes.NewWTypes (F : Container) where

open import lib.Base hiding (S)
open import lib.PathGroupoid
open import lib.PathFunctor
open import lib.types.PathSeq
open import lib.Funext using (λ= ; app=-β ; λ=-η ; app=)
open Container.Container F renaming (Shapes to S ; Positions to P)
open import Utils

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
     (p₀ : (x : ⟦ F ⟧₀ X) → transport (λ X → X (θ x) == ρ (⟦ F ⟧₁ X x)) p (f₀ morph-f x) == f₀ morph-g x)
   → morph-f == morph-g
  mk-alg-morph-eq {mk-alg-morph f f₀} {mk-alg-morph .f g₀} idp p₀ = ap (mk-alg-morph f) (λ= p₀)
  
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
    mk-alg-morph-eq p (λ x → (lemma-2-11-4'
                                     (X → Y)
                                     Y
                                     (λ X₁ → X₁ (θ x))
                                     (λ X₁ → ρ (⟦ F ⟧₁ X₁ x))
                                     p
                                     (f₀ x))
                             ∙ q x)
    
-- TODO: We need more notation for map operation on  □.
record HasInductionPrinciple (T' : Alg) : Type1 where
  open Alg T' renaming (X to T ; θ to c)
  field
    ind    : (B : T → Type0) (m : (x : ⟦ F ⟧₀ T) → □ F B x → B (c x)) → (x : T) → B x
    ind-β₀ : (B : T → Type0) (m : (x : ⟦ F ⟧₀ T) → □ F B x → B (c x))
             (s : S) (t : P s → T)
            → ind B m (c (s , t)) == m (s , t) (ind B m ∘ t)

module Induction⇒Initiality
  (T' : Alg)
  (ip : HasInductionPrinciple T')
  (X' : Alg)
  where
  open Alg T' renaming (X to T ; θ to c)
  open HasInductionPrinciple ip
  open Alg X'

  module Existence where
    B : T → Type0
    B = cst X

    m : (x : ⟦ F ⟧₀ T) → □ F (cst X) x → X
    m = λ { (s , t) f → θ (s , f) }

    rec : T → X
    rec = ind B m

    rec-β₀ : (s : S) (t : P s → T)
           → rec (c (s , t)) == θ (⟦ F ⟧₁ rec (s , t))
    rec-β₀ = ind-β₀ B m

    f : Alg-morph T' X'
    f = mk-alg-morph rec ((λ { (s , t) → rec-β₀ s t }))

    module Uniqueness
      (g : Alg-morph T' X')
        where
  
      unique : f == g
      unique = mk-alg-morph-eq' {!!} {!!}
    
