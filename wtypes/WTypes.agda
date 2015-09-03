{-# OPTIONS --without-K #-}

open import Container

module wtypes.WTypes (F : Container) where

open import lib.Basics hiding (S)
open import lib.Funext using (λ= ; app=-β ; λ=-η ; app=)
open Container.Container F renaming (Shapes to S ; Positions to P)
open import wtypes.Induction F
open import wtypes.Alg F

module Induction⇒Initiality
  (T' : Alg)
  (ind' : InductionPrinciple T') where
  
  open Alg T' renaming (X to T ; θ to c)
  open InductionPrinciple T' ind'

  module Existence (X' : Alg) where
    open Alg X'

    f-B : T → Type0
    f-B _ = X

    f-m : (x : ⟦ F ⟧₀ T) → □ F f-B x → X
    f-m (s , _) t = θ (s , t)

    f : T → X
    f = ind f-B f-m

    f₀ : (x : ⟦ F ⟧₀ T) → f (c x) == θ (⟦ F ⟧₁ f x)
    f₀ = ind-β₀ f-B f-m

    f' : Alg-morph T' X'
    f' = mk-alg-morph f f₀

    module Uniqueness (g' : Alg-morph T' X') where
      open Alg-morph g' renaming (f to g ; f₀ to g₀)

      f=g-B : T → Type0
      f=g-B x = f x == g x

      f=g-m : (x : ⟦ F ⟧₀ T) → □ F f=g-B x → f=g-B (c x)
      f=g-m x t = {!!}

      f=g : f == g
      f=g = λ= (ind f=g-B f=g-m)

      -- f₀=g₀ : (x : ⟦ F ⟧₀ X)
      --       → ! (ap (λ f' → f' ( x)) f=g) -- app= p (θ x)
      --         ∙ f₀ x
      --         ∙ ap (λ f' → c (⟦ F ⟧₁ f' x)) f=g
      --      == g₀ x
      -- f₀=g₀ x = ?

      f'=g' : f' == g'
      f'=g' = mk-alg-morph-eq' f=g {!!}
