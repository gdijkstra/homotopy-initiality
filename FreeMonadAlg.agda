{-# OPTIONS --without-K #-}

open import Container

-- Lifting of functor algebras to monad algebras
module FreeMonadAlg {F : Container} where

open import FreeMonad
open import lib.Base
open import lib.types.PathSeq

_*¹ : {X : Type0} → (⟦ F ⟧₀ X → X) → ⟦ F * ⟧₀ X → X
_*¹ {X} θ = rec* X X (idf X) θ

-- Functorial action on morphisms
module Morphisms
         {X : Type0} (θ : ⟦ F ⟧₀ X → X) 
         {Y : Type0} (ρ : ⟦ F ⟧₀ Y → Y) 
         (f : X → Y)
         (comm : (x : ⟦ F ⟧₀ X) → ρ (⟦ F ⟧₁ f x) == f (θ x))
  where
 open import lib.Funext using (λ=)
 open Ind

 comm* : (x : ⟦ F * ⟧₀ X) → (ρ *¹) (⟦ F * ⟧₁ f x) == f ((θ *¹) x)
 comm* = ind* X (λ x → (ρ *¹) (⟦ F * ⟧₁ f x) == f ((θ *¹) x)) 
              (λ x → idp) 
              (λ x g → ↯
                (ρ *¹) (⟦ F * ⟧₁ f (c* x))
                 =⟪idp⟫ -- comp. rule for ⟦ F * ⟧₁
                (ρ *¹) (c* (⟦ F ⟧₁ (⟦ F * ⟧₁ f) x))
                 =⟪idp⟫ -- comp. rule for ρ *¹
                ρ (⟦ F ⟧₁ (ρ *¹) (⟦ F ⟧₁ (⟦ F * ⟧₁ f) x))
                 =⟪idp⟫ -- functoriality of F
                ρ (⟦ F ⟧₁ ((ρ *¹) ∘ (⟦ F * ⟧₁ f)) x)
                 =⟪ ap ρ (lift-func-eq F ((ρ *¹) ∘ ⟦ F * ⟧₁ f) (f ∘ (θ *¹)) x g) ⟫ -- ind. hyp.
                ρ (⟦ F ⟧₁ (f ∘ (θ *¹)) x)
                 =⟪idp⟫ -- functoriality of F
                ρ (⟦ F ⟧₁ f (⟦ F ⟧₁ (θ *¹) x))
                 =⟪ comm (⟦ F ⟧₁ (θ *¹) x) ⟫
                f (θ (⟦ F ⟧₁ (θ *¹) x))
                 =⟪idp⟫ -- comp. rule for θ *¹
                f ((θ *¹) (c* x)) ∎∎)

 comm*-ext : (ρ *¹) ∘ ⟦ F * ⟧₁ f == f ∘ (θ *¹)
 comm*-ext = λ= comm*

-- Functor laws for *
-- Preserves id
module _ {X : Type0} (θ : ⟦ F ⟧₀ X → X) where
  open import lib.Funext using (λ=)
  open import lib.types.PathSeq
  open import lib.PathFunctor
  open import lib.PathGroupoid

  -- TODO: This is also in Funext.agda but not exported properly.
  postulate
    λ=-idp : ∀ {i} {A : Type i} {j} {B : A → Type j} {f : (x : A) → B x}
      → idp {a = f} == λ= (λ x → idp)

  open Ind
  open Morphisms θ θ (idf X) (λ _ → idp)

  comm*-id : (x : ⟦ F * ⟧₀ X) → comm* x == idp
  comm*-id = ind* X (λ x → comm* x == idp) (λ x → idp) (λ { x g → ↯
    comm* (c* x)
     =⟪idp⟫ -- comp. rule for comm*
    ap θ (lift-func-eq F (θ *¹) (θ *¹) x (□-lift F comm* x)) ∙ idp
     =⟪ ap (λ p → ap θ (lift-func-eq F (θ *¹) (θ *¹) x p) ∙ idp) (λ= g) ⟫
    ap θ (lift-func-eq F (θ *¹) (θ *¹) x (λ x' → idp)) ∙ idp
     =⟪ ap (λ p' → ap θ (ap (λ p → fst x , p) p') ∙ idp) (! λ=-idp) ⟫ 
    idp ∎∎ })
  
