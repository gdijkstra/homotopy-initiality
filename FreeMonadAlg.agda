{-# OPTIONS --without-K #-}

open import Container

-- Lifting of functor algebras to monad algebras
module FreeMonadAlg {F : Container} where

open import Alg
open import FreeMonad
open Ind
open import lib.Basics
open import lib.types.PathSeq
open import Utils

_*¹ : {X : Type0} → (⟦ F ⟧₀ X → X) → ⟦ F * ⟧₀ X → X
_*¹ {X} θ = rec* X X (idf X) θ

_*-alg : Alg F → Alg (F *)
(mk-alg X θ) *-alg = mk-alg X (θ *¹)

-- Functorial action on morphisms
module Morphisms
  (X' Y' : Alg F)
  where
 open Alg.Alg F X'
 open Alg.Alg F Y' renaming (X to Y ; θ to ρ)

 _*-alg₁ : Alg-hom F X' Y' → Alg-hom (F *) (X' *-alg) (Y' *-alg)
 (mk-alg-hom f comm) *-alg₁ =
   mk-alg-hom f (ind* X (λ x → f ((θ *¹) x) == (ρ *¹) (⟦ F * ⟧₁ f x))
                        (λ x → idp)
                        (λ x g → ↯ 
                f ((θ *¹) (c* x))
                 =⟪idp⟫ -- comp. rule for θ *¹
                f (θ (⟦ F ⟧₁ (θ *¹) x))
                 =⟪ comm (⟦ F ⟧₁ (θ *¹) x) ⟫
                ρ (⟦ F ⟧₁ f (⟦ F ⟧₁ (θ *¹) x))
                 =⟪idp⟫ -- functoriality of F
                ρ (⟦ F ⟧₁ (f ∘ (θ *¹)) x)
                 =⟪ ap ρ (lift-func-eq F (f ∘ (θ *¹)) ((ρ *¹) ∘ ⟦ F * ⟧₁ f) x g) ⟫
                ρ (⟦ F ⟧₁ ((ρ *¹) ∘ (⟦ F * ⟧₁ f)) x)
                 =⟪idp⟫ -- functoriality of F
                ρ (⟦ F ⟧₁ (ρ *¹) (⟦ F ⟧₁ (⟦ F * ⟧₁ f) x))
                 =⟪idp⟫ -- comp. rule for ρ *¹
                (ρ *¹) (c* (⟦ F ⟧₁ (⟦ F * ⟧₁ f) x))
                 =⟪idp⟫ -- comp. rule for ⟦ F * ⟧₁
                (ρ *¹) (⟦ F * ⟧₁ f (c* x)) ∎∎))

-- Functor laws for *
-- Preserves id
module MorphismsId (X : Alg F) where
  open Morphisms X X 
  open Alg.Alg F X

  comm*-id : (x : ⟦ F * ⟧₀ (Alg.X X)) → Alg-hom.f₀ (id-hom F X *-alg₁) x == idp
  comm*-id = ind* (Alg.X X)
          (λ x → comm* x == idp)
          (λ x → idp)
          (λ x g → ↯ (
           comm* (c* x)
            =⟪idp⟫ -- comp. rule for comm*
           ap θ (lift-func-eq F (θ *¹) (θ *¹) x (□-lift F comm* x))
            =⟪ ap (λ p → ap θ (lift-func-eq F (θ *¹) (θ *¹) x p)) (λ= g) ⟫
           ap θ (lift-func-eq F (θ *¹) (θ *¹) x (λ x' → idp))
            =⟪ ap (λ p' → ap θ (ap (λ p → fst x , p) p')) (! λ=-idp) ⟫ 
           idp ∎∎))
    where comm* = Alg-hom.f₀ (id-hom F X *-alg₁)

  id*-alg₁ : (id-hom F X *-alg₁) == id-hom (F *) (X *-alg)
  id*-alg₁ = mk-alg-hom-eq (F *) idp comm*-id
