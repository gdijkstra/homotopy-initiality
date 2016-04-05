{-# OPTIONS --without-K #-}

open import lib.Basics
open import 1-hits.Core
open import Container
open import FreeMonad
open import lib.types.PathSeq
open import lib.types.Sigma

module 1-hits.Target.Product (s : Spec) where

open Spec s
open import 1-hits.Alg0 F₀
open import 1-hits.Target.Core s

-- Target functor preserves products
module _
  (𝓧 𝓨 : Alg₀-obj)
  where

  open Alg₀-obj 𝓧 renaming (θ to θ₀)
  open Alg₀-obj 𝓨 renaming (X to Y ; θ to ρ₀)

  module _
    (x : ⟦ F₁ ⟧₀ (X × Y))
    (p : G₁₀ 𝓧 (⟦ F₁ ⟧₁ fst x))
    (q : G₁₀ 𝓨 (⟦ F₁ ⟧₁ snd x))
    where

    prodfst : fst (((×₀ 𝓧 𝓨) *¹) (l ‼ x)) == fst (((×₀ 𝓧 𝓨) *¹) (r ‼ x))
    prodfst = ↯
      fst (((×₀ 𝓧 𝓨) *¹) (l ‼ x))
       =⟪ star-hom₀ (π₁-alg₀ 𝓧 𝓨) (l ‼ x) ⟫
      (θ₀ *¹) (⟦ F₀ * ⟧₁ fst (l ‼ x))
       =⟪idp⟫
      (θ₀ *¹) (l ‼ (⟦ F₁ ⟧₁ fst x))
       =⟪ p ⟫
      (θ₀ *¹) (r ‼ (⟦ F₁ ⟧₁ fst x))
       =⟪ ! (star-hom₀ (π₁-alg₀ 𝓧 𝓨) (r ‼ x)) ⟫
      fst (((×₀ 𝓧 𝓨) *¹) (r ‼ x)) ∎∎

    prodsnd : snd (((×₀ 𝓧 𝓨) *¹) (l ‼ x)) == snd (((×₀ 𝓧 𝓨) *¹) (r ‼ x))
    prodsnd = ↯
      snd (((×₀ 𝓧 𝓨) *¹) (l ‼ x))
       =⟪ star-hom₀ (π₂-alg₀ 𝓧 𝓨) (l ‼ x) ⟫
      (ρ₀ *¹) (⟦ F₀ * ⟧₁ snd (l ‼ x))
       =⟪idp⟫
      (ρ₀ *¹) (l ‼ (⟦ F₁ ⟧₁ snd x))
       =⟪ q ⟫
      (ρ₀ *¹) (r ‼ (⟦ F₁ ⟧₁ snd x))
       =⟪ ! (star-hom₀ (π₂-alg₀ 𝓧 𝓨) (r ‼ x)) ⟫
      snd (((×₀ 𝓧 𝓨) *¹) (r ‼ x)) ∎∎

    G₁₀-prod : G₁₀ (×-alg₀ 𝓧 𝓨) x
    G₁₀-prod = pair×= prodfst prodsnd --prodfst prodsnd
  
    -- Straight-forward but verbose path algebra shows that we can
    -- project out the parts of product as expected.
    G₁₀-π₁ : G₁₁ (π₁-alg₀ 𝓧 𝓨) x G₁₀-prod == p
    G₁₀-π₁ = ↯ 
      G₁₁ (π₁-alg₀ 𝓧 𝓨) x G₁₀-prod
       =⟪idp⟫
      ! fst₀-l ∙ fst×= G₁₀-prod ∙ fst₀-r
       =⟪ ap (λ h → ! fst₀-l ∙ h ∙ fst₀-r) (fst×=-β prodfst prodsnd ) ⟫
      ! fst₀-l ∙ (fst₀-l ∙ p ∙ ! fst₀-r) ∙ fst₀-r
       =⟪ ! (∙-assoc (! fst₀-l) _ fst₀-r) ⟫
      (! fst₀-l ∙ (fst₀-l ∙ p ∙ ! fst₀-r)) ∙ fst₀-r
       =⟪ ap (λ h → h ∙ fst₀-r) (! (∙-assoc (! fst₀-l) fst₀-l (p ∙ ! fst₀-r))) ⟫
      ((! fst₀-l ∙ fst₀-l) ∙ p ∙ ! fst₀-r) ∙ fst₀-r
       =⟪ ap (λ h → (h ∙ p ∙ ! fst₀-r) ∙ fst₀-r) (!-inv-l fst₀-l) ⟫
      (p ∙ ! fst₀-r) ∙ fst₀-r
       =⟪ ∙-assoc p (! fst₀-r) fst₀-r ⟫
      p ∙ (! fst₀-r ∙ fst₀-r)
       =⟪ ap (λ h → p ∙ h) (!-inv-l fst₀-r) ⟫
      p ∙ idp
       =⟪ ∙-unit-r p ⟫
      p ∎∎
      where fst₀-l = star-hom₀ (π₁-alg₀ 𝓧 𝓨) (l ‼ x)
            fst₀-r = star-hom₀ (π₁-alg₀ 𝓧 𝓨) (r ‼ x)
  
    G₁₀-π₂ : G₁₁ (π₂-alg₀ 𝓧 𝓨) x G₁₀-prod == q
    G₁₀-π₂ = ↯
      G₁₁ (π₂-alg₀ 𝓧 𝓨) x G₁₀-prod
       =⟪idp⟫
      ! snd₀-l ∙ snd×= G₁₀-prod ∙ snd₀-r
       =⟪ ap (λ h → ! snd₀-l ∙ h ∙ snd₀-r) (snd×=-β prodfst prodsnd ) ⟫
      ! snd₀-l ∙ (snd₀-l ∙ q ∙ ! snd₀-r) ∙ snd₀-r
       =⟪ ! (∙-assoc (! snd₀-l) _ snd₀-r) ⟫
      (! snd₀-l ∙ (snd₀-l ∙ q ∙ ! snd₀-r)) ∙ snd₀-r
       =⟪ ap (λ h → h ∙ snd₀-r) (! (∙-assoc (! snd₀-l) snd₀-l (q ∙ ! snd₀-r))) ⟫
      ((! snd₀-l ∙ snd₀-l) ∙ q ∙ ! snd₀-r) ∙ snd₀-r
       =⟪ ap (λ h → (h ∙ q ∙ ! snd₀-r) ∙ snd₀-r) (!-inv-l snd₀-l) ⟫
      (q ∙ ! snd₀-r) ∙ snd₀-r
       =⟪ ∙-assoc q (! snd₀-r) snd₀-r ⟫
      q ∙ (! snd₀-r ∙ snd₀-r)
       =⟪ ap (λ h → q ∙ h) (!-inv-l snd₀-r) ⟫
      q ∙ idp
       =⟪ ∙-unit-r q ⟫
      q ∎∎
      where snd₀-l = star-hom₀ (π₂-alg₀ 𝓧 𝓨) (l ‼ x)
            snd₀-r = star-hom₀ (π₂-alg₀ 𝓧 𝓨) (r ‼ x)
