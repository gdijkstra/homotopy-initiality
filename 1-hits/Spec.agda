{-# OPTIONS --without-K #-}

module 1-hits.Spec where

open import lib.Basics
open import lib.types.Sigma
open import Container
open import FreeMonad
open import 1-hits.Alg0.Alg 
open import Admit
open import lib.types.PathSeq

record Spec : Type1 where
  constructor mk-spec
  field
    F₀ : Container
    F₁ : Container
    l r : ContHom F₁ (F₀ *)

  open import 1-hits.Alg0.FreeMonad F₀

  abstract -- abstract for now, to make life hopefully easier
    G₁₀ : (X : Type0) (θ₀ : has-alg₀ F₀ X) (x : ⟦ F₁ ⟧₀ X) → Type0
    G₁₀ X θ₀ x = ((θ₀ *¹) (l ‼ x) == (θ₀ *¹) (r ‼ x))
  
    G₁₁ :
      {X Y : Type0}
      (θ₀ : has-alg₀ F₀ X)
      (ρ₀ : has-alg₀ F₀ Y)
      (f : X → Y)
      (f₀ : is-alg₀-hom F₀ θ₀ ρ₀ f)
      (x : ⟦ F₁ ⟧₀ X)
      → G₁₀ X θ₀ x → G₁₀ Y ρ₀ ((⟦ F₁ ⟧₁ f) x)
    G₁₁ θ₀ ρ₀ f f₀ x p = ↯
      (ρ₀ *¹) (l ‼ ⟦ F₁ ⟧₁ f x)
       =⟪idp⟫
      (ρ₀ *¹) (⟦ F₀ * ⟧₁ f (l ‼ x))
       =⟪ ! ((f , f₀ *-hom) (l ‼ x)) ⟫
      f ((θ₀ *¹) (l ‼ x))
       =⟪ ap f p ⟫
      f ((θ₀ *¹) (r ‼ x))
       =⟪ (f , f₀ *-hom) (r ‼ x) ⟫
      (ρ₀ *¹) (⟦ F₀ * ⟧₁ f (r ‼ x))
       =⟪idp⟫
      (ρ₀ *¹) (r ‼ ⟦ F₁ ⟧₁ f x) ∎∎
