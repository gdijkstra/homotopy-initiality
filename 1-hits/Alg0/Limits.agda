{-# OPTIONS --without-K #-}

open import Container

-- Equality of algebra morphisms
module 1-hits.Alg0.Limits (F : Container) where

open import lib.Basics
open import lib.types.Sigma
open import lib.types.PathSeq
open import lib.cubical.Cubical
open import 1-hits.Alg0.Alg F
open import 1-hits.Alg0.Eq F
open import 1-hits.Alg0.Cat F
open import General Alg₀
open import Admit

_×-alg₀_ :
  {X Y : Type0}
  (θ : has-alg₀ X)
  (ρ : has-alg₀ Y)
  → has-alg₀ (X × Y)
θ ×-alg₀ ρ = λ x → θ (⟦ F ⟧₁ fst x) , ρ (⟦ F ⟧₁ snd x)

products : has-products
products = record
  { prod = λ { (X , θ) (Y , ρ) → X × Y , (θ ×-alg₀ ρ) }
  ; π₁ = λ { {X , θ} {Y , ρ} → fst , (λ x → idp) }
  ; π₂ = λ { {X , θ} {Y , ρ} → snd , (λ x → idp) }
  }

module Equaliser
  (𝓧 𝓨 : Alg₀-obj)
  (𝓯 𝓰 : Alg₀-hom 𝓧 𝓨)
  where

  open Σ 𝓧 renaming (fst to X; snd to θ)
  open Σ 𝓨 renaming (fst to Y; snd to ρ)
  open Σ 𝓯 renaming (fst to f; snd to f₀)
  open Σ 𝓰 renaming (fst to g; snd to g₀)

  E : Type0
  E = Σ X (λ x → f x == g x)

  i : E → X
  i = fst

  p' : (x : E) → (f ∘ i) x == (g ∘ i) x
  p' (x , q) = q

  p : f ∘ i == g ∘ i
  p = λ= p'

  lemma :
    (x : ⟦ F ⟧₀ E)
    → ⟦ F ⟧₁ (f ∘ i) x == ⟦ F ⟧₁ (g ∘ i) x
  lemma x = ap (λ h → ⟦ F ⟧₁ h x) p

  ε : has-alg₀ E
  ε x = (θ (⟦ F ⟧₁ i x))
        , (↯ (f (θ (⟦ F ⟧₁ i x))
            =⟪ f₀ (⟦ F ⟧₁ i x) ⟫
           ρ (⟦ F ⟧₁ f (⟦ F ⟧₁ i x))
            =⟪idp⟫
           ρ (⟦ F ⟧₁ (f ∘ i) x)
            =⟪ ap ρ (lemma x) ⟫ 
           ρ (⟦ F ⟧₁ (g ∘ i) x)
            =⟪idp⟫ 
           ρ (⟦ F ⟧₁ g (⟦ F ⟧₁ i x))
            =⟪ ! (g₀ (⟦ F ⟧₁ i x)) ⟫
           g (θ (⟦ F ⟧₁ i x)) ∎∎))

  i₀ : is-alg₀-hom ε θ i
  i₀ = (λ x → idp)

  -- TODO: Prove this, which is doable, but a tad tedious.
  p₀ :
    (x : ⟦ F ⟧₀ E) →
      Square
        (f₀ (⟦ F ⟧₁ i x))
        (p' (ε x))
        (ap (λ h → ρ (⟦ F ⟧₁ h x)) p)
        (g₀ (⟦ F ⟧₁ i x))
  p₀ x = admit _

  𝓔 : Alg₀-obj
  𝓔 = (E , ε)

  𝓲 : Alg₀-hom 𝓔 𝓧
  𝓲 = (i , i₀)

  comm : Alg₀-comp {𝓔} {𝓧} {𝓨} 𝓯 𝓲 == Alg₀-comp {𝓔} {𝓧} {𝓨} 𝓰 𝓲 
  comm = mk-alg₀-hom-eq-square-λ= {𝓔} {𝓨}
          (Alg₀-comp {𝓔} {𝓧} {𝓨} 𝓯 𝓲)
          (Alg₀-comp {𝓔} {𝓧} {𝓨} 𝓰 𝓲)
          p'
          p₀ 

equalisers : has-equalisers
equalisers {𝓧} {𝓨} 𝓯 𝓰 = record
  { E = Equaliser.𝓔 𝓧 𝓨 𝓯 𝓰
  ; i = Equaliser.𝓲 𝓧 𝓨 𝓯 𝓰
  ; comm = Equaliser.comm 𝓧 𝓨 𝓯 𝓰
  }

