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

module _
  (𝓧 𝓨 : Alg₀-obj)
  where

  open Alg₀-obj 𝓧
  open Alg₀-obj 𝓨 renaming (X to Y ; θ to ρ)
  
  ×₀ : has-alg₀ (X × Y)
  ×₀ = λ x → θ (⟦ F ⟧₁ fst x) , ρ (⟦ F ⟧₁ snd x)
  
  ×-alg₀ : Alg₀-obj
  ×-alg₀ = mk-alg₀ (X × Y) ×₀

  π₁-alg₀ : Alg₀-hom ×-alg₀ 𝓧
  π₁-alg₀ = mk-alg₀-hom fst (λ _ → idp)

  π₂-alg₀ : Alg₀-hom ×-alg₀ 𝓨
  π₂-alg₀ = mk-alg₀-hom snd (λ _ → idp)

products : has-products
products = record
  { prod = ×-alg₀
  ; π₁ = λ {𝓧} {𝓨} → π₁-alg₀ 𝓧 𝓨
  ; π₂ = λ {𝓧} {𝓨} → π₂-alg₀ 𝓧 𝓨
  }

module Equaliser
  (𝓧 𝓨 : Alg₀-obj)
  (𝓯 𝓰 : Alg₀-hom 𝓧 𝓨)
  where

  open Alg₀-obj 𝓧
  open Alg₀-obj 𝓨 renaming (X to Y; θ to ρ)
  open Alg₀-hom 𝓯
  open Alg₀-hom 𝓰 renaming (f to g; f₀ to g₀)

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

  𝓔 : Alg₀-obj
  𝓔 = mk-alg₀ E ε

  i₀ : is-alg₀-hom 𝓔 𝓧 i
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

  𝓲 : Alg₀-hom 𝓔 𝓧
  𝓲 = mk-alg₀-hom i i₀

  comm : ∘-alg₀ 𝓯 𝓲 == ∘-alg₀ 𝓰 𝓲 
  comm = mk-alg₀-hom-eq-square-λ= {𝓔} {𝓨}
          (∘-alg₀ 𝓯 𝓲)
          (∘-alg₀ 𝓰 𝓲)
          p'
          p₀ 

equalisers : has-equalisers
equalisers {𝓧} {𝓨} 𝓯 𝓰 = record
  { E = Equaliser.𝓔 𝓧 𝓨 𝓯 𝓰
  ; i = Equaliser.𝓲 𝓧 𝓨 𝓯 𝓰
  ; comm = Equaliser.comm 𝓧 𝓨 𝓯 𝓰
  }
