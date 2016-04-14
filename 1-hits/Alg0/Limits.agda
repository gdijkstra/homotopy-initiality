{-# OPTIONS --without-K #-}

open import Container

-- Equality of algebra morphisms
module 1-hits.Alg0.Limits (F : Container) where

open import lib.Basics
open import lib.types.Sigma
open import lib.types.PathSeq
open import lib.cubical.Cubical
open import 1-hits.Alg0.Core F
open import 1-hits.Alg0.Eq F
open import Cat

module _
  (𝓧 𝓨 : Alg₀-obj)
  where

  open Alg₀-obj 𝓧
  open Alg₀-obj 𝓨 renaming (X to Y ; θ to ρ)
  
  product-alg₀ : Product Alg₀ 𝓧 𝓨
  product-alg₀ = record
    { prod = ×-alg₀
    ; π₁ = π₁-alg₀
    ; π₂ = π₂-alg₀
    }
    where
      ×₀ : has-alg₀ (X × Y)
      ×₀ = λ x → θ (⟦ F ⟧₁ fst x) , ρ (⟦ F ⟧₁ snd x)
      
      ×-alg₀ : Alg₀-obj
      ×-alg₀ = alg₀ (X × Y) ×₀
    
      π₁-alg₀ : Alg₀-hom ×-alg₀ 𝓧
      π₁-alg₀ = alg₀-hom fst (λ _ → idp)
    
      π₂-alg₀ : Alg₀-hom ×-alg₀ 𝓨
      π₂-alg₀ = alg₀-hom snd (λ _ → idp)

module _
  {𝓧 𝓨 : Alg₀-obj}
  (𝓯 𝓰 : Alg₀-hom 𝓧 𝓨)
  where

  open Alg₀-obj 𝓧
  open Alg₀-obj 𝓨 renaming (X to Y; θ to ρ)
  open Alg₀-hom 𝓯
  open Alg₀-hom 𝓰 renaming (f to g; f₀ to g₀)

  equaliser-alg₀ : Equaliser Alg₀ 𝓯 𝓰
  equaliser-alg₀ = record
    { E = 𝓔
    ; i = 𝓲
    ; comm = comm
    }
    where
      E : Type0
      E = Σ X (λ x → f x == g x)
    
      i : E → X
      i = fst
    
      p' : (x : E) → (f ∘ i) x == (g ∘ i) x
      p' (x , q) = q
    
      p : f ∘ i == g ∘ i
      p = λ= p'
    
      ε : has-alg₀ E
      ε x = (θ (⟦ F ⟧₁ i x))
            , (↯ (f (θ (⟦ F ⟧₁ i x))
                =⟪ f₀ (⟦ F ⟧₁ i x) ⟫
               ρ (⟦ F ⟧₁ f (⟦ F ⟧₁ i x))
                =⟪idp⟫
               ρ (⟦ F ⟧₁ (f ∘ i) x)
                =⟪ ap (λ h → ρ (⟦ F ⟧₁ h x)) p ⟫
               ρ (⟦ F ⟧₁ (g ∘ i) x)
                =⟪idp⟫ 
               ρ (⟦ F ⟧₁ g (⟦ F ⟧₁ i x))
                =⟪ ! (g₀ (⟦ F ⟧₁ i x)) ⟫
               g (θ (⟦ F ⟧₁ i x)) ∎∎))
    
      𝓔 : Alg₀-obj
      𝓔 = alg₀ E ε
    
      i₀ : is-alg₀-hom 𝓔 𝓧 i
      i₀ = (λ x → idp)
    
      p₀ :
        (x : ⟦ F ⟧₀ E) →
          Square
            (f₀ (⟦ F ⟧₁ i x))
            (p' (ε x))
            (ap (λ h → ρ (⟦ F ⟧₁ h x)) p)
            (g₀ (⟦ F ⟧₁ i x))
      p₀ x =
        (connection2 {p = f₀ (⟦ F ⟧₁ i x)}
                     {q = ap (λ h → ρ (⟦ F ⟧₁ h x)) p}
         ⊡h lt-square (ap (λ h → ρ (⟦ F ⟧₁ h x)) p)
         ⊡h rt-square (g₀ (⟦ F ⟧₁ i x)))
        ⊡v∙ ∙-unit-r (ap (λ h → ρ (⟦ F ⟧₁ h x)) p)
    
      𝓲 : Alg₀-hom 𝓔 𝓧
      𝓲 = alg₀-hom i i₀
    
      comm : ∘-alg₀ 𝓯 𝓲 == ∘-alg₀ 𝓰 𝓲 
      comm = alg₀-hom=⊡-λ= {𝓔} {𝓨}
              (∘-alg₀ 𝓯 𝓲)
              (∘-alg₀ 𝓰 𝓲)
              p'
              p₀ 
