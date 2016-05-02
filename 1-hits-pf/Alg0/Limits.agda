{-# OPTIONS --without-K #-}

open import Container

module 1-hits-pf.Alg0.Limits (F : Container) where

open import Eq
open import lib.Basics
open import lib.types.Sigma
open import Cat
open import 1-hits-pf.Alg0.Core F
open import 1-hits-pf.Alg0.Eq F

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
      π₁-alg₀ = alg₀-hom fst refl
    
      π₂-alg₀ : Alg₀-hom ×-alg₀ 𝓨
      π₂-alg₀ = alg₀-hom snd refl

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
    ; comm = Correctness.from comm
    }
    where
      E : Type0
      E = Σ X (λ x → Eq (f x) (g x))
    
      i : E → X
      i = fst
    
      p' : (x : E) → Eq ((f ∘ i) x) ((g ∘ i) x)
      p' (x , q) = q
    
      p : Eq (f ∘ i) (g ∘ i)
      p = Funext p'

      q : Eq (f ∘ θ ∘ ⟦ F ⟧₁ i) (g ∘ θ ∘ ⟦ F ⟧₁ i)
      q = Ap (`∘ ⟦ F ⟧₁ i) f₀ * Ap (ρ ∘`) (⟦ F ⟧₌ p) * sym (Ap (`∘ ⟦ F ⟧₁ i) g₀)

      ε : has-alg₀ E
      ε x = ((θ ∘ ⟦ F ⟧₁ i) x
            , App= q x
            )
    
      𝓔 : Alg₀-obj
      𝓔 = alg₀ E ε
    
      i₀ : is-alg₀-hom 𝓔 𝓧 i
      i₀ = refl
    
      𝓲 : Alg₀-hom 𝓔 𝓧
      𝓲 = alg₀-hom i i₀

      lem : Eq q (Ap (`∘ ε) p)
      lem =
        q
         *⟨ Funext-η q ⟩
        Funext (App= q)
         *⟨ App=-β' p' ε ⟩
        Ap (`∘ ε) p ∎*

      goal : Eq (Ap (`∘ ⟦ F ⟧₁ i) f₀ * Ap (ρ ∘`) (⟦ F ⟧₌ p))
                (Ap (`∘ ε) p * Ap (`∘ ⟦ F ⟧₁ i) g₀)
      goal =
        Ap (`∘ ⟦ F ⟧₁ i) f₀ * Ap (ρ ∘`) (⟦ F ⟧₌ p)
         *⟨ Ap (λ P → Ap (`∘ ⟦ F ⟧₁ i) f₀ * Ap (ρ ∘`) (⟦ F ⟧₌ p) * P) (sym (sym-*-inv-l (Ap (`∘ ⟦ F ⟧₁ i) g₀))) ⟩ -- sym 
        Ap (`∘ ⟦ F ⟧₁ i) f₀ * Ap (ρ ∘`) (⟦ F ⟧₌ p) * sym (Ap (`∘ ⟦ F ⟧₁ i) g₀) * Ap (`∘ ⟦ F ⟧₁ i) g₀
         *⟨ Ap (λ P → P * Ap (`∘ ⟦ F ⟧₁ i) g₀) lem ⟩
        Ap (`∘ ε) p * Ap (`∘ ⟦ F ⟧₁ i) g₀ ∎*
    
      comm : Eq (∘-alg₀ 𝓯 𝓲) (∘-alg₀ 𝓰 𝓲)
      comm = alg₀-hom= (∘-alg₀ 𝓯 𝓲) (∘-alg₀ 𝓰 𝓲) p goal
