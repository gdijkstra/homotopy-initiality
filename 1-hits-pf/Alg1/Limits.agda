{-# OPTIONS --without-K #-}

open import 1-hits-pf.Core

module 1-hits-pf.Alg1.Limits (s : Spec) where

open Spec s

open import Container
open import FreeMonad
open import lib.Basics
open import lib.types.Sigma
open import Cat
open import Eq
open import 1-hits-pf.Alg1.Core s
open import 1-hits-pf.Alg0.Core F₀
open import 1-hits-pf.Alg0.FreeMonad F₀

module _
  (𝓧 𝓨 : Alg₁-obj)
  where

  open Alg₁-obj 𝓧
  open Alg₁-obj 𝓨 renaming (𝓧' to 𝓨' ; X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)
  
  product-alg₁ : Product Alg₁ 𝓧 𝓨
  product-alg₁ = record
    { prod = ×-alg₁
    ; π₁ = π₁-alg₁
    ; π₂ = π₂-alg₁
    }
    where
      ×₀ : has-alg₀ (X × Y)
      ×₀ = λ x → θ₀ (⟦ F₀ ⟧₁ fst x) , ρ₀ (⟦ F₀ ⟧₁ snd x)
      
      π₁-alg₀ : Alg₀-hom (alg₀ (X × Y) ×₀) 𝓧'
      π₁-alg₀ = alg₀-hom fst refl

      π₂-alg₀ : Alg₀-hom (alg₀ (X × Y) ×₀) 𝓨'
      π₂-alg₀ = alg₀-hom snd refl

      fst-part : Eq (fst ∘ (×₀ *¹) ∘ apply l (X × Y)) (fst ∘ (×₀ *¹) ∘ apply r (X × Y))
      fst-part =
        fst ∘ (×₀ *¹) ∘ apply l (X × Y)
          *⟨ star-hom₀ π₁-alg₀ ₌∘ apply l (X × Y) ⟩
        (θ₀ *¹) ∘ ⟦ F₀ * ⟧₁ fst ∘ apply l (X × Y)
         *⟨ refl ⟩
        (θ₀ *¹) ∘ apply l X ∘ ⟦ F₁ ⟧₁ fst
         *⟨ θ₁ ₌∘ ⟦ F₁ ⟧₁ fst ⟩
        (θ₀ *¹) ∘ apply r X ∘ ⟦ F₁ ⟧₁ fst
          *⟨ refl ⟩
        (θ₀ *¹) ∘ ⟦ F₀ * ⟧₁ fst ∘ apply r (X × Y)
          *⟨ sym (star-hom₀ π₁-alg₀ ₌∘ apply r (X × Y)) ⟩
        fst ∘ (×₀ *¹) ∘ apply r (X × Y)
         ∎*

      snd-part : Eq (snd ∘ (×₀ *¹) ∘ apply l (X × Y)) (snd ∘ (×₀ *¹) ∘ apply r (X × Y))
      snd-part = (star-hom₀ π₂-alg₀ ₌∘ apply l (X × Y)) * (ρ₁ ₌∘ ⟦ F₁ ⟧₁ snd) * sym (star-hom₀ π₂-alg₀ ₌∘ apply r (X × Y))

      ×₁ : has-alg₁ (alg₀ (X × Y) ×₀) --has-alg₁ 
      ×₁ = pair-fun-eq fst-part snd-part

      ×-alg₁ : Alg₁-obj
      ×-alg₁ = alg₁ (alg₀ (X × Y) ×₀) ×₁

      lem : Eq (fst ∘₌ ×₁) fst-part
      lem = pair-fun-eq-fst-β fst-part snd-part

      private
        π₁₁ : Square
          (star-hom₀ π₁-alg₀ ₌∘ apply l (X × Y))
          (fst ∘₌ ×₁)
          (θ₁ ₌∘ ⟦ F₁ ⟧₁ fst)
          (star-hom₀ π₁-alg₀ ₌∘ apply r (X × Y))
        π₁₁ = from-disc (
          (star-hom₀ π₁-alg₀ ₌∘ apply l (X × Y)) * (θ₁ ₌∘ ⟦ F₁ ⟧₁ fst)
           *⟨ Ap (λ P → (star-hom₀ π₁-alg₀ ₌∘ apply l (X × Y)) * (θ₁ ₌∘ ⟦ F₁ ⟧₁ fst) * P)
                 (sym (sym-*-inv-l (star-hom₀ π₁-alg₀ ₌∘ apply r (X × Y))))
            ⟩
          (star-hom₀ π₁-alg₀ ₌∘ apply l (X × Y)) * (θ₁ ₌∘ ⟦ F₁ ⟧₁ fst)
            * sym (star-hom₀ π₁-alg₀ ₌∘ apply r (X × Y)) * star-hom₀ π₁-alg₀ ₌∘ apply r (X × Y)
           *⟨ Ap (λ P → P * star-hom₀ π₁-alg₀ ₌∘ apply r (X × Y))
                 (sym (pair-fun-eq-fst-β fst-part snd-part))
            ⟩
          (fst ∘₌ ×₁) * star-hom₀ π₁-alg₀ ₌∘ apply r (X × Y) ∎*)
    
        π₂₁ : Square
          (star-hom₀ π₂-alg₀ ₌∘ apply l (X × Y))
          (snd ∘₌ ×₁)
          (ρ₁ ₌∘ ⟦ F₁ ⟧₁ snd)
          (star-hom₀ π₂-alg₀ ₌∘ apply r (X × Y))
        π₂₁ = from-disc (
          (star-hom₀ π₂-alg₀ ₌∘ apply l (X × Y)) * (ρ₁ ₌∘ ⟦ F₁ ⟧₁ snd)
           *⟨ Ap (λ P → (star-hom₀ π₂-alg₀ ₌∘ apply l (X × Y)) * (ρ₁ ₌∘ ⟦ F₁ ⟧₁ snd) * P)
                 (sym (sym-*-inv-l (star-hom₀ π₂-alg₀ ₌∘ apply r (X × Y))))
            ⟩
          (star-hom₀ π₂-alg₀ ₌∘ apply l (X × Y)) * (ρ₁ ₌∘ ⟦ F₁ ⟧₁ snd)
            * sym (star-hom₀ π₂-alg₀ ₌∘ apply r (X × Y)) * star-hom₀ π₂-alg₀ ₌∘ apply r (X × Y)
           *⟨ Ap (λ P → P * star-hom₀ π₂-alg₀ ₌∘ apply r (X × Y))
                 (sym (pair-fun-eq-snd-β fst-part snd-part))
            ⟩
          (snd ∘₌ ×₁) * star-hom₀ π₂-alg₀ ₌∘ apply r (X × Y) ∎*)
    
      π₁-alg₁ : Alg₁-hom ×-alg₁ 𝓧
      π₁-alg₁ = alg₁-hom (alg₀-hom fst refl) π₁₁
    
      π₂-alg₁ : Alg₁-hom ×-alg₁ 𝓨
      π₂-alg₁ = alg₁-hom (alg₀-hom snd refl) π₂₁
