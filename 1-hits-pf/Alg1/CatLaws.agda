{-# OPTIONS --without-K #-}

open import 1-hits-pf.Core
open import Container

-- Equality of algebra morphisms
module 1-hits-pf.Alg1.CatLaws (s : Spec) where

open import Eq
open import lib.Basics
open import 1-hits-pf.Alg1.Core s
open Spec s
open import 1-hits-pf.Alg0 F₀
open import 1-hits-pf.Alg0.FreeMonad F₀
open import 1-hits-pf.Alg1.Eq s

module _
  {𝓧 𝓨 : Alg₁-obj}
  (𝓯 : Alg₁-hom 𝓧 𝓨)
  where
  
  open Alg₁-obj 𝓧
  open Alg₁-obj 𝓨 renaming (𝓧' to 𝓨' ; X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)
  open Alg₁-hom 𝓯

  left-id₀ = Ap-idf f₀

  left-id-alg₁ : Eq (∘-alg₁ (id-alg₁ 𝓨) 𝓯) 𝓯
  left-id-alg₁ = alg₁-hom='
    f
    (∘₀ {𝓧'} {𝓨'} (id-alg₀ 𝓨') 𝓯')
    f₀
    (∘₁ (id-alg₁ 𝓨) 𝓯)
    f₁
    left-id₀
    goal
    where
      T = Ap-∘ (idf Y ∘`) (f ∘`) θ₁ *v⊡ Ap-sq (idf _) f₁ ⊡v* sym (Ap-∘ (idf Y ∘`) (`∘ ⟦ F₁ ⟧₁ f) ρ₁)
      B = Ap-∘ (`∘ ⟦ F₁ ⟧₁ f) (idf Y ∘`) ρ₁ *v⊡ Ap-sq (`∘ ⟦ F₁ ⟧₁ f) (id₁ 𝓨) ⊡v* sym (Ap-∘ (`∘ ⟦ F₁ ⟧₁ f) (`∘ idf (⟦ F₁ ⟧₀ Y)) ρ₁)
      L = {!!}
      R = {!!}
      goal : Eq
        ((L *h⊡ (T ⊡v B) ⊡h* R) ⊡h* Ap (λ h₀ → (star-hom₀ (alg₀-hom f h₀)) ₌∘ apply r X) left-id₀)
        (Ap (λ h₀ → (star-hom₀ (alg₀-hom f h₀)) ₌∘ apply l X) left-id₀ *h⊡ f₁)
      goal = {!!}
      

  right-id-alg₁ : Eq (∘-alg₁ 𝓯 (id-alg₁ 𝓧)) 𝓯
  right-id-alg₁ = {!!} --Ap (alg₁-hom f) (Ap-idf f₁)
