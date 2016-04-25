{-# OPTIONS --without-K #-}

open import lib.Basics
open import Container
open import 1-hits-pf.Core

module 1-hits-pf.Alg1.Core (s : Spec) where

open Spec s
open import 1-hits-pf.Alg0 F₀
open import 1-hits-pf.Alg0.FreeMonad F₀
open import Eq

has-alg₁ :
  (𝓧 : Alg₀-obj)
  → Type0
has-alg₁ (alg₀ X θ₀) = Eq ((θ₀ *¹) ∘ apply l X)
                          ((θ₀ *¹) ∘ apply r X)

record Alg₁-obj : Type1 where
  constructor alg₁

  field
   𝓧' : Alg₀-obj
   θ₁ : has-alg₁ 𝓧'

  X = Alg₀-obj.X 𝓧'
  θ₀ = Alg₀-obj.θ 𝓧'

module _
  (𝓧 𝓨 : Alg₁-obj)
  where

  open Alg₁-obj 𝓧
  open Alg₁-obj 𝓨 renaming (𝓧' to 𝓨' ; X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)
  
  module _ (𝓯' : Alg₀-hom 𝓧' 𝓨') where
    open Alg₀-hom 𝓯'
    is-alg₁-hom : Type0
    is-alg₁-hom =
      Eq (Ap (f ∘`) θ₁ * Ap (`∘ apply r X) (star-hom₀ 𝓯'))
         (Ap (`∘ apply l X) (star-hom₀ 𝓯') * Ap (`∘ ⟦ F₁ ⟧₁ f) ρ₁)
         
record Alg₁-hom (𝓧 𝓨 : Alg₁-obj) : Type0 where
  constructor alg₁-hom

  open Alg₁-obj 𝓧
  open Alg₁-obj 𝓨 renaming (𝓧' to 𝓨' ; X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)
  
  field
    𝓯' : Alg₀-hom 𝓧' 𝓨'
    f₁ : is-alg₁-hom 𝓧 𝓨 𝓯'

  f = Alg₀-hom.f 𝓯'
  f₀ = Alg₀-hom.f₀ 𝓯'

module _
  {𝓧 𝓨 𝓩 : Alg₁-obj}
  (𝓰 : Alg₁-hom 𝓨 𝓩)
  (𝓯 : Alg₁-hom 𝓧 𝓨)
  where
  
  open Alg₁-obj 𝓧
  open Alg₁-obj 𝓩 renaming (X to Z ; θ₀ to ζ₀ ; θ₁ to ζ₁)
  open Alg₁-hom 𝓰 renaming (𝓯' to 𝓰' ; f to g ; f₀ to g₀ ; f₁ to g₁)
  open Alg₁-hom 𝓯

  -- Have:

  --  f₁   Eq (Ap (f ∘`) θ₁ * Ap (`∘ apply r X) (star-hom₀ 𝓯'))
  --        (Ap (`∘ apply l X) (star-hom₀ 𝓯') * Ap (`∘ ⟦ F₁ ⟧₁ f) ρ₁)

  --  g₁   Eq (Ap (g ∘`) ρ₁ * Ap (`∘ apply r Y) (star-hom₀ 𝓰'))
  --        (Ap (`∘ apply l Y) (star-hom₀ 𝓰') * Ap (`∘ ⟦ F₁ ⟧₁ g) ζ₁)

  ∘₁ : is-alg₁-hom 𝓧 𝓩 (∘-alg₀ 𝓰' 𝓯')
  ∘₁ =
    Ap (g ∘ f ∘`) θ₁ * Ap (`∘ apply r X) (star-hom₀ (∘-alg₀ 𝓰' 𝓯'))
     *⟨ {!f₁!} ⟩
    Ap (`∘ apply l X) (star-hom₀ (∘-alg₀ 𝓰' 𝓯')) * Ap (`∘ ⟦ F₁ ⟧₁ (g ∘ f)) ζ₁ ∎*

  ∘-alg₁ : Alg₁-hom 𝓧 𝓩
  ∘-alg₁ = alg₁-hom (∘-alg₀ 𝓰' 𝓯') ∘₁ 

module _
  (𝓧 : Alg₁-obj)
  where

  open Alg₁-obj 𝓧

  id₁ : is-alg₁-hom 𝓧 𝓧 (id-alg₀ 𝓧')
  id₁ =
    Ap (idf X ∘`) θ₁ * Ap (`∘ apply r X) (star-hom₀ (id-alg₀ 𝓧'))
     *⟨ Ap (λ P → Ap (idf X ∘`) θ₁ * Ap (`∘ apply r X) P) (*-id 𝓧') ⟩
    Ap (idf X ∘`) θ₁
     *⟨ refl ⟩
    Ap (`∘ ⟦ F₁ ⟧₁ (idf X)) θ₁
     *⟨ Ap (λ P → Ap (`∘ apply l X) P * Ap (`∘ ⟦ F₁ ⟧₁ (idf X)) θ₁) (sym (*-id 𝓧')) ⟩
    Ap (`∘ apply l X) (star-hom₀ (id-alg₀ 𝓧')) * Ap (`∘ ⟦ F₁ ⟧₁ (idf X)) θ₁ ∎*

  id-alg₁ : Alg₁-hom 𝓧 𝓧
  id-alg₁ = alg₁-hom (id-alg₀ 𝓧') id₁
