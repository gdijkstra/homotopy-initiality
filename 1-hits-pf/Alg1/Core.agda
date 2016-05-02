{-# OPTIONS --without-K #-}

open import lib.Basics
open import Container
open import 1-hits-pf.Core
open import FreeMonad renaming (_* to _⋆)
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
      Square
        (star-hom₀ 𝓯' ₌∘ apply l X)
        (f ∘₌ θ₁)
        (ρ₁ ₌∘ ⟦ F₁ ⟧₁ f)
        (star-hom₀ 𝓯' ₌∘ apply r X)
         
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
  open Alg₁-obj 𝓨 renaming (X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)
  open Alg₁-obj 𝓩 renaming (X to Z ; θ₀ to ζ₀ ; θ₁ to ζ₁)
  open Alg₁-hom 𝓰 renaming (𝓯' to 𝓰' ; f to g ; f₀ to g₀ ; f₁ to g₁)
  open Alg₁-hom 𝓯

  ∘₁ : is-alg₁-hom 𝓧 𝓩 (∘-alg₀ 𝓰' 𝓯')
  ∘₁ = lem l *h⊡ ((lem-top l *h⊡ T ⊡h* sym (lem-top r))
              ⊡v  (lem-bot l *h⊡ B ⊡h* sym (lem-bot r)))
              ⊡h* sym (lem r)
    where
      T : Square (g ∘₌ star-hom₀ 𝓯' ₌∘ apply l X) ((g ∘ f) ∘₌ θ₁) (Ap (λ H → g ∘ H ∘ ⟦ F₁ ⟧₁ f) ρ₁) (g ∘₌ star-hom₀ 𝓯' ₌∘ apply r X)
      T = Ap-∘ (g ∘`) (f ∘`) θ₁
          *v⊡ Ap-sq (g ∘`) f₁
          ⊡v* sym (Ap-∘ (g ∘`) (`∘ ⟦ F₁ ⟧₁ f) ρ₁)

      B : Square ((star-hom₀ 𝓰' ₌∘ apply l Y) ₌∘ ⟦ F₁ ⟧₁ f) (Ap (λ H → g ∘ H ∘ ⟦ F₁ ⟧₁ f) ρ₁) (ζ₁ ₌∘ ⟦ F₁ ⟧₁ (g ∘ f)) ((star-hom₀ 𝓰' ₌∘ apply r Y) ₌∘ ⟦ F₁ ⟧₁ f)
      B = Ap-∘ (`∘ ⟦ F₁ ⟧₁ f) (g ∘`) ρ₁
          *v⊡ Ap-sq (`∘ ⟦ F₁ ⟧₁ f) g₁
          ⊡v* sym (Ap-∘ (`∘ ⟦ F₁ ⟧₁ f) (`∘ ⟦ F₁ ⟧₁ g) ζ₁)

      lem-top : (α : ContHom F₁ (F₀ ⋆))
        → Eq ((g ∘₌ star-hom₀ 𝓯') ₌∘ apply α X) (g ∘₌ (star-hom₀ 𝓯' ₌∘ apply α X))
      lem-top α = Ap-swap g (apply α X) (star-hom₀ 𝓯')

      lem-bot : (α : ContHom F₁ (F₀ ⋆))
        → Eq ((star-hom₀ 𝓰' ₌∘ ⟦ F₀ ⋆ ⟧₁ f) ₌∘ apply α X) ((star-hom₀ 𝓰' ₌∘ apply α Y) ₌∘ ⟦ F₁ ⟧₁ f) 
      lem-bot α = sym (Ap-∘ (`∘ apply α X) (`∘ ⟦ F₀ ⋆ ⟧₁ f) (star-hom₀ 𝓰'))
                * Ap-∘ (`∘ ⟦ F₁ ⟧₁ f) (`∘ apply α Y) (star-hom₀ 𝓰')
      
      lem : (α : ContHom F₁ (F₀ ⋆))
        → Eq (star-hom₀ (∘-alg₀ 𝓰' 𝓯') ₌∘ apply α X)
             (((g ∘₌ star-hom₀ 𝓯') ₌∘ apply α X) * ((star-hom₀ 𝓰' ₌∘ ⟦ F₀ ⋆ ⟧₁ f) ₌∘ apply α X))
      lem α =
        (star-hom₀ (∘-alg₀ 𝓰' 𝓯') ₌∘ apply α X)

          *⟨ Ap (λ P → Ap (`∘ apply α X) P) (*-∘ 𝓰' 𝓯') ⟩ -- *-∘

        ((g ∘₌ star-hom₀ 𝓯') * (star-hom₀ 𝓰' ₌∘ ⟦ F₀ ⋆ ⟧₁ f)) ₌∘ apply α X

          *⟨ Ap-* (`∘ apply α X) (Ap (g ∘`) (star-hom₀ 𝓯')) (Ap (`∘ ⟦ F₀ ⋆ ⟧₁ f) (star-hom₀ 𝓰')) ⟩ -- ap-*

        ((g ∘₌ star-hom₀ 𝓯') ₌∘ apply α X) * ((star-hom₀ 𝓰' ₌∘ ⟦ F₀ ⋆ ⟧₁ f) ₌∘ apply α X) ∎*

  ∘-alg₁ : Alg₁-hom 𝓧 𝓩
  ∘-alg₁ = alg₁-hom (∘-alg₀ 𝓰' 𝓯') ∘₁ 

module _
  (𝓧 : Alg₁-obj)
  where

  open Alg₁-obj 𝓧

  id₁ : is-alg₁-hom 𝓧 𝓧 (id-alg₀ 𝓧')
  id₁ =
    Ap (λ P → P ₌∘ apply l X) (*-id _)
    *h⊡ vid-square (Ap (idf (⟦ F₁ ⟧₀ X → X)) θ₁)
    ⊡h* sym (Ap (λ P → P ₌∘ apply r X) (*-id _))

  id-alg₁ : Alg₁-hom 𝓧 𝓧
  id-alg₁ = alg₁-hom (id-alg₀ 𝓧') id₁

open import Cat

Alg₁ : Cat
Alg₁ = record
  { obj = Alg₁-obj
  ; hom = Alg₁-hom
  ; comp = ∘-alg₁
  ; id = id-alg₁
  }
