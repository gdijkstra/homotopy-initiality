{-# OPTIONS --without-K #-}

open import 1-hits-pf.Core
open import Container

-- Equality of algebra morphisms
module 1-hits-pf.Alg1.CatLaws.LeftId (s : Spec) where

open import Eq
open import lib.Basics
open import 1-hits-pf.Alg1.Core s
open Spec s
open import 1-hits-pf.Alg0 F₀
open import FreeMonad renaming (_* to _⋆)
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
      T : Square
            (idf Y ∘₌ star-hom₀ 𝓯' ₌∘ apply l X)
            (f ∘₌ θ₁)
            (ρ₁ ₌∘ ⟦ F₁ ⟧₁ f)
            (idf Y ∘₌ star-hom₀ 𝓯' ₌∘ apply r X)
      T = Ap-∘ (idf Y ∘`) (f ∘`) θ₁
          *v⊡ Ap-sq (idf Y ∘`) f₁
          ⊡v* sym (Ap-∘ (idf Y ∘`) (`∘ ⟦ F₁ ⟧₁ f) ρ₁)

      B : Square
            ((star-hom₀ (id-alg₀ 𝓨') ₌∘ apply l Y) ₌∘ ⟦ F₁ ⟧₁ f)
            (ρ₁ ₌∘ ⟦ F₁ ⟧₁ f)
            (ρ₁ ₌∘ ⟦ F₁ ⟧₁ f)
            ((star-hom₀ (id-alg₀ 𝓨') ₌∘ apply r Y) ₌∘ ⟦ F₁ ⟧₁ f)
      B = Ap-∘ (`∘ ⟦ F₁ ⟧₁ f) (idf Y ∘`) ρ₁
          *v⊡ Ap-sq (`∘ ⟦ F₁ ⟧₁ f) (id₁ 𝓨)
          ⊡v* sym (Ap-∘ (`∘ ⟦ F₁ ⟧₁ f) (`∘ ⟦ F₁ ⟧₁ (idf Y)) ρ₁)

      lem-top : (α : ContHom F₁ (F₀ ⋆))
        → Eq ((idf Y ∘₌ star-hom₀ 𝓯') ₌∘ apply α X) (idf Y ∘₌ (star-hom₀ 𝓯' ₌∘ apply α X))
      lem-top α = Ap-swap (idf Y) (apply α X) (star-hom₀ 𝓯')

      lem-bot : (α : ContHom F₁ (F₀ ⋆))
        → Eq ((star-hom₀ (id-alg₀ 𝓨') ₌∘ ⟦ F₀ ⋆ ⟧₁ f) ₌∘ apply α X)
             ((star-hom₀ (id-alg₀ 𝓨') ₌∘ apply α Y) ₌∘ ⟦ F₁ ⟧₁ f) 
      lem-bot α = sym (Ap-∘ (`∘ apply α X) (`∘ ⟦ F₀ ⋆ ⟧₁ f) (star-hom₀ (id-alg₀ 𝓨')))
                * Ap-∘ (`∘ ⟦ F₁ ⟧₁ f) (`∘ apply α Y) (star-hom₀ (id-alg₀ 𝓨'))
      
      lem : (α : ContHom F₁ (F₀ ⋆))
        → Eq (star-hom₀ (∘-alg₀ (id-alg₀ 𝓨') 𝓯') ₌∘ apply α X)
             (((idf Y ∘₌ star-hom₀ 𝓯') ₌∘ apply α X) *
              ((star-hom₀ (id-alg₀ 𝓨') ₌∘ ⟦ F₀ ⋆ ⟧₁ f) ₌∘ apply α X))
      lem α =
        (star-hom₀ (∘-alg₀ (id-alg₀ 𝓨') 𝓯') ₌∘ apply α X)

          *⟨ Ap (λ P → Ap (`∘ apply α X) P) (*-∘ (id-alg₀ 𝓨') 𝓯') ⟩ -- *-∘

        ((idf Y ∘₌ star-hom₀ 𝓯') * (star-hom₀ (id-alg₀ 𝓨') ₌∘ ⟦ F₀ ⋆ ⟧₁ f)) ₌∘ apply α X

          *⟨ Ap-* (`∘ apply α X)
                  (Ap ((idf Y) ∘`) (star-hom₀ 𝓯'))
                  (Ap (`∘ ⟦ F₀ ⋆ ⟧₁ f) (star-hom₀ (id-alg₀ 𝓨')))
           ⟩ -- ap-*

        ((idf Y ∘₌ star-hom₀ 𝓯') ₌∘ apply α X) * ((star-hom₀ (id-alg₀ 𝓨') ₌∘ ⟦ F₀ ⋆ ⟧₁ f) ₌∘ apply α X) ∎*

      id∘𝓯 : Square (star-hom₀ (∘-alg₀ (id-alg₀ 𝓨') 𝓯') ₌∘ apply l X)
                    (f ∘₌ θ₁) (ρ₁ ₌∘ ⟦ F₁ ⟧₁ f)
                    (star-hom₀ (∘-alg₀ (id-alg₀ 𝓨') 𝓯') ₌∘ apply r X)
      id∘𝓯 = lem l *h⊡ ((lem-top l *h⊡ T ⊡h* sym (lem-top r))
              ⊡v  (lem-bot l *h⊡ B ⊡h* sym (lem-bot r)))
              ⊡h* sym (lem r)

      goal : Eq
        (id∘𝓯 ⊡h* Ap (λ h₀ → star-hom₀ (alg₀-hom f h₀) ₌∘ apply r X) left-id₀)
        (Ap (λ h₀ → star-hom₀ (alg₀-hom f h₀) ₌∘ apply l X) left-id₀ *h⊡
           f₁)
      goal = {!!}
