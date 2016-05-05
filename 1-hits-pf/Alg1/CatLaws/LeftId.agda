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

  left-id₀* = star-hom₀ (∘-alg₀ (id-alg₀ 𝓨') 𝓯')

  id₀* = star-hom₀ (id-alg₀ 𝓨')
  f₀* = star-hom₀ 𝓯'
  h₀* : is-alg₀-hom 𝓧' 𝓨' f → Eq (f ∘ (θ₀ *¹)) ((ρ₀ *¹) ∘ ⟦ F₀ ⋆ ⟧₁ f)
  h₀* = λ h₀ → star-hom₀ (alg₀-hom f h₀)

  -- Simplifying top
  T T' : Square
        (idf Y ∘₌ star-hom₀ 𝓯' ₌∘ apply l X)
        (f ∘₌ θ₁)
        (ρ₁ ₌∘ ⟦ F₁ ⟧₁ f)
        (idf Y ∘₌ star-hom₀ 𝓯' ₌∘ apply r X)
  T = Ap-∘ (idf Y ∘`) (f ∘`) θ₁
      *v⊡ Ap-sq (idf Y ∘`) f₁
      ⊡v* sym (Ap-∘ (idf Y ∘`) (`∘ ⟦ F₁ ⟧₁ f) ρ₁)

  T' = Ap-idf (f₀* ₌∘ apply l X) *h⊡ f₁ ⊡h* sym (Ap-idf (f₀* ₌∘ apply r X))

  -- T-simpl : Eq T T'
  -- T-simpl = {!!}

  lem-top : (α : ContHom F₁ (F₀ ⋆))
    → Eq ((idf Y ∘₌ f₀*) ₌∘ apply α X) (idf Y ∘₌ (f₀* ₌∘ apply α X))
  lem-top α = Ap-swap (idf Y) (apply α X) f₀*

  top top' : Square ((idf Y ∘₌ f₀*) ₌∘ apply l X) (f ∘₌ θ₁) (ρ₁ ₌∘ ⟦ F₁ ⟧₁ f) ((idf Y ∘₌ f₀*) ₌∘ apply r X)
  top = lem-top l *h⊡ T ⊡h* sym (lem-top r)

  top' = Ap (λ P → P ₌∘ apply l X) (Ap-idf f₀*) *h⊡ f₁ ⊡h* sym (Ap (λ P → P ₌∘ apply r X) (Ap-idf f₀*))

  --top-simpl : Eq top top'
  --top-simpl = ?

  -- Simplifying bottom
  B B' : Square
        ((id₀* ₌∘ apply l Y) ₌∘ ⟦ F₁ ⟧₁ f)
        (ρ₁ ₌∘ ⟦ F₁ ⟧₁ f)
        (ρ₁ ₌∘ ⟦ F₁ ⟧₁ f)
        ((id₀* ₌∘ apply r Y) ₌∘ ⟦ F₁ ⟧₁ f)
  B = Ap-∘ (`∘ ⟦ F₁ ⟧₁ f) (idf Y ∘`) ρ₁
      *v⊡ Ap-sq (`∘ ⟦ F₁ ⟧₁ f) (id₁ 𝓨)
      ⊡v* sym (Ap-∘ (`∘ ⟦ F₁ ⟧₁ f) (`∘ ⟦ F₁ ⟧₁ (idf Y)) ρ₁)

  B' = (Ap (λ P → (P ₌∘ apply l Y) ₌∘ ⟦ F₁ ⟧₁ f) (*-id 𝓨')
         *h⊡ vid-square (ρ₁ ₌∘ ⟦ F₁ ⟧₁ f)
         ⊡h* sym (Ap (λ P → (P ₌∘ apply r Y) ₌∘ ⟦ F₁ ⟧₁ f) (*-id 𝓨')))

  -- B-simpl : Eq B B'
  -- B-simpl = ?

  lem-bot : (α : ContHom F₁ (F₀ ⋆))
    → Eq ((id₀* ₌∘ ⟦ F₀ ⋆ ⟧₁ f) ₌∘ apply α X)
         ((id₀* ₌∘ apply α Y) ₌∘ ⟦ F₁ ⟧₁ f) 
  lem-bot α = sym (Ap-∘ (`∘ apply α X) (`∘ ⟦ F₀ ⋆ ⟧₁ f) id₀*)
            * Ap-∘ (`∘ ⟦ F₁ ⟧₁ f) (`∘ apply α Y) id₀*
  
  bot bot' : Square ((id₀* ₌∘ ⟦ F₀ ⋆ ⟧₁ f) ₌∘ apply l X) (ρ₁ ₌∘ ⟦ F₁ ⟧₁ f) (ρ₁ ₌∘ ⟦ F₁ ⟧₁ f) ((id₀* ₌∘ ⟦ F₀ ⋆ ⟧₁ f) ₌∘ apply r X)
  bot = lem-bot l *h⊡ B ⊡h* sym (lem-bot r)

  bot' = Ap (λ P → P ₌∘ apply l X) (Ap (λ P → P ₌∘ ⟦ F₀ ⋆ ⟧₁ f) (*-id 𝓨'))
         *h⊡ vid-square (ρ₁ ₌∘ ⟦ F₁ ⟧₁ f)
         ⊡h* sym (Ap (λ P → P ₌∘ apply r X) (Ap (λ P → P ₌∘ ⟦ F₀ ⋆ ⟧₁ f) (*-id 𝓨')))

  --bot-simpl : Eq bot bot'
  --bot-simpl = ?

  -- Simplifying top and bottom

  top-bot top-bot' : Square
    (((idf Y ∘₌ f₀*) ₌∘ apply l X) * ((id₀* ₌∘ ⟦ F₀ ⋆ ⟧₁ f) ₌∘ apply l X))
    (f ∘₌ θ₁)
    (ρ₁ ₌∘ ⟦ F₁ ⟧₁ f)
    (((idf Y ∘₌ f₀*) ₌∘ apply r X) * ((id₀* ₌∘ ⟦ F₀ ⋆ ⟧₁ f) ₌∘ apply r X))
  top-bot = top ⊡v bot

  --top-bot' = {!!} *h⊡ f₁ ⊡h* {!!}

  --top-bot-simpl : Eq top-bot top-bot'
  --top-bot-simpl = ?

  -- Further simplification

  -- -- lem : (α : ContHom F₁ (F₀ ⋆))
  -- --   → Eq (left-id₀* ₌∘ apply α X)
  -- --        (((idf Y ∘₌ f₀*) ₌∘ apply α X) *
  -- --         ((id₀* ₌∘ ⟦ F₀ ⋆ ⟧₁ f) ₌∘ apply α X))
  -- -- lem α =
  -- --   (left-id₀* ₌∘ apply α X)

  -- --     *⟨ Ap (λ P → Ap (`∘ apply α X) P) (*-∘ (id-alg₀ 𝓨') 𝓯') ⟩ -- *-∘

  -- --   ((idf Y ∘₌ f₀*) * (id₀* ₌∘ ⟦ F₀ ⋆ ⟧₁ f)) ₌∘ apply α X

  -- --     *⟨ Ap-* (`∘ apply α X)
  -- --             (Ap ((idf Y) ∘`) f₀*)
  -- --             (Ap (`∘ ⟦ F₀ ⋆ ⟧₁ f) id₀*)
  -- --      ⟩ -- ap-*

  -- --   ((idf Y ∘₌ f₀*) ₌∘ apply α X) * ((id₀* ₌∘ ⟦ F₀ ⋆ ⟧₁ f) ₌∘ apply α X) ∎*

  -- -- id∘𝓯 : Square (left-id₀* ₌∘ apply l X)
  -- --               (f ∘₌ θ₁)
  -- --               (ρ₁ ₌∘ ⟦ F₁ ⟧₁ f)
  -- --               (left-id₀* ₌∘ apply r X)
  -- -- id∘𝓯 = lem l *h⊡ ((lem-top l *h⊡ T ⊡h* sym (lem-top r))
  -- --         ⊡v  (lem-bot l *h⊡ B ⊡h* sym (lem-bot r)))
  -- --         ⊡h* sym (lem r)

  -- -- id∘𝓯-simpl :
  -- --   Eq id∘𝓯
  -- --      (Ap (h₀* ₌∘ apply l X) left-id₀ *h⊡ f₁ ⊡h* sym (Ap (h₀* ₌∘ apply r X) left-id₀))
  -- -- id∘𝓯-simpl = {!!} -- ⊡-magic and coh for *

  -- -- goal : Eq
  -- --   (id∘𝓯 ⊡h* Ap (h₀* ₌∘ apply r X) left-id₀)
  -- --   (Ap (h₀* ₌∘ apply l X) left-id₀ *h⊡ f₁)
  -- -- goal =
  -- --   (id∘𝓯 ⊡h* z)
  -- --   *⟨ Ap (λ H → H ⊡h* z) id∘𝓯-simpl ⟩
  -- --   (x *h⊡ y ⊡h* sym z) ⊡h* z
  -- --   *⟨ Ap (λ P → P ⊡h* z) (⊡h-assoc x y (sym z)) ⟩
  -- --   ((x *h⊡ y) ⊡h* sym z) ⊡h* z
  -- --   *⟨ ⊡h** (x *h⊡ y) (sym z) z ⟩
  -- --   (x *h⊡ y) ⊡h* (sym z * z)
  -- --   *⟨ Ap (λ P → (x *h⊡ y) ⊡h* P) (sym-*-inv-l z) ⟩
  -- --   x *h⊡ y ∎*
  -- --     where
  -- --       x = Ap (h₀* ₌∘ apply l X) left-id₀
  -- --       y = f₁
  -- --       z = Ap (h₀* ₌∘ apply r X) left-id₀

  -- -- left-id-alg₁ : Eq (∘-alg₁ (id-alg₁ 𝓨) 𝓯) 𝓯
  -- -- left-id-alg₁ = alg₁-hom='
  -- --   f
  -- --   (∘₀ {𝓧'} {𝓨'} (id-alg₀ 𝓨') 𝓯')
  -- --   f₀
  -- --   (∘₁ (id-alg₁ 𝓨) 𝓯)
  -- --   f₁
  -- --   left-id₀
  -- --   {!!} --goal
  -- --   where
