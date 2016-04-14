{-# OPTIONS --without-K #-}

open import Admit

open import lib.Basics
open import Container

-- Lifting F-algebras to monad algebras of the free monad F *
module 1-hits.Alg0.FreeMonad (F : Container) where

open import 1-hits.Alg0.Core
open import FreeMonad
open import lib.types.PathSeq

_*¹ : {X : Type0} (θ : has-alg₀ F X) → has-alg₀ (F *) X
_*¹ {X} θ = rec* X X (idf X) θ

star : Alg₀-obj F → Alg₀-obj (F *)
star (alg₀ X θ) = alg₀ X (θ *¹)

module _
  {𝓧 𝓨 : Alg₀-obj F}
  (𝓯 : Alg₀-hom F 𝓧 𝓨)
  where
  
  open Alg₀-obj F 𝓧
  open Alg₀-obj F 𝓨 renaming (X to Y ; θ to ρ)  
  open Alg₀-hom F 𝓯

  star-hom₀ : is-alg₀-hom (F *) (star 𝓧) (star 𝓨) f
  star-hom₀ = Ind.ind*
           X
           (λ z → f ((θ *¹) z) == (ρ *¹) (⟦ F * ⟧₁ f z))
           (λ x → idp)
           (λ x p → ↯
                f ((θ *¹) (c* x))
                 =⟪idp⟫ -- comp. rule for θ *¹
                f (θ (⟦ F ⟧₁ (θ *¹) x))
                 =⟪ f₀ (⟦ F ⟧₁ (θ *¹) x) ⟫
                ρ (⟦ F ⟧₁ f (⟦ F ⟧₁ (θ *¹) x))
                 =⟪idp⟫ -- functoriality of F
                ρ (⟦ F ⟧₁ (f ∘ (θ *¹)) x)
                 =⟪ ap ρ (lift-func-eq F (f ∘ (θ *¹)) ((ρ *¹) ∘ ⟦ F * ⟧₁ f) x p) ⟫
                ρ (⟦ F ⟧₁ ((ρ *¹) ∘ (⟦ F * ⟧₁ f)) x)
                 =⟪idp⟫ -- functoriality of F
                ρ (⟦ F ⟧₁ (ρ *¹) (⟦ F ⟧₁ (⟦ F * ⟧₁ f) x))
                 =⟪idp⟫ -- comp. rule for ρ *¹
                (ρ *¹) (c* (⟦ F ⟧₁ (⟦ F * ⟧₁ f) x))
                 =⟪idp⟫ -- comp. rule for c*
                (ρ *¹) (⟦ F * ⟧₁ f (c* x)) ∎∎)

  star-hom : Alg₀-hom (F *) (star 𝓧) (star 𝓨)
  star-hom = alg₀-hom f star-hom₀
  
-- Functor laws, we're only focusing on the second part of the
-- morphisms, as the functions between algebra carriers remain
-- unchanged.
module _
  (𝓧 : Alg₀-obj F)
  where

  open Alg₀-obj F 𝓧

  -- Can cubical reasoning make this more readable?
  star-hom-id :
    (x : ⟦ F * ⟧₀ X)
    → star-hom₀ (id-alg₀ F 𝓧) x == idp
  star-hom-id = 
    Ind.ind* X
             (λ x → id*₀ x == idp)
             (λ x → idp)
             (λ x p → ↯
                id*₀ (c* x)
                 =⟪idp⟫
                ap θ (lift-func-eq F (θ *¹) (θ *¹) x (bar F id*₀ x))
                 =⟪ ap (λ h → ap θ (lift-func-eq F (θ *¹) (θ *¹) x h)) (λ= p) ⟫
                ap θ (lift-func-eq F (θ *¹) (θ *¹) x (λ _ → idp))
                 =⟪ ap (λ h → ap θ h) (lift-func-eq-idp F (θ *¹) x) ⟫
                idp ∎∎)
    where id*₀ = star-hom₀ (id-alg₀ F 𝓧)

module _
  {𝓧 𝓨 𝓩 : Alg₀-obj F}
  (𝓰 : Alg₀-hom F 𝓨 𝓩)
  (𝓯 : Alg₀-hom F 𝓧 𝓨)
  where

  open Alg₀-obj F 𝓧
  open Alg₀-obj F 𝓨 renaming (X to Y ; θ to ρ)
  open Alg₀-obj F 𝓩 renaming (X to Z ; θ to ζ)  
  open Alg₀-hom F 𝓰 renaming (f to g ; f₀ to g₀)
  open Alg₀-hom F 𝓯
  
  star-hom-comp :
    (x : ⟦ F * ⟧₀ X)
    → star-hom₀ (∘-alg₀ F 𝓰 𝓯) x == ∘₀ (F *) (star-hom 𝓰) (star-hom 𝓯) x 
  star-hom-comp =
    Ind.ind* X
           (λ x → g₀∘f₀* x == g₀*∘f₀* x)
           (λ x → idp)
           (λ x p → ↯
              g₀∘f₀* (c* x)
               =⟪idp⟫
              g₀∘f₀ (⟦ F ⟧₁ (θ *¹) x)
              ∙ ap ζ (rec-gf x)
               =⟪idp⟫
              (ap g (f₀ (⟦ F ⟧₁ (θ *¹) x))
              ∙ g₀ (⟦ F ⟧₁ (f ∘ (θ *¹)) x))
              ∙ ap ζ (rec-gf x)
                =⟪ admit _ ⟫ -- some mad reasoning yo
              (ap g (f₀ (⟦ F ⟧₁ (θ *¹) x))
              ∙ g₀ (⟦ F ⟧₁ (f ∘ (θ *¹)) x))
              ∙ (ap (ζ ∘ ⟦ F ⟧₁ g) (rec-f x)
              ∙ ap ζ (rec-g (⟦ F ⟧₁ (⟦ F * ⟧₁ f) x)))
                =⟪ admit _ ⟫ -- assoc
              ap g (f₀ (⟦ F ⟧₁ (θ *¹) x))
              ∙ (g₀ (⟦ F ⟧₁ (f ∘ (θ *¹)) x)
              ∙ ap (ζ ∘ ⟦ F ⟧₁ g) (rec-f x))
              ∙ ap ζ (rec-g (⟦ F ⟧₁ (⟦ F * ⟧₁ f) x))
               =⟪ admit _ ⟫ -- htpy-natural g₀ (rec-f x)
              ap g (f₀ (⟦ F ⟧₁ (θ *¹) x))
              ∙ (ap (g ∘ ρ) (rec-f x)
              ∙ g₀ (⟦ F ⟧₁ ((ρ *¹) ∘ ⟦ F * ⟧₁ f) x))
              ∙ ap ζ (rec-g (⟦ F ⟧₁ (⟦ F * ⟧₁ f) x))
               =⟪ admit _ ⟫ -- assoc.
              (ap g (f₀ (⟦ F ⟧₁ (θ *¹) x)) ∙ ap (g ∘ ρ) (rec-f x)) ∙ g₀ (⟦ F ⟧₁ ((ρ *¹) ∘ ⟦ F * ⟧₁ f) x) ∙ ap ζ (rec-g (⟦ F ⟧₁ (⟦ F * ⟧₁ f) x))
               =⟪ admit _ ⟫ -- ap-∘
              (ap g (f₀ (⟦ F ⟧₁ (θ *¹) x)) ∙ ap g (ap ρ (rec-f x))) ∙ g₀ (⟦ F ⟧₁ ((ρ *¹) ∘ ⟦ F * ⟧₁ f) x) ∙ ap ζ (rec-g (⟦ F ⟧₁ (⟦ F * ⟧₁ f) x))
               =⟪ admit _ ⟫ -- ap-∙ 
              ap g (f₀ (⟦ F ⟧₁ (θ *¹) x) ∙ ap ρ (rec-f x)) ∙ g₀ (⟦ F ⟧₁ ((ρ *¹) ∘ ⟦ F * ⟧₁ f) x) ∙ ap ζ (rec-g (⟦ F ⟧₁ (⟦ F * ⟧₁ f) x))
               =⟪idp⟫
              ap g (f₀* (c* x))  ∙ g₀* (⟦ F * ⟧₁ f (c* x))
               =⟪idp⟫
              g₀*∘f₀* (c* x) ∎∎)
    where g₀∘f₀ = ∘₀ F 𝓰 𝓯
          g₀∘f₀* = star-hom₀ (∘-alg₀ F 𝓰 𝓯)
          g₀* = star-hom₀ 𝓰
          f₀* = star-hom₀ 𝓯
          g₀*∘f₀* = ∘₀ (F *) (star-hom 𝓰) (star-hom 𝓯)
          rec-gf = (λ x → (lift-func-eq F (g ∘ f ∘ (θ *¹)) ((ζ *¹) ∘ ⟦ F * ⟧₁ (g ∘ f)) x (bar F g₀∘f₀* x)))
          rec-f = (λ x → lift-func-eq F (f ∘ (θ *¹)) ((ρ *¹) ∘ ⟦ F * ⟧₁ f) x (bar F f₀* x))
          rec-g = (λ x → lift-func-eq F (g ∘ (ρ *¹)) ((ζ *¹) ∘ ⟦ F * ⟧₁ g) x (bar F g₀* x))
