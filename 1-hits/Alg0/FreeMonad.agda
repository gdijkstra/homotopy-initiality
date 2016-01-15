{-# OPTIONS --without-K #-}

open import lib.Basics
open import Container

-- Lifting F-algebras to monad algebras of the free monad F *
module 1-hits.Alg0.FreeMonad (F : Container) where

open import 1-hits.Alg0.Alg
open import FreeMonad
open import lib.types.PathSeq

_*¹ : {X : Type0} (θ : has-alg₀ F X) → has-alg₀ (F *) X
_*¹ {X} θ = rec* X X (idf X) θ

_,_*-hom : {X Y : Type0} {θ : has-alg₀ F X} {ρ : has-alg₀ F Y}
  (f : X → Y) (f₀ : is-alg₀-hom F θ ρ f) → is-alg₀-hom (F *) (θ *¹) (ρ *¹) f
_,_*-hom {X} {Y} {θ} {ρ} f f₀ =
  Ind.ind* X
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
                 =⟪idp⟫ -- comp. rule for ⟦ F * ⟧₁
                (ρ *¹) (⟦ F * ⟧₁ f (c* x)) ∎∎)

-- Note that if f₀ x = idp, then the recursive part becomes idp?

id*-hom : {X : Type0} {θ : has-alg₀ F X}
  → _,_*-hom {θ = θ} (idf X) (λ _ → idp) == (λ x → idp)
id*-hom {X} {θ} = λ= 
  (Ind.ind* X
           (λ x → _,_*-hom {θ = θ} (idf X) (λ _ → idp) x == idp)
           (λ _ → idp)
           (λ x p → {!!}))

