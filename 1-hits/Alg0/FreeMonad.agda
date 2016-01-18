{-# OPTIONS --without-K #-}

open import lib.Basics
open import Container

-- Lifting F-algebras to monad algebras of the free monad F *
module 1-hits.Alg0.FreeMonad (F : Container) where

open import 1-hits.Alg0.Alg
open import FreeMonad
open import lib.types.PathSeq
open import Admit

_*¹ : {X : Type0} (θ : has-alg₀ F X) → has-alg₀ (F *) X
_*¹ {X} θ = rec* X X (idf X) θ

-- TODO: Get better notation for this.
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

-- Functor laws
id*-hom :
  {X : Type0}
  {θ : has-alg₀ F X}
  (x : ⟦ F * ⟧₀ X)
  → _,_*-hom {X} {X} {θ} {θ} (idf X) (λ _ → idp) x == idp
id*-hom {X} {θ} =
  Ind.ind* X
           (λ x → id*₀ x == idp)
           (λ x → idp)
           (λ x p → ↯
              (idf X , (λ _ → idp) *-hom) (c* x)
               =⟪idp⟫
              ap θ (lift-func-eq F (θ *¹) (θ *¹) x (bar F id*₀ x))
               =⟪ ap (λ h → ap θ (lift-func-eq F (θ *¹) (θ *¹) x h)) (λ= p) ⟫
              ap θ (lift-func-eq F (θ *¹) (θ *¹) x (λ _ → idp))
               =⟪ ap (λ h → ap θ h) (lift-func-eq-idp F (θ *¹) x) ⟫
              idp ∎∎)
  where id*₀ = (idf X , (λ _ → idp) *-hom)

comp*-hom :
    {X Y Z : Type0}
    (θ : has-alg₀ F X)
    (ρ : has-alg₀ F Y)
    (ζ : has-alg₀ F Z)
    (g : Y → Z)
    (f : X → Y)
    (g₀ : is-alg₀-hom F ρ ζ g)
    (f₀ : is-alg₀-hom F θ ρ f)
    (x : ⟦ F * ⟧₀ X)
    →  (g ∘ f , _∘₀_ F {X} {Y} {Z} {θ} {ρ} {ζ} {g} {f} g₀ f₀ *-hom) x
    == _∘₀_ (F *) {X} {Y} {Z} {θ *¹} {ρ *¹} {ζ *¹} {g = g} {f = f} (g , g₀ *-hom) (f , f₀ *-hom) x
comp*-hom {X} {Y} {Z} θ ρ ζ g f g₀ f₀ =
  Ind.ind* X
           (λ x → g₀∘f₀* x == g₀*∘f₀* x)
           (λ x → idp)
           (λ x p → ↯
              g₀∘f₀* (c* x)
               =⟪idp⟫
              g₀∘f₀ (⟦ F ⟧₁ (θ *¹) x) ∙ ap ζ (rec-gf x)
               =⟪idp⟫
              (ap g (f₀ (⟦ F ⟧₁ (θ *¹) x)) ∙ g₀ (⟦ F ⟧₁ (f ∘ (θ *¹)) x)) ∙ ap ζ (rec-gf x)
                =⟪ admit _ ⟫ -- some mad reasoning yo
              (ap g (f₀ (⟦ F ⟧₁ (θ *¹) x)) ∙ g₀ (⟦ F ⟧₁ (f ∘ (θ *¹)) x)) ∙ (ap (ζ ∘ ⟦ F ⟧₁ g) (rec-f x) ∙ ap ζ (rec-g (⟦ F ⟧₁ (⟦ F * ⟧₁ f) x)))
                =⟪ admit _ ⟫ -- assoc
              ap g (f₀ (⟦ F ⟧₁ (θ *¹) x)) ∙ (g₀ (⟦ F ⟧₁ (f ∘ (θ *¹)) x) ∙ ap (ζ ∘ ⟦ F ⟧₁ g) (rec-f x)) ∙ ap ζ (rec-g (⟦ F ⟧₁ (⟦ F * ⟧₁ f) x))
               =⟪ admit _ ⟫ -- htpy-natural g₀ (rec-f x)
              ap g (f₀ (⟦ F ⟧₁ (θ *¹) x)) ∙ (ap (g ∘ ρ) (rec-f x) ∙ g₀ (⟦ F ⟧₁ ((ρ *¹) ∘ ⟦ F * ⟧₁ f) x)) ∙ ap ζ (rec-g (⟦ F ⟧₁ (⟦ F * ⟧₁ f) x))
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
    where g₀∘f₀ = _∘₀_ F {X} {Y} {Z} {θ} {ρ} {ζ} {g} {f} g₀ f₀
          g₀∘f₀* = (g ∘ f , _∘₀_ F {X} {Y} {Z} {θ} {ρ} {ζ} {g} {f} g₀ f₀ *-hom)
          g₀* = (g , g₀ *-hom)
          f₀* = (f , f₀ *-hom)
          g₀*∘f₀* = _∘₀_ (F *) {X} {Y} {Z} {θ *¹} {ρ *¹} {ζ *¹} {g = g} {f = f} g₀* f₀*
          rec-gf = (λ x → (lift-func-eq F (g ∘ f ∘ (θ *¹)) ((ζ *¹) ∘ ⟦ F * ⟧₁ (g ∘ f)) x (bar F g₀∘f₀* x)))
          rec-f = (λ x → lift-func-eq F (f ∘ (θ *¹)) ((ρ *¹) ∘ ⟦ F * ⟧₁ f) x (bar F f₀* x))
          rec-g = (λ x → lift-func-eq F (g ∘ (ρ *¹)) ((ζ *¹) ∘ ⟦ F * ⟧₁ g) x (bar F g₀* x))
