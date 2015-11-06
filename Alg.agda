{-# OPTIONS --without-K #-}

open import Container

module Alg (F : Container) where

open import lib.Basics
open import lib.types.PathSeq
open import Utils

record Alg : Type1 where
  constructor mk-alg
  field
    X : Type0
    θ : ⟦ F ⟧₀ X → X

record Alg-hom (𝓧 𝓨 : Alg) : Type0 where
  constructor mk-alg-hom
  open Alg 𝓧
  open Alg 𝓨 renaming (X to Y ; θ to ρ)

  field
    f : X → Y
    f₀ : (x : ⟦ F ⟧₀ X) → f (θ x) == ρ (⟦ F ⟧₁ f x)

-- Equality of algebra morphisms
module _ {𝓧 𝓨 : Alg} where
  open Alg 𝓧
  open Alg 𝓨 renaming (X to Y ; θ to ρ)
  open Alg-hom

  mk-alg-hom-eq-0 :
     {𝓯 𝓰 : Alg-hom 𝓧 𝓨}
     (p : f 𝓯 == f 𝓰)
     (p₀ : f₀ 𝓯 == f₀ 𝓰 [ (λ h → (x : ⟦ F ⟧₀ X) → h (θ x) == ρ (⟦ F ⟧₁ h x)) ↓ p ])
   → 𝓯 == 𝓰
  mk-alg-hom-eq-0 {mk-alg-hom f f₀} {mk-alg-hom .f g₀} idp = ap (mk-alg-hom f)

  mk-alg-hom-eq-1 :
     {𝓯 𝓰 : Alg-hom 𝓧 𝓨}
     (p : f 𝓯 == f 𝓰)
     (p₀ : (x : ⟦ F ⟧₀ X)
         → transport (λ h → h (θ x) == ρ (⟦ F ⟧₁ h x)) p (f₀ 𝓯 x)
        == f₀ 𝓰 x)
   → 𝓯 == 𝓰
  mk-alg-hom-eq-1 {mk-alg-hom f f₀} {mk-alg-hom .f f₁} idp p₀ = ap (mk-alg-hom f) (λ= p₀)

  mk-alg-hom-eq-2 :
     {𝓯 𝓰 : Alg-hom 𝓧 𝓨}
     (p : f 𝓯 == f 𝓰)
     (p₀ : (x : ⟦ F ⟧₀ X)
         → f₀ 𝓯 x ∙ ap (λ h → ρ (⟦ F ⟧₁ h x)) p
        == ap (λ h → h (θ x)) p ∙ f₀ 𝓰 x)
   → 𝓯 == 𝓰
  mk-alg-hom-eq-2 {mk-alg-hom f f₀} {mk-alg-hom g g₀} p p₀ =
    mk-alg-hom-eq-1 p
                    (λ x → transport-id-nondep (X → Y) Y (λ h → h (θ x)) (λ h → ρ (⟦ F ⟧₁ h x)) p
                             (f₀ x)
                             ∙ p=q∙r→!p∙q=r (ap (λ h → h (θ x)) p)
                                            (f₀ x ∙ ap (λ h → ρ (⟦ F ⟧₁ h x)) p)
                                            (g₀ x)
                                            (p₀ x))

  -- mk-alg-hom-eq-3 :
  --    {𝓯 𝓰 : Alg-hom 𝓧 𝓨}
  --    (p : (x : X) → f 𝓯 x == f 𝓰 x)
  --    (p₀ : (x : ⟦ F ⟧₀ X)
  --        → f₀ 𝓯 x ∙ ap (λ h → ρ (⟦ F ⟧₁ h x)) (λ= p)
  --       == p (θ x) ∙ f₀ 𝓰 x)
  --  → 𝓯 == 𝓰
  -- mk-alg-hom-eq-3 {mk-alg-hom f f₀} {mk-alg-hom g g₀} p p₀ = mk-alg-hom-eq-2 (λ= p)
  --   {!!}


-- Category structure of algebras
id-hom : (𝓧 : Alg) → Alg-hom 𝓧 𝓧
id-hom 𝓧 = mk-alg-hom (λ x → x) (λ _ → idp)

_∘-hom_ : {𝓧 𝓨 𝓩 : Alg} → Alg-hom 𝓨 𝓩 → Alg-hom 𝓧 𝓨 → Alg-hom 𝓧 𝓩
_∘-hom_ {mk-alg X θ} {mk-alg Y ρ} {mk-alg Z ζ} (mk-alg-hom g g₀) (mk-alg-hom f f₀) =
  mk-alg-hom (g ∘ f) (λ x → ↯
    g (f (θ x))
     =⟪ ap g (f₀ x) ⟫
    g (ρ (⟦ F ⟧₁ f x))
     =⟪ g₀ (⟦ F ⟧₁ f x) ⟫
    ζ (⟦ F ⟧₁ g (⟦ F ⟧₁ f x))
     =⟪idp⟫ -- containers satisfy functor laws strictly
    ζ (⟦ F ⟧₁ (g ∘ f) x) ∎∎)

infixr 80 _∘-hom_

open import lib.PathFunctor

∘-assoc :
    {X Y Z W : Alg}
    (h : Alg-hom Z W)
    (g : Alg-hom Y Z)
    (f : Alg-hom X Y)
  → h ∘-hom (g ∘-hom f) == (h ∘-hom g) ∘-hom f
∘-assoc
 {mk-alg X θ}
 {mk-alg Y ρ}
 {mk-alg Z ζ}
 {mk-alg W ω}
 (mk-alg-hom h h₀)
 (mk-alg-hom g g₀)
 (mk-alg-hom f f₀)
  = mk-alg-hom-eq-1 idp (λ x → ↯
    ap h (g₀∘f₀ x) ∙ h₀ (⟦ F ⟧₁ (g ∘ f) x)
     =⟪idp⟫
    ap h (ap g (f₀ x) ∙ g₀ (⟦ F ⟧₁ f x)) ∙ h₀ (⟦ F ⟧₁ (g ∘ f) x)
     =⟪ ap (λ p → p ∙ h₀ (⟦ F ⟧₁ (g ∘ f) x)) (ap-∙ h (ap g (f₀ x)) (g₀ (⟦ F ⟧₁ f x))) ⟫
    (ap h (ap g (f₀ x)) ∙ ap h (g₀ (⟦ F ⟧₁ f x))) ∙ h₀ (⟦ F ⟧₁ (g ∘ f) x)
     =⟪ ∙-assoc (ap h (ap g (f₀ x))) (ap h (g₀ (⟦ F ⟧₁ f x))) (h₀ (⟦ F ⟧₁ (g ∘ f) x)) ⟫
    ap h (ap g (f₀ x)) ∙ ap h (g₀ (⟦ F ⟧₁ f x)) ∙ h₀ (⟦ F ⟧₁ (g ∘ f) x)
     =⟪ ap (λ p → p ∙ ap h (g₀ (⟦ F ⟧₁ f x)) ∙ h₀ (⟦ F ⟧₁ (g ∘ f) x)) (∘-ap h g (f₀ x)) ⟫
    ap (h ∘ g) (f₀ x) ∙ ap h (g₀ (⟦ F ⟧₁ f x)) ∙ h₀ (⟦ F ⟧₁ (g ∘ f) x)
     =⟪idp⟫
    ap (h ∘ g) (f₀ x) ∙ h₀∘g₀ (⟦ F ⟧₁ f x) ∎∎)
  where
    g₀∘f₀ : (x : ⟦ F ⟧₀ X) → g (f (θ x)) == ζ (⟦ F ⟧₁ (g ∘ f) x)
    g₀∘f₀ x = ap g (f₀ x) ∙ g₀ (⟦ F ⟧₁ f x)

    h₀∘g₀ : (x : ⟦ F ⟧₀ Y) → h (g (ρ x)) == ω (⟦ F ⟧₁ (h ∘ g) x)
    h₀∘g₀ x = ap h (g₀ x) ∙ h₀ (⟦ F ⟧₁ g x)

∘-unit-l : {𝓧 𝓨 : Alg} (f : Alg-hom 𝓧 𝓨) → id-hom 𝓨 ∘-hom f == f
∘-unit-l {mk-alg X θ} {mk-alg Y ρ} (mk-alg-hom f f₀)
  = mk-alg-hom-eq-1 idp (λ x → ∙-unit-r (ap (idf Y) (f₀ x)) ∙ ap-idf (f₀ x))

∘-unit-r : {𝓧 𝓨 : Alg} (f : Alg-hom 𝓧 𝓨) → f ∘-hom id-hom 𝓧 == f
∘-unit-r f = idp

is-initial : Alg → Type1
is-initial θ = (ρ : Alg) → is-contr (Alg-hom θ ρ)
