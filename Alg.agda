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

record Alg-hom (a b : Alg) : Type0 where
  constructor mk-alg-hom

  open Alg a 
  open Alg b renaming (X to Y ; θ to ρ)

  field
    f : X → Y
    f₀ : (x : ⟦ F ⟧₀ X) → f (θ x) == ρ (⟦ F ⟧₁ f x)

-- Equality of algebra homisms
module _ {a b : Alg} where
  open Alg a
  open Alg b renaming (X to Y ; θ to ρ)
  open Alg-hom

  mk-alg-hom-eq-orig :
     {hom-f hom-g : Alg-hom a b}
     (p : f hom-f == f hom-g)
     (p₀ : f₀ hom-f == f₀ hom-g [ (λ f' → (x : ⟦ F ⟧₀ X) → f' (θ x) == ρ (⟦ F ⟧₁ f' x)) ↓ p ])
   → hom-f == hom-g
  mk-alg-hom-eq-orig {mk-alg-hom f f₀} {mk-alg-hom .f g₀} idp = ap (mk-alg-hom f)

  mk-alg-hom-eq :
     {hom-f hom-g : Alg-hom a b}
     (p : f hom-f == f hom-g)
     (p₀ : (x : ⟦ F ⟧₀ X)
         → transport (λ f' → f' (θ x)
        == ρ (⟦ F ⟧₁ f' x)) p (f₀ hom-f x) == f₀ hom-g x)
   → hom-f == hom-g
  mk-alg-hom-eq {mk-alg-hom f f₀} {mk-alg-hom .f f₁} idp p₀ = ap (mk-alg-hom f) (λ= p₀)

module _ {a b : Alg} {hom-f hom-g : Alg-hom a b} where
  open Alg a
  open Alg b renaming (X to Y ; θ to ρ)
  open Alg-hom hom-f
  open Alg-hom hom-g renaming (f to g ; f₀ to g₀)
    
  mk-alg-hom-eq' :
     (p : f == g)
     (q : (x : ⟦ F ⟧₀ X)
        → ! (ap (λ f' → f' (θ x)) p) -- app= p (θ x)
          ∙ f₀ x
          ∙ ap (λ f' → ρ (⟦ F ⟧₁ f' x)) p
       == g₀ x)
   → hom-f == hom-g
  mk-alg-hom-eq' p p₀ =
    mk-alg-hom-eq p
                    (λ x → (transport-id-nondep (X → Y)
                                                Y
                                                (λ f' → f' (θ x))
                                                (λ f' → ρ (⟦ F ⟧₁ f' x)) p (f₀ x))
                    ∙ p₀ x)

-- Category structure of algebras
id-hom : (X : Alg) → Alg-hom X X
id-hom X = mk-alg-hom (λ x → x) (λ _ → idp)

_∘-hom_ : {X Y Z : Alg} → Alg-hom Y Z → Alg-hom X Y → Alg-hom X Z
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
  = mk-alg-hom-eq idp (λ x → ↯
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

∘-unit-l : {X Y : Alg} (f : Alg-hom X Y) → id-hom Y ∘-hom f == f
∘-unit-l {mk-alg X θ} {mk-alg Y ρ} (mk-alg-hom f f₀)
  = mk-alg-hom-eq idp (λ x → ∙-unit-r (ap (idf Y) (f₀ x)) ∙ ap-idf (f₀ x))

∘-unit-r : {X Y : Alg} (f : Alg-hom X Y) → f ∘-hom id-hom X == f
∘-unit-r f = idp

is-initial : Alg → Type1
is-initial θ = (ρ : Alg) → is-contr (Alg-hom θ ρ)
