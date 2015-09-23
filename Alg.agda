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

record Alg-morph (a b : Alg) : Type0 where
  constructor mk-alg-morph

  open Alg a 
  open Alg b renaming (X to Y ; θ to ρ)

  field
    f : X → Y
    f₀ : (x : ⟦ F ⟧₀ X) → f (θ x) == ρ (⟦ F ⟧₁ f x)

-- Equality of algebra morphisms
module _ {a b : Alg} where
  open Alg a
  open Alg b renaming (X to Y ; θ to ρ)
  open Alg-morph

  mk-alg-morph-eq-orig :
     {morph-f morph-g : Alg-morph a b}
     (p : f morph-f == f morph-g)
     (p₀ : f₀ morph-f == f₀ morph-g [ (λ f' → (x : ⟦ F ⟧₀ X) → f' (θ x) == ρ (⟦ F ⟧₁ f' x)) ↓ p ])
   → morph-f == morph-g
  mk-alg-morph-eq-orig {mk-alg-morph f f₀} {mk-alg-morph .f g₀} idp = ap (mk-alg-morph f)

  mk-alg-morph-eq :
     {morph-f morph-g : Alg-morph a b}
     (p : f morph-f == f morph-g)
     (p₀ : (x : ⟦ F ⟧₀ X)
         → transport (λ f' → f' (θ x)
        == ρ (⟦ F ⟧₁ f' x)) p (f₀ morph-f x) == f₀ morph-g x)
   → morph-f == morph-g
  mk-alg-morph-eq {mk-alg-morph f f₀} {mk-alg-morph .f f₁} idp p₀ = ap (mk-alg-morph f) (λ= p₀)

module _ {a b : Alg} {morph-f morph-g : Alg-morph a b} where
  open Alg a
  open Alg b renaming (X to Y ; θ to ρ)
  open Alg-morph morph-f
  open Alg-morph morph-g renaming (f to g ; f₀ to g₀)
    
  mk-alg-morph-eq' :
     (p : f == g)
     (q : (x : ⟦ F ⟧₀ X)
        → ! (ap (λ f' → f' (θ x)) p) -- app= p (θ x)
          ∙ f₀ x
          ∙ ap (λ f' → ρ (⟦ F ⟧₁ f' x)) p
       == g₀ x)
   → morph-f == morph-g
  mk-alg-morph-eq' p p₀ =
    mk-alg-morph-eq p
                    (λ x → (transport-id-nondep (X → Y)
                                                Y
                                                (λ f' → f' (θ x))
                                                (λ f' → ρ (⟦ F ⟧₁ f' x)) p (f₀ x))
                    ∙ p₀ x)

-- Category structure of algebras
id-morph : (X : Alg) → Alg-morph X X
id-morph X = mk-alg-morph (λ x → x) (λ _ → idp)

_∘-morph_ : {X Y Z : Alg} → Alg-morph Y Z → Alg-morph X Y → Alg-morph X Z
_∘-morph_ {mk-alg X θ} {mk-alg Y ρ} {mk-alg Z ζ} (mk-alg-morph g g₀) (mk-alg-morph f f₀) =
  mk-alg-morph (g ∘ f) (λ x → ↯
    g (f (θ x))
     =⟪ ap g (f₀ x) ⟫
    g (ρ (⟦ F ⟧₁ f x))
     =⟪ g₀ (⟦ F ⟧₁ f x) ⟫
    ζ (⟦ F ⟧₁ g (⟦ F ⟧₁ f x))
     =⟪idp⟫ -- containers satisfy functor laws strictly
    ζ (⟦ F ⟧₁ (g ∘ f) x) ∎∎)

infixr 80 _∘-morph_

open import lib.PathFunctor

∘-assoc :
    {X Y Z W : Alg}
    (h : Alg-morph Z W)
    (g : Alg-morph Y Z)
    (f : Alg-morph X Y)
  → h ∘-morph (g ∘-morph f) == (h ∘-morph g) ∘-morph f
∘-assoc
 {mk-alg X θ}
 {mk-alg Y ρ}
 {mk-alg Z ζ}
 {mk-alg W ω}
 (mk-alg-morph h h₀)
 (mk-alg-morph g g₀)
 (mk-alg-morph f f₀)
  = mk-alg-morph-eq idp (λ x → ↯
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

∘-unit-l : {X Y : Alg} (f : Alg-morph X Y) → id-morph Y ∘-morph f == f
∘-unit-l {mk-alg X θ} {mk-alg Y ρ} (mk-alg-morph f f₀)
  = mk-alg-morph-eq idp (λ x → ∙-unit-r (ap (idf Y) (f₀ x)) ∙ ap-idf (f₀ x))

∘-unit-r : {X Y : Alg} (f : Alg-morph X Y) → f ∘-morph id-morph X == f
∘-unit-r f = idp

is-initial : Alg → Type1
is-initial θ = (ρ : Alg) → is-contr (Alg-morph θ ρ)
