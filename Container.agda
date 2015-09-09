{-# OPTIONS --without-K #-}

module Container where

open import lib.Base
open import lib.types.Sigma

infix 5 _◁_

record Container : Type1 where
  constructor _◁_
  field
    Shapes    : Type0
    Positions : Shapes → Type0

-- Functorial actions
module _ where
  -- Action on objects
  ⟦_⟧₀ : Container → Type0 → Type0
  ⟦_⟧₀ (Sh ◁ Pos) X = Σ Sh (λ s → Pos s → X)

  -- Action on morphisms
  ⟦_⟧₁ : {X Y : Type0} → (F : Container) → (X → Y) → ⟦ F ⟧₀ X → ⟦ F ⟧₀ Y
  ⟦_⟧₁ (Sh ◁ Pos) f (s , t) = (s , f ∘ t)

  -- Functor laws only hold strictly if id-unit-l and comp-assoc hold
  -- strictly.
  module _ (F : Container) where
    ⟦id⟧₁=id : {X : Type0} → (x : ⟦ F ⟧₀ X) → ⟦ F ⟧₁ (idf X) x == x
    ⟦id⟧₁=id (s , t) = ap (λ x → s , x) idp

    FgFf=Fgf : {X Y Z : Type0} → (g : Y → Z) (f : X → Y)
               (x : ⟦ F ⟧₀ X) → ⟦ F ⟧₁ g (⟦ F ⟧₁ f x) == ⟦ F ⟧₁ (g ∘ f) x
    FgFf=Fgf g f (s , t) = ap (λ y → s , y) idp

module _ (F G : Container) where
  record ContainerMorphism : Type0 where
    constructor mk-cont-morphism
    
    open Container F renaming ( Shapes to Sh₀ ; Positions to Pos₀ )
    open Container G renaming ( Shapes to Sh₁ ; Positions to Pos₁ )
  
    field
      f : Sh₀ → Sh₁
      g : (s : Sh₀) → Pos₁ (f s) → Pos₀ s

apply : {F G : Container} (α : ContainerMorphism F G) (X : Type0) → ⟦ F ⟧₀ X → ⟦ G ⟧₀ X
apply (mk-cont-morphism f g) X (s , t) = f s , t ∘ (g s)

_‼_ : {F G : Container} (α : ContainerMorphism F G) {X : Type0} → ⟦ F ⟧₀ X → ⟦ G ⟧₀ X
_‼_ α {X} = apply α X

-- FX - Ff -> FY
--  |          |
-- apply X    apply Y
--  |          |
--  v          v
-- GX - Gf -> GY
module _ {F G : Container} (α : ContainerMorphism F G) where
  apply-natural : {X Y : Type0} (f : X → Y) → apply α Y ∘ ⟦ F ⟧₁ f == ⟦ G ⟧₁ f ∘ apply α X
  apply-natural f = idp

open import lib.types.Empty

Const : Type0 → Container
Const X = X ◁ cst ⊥

all : (F : Container) {X : Type0} (A : X → Type0) → ⟦ F ⟧₀ X → Type0
all (Sh ◁ Pos) A (s , t) = (x : Pos s) → A (t x)

□ = all

-- We can lift sections of a family B : A → Type to □ B : FA → Type.
module _ (F : Container) {A : Type0} {B : A → Type0} (f : (x : A) → B x) where
  □-lift : (x : ⟦ F ⟧₀ A) → □ F B x
  □-lift (s , t) = f ∘ t

  f~ : A → Σ A B
  f~ x = (x , f x)

  □-lift=sndFf~ : (x : ⟦ F ⟧₀ A) → snd ∘ snd (⟦ F ⟧₁ f~ x) == □-lift x
  □-lift=sndFf~ x = idp

-- Containers preserve Σ-types in the following sense.
module Σ-□ (A : Type0) (B : A → Type0) (F : Container)  where
  to-Σ-□ : ⟦ F ⟧₀ (Σ A B) → Σ (⟦ F ⟧₀ A) (□ F B)
  to-Σ-□ (s , t) = (s , (λ x → fst (t x))) , (λ x → snd (t x))

  from-Σ-□ : Σ (⟦ F ⟧₀ A) (□ F B) → ⟦ F ⟧₀ (Σ A B)
  from-Σ-□ ((s , t) , a) = s , (λ z → t z , a z)

  from-to-Σ-□ : (x : ⟦ F ⟧₀ (Σ A B)) → from-Σ-□ (to-Σ-□ x) == x
  from-to-Σ-□ _ = idp

  to-from-Σ-□ : (x : Σ (⟦ F ⟧₀ A) (□ F B)) → (to-Σ-□ (from-Σ-□ x)) == x
  to-from-Σ-□ _ = idp

open Σ-□

module _ (F G : Container) (α : ContainerMorphism F G) (A : Type0) (B : A → Type0) where
  open ContainerMorphism F G α

  □-base-change : (x : ⟦ F ⟧₀ A) → □ F B x → □ G B (apply α A x)
  □-base-change (s , t) a p = a (g s p)

  -- ⟦ F ⟧₀ (Σ A B) → ⟦ G ⟧₀ (Σ A B)
