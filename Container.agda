{-# OPTIONS --without-K #-}

module Container where

open import lib.Base
open import lib.types.Sigma

infix 5 _◁_

record Container : Type1 where
  constructor _◁_
  field
    Sh : Type0
    Ps : Sh → Type0

-- Functorial actions
module _ where
  -- Action on objects
  ⟦_⟧₀ : Container → Type0 → Type0
  ⟦_⟧₀ (Sh ◁ Ps) X = Σ Sh (λ s → Ps s → X)

  -- Action on morphisms
  ⟦_⟧₁ : {X Y : Type0} → (F : Container) → (X → Y) → ⟦ F ⟧₀ X → ⟦ F ⟧₀ Y
  ⟦_⟧₁ (Sh ◁ Ps) f (s , t) = (s , f ∘ t)

record ContHom (A B : Container) : Type0 where
  constructor mk-cont-hom
  open Container A
  open Container B renaming (Sh to Th ; Ps to Qs)
  field
    sh : Sh → Th
    ps : (s : Sh) → Qs (sh s) → Ps s

apply : {F G : Container} (α : ContHom F G) (X : Type0) → ⟦ F ⟧₀ X → ⟦ G ⟧₀ X
apply (mk-cont-hom sh ps) X (s , t) = sh s , t ∘ (ps s)

_‼_ : {F G : Container} (α : ContHom F G) {X : Type0} → ⟦ F ⟧₀ X → ⟦ G ⟧₀ X
_‼_ α {X} = apply α X
