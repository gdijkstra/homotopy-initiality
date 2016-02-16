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

module _ (F : Container) where
  open Container F

  □ : {A : Type0} (B : A → Type0) → ⟦ F ⟧₀ A → Type0
  □ B (s , t) = (p : Ps s) → B (t p)

  φ : {A : Type0} (B : A → Type0) → ⟦ F ⟧₀ (Σ A B) → Σ (⟦ F ⟧₀ A) (□ B)
  φ B (s , t) = (⟦ F ⟧₁ fst (s , t)) , (λ p → snd (t p))

  φ⁻¹ : {A : Type0} (B : A → Type0) → Σ (⟦ F ⟧₀ A) (□ B) → ⟦ F ⟧₀ (Σ A B)
  φ⁻¹ B ((s , t) , p) = s , (λ x → (t x) , (p x))
  
  bar : {A : Type0} {B : A → Type0}
    → ((x : A) → B x) → (x : ⟦ F ⟧₀ A) → □ B x
  bar 𝓼 (s , t) = λ p → 𝓼 (t p)
  
  open import lib.Funext using (λ=)

  postulate
    λ=-idp :
      {A : Type0}
      {P : A → Type0}
      (f : Π A P) → λ= (λ x → idp {a = f x}) == idp

  lift-func-eq :
    {A B : Type0} (f g : A → B)
    (x : ⟦ F ⟧₀ A) (y : □ (λ x' → f x' == g x') x)
    → ⟦ F ⟧₁ f x == ⟦ F ⟧₁ g x
  lift-func-eq f g (s , t) h = ap (λ p → s , p) (λ= h)

  lift-func-eq-idp :
    {A B : Type0}
    (f : A → B)
    (x : ⟦ F ⟧₀ A) 
    → lift-func-eq f f x (λ _ → idp) == idp
  lift-func-eq-idp f (s , t) =
    ap (λ h → ap (λ p → s , p) h) (λ=-idp _)
