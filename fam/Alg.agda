{-# OPTIONS --without-K #-}

-- F-algebras on the category of families / arrow category

open import Container

module fam.Alg (F : Container) where

open import fam.Fam
open import fam.Container
open import lib.Basics

record FamAlg : Type1 where
  constructor mk-fam-alg
  field
    X : Fam
    θ : Fam-hom (⟦ F ⟧-Fam₀ X) X

record FamAlg-hom (a b : FamAlg) : Type0 where
  constructor mk-fam-alg-hom

  open FamAlg a 
  open FamAlg b renaming (X to Y ; θ to ρ)

  field
    f  : Fam-hom X Y
    f₀ : (f ∘-Fam θ)
      == (ρ ∘-Fam (⟦ F ⟧-Fam₁ f))

mk-fam-alg' :
  (A : Type0)
  (B : A → Type0)
  (θ-f : ⟦ F ⟧₀ A → A)
  (θ-g : (a : ⟦ F ⟧₀ A) → □ F B a → B (θ-f a))
  → FamAlg
mk-fam-alg' A B θ-f θ-g = mk-fam-alg (mk-fam A B) (mk-fam-hom θ-f θ-g)
  
mk-fam-alg-hom' :
  (A : Type0)
  (B : A → Type0)
  (θ-f : ⟦ F ⟧₀ A → A)
  (θ-g : (a : ⟦ F ⟧₀ A) → □ F B a → B (θ-f a))
  (C : Type0)
  (D : C → Type0)
  (ρ-f : ⟦ F ⟧₀ C → C)
  (ρ-g : (a : ⟦ F ⟧₀ C) → □ F D a → D (ρ-f a))
  (f-f : A → C)
  (f-g : (a : A) → B a → D (f-f a))
  (β-f : f-f ∘ θ-f == ρ-f ∘ ⟦ F ⟧₁ f-f)
  (β-g : (λ a b → f-g (θ-f a) (θ-g a b)) == (λ a b → ρ-g (⟦ F ⟧₁ f-f a) (λ p' → f-g (snd a p') (b p'))) [ (λ f → (x : ⟦ F ⟧₀ A) → □ F B x → D (f x)) ↓ β-f ])
  → FamAlg-hom (mk-fam-alg' A B θ-f θ-g) (mk-fam-alg' C D ρ-f ρ-g)
mk-fam-alg-hom' A B θ-f θ-g C D ρ-f ρ-g f-f f-g β-f β-g = 
 mk-fam-alg-hom (mk-fam-hom f-f f-g) (mk-fam-hom-eq (f ∘-Fam θ) (ρ ∘-Fam ⟦ F ⟧-Fam₁ f) β-f β-g)
 where f = mk-fam-hom f-f f-g
       θ = mk-fam-hom θ-f θ-g
       ρ = mk-fam-hom ρ-f ρ-g

record ArrAlg : Type1 where
  constructor mk-arr-alg
  field
    X : Arr
    θ : Arr-hom (⟦ F ⟧-Arr₀ X) X

record ArrAlg-hom (a b : ArrAlg) : Type0 where
  constructor mk-arr-alg-hom

  open ArrAlg a 
  open ArrAlg b renaming (X to Y ; θ to ρ)

  field
    f : Arr-hom X Y
    f₀ : (f ∘-Arr θ)
      == (ρ ∘-Arr (⟦ F ⟧-Arr₁ f))
open Σ-□ 

to : (X : Fam) → Arr-hom (Fam⇒Arr₀ (⟦ F ⟧-Fam₀ X)) (⟦ F ⟧-Arr₀ (Fam⇒Arr₀ X))
to (mk-fam A B) = mk-arr-hom (from-Σ-□ A B F) (idf (⟦ F ⟧₀ A)) (λ x → idp)

from : (X : Fam) → Arr-hom (⟦ F ⟧-Arr₀ (Fam⇒Arr₀ X)) (Fam⇒Arr₀ (⟦ F ⟧-Fam₀ X))
from (mk-fam A B) = mk-arr-hom (to-Σ-□ A B F) (idf (⟦ F ⟧₀ A)) (λ x → idp)

FamAlg⇒ArrAlg₀ : FamAlg → ArrAlg
FamAlg⇒ArrAlg₀ (mk-fam-alg X θ) =
  mk-arr-alg (Fam⇒Arr₀ X) (_∘-Arr_ {⟦ F ⟧-Arr₀ (Fam⇒Arr₀ X)} {Fam⇒Arr₀ (⟦ F ⟧-Fam₀ X)} {Fam⇒Arr₀ X} (Fam⇒Arr₁ θ) (from X))

lemma :
    (A B : Type0) (f : A → B)
    (a : ⟦ F ⟧₀ B)
    (p : Σ (⟦ F ⟧₀ A) (λ x → ⟦ F ⟧₁ f x == a))
    (x : Container.Positions F (fst a))
  → Σ A (λ x₁ → f x₁ == snd a x)
lemma A B f ._ ((s , t) , idp) x' = (t x') , idp

lemma' :
    (A B : Type0) (f : A → B)
    (a : ⟦ F ⟧₀ B)
    (p : (x : Container.Positions F (fst a)) → Σ A (λ x₁ → f x₁ == snd a x)) → 
    (Σ (⟦ F ⟧₀ A) (λ x → ⟦ F ⟧₁ f x == a))
lemma' A B f (s , t) p = (s , (λ z → fst (p z))) , ap (λ r → s , r) (λ= (λ x → snd (p x)))

toA : (X : Arr) → Fam-hom (Arr⇒Fam₀ (⟦ F ⟧-Arr₀ X)) (⟦ F ⟧-Fam₀ (Arr⇒Fam₀ X))
toA (mk-arr A B f) = mk-fam-hom (λ x → x) (lemma A B f)

fromA : (X : Arr) → Fam-hom (⟦ F ⟧-Fam₀ (Arr⇒Fam₀ X)) (Arr⇒Fam₀ (⟦ F ⟧-Arr₀ X))
fromA (mk-arr A B f) = mk-fam-hom (λ x → x) (lemma' A B f)

ArrAlg⇒FamAlg₀ : ArrAlg → FamAlg
ArrAlg⇒FamAlg₀ (mk-arr-alg X θ) = mk-fam-alg (Arr⇒Fam₀ X) (_∘-Fam_ {⟦ F ⟧-Fam₀ (Arr⇒Fam₀ X)} {Arr⇒Fam₀ (⟦ F ⟧-Arr₀ X)} {Arr⇒Fam₀ X} (Arr⇒Fam₁ θ) (fromA X))
