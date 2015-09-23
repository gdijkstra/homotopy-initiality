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

record FamAlg-morph (a b : FamAlg) : Type0 where
  constructor mk-fam-alg-morph

  open FamAlg a 
  open FamAlg b renaming (X to Y ; θ to ρ)

  field
    f : Fam-hom X Y
    f₀ : (_∘-Fam_ {⟦ F ⟧-Fam₀ X} {X} {Y} f θ)
      == (_∘-Fam_ {⟦ F ⟧-Fam₀ X} {⟦ F ⟧-Fam₀ Y} {Y} ρ (⟦_⟧-Fam₁ {X} {Y} F f))

record ArrAlg : Type1 where
  constructor mk-arr-alg
  field
    X : Arr
    θ : Arr-hom (⟦ F ⟧-Arr₀ X) X

record ArrAlg-morph (a b : ArrAlg) : Type0 where
  constructor mk-arr-alg-morph

  open ArrAlg a 
  open ArrAlg b renaming (X to Y ; θ to ρ)

  field
    f : Arr-hom X Y
    f₀ : (_∘-Arr_ {⟦ F ⟧-Arr₀ X} {X} {Y} f θ)
      == (_∘-Arr_ {⟦ F ⟧-Arr₀ X} {⟦ F ⟧-Arr₀ Y} {Y} ρ (⟦_⟧-Arr₁ {X} {Y} F f))

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
