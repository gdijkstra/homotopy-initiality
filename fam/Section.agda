{-# OPTIONS --without-K #-}

module fam.Section where

open import lib.Basics
open import lib.types.Unit
open import fam.Fam

π-Fam₀ : Fam → Fam
π-Fam₀ (mk-fam A B) = mk-fam A (cst ⊤)

π-Fam₁ : (X : Fam) → Fam-hom X (π-Fam₀ X)
π-Fam₁ (mk-fam A B) = mk-fam-hom (idf A) (λ _ _ → unit)

is-section-Fam : {X : Fam} → Fam-hom (π-Fam₀ X) X → Type0
is-section-Fam {mk-fam A B} (mk-fam-hom f g) = (x : A) → f x == x

to-section : {X : Fam} (f : Fam-hom (π-Fam₀ X) X) → is-section-Fam f → (x : Fam.A X) → Fam.B X x
to-section {mk-fam A B} (mk-fam-hom f g) p x = transport B (p x) (g x unit)

from-section : {X : Fam} (f : (x : Fam.A X) → Fam.B X x) → Σ (Fam-hom (π-Fam₀ X) X) is-section-Fam
from-section {mk-fam A B} f = (mk-fam-hom (idf A) (λ a _ → f a)) , (λ x → idp)

to-from :
  {X : Fam}
  (f : (x : Fam.A X) → Fam.B X x)
  → uncurry to-section (from-section f) == f
to-from {mk-fam A B} f = λ= (λ x → idp)

-- from-to :
--  {X : Fam}
--  (x : Σ (Fam-hom (π-Fam₀ X) X) is-section-Fam)
--  → from-section (uncurry to-section x) == x
-- from-to {mk-fam A B} (mk-fam-hom f g , p) = pair= (mk-fam-hom-eq (fst (from-section (to-section (mk-fam-hom f g) p))) (mk-fam-hom f g) (λ= (λ x → ! (p x))) {!!}) {!!}
