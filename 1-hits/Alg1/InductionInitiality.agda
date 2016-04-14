{-# OPTIONS --without-K #-}

open import 1-hits.Core

-- Everything put together
module 1-hits.Alg1.InductionInitiality (s : Spec) where

open import lib.Basics
open import 1-hits.Alg1.Core s
open import 1-hits.Alg1.CatLaws s
open import 1-hits.Alg1.Limits s
open import General
open import Cat

initiality-to-section-induction :
  (𝓧 : Alg₁-obj)
  (initial : is-initial Alg₁ 𝓧)
  → has-section-principle Alg₁ 𝓧
initiality-to-section-induction = Initiality⇒SectionInduction.section-induction Alg₁

section-principle-to-initiality :
  (𝓧 : Alg₁-obj)
  (section-principle : has-section-principle Alg₁ 𝓧)
  → is-initial Alg₁ 𝓧
section-principle-to-initiality =
  SectionInduction⇒Initiality.initial Alg₁
    right-id-alg₁
    assoc-alg₁
    product-alg₁
    equaliser-alg₁

-- TODO: section principle and induction principle
