{-# OPTIONS --without-K #-}

open import Container

-- Everything put together
module 1-hits.Alg0.InductionInitiality (F : Container) where

open import lib.Basics
open import 1-hits.Alg0.Core F
open import 1-hits.Alg0.CatLaws F
open import 1-hits.Alg0.Limits F
open import General
open import Cat

initiality-to-section-induction :
  (𝓧 : Alg₀-obj)
  (initial : is-initial Alg₀ 𝓧)
  → has-section-principle Alg₀ 𝓧
initiality-to-section-induction = Initiality⇒SectionInduction.section-induction Alg₀

section-principle-to-initiality :
  (𝓧 : Alg₀-obj)
  (section-principle : has-section-principle Alg₀ 𝓧)
  → is-initial Alg₀ 𝓧
section-principle-to-initiality =
  SectionInduction⇒Initiality.initial Alg₀
    right-id-alg₀
    assoc-alg₀
    product-alg₀
    equaliser-alg₀

-- TODO: section principle and induction principle
