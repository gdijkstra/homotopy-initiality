{-# OPTIONS --without-K #-}

module 1-hits.Spec where

open import lib.Basics
open import lib.types.Sigma
open import Container
open import FreeMonad
open import 1-hits.Alg0.Alg 
open import Admit
open import lib.types.PathSeq

record Spec : Type1 where
  constructor mk-spec
  field
    F₀ : Container
    F₁ : Container
    l r : ContHom F₁ (F₀ *)
