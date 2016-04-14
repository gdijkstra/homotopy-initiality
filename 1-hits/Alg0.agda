{-# OPTIONS --without-K #-}

open import Container

module 1-hits.Alg0 (F : Container) where

open import 1-hits.Alg0.Core F public
open import 1-hits.Alg0.Eq F public
open import 1-hits.Alg0.CatLaws F public
open import 1-hits.Alg0.FreeMonad F public
open import 1-hits.Alg0.Limits F public
open import 1-hits.Alg0.Fam F public
open import 1-hits.Alg0.FamCorrect F public
open import 1-hits.Alg0.InductionInitiality F public
