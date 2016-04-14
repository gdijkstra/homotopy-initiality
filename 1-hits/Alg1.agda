{-# OPTIONS --without-K #-}

open import 1-hits.Core

module 1-hits.Alg1 (s : Spec) where

open import 1-hits.Alg1.Core s
open import 1-hits.Alg1.Eq s
open import 1-hits.Alg1.CatLaws s
open import 1-hits.Alg1.Limits s
open import 1-hits.Alg1.InductionInitiality s
