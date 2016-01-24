{-# OPTIONS --without-K #-}

open import Container

module 1-hits.Alg0 (F : Container) where

open import 1-hits.Alg0.Core F public
open import 1-hits.Alg0.Eq F public
open import 1-hits.Alg0.Cat F public
open import 1-hits.Alg0.FreeMonad F public
open import 1-hits.Alg0.Limits F public
