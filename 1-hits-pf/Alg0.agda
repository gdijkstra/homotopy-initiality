{-# OPTIONS --without-K #-}

open import Container

module 1-hits-pf.Alg0 (F : Container) where

open import 1-hits-pf.Alg0.Core F public
open import 1-hits-pf.Alg0.CatLaws F public
open import 1-hits-pf.Alg0.Eq F public
open import 1-hits-pf.Alg0.Limits F public
