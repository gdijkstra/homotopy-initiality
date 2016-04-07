{-# OPTIONS --without-K #-}

open import 1-hits.Core

module 1-hits.Target (s : Spec) where

open import 1-hits.Target.Core s public
open import 1-hits.Target.Id s public
open import 1-hits.Target.Comp s public
open import 1-hits.Target.IdLaws s public
open import 1-hits.Target.AssocLaw s public
open import 1-hits.Target.Product s public
open import 1-hits.Target.Apd s public
