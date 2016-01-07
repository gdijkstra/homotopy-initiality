{-# OPTIONS --without-K #-}

module Admit where

open import lib.Basics

postulate
  admit : {i : ULevel} (X : Type i) →  X

