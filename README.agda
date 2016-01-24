{-# OPTIONS --without-K #-}

-- This project aims to formalise a notion of higher inductive types
-- and prove general properties about them. Most importantly we want
-- to be able to do the following:

--  * give a specification of a higher inductive type

--  * generate the induction principle of that type given its
--    specification

--  * specify its algebras and algebra morphisms

--  * show that the induction principle implies homotopy initiality
--    and vice versa

-- In order to avoid coherence issues as much as possible, we will
-- lazily introduce all the category structure we need in order to do
-- what we want.

-- We can perform the proof that induction implies initiality and vice
-- versa in relative generality, as can be seen in the following module:
import General

-- General specification of HITs as towers of dependent dialgebras:
import Dep

-- Experiments with towers of ordinary (non-dependent) dialgebras.
import Nondep

-- Restricted specification of 1-HITs, using containers.
import 1-hits

