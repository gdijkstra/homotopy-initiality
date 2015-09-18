{-# OPTIONS --without-K #-}

module ContainerFam where

open import lib.Base hiding (S)
open import lib.types.Sigma
open import Container
open import Fam

⟦_⟧-Fam₀ : Container → Fam → Fam
⟦_⟧-Fam₀ F (A , B) = (⟦ F ⟧₀ A , □ F B)

⟦_⟧-Fam₁ : {X Y : Fam} (F : Container) → Fam-hom X Y → Fam-hom (⟦ F ⟧-Fam₀ X) (⟦ F ⟧-Fam₀ Y)
⟦_⟧-Fam₁ F (f , g) = (⟦ F ⟧₁ f) , (λ x p p' → □-lift F g x p' (p p') )

⟦_⟧-Fam₁-id : {X : Fam} (F : Container) → ⟦_⟧-Fam₁ {X} {X} F (Fam-id X) == Fam-id (⟦ F ⟧-Fam₀ X)
⟦_⟧-Fam₁-id F = idp

