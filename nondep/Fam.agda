
{-# OPTIONS --without-K #-}

module nondep.Fam where

open import lib.Basics
open import Cat
open import nondep.Core

-- Family over a given algebra
Fam : (s : Spec) → / Alg s / → Type1

□ :
  (s : Spec)
  (F : Alg s ⇒ TypeCat)
  (𝓧 : / Alg s /)
  (P : Fam s 𝓧)
  → F ⋆ 𝓧 → Type0

total :
  (s : Spec)
  (𝓧 : / Alg s /)
  → Fam s 𝓧 → / Alg s /

proj :
  (s : Spec)
  (𝓧 : / Alg s /)
  (P : Fam s 𝓧)
  → Alg s [ total s 𝓧 P , 𝓧 ]

φ :
  (s : Spec)
  (F : Alg s ⇒ TypeCat)
  (𝓧 : / Alg s /)
  (P : Fam s 𝓧)
  → Σ (F ⋆ 𝓧) (□ s F 𝓧 P) → F ⋆ (total s 𝓧 P)

φ⁻¹ :
  (s : Spec)
  (F : Alg s ⇒ TypeCat)
  (𝓧 : / Alg s /)
  (P : Fam s 𝓧)
  → F ⋆ (total s 𝓧 P) → Σ (F ⋆ 𝓧) (□ s F 𝓧 P)

Fam ε X
  = X → Type0
Fam (s ▸ mk-constr F G) (𝓧 , θ)
  = Σ (Fam s 𝓧) (λ P → (x : Σ (F ⋆ 𝓧) (□ s F 𝓧 P)) → □ s G 𝓧 P (θ (fst x)))

□ s F 𝓧 P x
  = Σ (F ⋆ total s 𝓧 P) (λ y → (F ⋆⋆ proj s 𝓧 P) y == x)

φ s F 𝓧 P (x , y , p)
  = y

φ⁻¹ s F 𝓧 P x
  = ((F ⋆⋆ proj s 𝓧 P) x) , (x , idp)

total ε X P
  = Σ X P
total (s ▸ mk-constr F G) (𝓧 , θ) (P , m)
  = (total s 𝓧 P)
  , (λ x → φ s G 𝓧 P ((θ (fst (φ⁻¹ s F 𝓧 P x))) , (m (φ⁻¹ s F 𝓧 P x))))

proj ε 𝓧 P x
  = fst x
proj (s ▸ mk-constr F G) (𝓧 , θ) (P , m)
  = (proj s 𝓧 P)
  , (λ x → snd (m (φ⁻¹ s F 𝓧 P x)))

module _
  (s : Spec)
  (F : Alg s ⇒ TypeCat)
  (𝓧 : / Alg s /)
  (P : Fam s 𝓧)
  where

  φ-φ⁻¹ :
    (x : F ⋆ (total s 𝓧 P))
    → φ s F 𝓧 P (φ⁻¹ s F 𝓧 P x) == x
  φ-φ⁻¹ x = idp
  
  φ⁻¹-φ :
    (x : Σ (F ⋆ 𝓧) (□ s F 𝓧 P))
    → φ⁻¹ s F 𝓧 P (φ s F 𝓧 P x) == x
  φ⁻¹-φ (.(Func.hom F (proj s 𝓧 P) x) , x , idp) = idp
