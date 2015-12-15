{-# OPTIONS --without-K #-}

module IndDefFib where

open import lib.Basics
open import lib.types.Sigma
open import lib.types.Unit
open import lib.types.Empty
open import lib.PathGroupoid
open import IndDefBase

-- Fibration over a given algebra
Fib : (s : Spec) → / Alg s / → Type1

□-F :
  (s : Spec)
  (F : Alg s ⇒ TypeCat)
  (𝓧 : / Alg s /)
  (P : Fib s 𝓧)
  → F ⋆ 𝓧 → Type0

□-G :
  (s : Spec)
  (F : Alg s ⇒ TypeCat)
  (G : ∫ (Alg s) F ⇒ TypeCat)
  (𝓧 : / Alg s /)
  (P : Fib s 𝓧)
  (x : F ⋆ 𝓧)
  (y : □-F s F 𝓧 P x)
  → G ⋆ (𝓧 , x) → Type0

total :
  (s : Spec)
  (𝓧 : / Alg s /)
  → Fib s 𝓧 → / Alg s /

proj :
  (s : Spec)
  (𝓧 : / Alg s /)
  (P : Fib s 𝓧)
  → Alg s [ total s 𝓧 P , 𝓧 ]

φ-F :
  (s : Spec)
  (F : Alg s ⇒ TypeCat)
  (𝓧 : / Alg s /)
  (P : Fib s 𝓧)
  → Σ (F ⋆ 𝓧) (□-F s F 𝓧 P) → F ⋆ (total s 𝓧 P)

φ⁻¹-F :
  (s : Spec)
  (F : Alg s ⇒ TypeCat)
  (𝓧 : / Alg s /)
  (P : Fib s 𝓧)
  → F ⋆ (total s 𝓧 P) → Σ (F ⋆ 𝓧) (□-F s F 𝓧 P)

φ-G :
  (s : Spec)
  (F : Alg s ⇒ TypeCat)
  (G : ∫ (Alg s) F ⇒ TypeCat)
  (𝓧 : / Alg s /)
  (P : Fib s 𝓧)
  (x : F ⋆ 𝓧)
  (y : □-F s F 𝓧 P x)
  → Σ (G ⋆ (𝓧 , x)) (□-G s F G 𝓧 P x y) → G ⋆ (total s 𝓧 P , φ-F s F 𝓧 P (x , y))

φ⁻¹-G :
  (s : Spec)
  (F : Alg s ⇒ TypeCat)
  (G : ∫ (Alg s) F ⇒ TypeCat)
  (𝓧 : / Alg s /)
  (P : Fib s 𝓧)
  (x : F ⋆ 𝓧)
  (y : □-F s F 𝓧 P x)
  → G ⋆ (total s 𝓧 P , φ-F s F 𝓧 P (x , y)) → Σ (G ⋆ (𝓧 , x)) (□-G s F G 𝓧 P x y)

Fib ε X
  = X → Type0
Fib (s ▸ mk-constr F G) (𝓧 , θ)
  = Σ (Fib s 𝓧) (λ P → (x : Σ (F ⋆ 𝓧) (□-F s F 𝓧 P)) → □-G s F G 𝓧 P (fst x) (snd x) (θ (fst x)))

□-F s F 𝓧 P x
  = Σ (F ⋆ total s 𝓧 P) (λ y → (F ⋆⋆ proj s 𝓧 P) y == x)

φ-F s F 𝓧 P (x , y , p)
  = y

φ⁻¹-F s F 𝓧 P x
  = ((F ⋆⋆ proj s 𝓧 P) x) , (x , idp)

□-G s F G 𝓧 P x y p
  = Σ (G ⋆ (total s 𝓧 P) , φ-F s F 𝓧 P (x , y)) (λ q →
      (G ⋆⋆ (proj s 𝓧 P) , snd y) q == p)

φ-G s F G 𝓧 P x y (p , q , r)
  = q

φ⁻¹-G s F G 𝓧 P x y p
  = ((G ⋆⋆ (proj s 𝓧 P) , (snd y)) p) , (p , idp)

total ε X P
  = Σ X P
total (s ▸ mk-constr F G) (𝓧 , θ) (P , m)
  = (total s 𝓧 P)
  , (λ x → φ-G s F G 𝓧 P
               (fst (φ⁻¹-F s F 𝓧 P x))
               (snd (φ⁻¹-F s F 𝓧 P x))
               ((θ (fst (φ⁻¹-F s F 𝓧 P x))) , (m (φ⁻¹-F s F 𝓧 P x))))

proj ε 𝓧 P x
  = fst x
proj (s ▸ mk-constr F G) (𝓧 , θ) (P , m)
  = (proj s 𝓧 P)
  , (λ x → snd (m (φ⁻¹-F s F 𝓧 P x)))
