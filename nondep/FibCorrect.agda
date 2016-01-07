{-# OPTIONS --without-K #-}

module nondep.FibCorrect where

open import lib.Basics
open import Cat
open import nondep.Base
open import nondep.Fib

module _
  (s : Spec)
  (F : Alg s ⇒ TypeCat)
  (𝓧 : / Alg s /)
  (P : Fib s 𝓧)
  where

  φ-φ⁻¹ :
    (x : F ⋆ (total s 𝓧 P))
    → φ s F 𝓧 P (φ⁻¹ s F 𝓧 P x) == x
  φ-φ⁻¹ x = idp
  
  φ⁻¹-φ :
    (x : Σ (F ⋆ 𝓧) (□ s F 𝓧 P))
    → φ⁻¹ s F 𝓧 P (φ s F 𝓧 P x) == x
  φ⁻¹-φ (.(Func.hom F (proj s 𝓧 P) x) , x , idp) = idp
  
Im :
  (s : Spec)
  (𝓧 𝓨 : / Alg s /)
  → Alg s [ 𝓨 , 𝓧 ] → Fib s 𝓧
Im ε X Y p x
  = Σ Y (λ y → p y == x)
Im (s ▸ mk-constr F G) (𝓧 , θ) (𝓨 , ρ) (p , p')
  = (Im s 𝓧 𝓨 p) , (λ { (.(Func.hom F (proj s 𝓧 (Im s 𝓧 𝓨 p)) y) , y , idp) → {!!} , {!!} })

-- from-to :
--   (s : Spec)
--   (𝓧 : / Alg s /)
--   (P : Fib s 𝓧) → Im s 𝓧 (total s 𝓧 P) (proj s 𝓧 P) == P
-- from-to s 𝓧 P = {!!}

-- to-from :
--   (s : Spec)
--   (𝓧 : / Alg s /)
--   (x : Σ (/ Alg s /) (λ 𝓨 → Alg s [ 𝓨 , 𝓧 ]))
--   → {!!}
-- to-from = {!!}

-- Fib-correct :
--   (s : Spec)
--   (𝓧 : / Alg s /)
--   → Fib s 𝓧 ≃ Σ (/ Alg s /) (λ 𝓨 → Alg s [ 𝓨 , 𝓧 ])
-- Fib-correct s 𝓧
--   = equiv (λ P → (total s 𝓧 P) , (proj s 𝓧 P))
--           (λ { (𝓨 , p) → Im s 𝓧 𝓨 p })
--           {!!} {!!}
