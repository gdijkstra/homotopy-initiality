{-# OPTIONS --without-K #-}

module dep.FibCorrect where

open import lib.Basics
open import Cat
open import dep.Core
open import dep.Fib
open import Admit

module _
  (s : Spec)
  (F : Alg s ⇒ TypeCat)
  (𝓧 : / Alg s /)
  (P : Fib s 𝓧)
  where

  φ-φ⁻¹-F :
    (x : F ⋆ (total s 𝓧 P))
    → φ-F s F 𝓧 P (φ⁻¹-F s F 𝓧 P x) == x
  φ-φ⁻¹-F x = idp
  
  φ⁻¹-φ-F :
    (x : Σ (F ⋆ 𝓧) (□-F s F 𝓧 P))
    → φ⁻¹-F s F 𝓧 P (φ-F s F 𝓧 P x) == x
  φ⁻¹-φ-F (.(Func.hom F (proj s 𝓧 P) x) , x , idp) = idp
  
  module _
    (G : ∫ (Alg s) F ⇒ TypeCat)
    (x : F ⋆ 𝓧)
    (y : □-F s F 𝓧 P x)
    where
    φ-φ⁻¹-G :
      (p : G ⋆ (total s 𝓧 P , φ-F s F 𝓧 P (x , y)))
      → φ-G s F G 𝓧 P x y (φ⁻¹-G s F G 𝓧 P x y p) == p
    φ-φ⁻¹-G p = idp  
    
    φ⁻¹-φ-G :
      (p : Σ (G ⋆ (𝓧 , x)) (□-G s F G 𝓧 P x y))
      → φ⁻¹-G s F G 𝓧 P x y (φ-G s F G 𝓧 P x y p) == p
    φ⁻¹-φ-G (.(Func.hom G (proj s 𝓧 P , snd y) p) , p , idp) = idp

Im :
  (s : Spec)
  (𝓧 𝓨 : / Alg s /)
  → Alg s [ 𝓨 , 𝓧 ] → Fib s 𝓧
Im ε X Y p x
  = Σ Y (λ y → p y == x)
Im (s ▸ mk-constr F G) (𝓧 , θ) (𝓨 , ρ) (p , p')
  = (Im s 𝓧 𝓨 p) , (λ { (.(Func.hom F (proj s 𝓧 (Im s 𝓧 𝓨 p)) y) , y , idp) → admit _ , admit _ })

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
