{-# OPTIONS --without-K #-}

module dep.FamCorrect where

open import lib.Basics
open import Cat
open import dep.Core
open import dep.Fam
open import dep.Fib
open import Admit

private
  singleton-elim-2 :
    (X : Set)
    (P : X → Set)
    (x : X)
    → Σ (Σ X P) (λ y → fst y == x) ≃ P x
  singleton-elim-2 X P x =
    equiv
      help-to
      help-from
      help-to-from
      help-from-to
      where
        help-to : Σ (Σ X P) (λ y → fst y == x) → P x
        help-to ((.x , p) , idp) = p
        help-from : P x → Σ (Σ X P) (λ y → fst y == x)
        help-from p = (x , p) , idp
        help-to-from : (b : P x) → help-to (help-from b) == b
        help-to-from b =  idp
        help-from-to : (a : Σ (Σ X P) (λ y → fst y == x)) → help-from (help-to a) == a
        help-from-to ((.x , p) , idp) = idp

-- The preimage operation needs to be defined mutually with its
-- correctness proof.
preimage : (s : Spec) (𝓧 : / Alg s /) (𝓟 : Fib s 𝓧) → Fam s 𝓧

fam-to-from : (s : Spec) (𝓧 : / Alg s /)
  → (b : Fam s 𝓧) → preimage s 𝓧 (total s 𝓧 b , proj s 𝓧 b) == b

fam-from-to-0 : (s : Spec) (𝓧 : / Alg s /)
  → (𝓨 : / Alg s /) (𝓹 : Alg s [ 𝓨 , 𝓧 ])
  → total s 𝓧 (preimage s 𝓧 (𝓨 , 𝓹)) == 𝓨

fam-from-to-1 : (s : Spec) (𝓧 : / Alg s /)
  → (𝓨 : / Alg s /) (𝓹 : Alg s [ 𝓨 , 𝓧 ])
  → proj s 𝓧 (preimage s 𝓧 (𝓨 , 𝓹)) == 𝓹 [ (λ h → Alg s [ h , 𝓧 ]) ↓ fam-from-to-0 s 𝓧 𝓨 𝓹 ]

fam-from-to : (s : Spec) (𝓧 : / Alg s /)
  → (a : Fib s 𝓧) → total s 𝓧 (preimage s 𝓧 a) , proj s 𝓧 (preimage s 𝓧 a) == a

preimage ε X (Y , p)
  = hfiber p
preimage (s ▸ mk-constr F G) (𝓧 , θ) ((𝓨 , ρ) , p , p₀)
  = (preimage s 𝓧 (𝓨 , p)) , (λ { (x , z , h) → admit _ })

fam-to-from ε X P = λ= (λ x → ua (singleton-elim-2 X P x))
fam-to-from (s ▸ mk-constr F G) (𝓧 , θ) (𝓟 , m) = admit _

fam-from-to-0 ε X Y p = admit _
fam-from-to-0 (s ▸ mk-constr F G) 𝓧 a 𝓹 = admit _

fam-from-to-1 ε X Y p = admit _
fam-from-to-1 (s ▸ mk-constr F G) 𝓧 a 𝓹 = admit _

fam-from-to s 𝓧 (𝓨 , 𝓹) = pair= (fam-from-to-0 s 𝓧 𝓨 𝓹) (fam-from-to-1 s 𝓧 𝓨 𝓹)

fam-correct : (s : Spec) (𝓧 : / Alg s /) → Fib s 𝓧 == Fam s 𝓧
fam-correct s 𝓧
  = ua (equiv
       (preimage s 𝓧)
       (λ 𝓟 → total s 𝓧 𝓟 , proj s 𝓧 𝓟)
       (fam-to-from s 𝓧)
       (fam-from-to s 𝓧))
