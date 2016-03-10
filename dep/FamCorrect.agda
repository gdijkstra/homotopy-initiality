{-# OPTIONS --without-K #-}

module dep.FamCorrect where

open import lib.Basics
open import Cat
open import dep.Core
open import dep.Fam
open import dep.Fib
open import Admit

data FamView (s : Spec) (𝓧 : / Alg s /) : Fib s 𝓧 → Type1 where
  mk-famview : (𝓟 : Fam s 𝓧) → FamView s 𝓧 ((total s 𝓧 𝓟) , (proj s 𝓧 𝓟))

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
famView : (s : Spec) (𝓧 : / Alg s /) (p : Fib s 𝓧) → FamView s 𝓧 p

preimage : (s : Spec) (𝓧 : / Alg s /) (𝓟 : Fib s 𝓧) → Fam s 𝓧

data FibView (s : Spec) (𝓧 : / Alg s /) : Fam s 𝓧 → Type1

fibView : (s : Spec) (𝓧 : / Alg s /) (𝓟 : Fam s 𝓧) → FibView s 𝓧 𝓟

fam-to-from : (s : Spec) (𝓧 : / Alg s /)
  → (b : Fam s 𝓧) → preimage s 𝓧 (total s 𝓧 b , proj s 𝓧 b) == b

fam-from-to : (s : Spec) (𝓧 : / Alg s /)
  → (a : Fib s 𝓧) → total s 𝓧 (preimage s 𝓧 a) , proj s 𝓧 (preimage s 𝓧 a) == a

famView ε X (Y , p) = admit _
famView (s ▸ c) (𝓧 , θ) ((𝓨 , ρ) , (p , p₀)) with famView s 𝓧 (𝓨 , p)
famView (s ▸ c) (𝓧 , θ) ((.(total s 𝓧 𝓟) , ρ) , .(proj s 𝓧 𝓟) , p₀) | mk-famview 𝓟 = mk-famview (𝓟 , (λ { (.(Func.hom (Constr.F c) (proj s 𝓧 𝓟) x) , x , idp) → (ρ x) , (p₀ x) }))

preimage ε X (Y , p) = hfiber p
preimage (s ▸ c) (𝓧 , θ) ((𝓨 , ρ) , p , p₀) with famView s 𝓧 (𝓨 , p)
preimage (s ▸ c) (𝓧 , θ) ((.(total s 𝓧 𝓟) , ρ) , .(proj s 𝓧 𝓟) , p₀) | mk-famview 𝓟 = 𝓟 , (λ { (.(Func.hom (Constr.F c) (proj s 𝓧 𝓟) x) , x , idp) → (ρ x) , (p₀ x) })

data FibView (s : Spec) (𝓧 : / Alg s /) where
  mk-fibview : (P : Fib s 𝓧) → FibView s 𝓧 (preimage s 𝓧 P)

fibView ε X P = admit _
fibView (s ▸ c) (𝓧 , θ) (𝓟 , m) = admit _

fam-to-from ε X P = λ= (λ x → ua (singleton-elim-2 X P x))
fam-to-from (s ▸ c) (𝓧 , θ) (𝓟 , m) with famView s 𝓧 (total s 𝓧 𝓟 , proj s 𝓧 𝓟)
fam-to-from (s ▸ c) (𝓧 , θ) (𝓟 , m) | f with fam-to-from s 𝓧 𝓟
fam-to-from (s ▸ c) (𝓧 , θ) (𝓟 , m) | f | p = admit _

fam-from-to ε X (Y , P) = admit _
fam-from-to (s ▸ c) (𝓧 , θ) ((𝓨 , ρ) , (p , p₀)) with famView s 𝓧 (𝓨 , p)
fam-from-to (s ▸ c) (𝓧 , θ) ((.(total s 𝓧 𝓟) , ρ) , .(proj s 𝓧 𝓟) , p₀) | mk-famview 𝓟 = idp

fam-correct : (s : Spec) (𝓧 : / Alg s /) → Fib s 𝓧 == Fam s 𝓧
fam-correct s 𝓧
  = ua (equiv
       (preimage s 𝓧)
       (λ 𝓟 → total s 𝓧 𝓟 , proj s 𝓧 𝓟)
       (fam-to-from s 𝓧)
       (fam-from-to s 𝓧))
