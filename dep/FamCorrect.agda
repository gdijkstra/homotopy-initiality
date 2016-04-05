{-# OPTIONS --without-K #-}

open import Admit

module dep.FamCorrect where

open import lib.Basics
open import Cat
open import dep.Core
open import dep.Fam
open import dep.Fib

-- TODO: Situation on Type
module _ (X : Type0) (P : X → Type0) where
  singleton-elim-2 : (x : X) → Σ (Σ X P) (λ y → fst y == x) ≃ P x
  singleton-elim-2 x =
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

data FamView (s : Spec) (𝓧 : / Alg s /) : Fib s 𝓧 → Type1 where
  mk-famview : (𝓟 : Fam s 𝓧) → FamView s 𝓧 ((total s 𝓧 𝓟) , (proj s 𝓧 𝓟))

famViewHelper :
  (s : Spec) (c : Constr (Alg s))
  (𝓧 : / Alg s /) (θ : has-alg c 𝓧)
  (𝓨 : / Alg s /) (ρ : has-alg c 𝓨)
  (p : Alg s [ 𝓨 , 𝓧 ]) (p₀ : is-alg-hom c ρ θ p)
  (w : FamView s 𝓧 (𝓨 , p))
  → FamView (s ▸ c) (𝓧 , θ) ((𝓨 , ρ) , p , p₀)
famViewHelper s c 𝓧 θ .(total s 𝓧 𝓟) ρ .(proj s 𝓧 𝓟) p₀ (mk-famview 𝓟)
  = mk-famview ((𝓟 , (λ { (.(Func.hom (Constr.F c) (proj s 𝓧 𝓟) x) , x , idp) → (ρ x) , (p₀ x) })))

famView : (s : Spec) (𝓧 : / Alg s /) (p : Fib s 𝓧) → FamView s 𝓧 p
famView ε X (Y , p) = admit _
famView (s ▸ c) (𝓧 , θ) ((𝓨 , ρ) , (p , p₀)) = famViewHelper s c 𝓧 θ 𝓨 ρ p p₀ (famView s 𝓧 (𝓨 , p))
-- famView (s ▸ c) (𝓧 , θ) ((.(total s 𝓧 𝓟) , ρ) , .(proj s 𝓧 𝓟) , p₀) | mk-famview 𝓟 = mk-famview (𝓟 , (λ { (.(Func.hom (Constr.F c) (proj s 𝓧 𝓟) x) , x , idp) → (ρ x) , (p₀ x) }))

preimageHelper :
  (s : Spec) (c : Constr (Alg s))
  (𝓧 : / Alg s /) (θ : has-alg c 𝓧)
  (𝓨 : / Alg s /) (ρ : has-alg c 𝓨)
  (p : Alg s [ 𝓨 , 𝓧 ]) (p₀ : is-alg-hom c ρ θ p)
  (w : FamView s 𝓧 (𝓨 , p))
  → Fam (s ▸ c) (𝓧 , θ)
preimageHelper s c 𝓧 θ .(total s 𝓧 𝓟) ρ .(proj s 𝓧 𝓟) p₀ (mk-famview 𝓟)
  = (𝓟 , (λ { (.(Func.hom (Constr.F c) (proj s 𝓧 𝓟) x) , x , idp) → (ρ x) , (p₀ x) }))

preimage : (s : Spec) (𝓧 : / Alg s /) (𝓟 : Fib s 𝓧) → Fam s 𝓧
preimage ε X (Y , p) = hfiber p
preimage (s ▸ c) (𝓧 , θ) ((𝓨 , ρ) , p , p₀) = preimageHelper s c 𝓧 θ 𝓨 ρ p p₀ (famView s 𝓧 (𝓨 , p))

preimage-β :
  (s : Spec)
   (c : Constr (Alg s))
  (𝓧 : / Alg s /)
  (θ : has-alg c 𝓧)
  (𝓟 : Fam s 𝓧)
  (m : has-fam s c 𝓧 θ 𝓟)
  (A : / Alg s /)
  (a : A == total s 𝓧 𝓟)
  (B : Alg s [ A , 𝓧 ])
  (b : B == proj s 𝓧 𝓟 [ (λ H → Alg s [ H , 𝓧 ]) ↓ a ])
  (p : FamView s 𝓧 (A , B))
  → preimage (s ▸ c) (𝓧 , θ) (((total s 𝓧 𝓟) , (λ x → fst (m (Func.hom (Constr.F c) (proj s 𝓧 𝓟) x , x , idp)))) , (proj s 𝓧 𝓟) , (λ x → snd (m (Func.hom (Constr.F c) (proj s 𝓧 𝓟) x , x , idp))))
  == (𝓟 , m)
preimage-β = admit _ --preimage-β s c 𝓧 θ 𝓟 m .(total s 𝓧 𝓟) idp .(proj s 𝓧 𝓟) idp (mk-famview .𝓟) = {!a!}

-- fam-to-from : (s : Spec) (𝓧 : / Alg s /)
--   → (𝓟 : Fam s 𝓧) → preimage s 𝓧 (total s 𝓧 𝓟 , proj s 𝓧 𝓟) == 𝓟
-- fam-to-from ε X P = λ= (λ x → ua (singleton-elim-2 X P x))
-- fam-to-from (s ▸ c) (𝓧 , θ) (𝓟 , m) = {!!}

-- fam-from-to : (s : Spec) (𝓧 : / Alg s /)
--   → (𝓟 : Fib s 𝓧) → (total s 𝓧 (preimage s 𝓧 𝓟) , proj s 𝓧 (preimage s 𝓧 𝓟)) == 𝓟
-- fam-from-to ε X (Y , p) = {!admit _!}
-- fam-from-to (s ▸ c) (𝓧 , θ) ((𝓨 , ρ) , (p , p₀)) with famView s 𝓧 (𝓨 , p)
-- fam-from-to (s ▸ c) (𝓧 , θ) ((.(total s 𝓧 𝓟) , ρ) , .(proj s 𝓧 𝓟) , p₀) | mk-famview 𝓟 = idp

-- fam-correct : (s : Spec) (𝓧 : / Alg s /) → Fib s 𝓧 == Fam s 𝓧
-- fam-correct s 𝓧
--   = ua (equiv
--        (preimage s 𝓧)
--        (λ 𝓟 → total s 𝓧 𝓟 , proj s 𝓧 𝓟)
--        (fam-to-from s 𝓧)
--        (fam-from-to s 𝓧))
