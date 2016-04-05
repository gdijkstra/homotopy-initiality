{-# OPTIONS --without-K #-}

open import Admit

module dep.Sect where

open import lib.Basics
open import Cat
open import dep.Core
open import dep.Fam

is-section :
  (s : Spec)
  (𝓧 : / Alg s /)
  (P : Fam s 𝓧)
  (𝓼 : Alg s [ 𝓧 , total s 𝓧 P ])
  → Type0
is-section s 𝓧 P 𝓼
  = (Cat.comp (Alg s) (proj s 𝓧 P) 𝓼 == Cat.id (Alg s) 𝓧)

to-is-section :
  (s : Spec)
  (F : Alg s ⇒ TypeCat)
  (G : ∫ (Alg s) F ⇒ TypeCat)
  (𝓧 : / Alg s /)
  (θ : (x : F ⋆ 𝓧) → G ⋆ (𝓧 , x))
  (P : Fam s 𝓧)
  (m : (x : Σ (F ⋆ 𝓧) (□-F s F 𝓧 P)) → □-G s F G 𝓧 P (fst x) (snd x) (θ (fst x)))
  (𝓼 : Alg s [ 𝓧 , total s 𝓧 P ])
  (𝓼' : (x : F ⋆ 𝓧) → (G ⋆⋆ 𝓼 , idp) (θ x) == fst (m (((F ⋆⋆ proj s 𝓧 P) ((F ⋆⋆ 𝓼) x)) , ((F ⋆⋆ 𝓼) x) , idp)))
  (a : is-section s 𝓧 P 𝓼)
  → is-section (s ▸ mk-constr F G) (𝓧 , θ) (P , m) (𝓼 , 𝓼')
to-is-section s F G 𝓧 θ P m 𝓼 𝓼' a
  = pair= a (admit _)

-- We want to define Π for algebra fibrations
Sect :
  (s : Spec)
  (𝓧 : / Alg s /)
  (P : Fam s 𝓧)
  → Type0

F-bar :
  (s : Spec)
  (F : Alg s ⇒ TypeCat)
  (𝓧 : / Alg s /)
  (P : Fam s 𝓧)
  → Sect s 𝓧 P
  → (x : F ⋆ 𝓧) → □-F s F 𝓧 P x

G-bar :
  (s : Spec)
  (F : Alg s ⇒ TypeCat)
  (G : ∫ (Alg s) F ⇒ TypeCat)
  (𝓧 : / Alg s /)
  (P : Fam s 𝓧)
  (x : F ⋆ 𝓧)
  → (𝓼 : Sect s 𝓧 P)
  → (p : G ⋆ (𝓧 , x)) → □-G s F G 𝓧 P x (F-bar s F 𝓧 P 𝓼 x) p

ψ :
  (s : Spec)
  (𝓧 : / Alg s /)
  (P : Fam s 𝓧)
  → Sect s 𝓧 P → Σ (Alg s [ 𝓧 , total s 𝓧 P ]) (is-section s 𝓧 P)

Sect ε X P
  = (x : X) → P x
Sect (s ▸ mk-constr F G) (𝓧 , θ) (P , m)
  = Σ (Sect s 𝓧 P) (λ 𝓼 → (x : F ⋆ 𝓧) → G-bar s F G 𝓧 P x 𝓼 (θ x) == m (x , (F-bar s F 𝓧 P 𝓼 x)))

F-bar s F 𝓧 P 𝓼 x
  = ((F ⋆⋆ fst (ψ s 𝓧 P 𝓼)) x)
  , ((F ⋆⋆ proj s 𝓧 P) ((F ⋆⋆ fst (ψ s 𝓧 P 𝓼)) x)
      =⟨ app= (! (Func.hom-∘ F (proj s 𝓧 P) (fst (ψ s 𝓧 P 𝓼)))) x ⟩
     (F ⋆⋆ (Cat.comp (Alg s) (proj s 𝓧 P) (fst (ψ s 𝓧 P 𝓼)))) x
      =⟨ ap (λ r → (F ⋆⋆ r) x) (snd (ψ s 𝓧 P 𝓼)) ⟩
     (F ⋆⋆ (Cat.id (Alg s) 𝓧)) x
      =⟨ app= (Func.hom-id F 𝓧) x ⟩
     x ∎)

ψ ε X P 𝓼
  = (λ x → x , (𝓼 x)) , idp
ψ (s ▸ mk-constr F G) (𝓧 , θ) (P , m) (𝓼 , 𝓼')
  = (f , admit _) , admit _
  where
    f : Alg s [ 𝓧 , total s 𝓧 P ]
    f = fst (ψ s 𝓧 P 𝓼)
    f' : is-section s 𝓧 P f
    f' = snd (ψ s 𝓧 P 𝓼)

G-bar s F G 𝓧 P x 𝓼 p
  = (G ⋆⋆ (fst (ψ s 𝓧 P 𝓼)) , idp) p
  , admit _

