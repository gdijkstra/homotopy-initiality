{-# OPTIONS --without-K #-}

module dep.Fam where

open import lib.Basics
open import Cat
open import dep.Core

-- Families over a given algebra
Fam : (s : Spec) → / Alg s / → Type1
has-fam : (s : Spec) (c : Constr (Alg s)) (𝓧 : / Alg s /) (θ : has-alg c 𝓧) → Fam s 𝓧 → Type0

□-F :
  (s : Spec)
  (F : Alg s ⇒ TypeCat)
  (𝓧 : / Alg s /)
  (P : Fam s 𝓧)
  → F ⋆ 𝓧 → Type0

□-G :
  (s : Spec)
  (F : Alg s ⇒ TypeCat)
  (G : ∫ (Alg s) F ⇒ TypeCat)
  (𝓧 : / Alg s /)
  (P : Fam s 𝓧)
  (x : F ⋆ 𝓧)
  (y : □-F s F 𝓧 P x)
  → G ⋆ (𝓧 , x) → Type0

total :
  (s : Spec)
  (𝓧 : / Alg s /)
  → Fam s 𝓧 → / Alg s /

proj :
  (s : Spec)
  (𝓧 : / Alg s /)
  (P : Fam s 𝓧)
  → Alg s [ total s 𝓧 P , 𝓧 ]

φ-F :
  (s : Spec)
  (F : Alg s ⇒ TypeCat)
  (𝓧 : / Alg s /)
  (P : Fam s 𝓧)
  → Σ (F ⋆ 𝓧) (□-F s F 𝓧 P) → F ⋆ (total s 𝓧 P)

φ⁻¹-F :
  (s : Spec)
  (F : Alg s ⇒ TypeCat)
  (𝓧 : / Alg s /)
  (P : Fam s 𝓧)
  → F ⋆ (total s 𝓧 P) → Σ (F ⋆ 𝓧) (□-F s F 𝓧 P)

φ-G :
  (s : Spec)
  (F : Alg s ⇒ TypeCat)
  (G : ∫ (Alg s) F ⇒ TypeCat)
  (𝓧 : / Alg s /)
  (P : Fam s 𝓧)
  (x : F ⋆ 𝓧)
  (y : □-F s F 𝓧 P x)
  → Σ (G ⋆ (𝓧 , x)) (□-G s F G 𝓧 P x y) → G ⋆ (total s 𝓧 P , φ-F s F 𝓧 P (x , y))

φ⁻¹-G :
  (s : Spec)
  (F : Alg s ⇒ TypeCat)
  (G : ∫ (Alg s) F ⇒ TypeCat)
  (𝓧 : / Alg s /)
  (P : Fam s 𝓧)
  (x : F ⋆ 𝓧)
  (y : □-F s F 𝓧 P x)
  → G ⋆ (total s 𝓧 P , φ-F s F 𝓧 P (x , y)) → Σ (G ⋆ (𝓧 , x)) (□-G s F G 𝓧 P x y)

has-fam s (mk-constr F G) 𝓧 θ P = (x : Σ (F ⋆ 𝓧) (□-F s F 𝓧 P)) → □-G s F G 𝓧 P (fst x) (snd x) (θ (fst x))

Fam ε X
  = X → Type0
Fam (s ▸ c) (𝓧 , θ)
  = Σ (Fam s 𝓧) (has-fam s c 𝓧 θ)

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

-- Correctness of φ.
module _
  (s : Spec)
  (F : Alg s ⇒ TypeCat)
  (𝓧 : / Alg s /)
  (P : Fam s 𝓧)
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
