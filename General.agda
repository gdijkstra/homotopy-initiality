{-# OPTIONS --without-K #-}

open import lib.Basics
open import Cat

module General (𝓒 : Cat) where

_∘'_ = Cat.comp 𝓒
Id = Cat.id 𝓒

is-initial : / 𝓒 / → Type1
is-initial X = (Y : / 𝓒 /) → is-contr (𝓒 [ X , Y ])

section-of :
  {X Y : / 𝓒 /}
  (p : 𝓒 [ Y , X ])
  (s : 𝓒 [ X , Y ])
  → Type0
section-of {X = X} p s = (p ∘' s) == Id X

-- We don't need the universal property for products or equalisers.
record has-products : Type1 where
  field
    prod : / 𝓒 / → / 𝓒 / → / 𝓒 /
    π₁ : {X Y : / 𝓒 /} → 𝓒 [ prod X Y , X ]
    π₂ : {X Y : / 𝓒 /} → 𝓒 [ prod X Y , Y ]

record equaliser {X Y : / 𝓒 /} (f g : 𝓒 [ X , Y ]) : Type1 where
  field
    E : / 𝓒 /
    i : 𝓒 [ E , X ]
    comm : (f ∘' i) == (g ∘' i)

has-equalisers : Type1
has-equalisers = {X Y : / 𝓒 /} (f g : 𝓒 [ X , Y ]) → equaliser f g

has-assoc : Type1
has-assoc =
  {X Y Z W : / 𝓒 /}
  (h : 𝓒 [ Z , W ])
  (g : 𝓒 [ Y , Z ])
  (f : 𝓒 [ X , Y ])
  → ((h ∘' g) ∘' f) == (h ∘' (g ∘' f))

has-right-id : Type1
has-right-id = {X Y : / 𝓒 /} (f : 𝓒 [ X , Y ]) → (f ∘' (Id X)) == f

module Initiality⇒SectionInduction
  (X : / 𝓒 /)
  (initial : is-initial X)
    where

  endo=id :
    (f : 𝓒 [ X , X ])
    → f == Id X
  endo=id f =
    f
     =⟨ ! (snd (initial X) f) ⟩
    fst (initial X)
     =⟨ snd (initial X) (Id X) ⟩
    Id X ∎

  section-induction :
    {Y : / 𝓒 /}
    (p : 𝓒 [ Y , X ])
    → Σ (𝓒 [ X , Y ]) (section-of p)
  section-induction {Y = Y} p = s , s-is-section
    where
      s : 𝓒 [ X , Y ]
      s = fst (initial Y)
      s-is-section : section-of p s
      s-is-section = endo=id (p ∘' s)

module SectionInduction⇒Initiality
  (X : / 𝓒 /)
  (section-induction : {Y : / 𝓒 /} (p : 𝓒 [ Y , X ]) → Σ (𝓒 [ X , Y ]) (section-of p))
  (products : has-products)
  (equalisers : has-equalisers)
  (assoc : has-assoc)
  (right-id : has-right-id)
  where

  module _ (Y : / 𝓒 /) where
    f : 𝓒 [ X , Y ]
    f = π₂ ∘' (fst (section-induction π₁))
     where X×Y : / 𝓒 /
           X×Y = has-products.prod products X Y
           π₁ : 𝓒 [ X×Y , X ]
           π₁ = has-products.π₁ products
           π₂ : 𝓒 [ X×Y , Y ]
           π₂ = has-products.π₂ products
  
    f-unique : (g : 𝓒 [ X , Y ]) → f == g
    f-unique g =
      f
       =⟨ ! (right-id f) ⟩
      f ∘' (Id X)
       =⟨ ap (λ h → f ∘' h) (! s') ⟩
      f ∘' (i ∘' s)
       =⟨ ! (assoc f i s) ⟩
      (f ∘' i) ∘' s
       =⟨ ap (λ h → h ∘' s) comm ⟩
      (g ∘' i) ∘' s
       =⟨ assoc g i s ⟩ -- assoc
      g ∘' (i ∘' s)
       =⟨ ap (λ h → g ∘' h) s' ⟩
      g ∘' (Id X)
       =⟨ right-id g ⟩ -- right unit
      g ∎
      where E : / 𝓒 /
            E = equaliser.E (equalisers f g)
            i : 𝓒 [ E , X ]
            i = equaliser.i (equalisers f g)
            comm : (f ∘' i) == (g ∘' i)
            comm = equaliser.comm (equalisers f g)
            s : 𝓒 [ X , E ]
            s = fst (section-induction i)
            s' : (i ∘' s) == Id X
            s' = snd (section-induction i)

  initial : is-initial X
  initial = λ Y → f Y , f-unique Y
