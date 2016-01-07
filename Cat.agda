{-# OPTIONS --without-K #-}

module Cat where

open import lib.Basics

record Cat : Type (lsucc (lsucc lzero)) where
  field
    obj : Type1
    hom : obj → obj → Type0
    comp : {X Y Z : obj} → hom Y Z → hom X Y → hom X Z
    id : (X : obj) → hom X X

TypeCat : Cat
TypeCat = record
  { obj  = Type0  
  ; hom  = (λ A B → A → B)
  ; comp = (λ g f x → g (f x))
  ; id   = (λ X x → x)
  }

/_/ : Cat → Type1
/ 𝓒 / = Cat.obj 𝓒

_[_,_] : (𝓒 : Cat) → Cat.obj 𝓒 → Cat.obj 𝓒 → Type0
𝓒 [ A , B ] = Cat.hom 𝓒 A B

record Func (𝓒 𝓓 : Cat) : Type1 where
  field
    obj : / 𝓒 / → / 𝓓 /
    hom : {A B : / 𝓒 /} → 𝓒 [ A , B ] → 𝓓 [ obj A , obj B ]
    hom-∘ : {A B C : / 𝓒 /} (g : 𝓒 [ B , C ]) (f : 𝓒 [ A , B ]) → hom (Cat.comp 𝓒 g f) == Cat.comp 𝓓 (hom g) (hom f)
    hom-id : (A : / 𝓒 /) → hom (Cat.id 𝓒 A) == Cat.id 𝓓 (obj A)

_⋆_ : {𝓒 𝓓 : Cat} (F : Func 𝓒 𝓓) → / 𝓒 / → / 𝓓 /
F ⋆ X = Func.obj F X

_⋆⋆_ : {𝓒 𝓓 : Cat} (F : Func 𝓒 𝓓) {A B : / 𝓒 /} → 𝓒 [ A , B ] → 𝓓 [ F ⋆ A , F ⋆ B ]
F ⋆⋆ f = Func.hom F f

_⇒_ : Cat → Cat → Type1
𝓒 ⇒ 𝓓 = Func 𝓒 𝓓

-- Category of elements.
-- This is problematic.
∫ : (𝓒 : Cat) → (F : 𝓒 ⇒ TypeCat) → Cat
∫ 𝓒 F = record
  { obj  = (Σ / 𝓒 / (λ X → F ⋆ X))
  ; hom  = (λ { (X , x) (Y , y) → Σ (𝓒 [ X , Y ]) (λ f → (F ⋆⋆ f) x == y) })
  ; comp = ( λ { {(X , x)} {(Y , y)} {(Z , z)} (g , g₀) (f , f₀) → (Cat.comp 𝓒 g f)
           , ap (λ h → h x) (Func.hom-∘ F g f) ∙' ap (λ w → (F ⋆⋆ g) w) f₀ ∙' g₀ })
  ; id   = (λ { (X , x) → Cat.id 𝓒 X , ap (λ f → f x) (Func.hom-id F X)})
  }

-- Any morphism in 𝓒 can be lifted to ∫ 𝓒 F, given an elt x : F A:
∫-lift :
   {𝓒 : Cat} (F : 𝓒 ⇒ TypeCat) {A B : / 𝓒 /}
   (x : F ⋆ A)
   (f : 𝓒 [ A , B ])
 → (∫ 𝓒 F) [ (A , x) , (B , (F ⋆⋆ f) x) ]
∫-lift F x f = f , idp

-- We only need naturality of functors into Type.
record NatTrans {𝓒 : Cat} (F G : 𝓒 ⇒ TypeCat) : Type1 where
  constructor mk-nat-trans
  field
    α : (X : / 𝓒 /) → F ⋆ X → G ⋆ X
    naturality :
      {X Y : / 𝓒 /}
      (f : 𝓒 [ X , Y ])
      (x : F ⋆ X)
      → α Y ((F ⋆⋆ f) x) == (G ⋆⋆ f) (α X x)

_‼_ : {𝓒 : Cat} {F G : 𝓒 ⇒ TypeCat} → NatTrans F G → {X : / 𝓒 /} → F ⋆ X → G ⋆ X
(mk-nat-trans α _) ‼ x = α _ x
