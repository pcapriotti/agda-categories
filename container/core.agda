{-# OPTIONS --without-K #-}

module container.core where

open import level
open import sum
open import function.core

module Container {li la lb}
                 (I : Set li)
                 (A : I → Set la)
                 (B : {i : I} → A i → Set lb)
                 (r : {i : I}{a : A i} → B a → I) where

  -- functor associated to this indexed container
  F : (I → Set (la ⊔ lb)) → I → Set _
  F X i = Σ (A i) λ a → (b : B a) → X (r b)

  -- homsets in the slice category
  _↝_ : (X Y : I → Set (la ⊔ lb)) → Set _
  X ↝ Y = {i : I} → X i → Y i

  -- morphism map for the functor F
  imap : (X : I → Set _)
       → {Y : I → Set _}
       → (X ↝ Y)
       → (F X ↝ F Y)
  imap _ g {i} (a , f) = a , g ∘ f
