{-# OPTIONS --without-K #-}
module category.univalence where

open import sum
open import equality.core
open import function.isomorphism
open import category.category
open import category.graph
open import category.isomorphism
open import hott.weak-equivalence
open import hott.level

univalent : ∀ {i j} → Category i j → Set _
univalent C = (x y : obj C) → weak-equiv (≡⇒iso C {x}{y})

univalent-h1 : ∀ {i j}(C : Category i j) → h 1 (univalent C)
univalent-h1 C = Π-level λ x → Π-level λ y → weak-equiv-h1 _

private
  module properties {i j}{C : Category i j}(univ : univalent C) where
    iso≅eq : (x y : obj C) → (x ≡ y) ≅ cat-iso C x y
    iso≅eq x y = ≈⇒≅ (≡⇒iso C , univ x y)

    -- the object set of a univalent category has h-level 3
    obj-h3 : h 3 (obj C)
    obj-h3 x y = iso-level (sym≅ (iso≅eq x y)) (cat-iso-hset x y)
open properties public
