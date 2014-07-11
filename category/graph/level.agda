{-# OPTIONS --without-K #-}

module category.graph.level where

open import sum
open import equality.core
open import category.graph.core
open import category.graph.morphism
open import function.isomorphism
open import sets.nat
open import hott.level

private
  module Properties {i j i' j'}
                    {A : Graph i j}
                    {B : Graph i' j'} where

    morphism-structure-iso : Morphism A B
                           ≅ Σ (obj A → obj B)
                               (IsMorphism {A = A} {B = B})
    morphism-structure-iso = record
      { to = λ {(morphism f m) → f , m }
      ; from = λ {(f , m) → morphism f m }
      ; iso₁ = λ _ → refl
      ; iso₂ = λ _ → refl }

    morph-level : {n : ℕ}
                 → h n (obj B)
                 → (∀ x y → h n (hom B x y))
                 → h n (Morphism A B)
    morph-level hB hB' = iso-level (sym≅ morphism-structure-iso)
      (Σ-level (Π-level (λ _ → hB))
                (λ f → Π-level-impl λ x
                     → Π-level-impl λ y
                     → Π-level λ _
                     → hB' (f x) (f y)))
      where
        isom : Morphism A B ≅ Σ (obj A → obj B) (IsMorphism {A = A} {B = B})
        isom = record
          { to = λ {(morphism f m) → f , m }
          ; from = λ {(f , m) → morphism f m }
          ; iso₁ = λ _ → refl
          ; iso₂ = λ _ → refl }
open Properties public
