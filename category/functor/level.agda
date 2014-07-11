{-# OPTIONS --without-K #-}

open import category.category

module category.functor.level {i j i' j'}
  {C : Category i j}{D : Category i' j'} where

open import level
open import sum
open import equality.core
open import function.core
open import function.overloading
open import function.isomorphism.core
open import category.graph
open import category.functor.core
open import category.functor.ops
open import category.trans.core
open import category.trans.ops
open import hott.level
open import overloading

open as-category C
open as-category D

private
  GMorphism : Set _
  GMorphism = Morphism (graph C) (graph D)

  Functorial : GMorphism → Set _
  Functorial = IsFunctor C D

functorial-structure-iso : (m : GMorphism)
                         → (MapId C D m × MapHom C D m)
                         ≅ Functorial m
functorial-structure-iso m = record
  { to = λ {(i , h) → record
               { map-id = i ; map-hom = h } }
  ; from = λ f → let module F = IsFunctor f
               in (F.map-id , F.map-hom)
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl }

is-func-prop : (m : GMorphism) → h 1 (Functorial m)
is-func-prop m = iso-level (functorial-structure-iso m)
  ( ×-level
    ( Π-level λ X → trunc _ _ _ _ )
    ( Π-level-impl λ X
      → Π-level-impl λ Y
      → Π-level-impl λ Z
      → Π-level λ f
      → Π-level λ g
      → trunc _ _ _ _ ) )

functor-structure-iso : Σ GMorphism Functorial ≅ Functor C D
functor-structure-iso = bundle-structure-iso Functorial

func-equality-iso : {F G : Functor C D}
                  → (graph-morphism F ≡ graph-morphism G)
                  ≅ (F ≡ G)
func-equality-iso = bundle-equality-iso Functorial is-func-prop

func-equality : {F G : Functor C D}
              → graph-morphism F ≡ graph-morphism G
              → F ≡ G
func-equality {F}{G} = apply func-equality-iso

func-coerce : {F G : Functor C D} → F ≡ G → F ⇒ G
func-coerce {F}{.F} refl = id
  where
    open as-category₀ (Func₀ C D)
