{-# OPTIONS --without-K #-}

module category.functor.properties where

open import function.core
open import equality.core
open import category.category
open import category.functor.core
open import category.functor.level
open import category.functor.ops

func-left-unit : ∀ {i₀ j₀ i₁ j₁}
                 {C : Category i₀ j₀} {D : Category i₁ j₁}
                 (F : Functor C D)
               → id ∘ F ≡ F
func-left-unit F = func-equality refl

func-right-unit : ∀ {i₀ j₀ i₁ j₁}
                 {C : Category i₀ j₀} {D : Category i₁ j₁}
                 (F : Functor C D)
               → F ∘ id ≡ F
func-right-unit F = func-equality refl

func-assoc : ∀ {i₀ j₀ i₁ j₁ i₂ j₂ i₃ j₃}
             {B : Category i₀ j₀} {C : Category i₁ j₁}
             {D : Category i₂ j₂} {E : Category i₃ j₃}
             (F : Functor D E) (G : Functor C D) (H : Functor B C)
           → (F ∘ G) ∘ H ≡ F ∘ (G ∘ H)
func-assoc F G H = func-equality refl
