{-# OPTIONS --without-K #-}
module functor.core where

open import level
open import equality
open import function
open import graph.core
open import graph.morphism
open import category.core

module _ {𝑖₁ 𝑗₁ 𝑖₂ 𝑗₂} {𝓒₁ : Graph 𝑖₁ 𝑗₁} {𝓒₂ : Graph 𝑖₂ 𝑗₂}
         ⦃ 𝓒₁-cat₀ : IsCategory₀ 𝓒₁ ⦄ ⦃ 𝓒₂-cat₀ : IsCategory₀ 𝓒₂ ⦄ where
  record IsFunctor (F : Morphism 𝓒₁ 𝓒₂) : Set (𝑖₁ ⊔ 𝑗₁ ⊔ 𝑗₂) where
    field
      map-id : (x : obj 𝓒₁) → map F (id- x) ≡ id
      map-hom : {x y z : obj 𝓒₁} (f : hom 𝓒₁ y z) (g : hom 𝓒₁ x y)
              → map F (f ∘ g) ≡ map F f ∘ map F g

  module _ (F : Morphism 𝓒₁ 𝓒₂) ⦃ F-func : IsFunctor F ⦄ where
    open IsFunctor F-func public


module _ {𝑖 𝑗} where
  instance
    functor-id : {𝓒 : Graph 𝑖 𝑗} ⦃ 𝓒-cat : IsCategory₀ 𝓒 ⦄ → IsFunctor id
    functor-id = record
      { map-id = λ _ → refl
      ; map-hom = λ _ _ → refl }

module _ {𝑖₁ 𝑗₁ 𝑖₂ 𝑗₂ 𝑖₃ 𝑗₃} {𝓒₁ : Graph 𝑖₁ 𝑗₁} {𝓒₂ : Graph 𝑖₂ 𝑗₂} {𝓒₃ : Graph 𝑖₃ 𝑗₃}
         ⦃ 𝓒₁-cat : IsCategory₀ 𝓒₁ ⦄ ⦃ 𝓒₂-cat : IsCategory₀ 𝓒₂ ⦄ ⦃ 𝓒₃-cat : IsCategory₀ 𝓒₃ ⦄ where

  instance
    functor-comp : {F : Morphism 𝓒₂ 𝓒₃} {G : Morphism 𝓒₁ 𝓒₂}
                 → ⦃ F-func : IsFunctor F ⦄ ⦃ G-func : IsFunctor G ⦄
                 → IsFunctor (F ∘ G)
    functor-comp {F}{G} = record
      { map-id = λ x → ap (map F) (map-id G x) · map-id F (apply G x)
      ; map-hom = λ f g → ap (map F) (map-hom G f g) · map-hom F (map G f) (map G g) }
