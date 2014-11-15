{-# OPTIONS --without-K #-}
module category.properties where

open import equality
open import function
open import graph.core
open import category.core

-- pasting commutative squares

module _ {𝑖 𝑗} {𝓒 : Graph 𝑖 𝑗}
         ⦃ 𝓒-cat₀ : IsCategory₀ 𝓒 ⦄ where
  Square : {x₀₀ x₁₀ x₀₁ x₁₁ : obj 𝓒}
         → hom 𝓒 x₀₀ x₁₀ → hom 𝓒 x₀₁ x₁₁
         → hom 𝓒 x₀₀ x₀₁ → hom 𝓒 x₁₀ x₁₁
         → Set _
  Square a b f₀ f₁ = f₁ ∘ a ≡ b ∘ f₀

  module _ ⦃ 𝓒-cat : IsCategory 𝓒 ⦄ where
    id-square : {x₀ x₁ : obj 𝓒} (f : hom 𝓒 x₀ x₁) → Square id id f f
    id-square f = runit f · sym (lunit f)

    comp-squares : {x₀₀ x₁₀ x₂₀ x₀₁ x₁₁ x₂₁ : obj 𝓒}
                 → {a₀ : hom 𝓒 x₀₀ x₁₀} {a₁ : hom 𝓒 x₁₀ x₂₀}
                 → {b₀ : hom 𝓒 x₀₁ x₁₁} {b₁ : hom 𝓒 x₁₁ x₂₁}
                 → {f₀ : hom 𝓒 x₀₀ x₀₁} {f₁ : hom 𝓒 x₁₀ x₁₁}
                 → {f₂ : hom 𝓒 x₂₀ x₂₁}
                 → Square a₁ b₁ f₁ f₂ → Square a₀ b₀ f₀ f₁
                 → Square (a₁ ∘ a₀) (b₁ ∘ b₀) f₀ f₂
    comp-squares {a₀ = a₀}{a₁}{b₀}{b₁}{f₀}{f₁}{f₂} sq₁ sq₀
      = sym (assoc f₂ a₁ a₀)
      · ap (λ h → h ∘ a₀) sq₁
      · assoc b₁ f₁ a₀
      · ap (λ h → b₁ ∘ h) sq₀
      · sym (assoc b₁ b₀ f₀)
