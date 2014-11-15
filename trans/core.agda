{-# OPTIONS --without-K #-}
module trans.core where

open import level
open import equality
open import function
open import graph.core
open import graph.morphism
open import category.core
open import category.properties

module _ {𝑖₁ 𝑗₁ 𝑖₂ 𝑗₂}
         {𝓒₁ : Graph 𝑖₁ 𝑗₁} {𝓒₂ : Graph 𝑖₂ 𝑗₂}
         ⦃ 𝓒₁-cat₀ : IsCategory₀ 𝓒₁ ⦄
         ⦃ 𝓒₂-cat₀ : IsCategory₀ 𝓒₂ ⦄ where
  record Trans (F₁ F₂ : Morphism 𝓒₁ 𝓒₂) : Set (𝑖₁ ⊔ 𝑗₂) where
    field
      applyt : (x : obj 𝓒₁) → hom 𝓒₂ (apply F₁ x) (apply F₂ x)

  open Trans public

  private
    idN : {F : Morphism 𝓒₁ 𝓒₂} → Trans F F
    idN = record
      { applyt = λ x → id }

  instance
    id-trans : Identity _ _
    id-trans = record
      { U = Morphism 𝓒₁ 𝓒₂
      ; endo = λ F → Trans F F
      ; id = idN }

  private
    compN : {F₁ F₂ F₃ : Morphism 𝓒₁ 𝓒₂}
          → Trans F₂ F₃ → Trans F₁ F₂ → Trans F₁ F₃
    compN α β = record
      { applyt = λ x → applyt α x ∘ applyt β x }

  instance
    comp-trans : Composition _ _ _ _ _ _
    comp-trans = record
      { U₁ = Morphism 𝓒₁ 𝓒₂ ; U₂ = Morphism 𝓒₁ 𝓒₂ ; U₃ = Morphism 𝓒₁ 𝓒₂
      ; hom₁₂ = Trans ; hom₂₃ = Trans ; hom₁₃ = Trans
      ; _∘_ = compN }

  record IsNat {F₁ : Morphism 𝓒₁ 𝓒₂} {F₂ : Morphism 𝓒₁ 𝓒₂}
               (α : Trans F₁ F₂) : Set (𝑖₁ ⊔ 𝑗₁ ⊔ 𝑗₂) where
    field
      nat : {x y : obj 𝓒₁} (f : hom 𝓒₁ x y)
          → Square (applyt α x) (applyt α y)
                   (map F₁ f) (map F₂ f)

  module _ {F₁ : Morphism 𝓒₁ 𝓒₂} {F₂ : Morphism 𝓒₁ 𝓒₂}
           (α : Trans F₁ F₂) ⦃ α-nat : IsNat α ⦄ where
    open IsNat α-nat public

  instance
    id-nat : ⦃ 𝓒₂-cat : IsCategory 𝓒₂ ⦄ {F : Morphism 𝓒₁ 𝓒₂} → IsNat (id- F)
    id-nat {F} = record { nat = λ f → id-square (map F f) }

    comp-nat : ⦃ 𝓒₂-cat : IsCategory 𝓒₂ ⦄ {F₁ F₂ F₃ : Morphism 𝓒₁ 𝓒₂}
             → {α : Trans F₂ F₃}{β : Trans F₁ F₂}
             → ⦃ α-nat : IsNat α ⦄ ⦃ β-nat : IsNat β ⦄ → IsNat (α ∘ β)
    comp-nat {F₁}{F₂}{F₃}{α}{β} = record
      { nat = λ f → comp-squares (nat α f) (nat β f) }
