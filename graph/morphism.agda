{-# OPTIONS --without-K #-}
module graph.morphism where

open import level
open import overloading
open import graph.core

record Morphism {𝑖₁ 𝑗₁ 𝑖₂ 𝑗₂} (G₁ : Graph 𝑖₁ 𝑗₁) (G₂ : Graph 𝑖₂ 𝑗₂) : Set (𝑖₁ ⊔ 𝑖₂ ⊔ 𝑗₁ ⊔ 𝑗₂) where
  field
    apply : obj G₁ → obj G₂
    map : {x y : obj G₁} → hom G₁ x y → hom G₂ (apply x) (apply y)

open Morphism public using (map)

instance
  mor-is-fun : ∀ {𝑖₁ 𝑗₁ 𝑖₂ 𝑗₂} {G₁ : Graph 𝑖₁ 𝑗₁} {G₂ : Graph 𝑖₂ 𝑗₂}
             → Coercion (Morphism G₁ G₂) (obj G₁ → obj G₂)
  mor-is-fun = record { coerce = Morphism.apply }

open import function

module _ {𝑖 𝑗} where
  private
    idG : {G : Graph 𝑖 𝑗} → Morphism G G
    idG = record
      { apply = λ x → x
      ; map = λ f → f }

  instance
    gmor-id : Identity _ _
    gmor-id = record
      { U = Graph 𝑖 𝑗
      ; endo = λ G → Morphism G G
      ; id = idG }

module _ {𝑖₁ 𝑗₁ 𝑖₂ 𝑗₂ 𝑖₃ 𝑗₃} where
  private
    Comp : {G₁ : Graph 𝑖₁ 𝑗₁} {G₂ : Graph 𝑖₂ 𝑗₂} {G₃ : Graph 𝑖₃ 𝑗₃}
         → Morphism G₂ G₃ → Morphism G₁ G₂ → Morphism G₁ G₃
    Comp F G = record
      { apply = λ x → apply F (apply G x)
      ; map = λ f → map F (map G f) }

  instance
    gmor-comp : Composition _ _ _ _ _ _
    gmor-comp = record
      { U₁ = Graph 𝑖₁ 𝑗₁ ; U₂ = Graph 𝑖₂ 𝑗₂ ; U₃ = Graph 𝑖₃ 𝑗₃
      ; hom₁₂ = Morphism ; hom₂₃ = Morphism ; hom₁₃ = Morphism
      ; _∘_ = Comp }
