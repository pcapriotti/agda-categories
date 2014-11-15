{-# OPTIONS --without-K #-}
module category.sets where

open import equality
open import sum
open import graph.core
open import category.core
open import hott.level

sets : ∀ 𝑖 → Graph _ _
sets 𝑖 = record
  { obj = HSet 𝑖
  ; hom = λ { (A , _) (B , _) → A → B } }

instance
  sets-is-cat₀ : ∀ {𝑖} → IsCategory₀ (sets 𝑖)
  sets-is-cat₀ = record
    { id = λ X x → x
    ; _∘_ = λ f g x → f (g x) }

  sets-is-cat : ∀ {𝑖} → IsCategory (sets 𝑖)
  sets-is-cat = record
    { lunit = λ _ → refl
    ; runit = λ _ → refl
    ; assoc = λ _ _ _ → refl
    ; trunc = λ { _ (_ , hB) → Π-level (λ _ → hB) } }
