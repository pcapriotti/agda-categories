{-# OPTIONS --without-K #-}
module graph.core where

open import level
open import sum

record Graph 𝑖 𝑗 : Set (lsuc (𝑖 ⊔ 𝑗)) where
  field
    obj : Set 𝑖
    hom : obj → obj → Set 𝑗

open Graph public

total : ∀ {𝑖 𝑗} → Graph 𝑖 𝑗 → Set _
total G = Σ (obj G × obj G) λ { (x , y) → hom G x y }
