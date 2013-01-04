{-# OPTIONS --without-K #-}
module sets.vec.dependent where

open import sets.nat
open import sets.fin

-- syntactic sugar to create finite dependent functions

module FiniteDep where
  [] : ∀ {i}{P : Fin 0 → Set i} → (i : Fin 0) → P i
  [] ()

  _∷_ : ∀ {i n}{P : Fin (suc n) → Set i}
      → (x : P zero)(xs : (i : Fin n) → P (suc i))
      → (i : Fin (suc n)) → P i
  _∷_ {P = P} x xs zero = x
  _∷_ {P = P} x xs (suc i) = xs i

  infixr 5 _∷_
