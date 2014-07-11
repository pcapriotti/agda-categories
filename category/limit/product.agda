{-# OPTIONS --without-K #-}

module category.limit.product where

open import sum
open import category.graph
open import category.category
open import category.functor
open import category.instances.discrete
open import category.limit.core
open import sets.fin
open import sets.unit
open import sets.vec
open import hott.level

product-graph : Category _ _
product-graph = discrete-cat (Fin 2 , h! (fin-set 2))

private
  module Definition {i j}{C : Category i j} where
    product-diagram : obj C → obj C → Functor product-graph C
    product-diagram X Y = discrete-lift (lookup (X ∷ Y ∷ []))

    Product : obj C → obj C → Set _
    Product A B = Lim (product-diagram A B)

open Definition public
