{-# OPTIONS --without-K #-}

open import sum
open import equality.core
open import function.core
open import category.category
open import category.functor.core
open import category.trans.core
open import category.trans.ops
open import category.trans.level
open import function.extensionality

module category.trans.properties {i}{j}{i'}{j'}
  (C : Category i j)(D : Category i' j') where

open as-category D
open as-category₀ (Func₀ C D)

private
  nat-right-unit : {F G : Functor C D}
                → (α : Nat F G)
                → α ∘ id ≡ α
  nat-right-unit {F}{G} (nt α α-nat) =
    nat-equality trans-right-unit
    where
      trans-right-unit : (λ X → α X ∘ id) ≡ α
      trans-right-unit = funext λ X → right-id (α X)

  nat-left-unit : {F G : Functor C D}
                → (α : Nat F G)
                → id ∘ α ≡ α
  nat-left-unit {F}{G} (nt α α-nat) =
    nat-equality trans-left-unit
    where
      trans-left-unit : (λ X → id ∘ α X) ≡ α
      trans-left-unit = funext λ X → left-id (α X)

  nat-assoc : {F G H K : Functor C D}
            → (α : Nat F G)
            → (β : Nat G H)
            → (γ : Nat H K)
            → (γ ∘ β) ∘ α ≡ γ ∘ (β ∘ α)
  nat-assoc {F}{G}{H}{K} (nt α α-nat) (nt β β-nat) (nt γ γ-nat) =
    nat-equality (funext trans-assoc)
    where
      trans-assoc : ∀ X → γ X ∘ β X ∘ α X ≡ γ X ∘ (β X ∘ α X)
      trans-assoc X = assoc _ _ _

Func : Category _ _
Func = mk-category record
  { obj = Functor C D
  ; hom = Nat
  ; id = λ _ → id
  ; _∘_ = _∘_
  ; trunc = nat-hset
  ; left-id = nat-left-unit
  ; right-id = nat-right-unit
  ; assoc = λ α β γ → nat-assoc γ β α }
