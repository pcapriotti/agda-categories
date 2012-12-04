{-# OPTIONS --without-K #-}
module function.extensionality where

open import sum
open import level using (lsuc)
open import equality.core
open import equality.reasoning
open import function using (_∘_ ; id)
open import function.isomorphism

open import hott.coherence
open import hott.weak-equivalence
open import hott.univalence

-- a proof that univalence implies extensionality

Extensionality : ∀ i → Set (lsuc i)
Extensionality i = {X Y : Set i}
                 → (f g : X → Y)
                 → ((x : X) → f x ≡ g x)
                 → f ≡ g

-- we begin with some preliminaries on path spaces
-- let's fix a set X
module Paths {i} (X : Set i) where
  -- Δ is the path space of X, i.e.
  -- the type of triples (x, x', p)
  -- where p : x ≡ x'
  Δ : Set _
  Δ = Σ X λ x₁
    → Σ X λ x₂
    → x₁ ≡ x₂

  -- there are obvious projections π₁ π₂ : Δ → X
  π₁ : Δ → X
  π₁ = proj₁
  
  π₂ : Δ → X
  π₂ = proj₁ ∘ proj₂
  
  -- X can be embedded into Δ via the "diagonal" function δ
  δ : X → Δ
  δ x = (x , (x , refl))

  -- δ and π₁ form an isomorphism between X and Δ
  Δ-iso : X ≅ Δ
  Δ-iso = iso δ π₁ H K
    where
      H : (x : X) → π₁ (δ x) ≡ x
      H x = refl
  
      K : (x' : Δ) → δ (π₁ x') ≡ x'
      K (x , (.x , refl)) = refl

  -- hence we obtain a weak equivalence
  Δ-equiv : X ≈ Δ
  Δ-equiv = ≅⇒≈ Δ-iso

-- now we use univalence to show that a weak equivalence between X and
-- Y lifts to a weak equivalence between the exponentials (A → X) and
-- (A → Y) for any type A
module Lift {i} (A : Set i) where
  -- lift a function to the exponentials
  lift : {X Y : Set i}
       → (X → Y) → (A → X) → (A → Y)
  lift f g a = f (g a)

  -- lift an equality of types to an equality of exponentials
  lift≡ : {X Y : Set i}
          → X ≡ Y → (A → X) ≡ (A → Y)
  lift≡ refl = refl

  -- coerce commutes with lifting
  lift-coherence : {X Y : Set i}(p : X ≡ Y)
                 → coerce (lift≡ p)
                 ≡ lift (coerce p)
  lift-coherence refl = refl

  -- Using univalence, lift a weak equivalence to the exponentials.
  -- Note that we really need univalence here, as it's not possible to
  -- prove that lift gives an isomorphism, unless we already have
  -- extensionality.
  lift≈ : {X Y : Set i}
        → X ≈ Y
        → (A → X) ≈ (A → Y)
  lift≈ = ≡⇒≈ ∘ lift≡ ∘ ≈⇒≡

  -- lift≈ acts like lift
  lift≈-coherence : {X Y : Set i}
                  → (f : X ≈ Y)
                  → apply≈ (lift≈ f) ≡ lift (apply≈ f)
  lift≈-coherence f = begin
      proj₁ (lift≈ f)
    ≡⟨ refl ⟩
      coerce (lift≡ (≈⇒≡ f))
    ≡⟨ lift-coherence (≈⇒≡ f) ⟩
      lift (coerce (≈⇒≡ f))
    ≡⟨ cong lift (uni-coherence f) ⟩
      lift (proj₁ f)
    ∎
    where open ≡-Reasoning

  -- lift≈ respects inverses
  lift≈-inverse : {X Y : Set i}
                → (f : X ≈ Y)
                → (g : Y → X)
                → g ∘ apply≈ f ≡ id
                → (u : A → Y)
                → lift g u ≡ invert≈ (lift≈ f) u
  lift≈-inverse f g p u = begin
      lift g u
    ≡⟨ cong (lift g) (sym (iso₂ u)) ⟩
      lift g (to (from u))
    ≡⟨ cong (λ z → lift g (z (from u)))
            (lift≈-coherence f) ⟩
      lift g (lift (apply≈ f) (from u))
    ≡⟨ refl ⟩
      lift (g ∘ apply≈ f) (from u)
    ≡⟨ cong (λ z → lift z (from u)) p ⟩
      from u
    ≡⟨ refl ⟩
      invert≈ (lift≈ f) u
    ∎
    where
      open ≡-Reasoning
      open _≅_ (≈⇒≅ (lift≈ f))

-- Now, to prove extensionality, we take a pair of extensionally equal
-- functions, and we want to prove that they are propositionally equal
extensionality : ∀ {i} → Extensionality i
extensionality {i} {X} {Y} f g h = main
  where
    -- Let Y' be the path space of Y
    open Paths Y renaming (Δ to Y')
    open Lift X

    -- Since Y and Y' are equivalent, we can lift the equivalence
    -- to the exponentials, and get an isomorphism.
    iso' : (X → Y) ≅ (X → Y')
    iso' = ≈⇒≅ (lift≈ Δ-equiv)

    -- We can now show that composing with δ is a left inverse to
    -- composing with π₁.
    -- Here we make use of the fact that the underlying function of
    -- the equivalence returned by lift≈ is just lift of the base
    -- function.
    lem : (k : X → Y') → δ ∘ π₁ ∘ k ≡ k
    lem k = begin
        δ ∘ π₁ ∘ k
      ≡⟨ cong (λ t → t (π₁ ∘ k))
               (sym (lift≈-coherence Δ-equiv)) ⟩
        to (π₁ ∘ k)
      ≡⟨ cong to (lift≈-inverse Δ-equiv π₁ refl k) ⟩
        to (from k)
      ≡⟨ iso₂ k ⟩
        k
      ∎
      where
        open ≡-Reasoning
        open _≅_ iso'
  
    -- Now we can finally show that f and g are equal.
    -- The idea of the proof is that
    --     δ ∘ f ≡ δ ∘ g
    -- since they are both equal to k below, hence they must be equal
    -- by injectivity of δ
    main : f ≡ g
    main = begin
        f
      ≡⟨ refl ⟩
        π₁ ∘ k
      ≡⟨ refl ⟩
        π₂ ∘ δ ∘ π₁ ∘ k
      ≡⟨ cong (_∘_ π₂) (lem k) ⟩
        π₂ ∘ k
      ≡⟨ refl ⟩
        g
      ∎
      where
        open ≡-Reasoning
        open _≅_ iso' using (iso₂)

        k : X → Y'
        k x = (f x , (g x , h x))