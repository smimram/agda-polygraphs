{-# OPTIONS --cubical #-}

module 1Polygraph.Truncated where

open import Cubical.Foundations.Prelude

open import 1Polygraph.Base
open import 1Polygraph.PathElimination

private variable
  ℓ₀ ℓ₁ ℓ : Level

module _ {P : 1Polygraph {ℓ₀} {ℓ₁}} where
  open Operations P

  recSet :
    (A : Type ℓ)
    (SA : isSet A)
    (f₀ : Σ₀ → A)
    (f₁ : {x y : Σ₀} (a : x ↝ y) → f₀ x ≡ f₀ y)
    (f₂ : {x y : Σ₀} (p q : x ↝* y) → (f₁ *) p ≡ (f₁ *) q) →
    ⟦ P ⟧ → A
  recSet A SA f₀ f₁ f₂ = rec f₁
