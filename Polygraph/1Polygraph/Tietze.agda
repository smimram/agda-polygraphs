{-# OPTIONS --cubical #-}

---
--- Tietze transformations for 1-polygraphs.
---

module 1Polygraph.Tietze where

open import Cubical.Foundations.Everything
open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.HITs.SetTruncation as ST

open import Over
open import 1Polygraph.Base

open 1Polygraph

private variable
  ℓ₀ ℓ₁ ℓ₂ ℓ₃ : Level

-- Presented set
⟦_⟧₀ : (P : 1Polygraph {ℓ₀} {ℓ₁}) → Type _
⟦ P ⟧₀ = ∥ ⟦ P ⟧ ∥₂

module _ (P : 1Polygraph {ℓ₀} {ℓ₁}) where

  module _  (X : Over ℓ₀ (Σ₀ P)) where

    expand₀ : 1Polygraph {ℓ₀} {ℓ₁}
    Σ₀ expand₀ = Σ₀ P ⊎ ⟨ X ⟩
    (expand₀ ↝ inl x) (inl y) = _↝_ P x y
    (expand₀ ↝ inl x) (inr y) = ?
    (expand₀ ↝ inr x) y = ⊥*

    expand₀-correct : ⟦ P ⟧₀ ≡ ⟦ expand₀ ⟧₀
    expand₀-correct = ua (isoToEquiv e)
      where
      open Iso
      e : Iso ⟦ P ⟧₀ ⟦ expand₀ ⟧₀
      fun e = ST.map {!!}
      inv e = {!!}
      rightInv e = {!!}
      leftInv e = {!!}

-- expand₁ : (P : 1Polygraph {ℓ₀} {ℓ₁}) (R : Σ₀ P → Σ₀ P → {!!}) → 1Polygraph {ℓ₀} {ℓ₁}
-- expand₁ = {!!}
