{-# OPTIONS --cubical --allow-unsolved-metas #-}

---
--- Tietze transformations for 1-polygraphs.
---

module 1Polygraph.Tietze where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.HITs.SetTruncation as ST

open import Over
open import 1Polygraph.Base

open 1Polygraph

private variable
  ℓ ℓ₀ ℓ₁ ℓ₂ ℓ₃ : Level

-- Presented set
⟦_⟧₀ : (P : 1Polygraph {ℓ₀} {ℓ₁}) → Type _
⟦ P ⟧₀ = ∥ ⟦ P ⟧ ∥₂

module _ (P : 1Polygraph {ℓ} {ℓ}) where

  module _  (L R : (Σ₀ P) → Type ℓ) where

    expand₀ : 1Polygraph {ℓ} {ℓ}
    Σ₀ expand₀ = Σ₀ P ⊎ (Σ (Σ₀ P) L ⊎ Σ (Σ₀ P) R)
    _↝_ expand₀ (inl x) (inl y) = _↝_ P x y
    _↝_ expand₀ (inl x) (inr (inl y)) = {!!}
    _↝_ expand₀ (inl x) (inr (inr y)) = {!fst y!}
    _↝_ expand₀ (inr (inl x)) y = {!!}
    _↝_ expand₀ (inr (inr x)) y = {!!}

    -- Σ₀ expand₀ = ? -- Σ₀ P ⊎ (⟨ {!Σ (Σ₀ P) L!} ⟩ ⊎ ⟨ {!!} ⟩)
    -- (expand₀ ↝ inl x) (inl y) = {!!} --_↝_ P x y
    -- (expand₀ ↝ inl x) (inr y) = {!!}
    -- (expand₀ ↝ inr x) y = {!!} -- ⊥*

    -- expand₀-correct : ⟦ P ⟧₀ ≡ ⟦ expand₀ ⟧₀
    -- expand₀-correct = ua (isoToEquiv e)
      -- where
      -- open Iso
      -- e : Iso ⟦ P ⟧₀ ⟦ expand₀ ⟧₀
      -- fun e = ST.map {!!}
      -- inv e = {!!}
      -- rightInv e = {!!}
      -- leftInv e = {!!}

-- expand₁ : (P : 1Polygraph {ℓ₀} {ℓ₁}) (R : Σ₀ P → Σ₀ P → {!!}) → 1Polygraph {ℓ₀} {ℓ₁}
-- expand₁ = {!!}
