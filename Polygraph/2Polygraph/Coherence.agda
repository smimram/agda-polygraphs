{-# OPTIONS --cubical --allow-unsolved-metas #-}

module 2Polygraph.Coherence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws as GL
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.SetTruncation
open import Cubical.HITs.GroupoidTruncation

open import Graph
open import 2Polygraph.Base
open import 2Polygraph.Rewriting
open import 2Polygraph.Base as 2Polygraph

private variable
  ℓ₀ ℓ₁ ℓ₂ ℓ : Level

module _ {P : 2Polygraph {ℓ₀} {ℓ₁} {ℓ₂}} (PCR : hasPCR P) where

  ---
  --- the coherence result
  ---

  coh : {x y : ⟦ P ⟧} (p q : x ≡ y) → ∥ p ≡ q ∥₁
  coh = {!!}

