{-# OPTIONS --cubical --allow-unsolved-metas #-}

module 2Polygraph.Coherence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws as GL
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation hiding (elim2)
open import Cubical.HITs.SetTruncation hiding (elim2)
open import Cubical.HITs.GroupoidTruncation hiding (elim2)

open import Graph
open import 1Polygraph renaming (⟦_⟧ to ⟦_⟧₁) hiding (module Operations ; rec ; elim ; elimPath ; elimProp)
open import 2Polygraph.Base
open import 2Polygraph.Rewriting
open import 2Polygraph.Base as 2Polygraph

private variable
  ℓ₀ ℓ₁ ℓ₂ ℓ : Level

module _ {P : 2Polygraph {ℓ₀} {ℓ₁} {ℓ₂}} (PCR : hasPCR P) where
  open Operations P

  ---
  --- the coherence result
  ---

  elim2 :
    (A : {x y : ⟦ P ⟧} → x ≡ y → Type ℓ) →
    -- ({x y : ⟦ P ⟧} (p : x ≡ y) → isProp (A p)) →
    (Ap : {x y : ⟦ Σ' ⟧₁} → {!!})
    {x y : ⟦ P ⟧} (p : x ≡ y) → A p
  elim2 = {!!}

  -- coh : {x y : ⟦ P ⟧} (p q : x ≡ y) → ∥ p ≡ q ∥₁
  -- coh {x} {y} p q =
    -- -- TODO: we need to show the property of paths of the form ∣ p ∣' (in a compatible way) and then use elimPathProp
    -- 2Polygraph.elimProp (λ x → (y : ⟦ P ⟧) (p q : x ≡ y) → ∥ p ≡ q ∥₁) (λ x → isPropΠ λ y → isPropΠ λ p → isPropΠ λ q → isPropPropTrunc) (λ x y p q → 
      -- 2Polygraph.elimProp (λ y → (p q : ∣ x ∣'' ≡ y) → ∥ p ≡ q ∥₁) (λ y → isPropΠ λ p → isPropΠ λ q → isPropPropTrunc) (λ y p q → {!
        
      -- !}) y p q
    -- ) x y p q

