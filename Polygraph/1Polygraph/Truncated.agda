{-# OPTIONS --cubical --allow-unsolved-metas #-}

module 1Polygraph.Truncated where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST

open import Graph
open import 1Polygraph.Base
open import 1Polygraph.PathElimination
open import 1Polygraph.PathPresentation

private variable
  ℓ₀ ℓ₁ ℓ : Level

module _ {P : 1Polygraph {ℓ₀} {ℓ₁}} where
  open Operations P

  surjPath : {x y : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) → ∥ Σ (FreePregroupoid.T _↝_ x y) (λ q → ∣ q ∣? ≡ p) ∥₁
  surjPath p = {!elimPath ? ? ? p!}

  elimPathProp : (A : {x y : ⟦ P ⟧} → x ≡ y → Type ℓ) → ({x y : ⟦ P ⟧} (p : x ≡ y) → isProp (A p)) → {!!}
  elimPathProp A PA = {!!}

  recSet :
    (A : Type ℓ)
    (GA : isGroupoid A)
    (f₀ : Σ₀ → A)
    (f₁ : {x y : Σ₀} (a : x ↝ y) → f₀ x ≡ f₀ y)
    (f₂ : {x y : Σ₀} (p q : x ↝* y) → (f₁ *) p ≡ (f₁ *) q) →
    ∥ ⟦ P ⟧ ∥₂ → A
  recSet A GA f₀ f₁ f₂ = rec→Gpd.fun GA (1Polygraph.Base.rec f₁ ) λ x y p q → {!!}
