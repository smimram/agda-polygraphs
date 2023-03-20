{-# OPTIONS --cubical #-}

module 2Polygraph.Base where

open import Cubical.Foundations.Prelude

open import Graph
open Graph.FreeCategory hiding (elim ; rec)
open Graph.FreePregroupoid
open import 1Polygraph renaming (⟦_⟧ to ⟦_⟧₁) hiding (module Operations ; rec ; elim ; elimPath)

private variable
  ℓ ℓ₀ ℓ₁ ℓ₂ ℓ₃ : Level

-- 2-polygraphs, type-theoretic definition
record 2Polygraph : Type (ℓ-suc (ℓ-max ℓ₀ (ℓ-max ℓ₁ ℓ₂))) where
  field
    Σ'  : 1Polygraph {ℓ₀} {ℓ₁}
    _⇒_ : {x y : 1Polygraph.Σ₀ Σ'} → Graph (FreeCategory (1Polygraph._↝_ Σ') x y) ℓ₂

module Operations (P : 2Polygraph {ℓ₀} {ℓ₁} {ℓ₂}) where
  open 2Polygraph P public
  open 1Polygraph.Operations Σ' public

  data _⇒w_ : {x y : Σ₀} → (x ↝* y) → (x ↝* y) → Type (ℓ-max ℓ₀ (ℓ-max ℓ₁ ℓ₂)) where
    whisk  : {x' x y y' : Σ₀} → (p : x' ↝* x) {q q' : x ↝* y} (α : q ⇒ q') (r : y ↝* y') → (p · q · r) ⇒w (p · q' · r)

  infix 4 _⇔*_

  -- TODO: rather use the groupoid closure?
  _⇔*_ : {x y : Σ₀} (p q : x ↝* y) → Type (ℓ-max ℓ₀ (ℓ-max ℓ₁ ℓ₂))
  _⇔*_ = FreePregroupoid _⇒w_

  whiskAssoc : {x'' x' x y y' y'' : Σ₀} (p' : x'' ↝* x') (p : x' ↝* x) (q : x ↝* y) (r : y ↝* y') (r' : y' ↝* y'') → p' · (p · q · r) · r' ≡ (p' · p) · q · (r · r')
  whiskAssoc p' p q r r' =
    p' · (p · q · r) · r'   ≡⟨ cong (λ p → p' · p) (FreeCategory.assoc p _ r') ⟩
    p' · (p · (q · r) · r') ≡⟨ sym (FreeCategory.assoc p' p _) ⟩
    (p' · p) · (q · r) · r' ≡⟨ cong (λ q → (p' · p) · q) (FreeCategory.assoc q _ r') ⟩
    (p' · p) · q · (r · r') ∎

  whisk* : {x' x y y' : Σ₀} → (p : x' ↝* x) {q q' : x ↝* y} (ϕ : q ⇔* q') (r : y ↝* y') → (p · q · r) ⇔* (p · q' · r)
  whisk* p [] q = []
  whisk* p (ϕ ∷+ whisk p' α r') r = whisk* p ϕ r ·? [≡ whiskAssoc p p' _ r' r ]? ·? [ whisk (p · p') α (r' · r) ]+ ·? [≡ sym (whiskAssoc p p' _ r' r) ]?
  whisk* p (ϕ ∷- whisk p' α r') r = whisk* p ϕ r ·? [≡ whiskAssoc p p' _ r' r ]? ·? [ whisk (p · p') α (r' · r) ]- ·? [≡ sym (whiskAssoc p p' _ r' r) ]?

module _ (P : 2Polygraph {ℓ₀} {ℓ₁} {ℓ₂}) where
  open Operations P
