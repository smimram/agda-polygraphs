{-# OPTIONS --cubical --allow-unsolved-metas #-}

module 2Polygraph.Truncated where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws as GL
open import Cubical.Foundations.HLevels
open import Cubical.HITs.SetTruncation
open import Cubical.HITs.GroupoidTruncation

open import Graph
open import 2Polygraph.Base

private variable
  ℓ₀ ℓ₁ ℓ₂ ℓ : Level

module _ {P : 2Polygraph {ℓ₀} {ℓ₁} {ℓ₂}} where
  open Operations P
  open FreeCategory
  open FreePregroupoid

  ---
  --- elimination to 2-groupoids
  ---

  -- elimPathSet :
    -- (A : {x y : ⟦ P ⟧} → x ≡ y → Type ℓ) →
    -- ({x y : ⟦ P ⟧} (p : x ≡ y) → isSet (A p)) →
    -- ({x y : Σ₀} (p : x ↝? y) → A ∣ p ∣?) →
    -- {x y : ⟦ P ⟧} (p : x ≡ y) → A p
  -- elimPathSet A AS f {x} {y} p =
    -- {!1Polygraph.elim !}

  whisk?? : {A : Type ℓ}
    (f₀ : Σ₀ → A)
    (f₁ : {x y : Σ₀} (a : x ↝ y) → f₀ x ≡ f₀ y)
    (f₂ : {x y : Σ₀} {p q : x ↝* y} (α : p ⇒ q) → (f₁ *) p ≡ (f₁ *) q) →
    {x y : Σ₀} {p q : x ↝? y} (w : p ⇒? q) → (f₁ *?) p ≡ (f₁ *?) q
  whisk?? f₀ f₁ f₂ {x} {y} (whisk? p {q} {q'} α r) = FreePregroupoid.toPath∙∙ f₁ p (ofFC q) r ∙ cong (λ q → p' ∙∙ q ∙∙ r') (toPathOfFC f₁ q ∙ f₂ α ∙ sym (toPathOfFC f₁ q')) ∙ sym (FreePregroupoid.toPath∙∙ f₁ p (ofFC q') r)
    where
    p' : f₀ x ≡ f₀ _
    p' = FreePregroupoid.toPath f₁ p
    r' : f₀ _ ≡ f₀ y
    r' = FreePregroupoid.toPath f₁ r

  rec2Groupoid :
    (A : Type ℓ)
    (GA : isGroupoid A)
    (f₀ : Σ₀ → A)
    (f₁ : {x y : Σ₀} (a : x ↝ y) → f₀ x ≡ f₀ y)
    (f₂ : {x y : Σ₀} {p q : x ↝* y} (α : p ⇒ q) → (f₁ *) p ≡ (f₁ *) q) →
    (f₃ : {x y : Σ₀} {p q : x ↝? y} (ϕ ψ : p ⇔? q) → (whisk?? f₀ f₁ f₂ *?) ϕ ≡ (whisk?? f₀ f₁ f₂ *?) ψ) →
    ∥ ⟦ P ⟧ ∥₃ → A
  rec2Groupoid A GA f₀ f₁ f₂ f₃ = {!!}
    -- rec→Gpd.fun GA (1Polygraph.rec f₁) λ x y p q → elimPathProp₂ (λ p q → cong (1Polygraph.rec f₁) p ≡ cong (1Polygraph.rec f₁) q) (λ p q → GA _ _ _ _) f₂' p q
    -- where
    -- open FreeCategory
    -- open FreePregroupoid
    -- lem : {x y : Σ₀} (p : x ↝? y) → cong (1Polygraph.rec f₁) ∣ p ∣? ≡ toPath f₁ p
    -- lem [] = refl
    -- lem (p ∷+ a) =
      -- cong (1Polygraph.rec f₁) (∣ p ∣? ∙ ∣ a ∣₁) ≡⟨ congFunct (1Polygraph.rec f₁) ∣ p ∣? ∣ a ∣₁ ⟩
      -- cong (1Polygraph.rec f₁) ∣ p ∣? ∙ cong (1Polygraph.rec λ {x} {y} a → f₁ {x} {y} a) ∣ a ∣₁ ≡⟨ cong₂ _∙_ (lem p) refl ⟩
      -- toPath f₁ p ∙ f₁ a ≡⟨ refl ⟩
      -- toPath f₁ (p ∷+ a) ∎
    -- lem (p ∷- a) =
      -- cong (1Polygraph.rec f₁) (∣ p ∣? ∙ (sym ∣ a ∣₁)) ≡⟨ congFunct (1Polygraph.rec f₁) ∣ p ∣? (sym ∣ a ∣₁) ⟩
      -- cong (1Polygraph.rec f₁) ∣ p ∣? ∙ cong (1Polygraph.rec λ {x} {y} a → f₁ {x} {y} a) (sym ∣ a ∣₁) ≡⟨ cong₂ _∙_ (lem p) refl ⟩
      -- toPath f₁ (p ∷- a) ∎
    -- f₂' : {x y : Σ₀} (p q : x ↝? y) → cong (1Polygraph.rec f₁) ∣ p ∣? ≡ cong (1Polygraph.rec f₁) ∣ q ∣?
    -- f₂' p q = subst2 _≡_ (sym (lem p)) (sym (lem q)) (f₂ p q)
