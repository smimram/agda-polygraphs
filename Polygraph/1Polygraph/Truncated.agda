{-# OPTIONS --cubical --allow-unsolved-metas #-}

module 1Polygraph.Truncated where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST

open import Graph
open import 1Polygraph.Base as 1Polygraph
open import 1Polygraph.PathElimination
open import 1Polygraph.PathPresentation

private variable
  ℓ₀ ℓ₁ ℓ : Level

module _ {P : 1Polygraph {ℓ₀} {ℓ₁}} where
  open Operations P

  -- zig-zags are surjective on groupoid morphisms
  surjPath : {x y : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) → ∥ Σ (x ↝? y) (λ q → ∣ q ∣? ≡ p) ∥₁
  surjPath {x = x} p = elimPath (λ {y} p → ∥ Σ (x ↝? y) (λ q → ∣ q ∣? ≡ p) ∥₁) ∣ [] , refl ∣₁ (λ p a → propBiimpl→Equiv isPropPropTrunc isPropPropTrunc (PT.map (λ { (q , r) → q ∷+ a , cong (λ p → p ∙ ∣ a ∣₁) r })) (PT.map λ { (q , r) → q ∷- a , cong (λ p → p ∙ sym ∣ a ∣₁) r ∙ sym (assoc _ _ _) ∙ cong (_∙_ p) (rCancel ∣ a ∣₁) ∙ sym (rUnit _) })) p
    where open FreePregroupoid

  -- in order to show a property on paths, it is enough to show it on zig-zags
  elimPathProp :
    (A : {x y : ⟦ P ⟧} → x ≡ y → Type ℓ) →
    ({x y : ⟦ P ⟧} (p : x ≡ y) → isProp (A p)) →
    ({x y : Σ₀} (p : x ↝? y) → A ∣ p ∣?) →
    {x y : ⟦ P ⟧} (p : x ≡ y) → A p
  elimPathProp A AP f {x} {y} p =
    elimProp (λ x → {y : ⟦ P ⟧} (p : x ≡ y) → A p) (λ x → isPropImplicitΠ λ y → isPropΠ AP) (λ x {y} p →
      elimProp (λ y → (p : ∣ x ∣ ≡ y) → A p) (λ y → isPropΠ AP) (λ y p →
        PT.elim (λ _ → AP p) (λ { (q , r) → subst A r (f q) }) (surjPath p)
      ) y p
    ) x {y} p

  recSet :
    (A : Type ℓ)
    (GA : isGroupoid A)
    (f₀ : Σ₀ → A)
    (f₁ : {x y : Σ₀} (a : x ↝ y) → f₀ x ≡ f₀ y)
    (f₂ : {x y : Σ₀} (p q : x ↝* y) → (f₁ *) p ≡ (f₁ *) q) →
    ∥ ⟦ P ⟧ ∥₂ → A
  recSet A GA f₀ f₁ f₂ = rec→Gpd.fun GA (1Polygraph.rec f₁ ) λ x y p q → {!!}
