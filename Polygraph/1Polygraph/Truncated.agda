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

  ---
  --- elimination to groupoids
  ---

  -- zig-zags are surjective on groupoid morphisms
  surjPath : {x y : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) → ∥ Σ (x ↝? y) (λ q → ∣ q ∣? ≡ p) ∥₁
  surjPath {x = x} p = elimPath (λ {y} p → ∥ Σ (x ↝? y) (λ q → ∣ q ∣? ≡ p) ∥₁) ∣ [] , refl ∣₁ (λ p a → propBiimpl→Equiv isPropPropTrunc isPropPropTrunc (PT.map (λ { (q , r) → q ∷+ a , cong (λ p → p ∙ ∣ a ∣₁) r })) (PT.map λ { (q , r) → q ∷- a , cong (λ p → p ∙ sym ∣ a ∣₁) r ∙ sym (assoc _ _ _) ∙ cong (_∙_ p) (rCancel ∣ a ∣₁) ∙ sym (rUnit _) })) p
    where open FreePregroupoid hiding (assoc)

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

  -- same but with two parallel paths
  elimPathProp₂ :
    (A : {x y : ⟦ P ⟧} → x ≡ y → x ≡ y → Type ℓ) →
    ({x y : ⟦ P ⟧} (p q : x ≡ y) → isProp (A p q)) →
    ({x y : Σ₀} (p q : x ↝? y) → A ∣ p ∣? ∣ q ∣?) →
    {x y : ⟦ P ⟧} (p q : x ≡ y) → A p q
  elimPathProp₂ A AP f {x} {y} p q =
    elimProp (λ x → {y : ⟦ P ⟧} (p q : x ≡ y) → A p q) (λ x → isPropImplicitΠ λ y → isPropΠ λ p → isPropΠ λ q → AP p q) (λ x {y} p q →
      elimProp (λ y → (p q : ∣ x ∣ ≡ y) → A p q) (λ y → isPropΠ λ p → isPropΠ λ q → AP p q) (λ y p q →
        PT.elim (λ _ → AP p q) (λ { (p' , p'') → 
          PT.elim (λ _ → AP p q) (λ { (q' , q'') → subst2 A p'' q'' (f p' q') }) (surjPath q)
          }) (surjPath p)
      ) y p q
    ) x {y} p q

  -- recurrence to a groupoid
  recGroupoid :
    (A : Type ℓ)
    (GA : isGroupoid A)
    (f₀ : Σ₀ → A)
    (f₁ : {x y : Σ₀} (a : x ↝ y) → f₀ x ≡ f₀ y)
    (f₂ : {x y : Σ₀} (p q : x ↝? y) → FreePregroupoid.toPath f₁ p ≡ FreePregroupoid.toPath f₁ q) →
    ∥ ⟦ P ⟧ ∥₂ → A
  recGroupoid A GA f₀ f₁ f₂ = rec→Gpd.fun GA (1Polygraph.rec f₁) λ x y p q → elimPathProp₂ (λ p q → cong (1Polygraph.rec f₁) p ≡ cong (1Polygraph.rec f₁) q) (λ p q → GA _ _ _ _) f₂' p q
    where
    open FreeCategory
    open FreePregroupoid
    lem : {x y : Σ₀} (p : x ↝? y) → cong (1Polygraph.rec f₁) ∣ p ∣? ≡ toPath f₁ p
    lem [] = refl
    lem (p ∷+ a) =
      cong (1Polygraph.rec f₁) (∣ p ∣? ∙ ∣ a ∣₁) ≡⟨ congFunct (1Polygraph.rec f₁) ∣ p ∣? ∣ a ∣₁ ⟩
      cong (1Polygraph.rec f₁) ∣ p ∣? ∙ cong (1Polygraph.rec λ {x} {y} a → f₁ {x} {y} a) ∣ a ∣₁ ≡⟨ cong₂ _∙_ (lem p) refl ⟩
      toPath f₁ p ∙ f₁ a ≡⟨ refl ⟩
      toPath f₁ (p ∷+ a) ∎
    lem (p ∷- a) =
      cong (1Polygraph.rec f₁) (∣ p ∣? ∙ (sym ∣ a ∣₁)) ≡⟨ congFunct (1Polygraph.rec f₁) ∣ p ∣? (sym ∣ a ∣₁) ⟩
      cong (1Polygraph.rec f₁) ∣ p ∣? ∙ cong (1Polygraph.rec λ {x} {y} a → f₁ {x} {y} a) (sym ∣ a ∣₁) ≡⟨ cong₂ _∙_ (lem p) refl ⟩
      toPath f₁ (p ∷- a) ∎
    f₂' : {x y : Σ₀} (p q : x ↝? y) → cong (1Polygraph.rec f₁) ∣ p ∣? ≡ cong (1Polygraph.rec f₁) ∣ q ∣?
    f₂' p q = subst2 _≡_ (sym (lem p)) (sym (lem q)) (f₂ p q)

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

  -- rec2Groupoid :
    -- (A : Type ℓ)
    -- (GA : isGroupoid A)
    -- (f₀ : Σ₀ → A)
    -- (f₁ : {x y : Σ₀} (a : x ↝ y) → f₀ x ≡ f₀ y)
    -- (f₂ : {x y : Σ₀} (p q : x ↝? y) → FreePregroupoid.toPath f₁ p ≡ FreePregroupoid.toPath f₁ q) →
    -- (f₃ : {x y : Σ₀} {p q : x ↝? y} (ϕ ψ : x) → {!!}) →
    -- ∥ ⟦ P ⟧ ∥₂ → A
  -- rec2Groupoid A GA f₀ f₁ f₂ f₃ = {!!}
    -- -- rec→Gpd.fun GA (1Polygraph.rec f₁) λ x y p q → elimPathProp₂ (λ p q → cong (1Polygraph.rec f₁) p ≡ cong (1Polygraph.rec f₁) q) (λ p q → GA _ _ _ _) f₂' p q
    -- -- where
    -- -- open FreeCategory
    -- -- open FreePregroupoid
    -- -- lem : {x y : Σ₀} (p : x ↝? y) → cong (1Polygraph.rec f₁) ∣ p ∣? ≡ toPath f₁ p
    -- -- lem [] = refl
    -- -- lem (p ∷+ a) =
      -- -- cong (1Polygraph.rec f₁) (∣ p ∣? ∙ ∣ a ∣₁) ≡⟨ congFunct (1Polygraph.rec f₁) ∣ p ∣? ∣ a ∣₁ ⟩
      -- -- cong (1Polygraph.rec f₁) ∣ p ∣? ∙ cong (1Polygraph.rec λ {x} {y} a → f₁ {x} {y} a) ∣ a ∣₁ ≡⟨ cong₂ _∙_ (lem p) refl ⟩
      -- -- toPath f₁ p ∙ f₁ a ≡⟨ refl ⟩
      -- -- toPath f₁ (p ∷+ a) ∎
    -- -- lem (p ∷- a) =
      -- -- cong (1Polygraph.rec f₁) (∣ p ∣? ∙ (sym ∣ a ∣₁)) ≡⟨ congFunct (1Polygraph.rec f₁) ∣ p ∣? (sym ∣ a ∣₁) ⟩
      -- -- cong (1Polygraph.rec f₁) ∣ p ∣? ∙ cong (1Polygraph.rec λ {x} {y} a → f₁ {x} {y} a) (sym ∣ a ∣₁) ≡⟨ cong₂ _∙_ (lem p) refl ⟩
      -- -- toPath f₁ (p ∷- a) ∎
    -- -- f₂' : {x y : Σ₀} (p q : x ↝? y) → cong (1Polygraph.rec f₁) ∣ p ∣? ≡ cong (1Polygraph.rec f₁) ∣ q ∣?
    -- -- f₂' p q = subst2 _≡_ (sym (lem p)) (sym (lem q)) (f₂ p q)
