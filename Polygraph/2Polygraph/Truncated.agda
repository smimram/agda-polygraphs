{-# OPTIONS --cubical --allow-unsolved-metas #-}

module 2Polygraph.Truncated where

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
open import 2Polygraph.Base as 2Polygraph

private variable
  ℓ₀ ℓ₁ ℓ₂ ℓ : Level

module _ {P : 2Polygraph {ℓ₀} {ℓ₁} {ℓ₂}} where
  open Operations P
  open FreeCategory
  open FreePregroupoid
  open FreePregroupoid'

  ---
  --- elimination to 2-groupoids
  ---

  surj2Path : {x y : Σ₀} {p q : x ↝? y} (ϕ : ∣ p ∣?' ≡ ∣ q ∣?') → ∥ Σ (p ⇔? q) (λ ψ → ϕ ≡ ∣ ψ ∣?*) ∥₁
  surj2Path = {!!}

  elim2PathProp :
    {ℓ : Level}
    (A : {x y : ⟦ P ⟧} {p q : x ≡ y} (ϕ : p ≡ q) → Type ℓ) →
    ({x y : ⟦ P ⟧} {p q : x ≡ y} (ϕ : p ≡ q) → isProp (A ϕ)) →
    ({x y : Σ₀} {p q : x ↝? y} (ϕ : p ⇔? q) → A ∣ ϕ ∣?*) → 
    {x y : ⟦ P ⟧} {p q : x ≡ y} (ϕ : p ≡ q) → A ϕ
  elim2PathProp A AP f {x} {y} {p} {q} ϕ = {!2Polygraph.elimProp ? ? ? ?!}

  elimPathSet :
    (A : {x y : ⟦ P ⟧} → x ≡ y → Type ℓ) →
    ({x y : ⟦ P ⟧} (p : x ≡ y) → isSet (A p)) →
    ({x y : Σ₀} (p : x ↝? y) → A ∣ p ∣?') →
    {x y : ⟦ P ⟧} (p : x ≡ y) → A p
  elimPathSet A AS f {x} {y} p =
    2Polygraph.elimSet (λ x → (y : ⟦ P ⟧) → (p : x ≡ y) → A p) (λ p → isSetΠ λ y → isSetΠ λ p → AS p) (λ x y p → 
      2Polygraph.elimSet (λ y → (p : ∣ x ∣'' ≡ y) → A p) (λ y → isSetΠ AS) (
        λ y p → {!!}
      ) {!!} y p
    ) {!!} x y p

  -- on veut la vriante de rec→Gpd.fun qui étant donnée f : A → B avec B 2-groupoide telle que
  -- - ∀ p,q : x ≡ y on a f p ≡ f q
  -- - ∀ α,β : p ≡ q on a cong f α ≡ cong f β

  -- _↝¿_ = FreePregroupoid' _↝_

  -- ∣_∣¿ : {x y : Σ₀} (p : x ↝¿ y) → _≡_ {A = ⟦ P ⟧} ∣ x ∣'' ∣ y ∣''
  -- ∣_∣¿ {x = x} p = elim≃ (λ {y} _ → ∣ x ∣'' ≡ ∣ y ∣'') refl (λ a → compPathrEquiv ∣ a ∣₁') p

  -- elimPathSet :
    -- (A : {x y : ⟦ P ⟧} → x ≡ y → Type ℓ) →
    -- ({x y : ⟦ P ⟧} (p : x ≡ y) → isSet (A p)) →
    -- ({x y : Σ₀} (p : x ↝¿ y) → A ∣ p ∣¿) →
    -- {x y : ⟦ P ⟧} (p : x ≡ y) → A p
  -- elimPathSet A AS f {x} {y} p =
    -- 2Polygraph.elimSet (λ x → (y : ⟦ P ⟧) → (p : x ≡ y) → A p) (λ p → isSetΠ λ y → isSetΠ λ p → AS p) (λ x y p → 
      -- 2Polygraph.elimSet (λ y → (p : ∣ x ∣'' ≡ y) → A p) (λ y → isSetΠ AS) (
        -- λ y p → {!!}
      -- ) {!!} y p
    -- ) {!!} x y p

  -- whisk?? : {A : Type ℓ}
    -- (f₀ : Σ₀ → A)
    -- (f₁ : {x y : Σ₀} (a : x ↝ y) → f₀ x ≡ f₀ y)
    -- (f₂ : {x y : Σ₀} {p q : x ↝* y} (α : p ⇒ q) → (f₁ *) p ≡ (f₁ *) q) →
    -- {x y : Σ₀} {p q : x ↝? y} (w : p ⇒? q) → (f₁ *?) p ≡ (f₁ *?) q
  -- -- whisk?? f₀ f₁ f₂ {x} {y} (whisk? p {q} {q'} α r) = FreePregroupoid.toPath∙∙ f₁ p (ofFC q) r ∙ cong (λ q → p' ∙∙ q ∙∙ r') (toPathOfFC f₁ q ∙ f₂ α ∙ sym (toPathOfFC f₁ q')) ∙ sym (FreePregroupoid.toPath∙∙ f₁ p (ofFC q') r)
    -- where
    -- p' : f₀ x ≡ f₀ _
    -- p' = FreePregroupoid.toPath f₁ p
    -- r' : f₀ _ ≡ f₀ y
    -- r' = FreePregroupoid.toPath f₁ r

  -- rec2Groupoid :
    -- (A : Type ℓ)
    -- (GA : is2Groupoid A)
    -- (f₀ : Σ₀ → A)
    -- (f₁ : {x y : Σ₀} (a : x ↝ y) → f₀ x ≡ f₀ y)
    -- (f₂ : {x y : Σ₀} {p q : x ↝* y} (α : p ⇒ q) → (f₁ *) p ≡ (f₁ *) q) →
    -- (f₃ : {x y : Σ₀} {p q : x ↝? y} (ϕ ψ : p ⇔? q) → (whisk?? f₀ f₁ f₂ *?) ϕ ≡ (whisk?? f₀ f₁ f₂ *?) ψ) →
    -- ∥ ⟦ P ⟧ ∥₃ → A
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
