{-# OPTIONS --cubical --allow-unsolved-metas #-}

module 2Polygraph.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws as GL
open import Cubical.Foundations.HLevels

open import Graph
open Graph.FreeCategory hiding (elim ; rec)
open Graph.FreePregroupoid
open import 1Polygraph renaming (⟦_⟧ to ⟦_⟧₁) hiding (module Operations ; rec ; elim ; elimPath ; elimProp)

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
    whisk : {x' x y y' : Σ₀} → (p : x' ↝* x) {q q' : x ↝* y} (α : q ⇒ q') (r : y ↝* y') → (p · q · r) ⇒w (p · q' · r)

  infix 4 _⇔*_

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

  ---
  --- groupoid whiskering
  ---

  infix 4 _⇒?_

  data _⇒?_ : {x y : Σ₀} → (x ↝? y) → (x ↝? y) → Type (ℓ-max ℓ₀ (ℓ-max ℓ₁ ℓ₂)) where
    whisk?  : {x' x y y' : Σ₀} → (p : x' ↝? x) {q q' : x ↝* y} (α : q ⇒ q') (r : y ↝? y') → p ·? ofFC q ·? r ⇒? p ·? ofFC q' ·? r
    whiskUL : {x' x y y' : Σ₀} → (p : x' ↝? x) (a : y ↝ x) (q : x ↝? y') → p ·? [ a ]- ·? [ a ]+ ·? q ⇒? p ·? q
    whiskUR : {x' x y y' : Σ₀} → (p : x' ↝? x) (a : x ↝ y) (q : x ↝? y') → p ·? [ a ]+ ·? [ a ]- ·? q ⇒? p ·? q

  infix 4 _⇔?_

  _⇔?_ : {x y : Σ₀} (p q : x ↝? y) → Type (ℓ-max ℓ₀ (ℓ-max ℓ₁ ℓ₂))
  _⇔?_ = FreePregroupoid _⇒?_

module _ (P : 2Polygraph {ℓ₀} {ℓ₁} {ℓ₂}) where
  open Operations P

  ---
  --- Presented category
  ---

  data ⟦_⟧ : Type (ℓ-max (ℓ-max ℓ₀ ℓ₁) ℓ₂) where
    ∣_∣' : ⟦ Σ' ⟧₁ → ⟦_⟧
    ∣_∣₂ : {x y : Σ₀} {p q : x ↝* y} → p ⇒ q → cong ∣_∣' ∣ p ∣* ≡ cong ∣_∣' ∣ q ∣*

module _ {P : 2Polygraph {ℓ₀} {ℓ₁} {ℓ₂}} where
  open Operations P

  ∣_∣'' : Σ₀ → ⟦ P ⟧
  ∣ x ∣'' = ∣ ∣ x ∣ ∣'

  ∣_∣₁' : {x y : Σ₀} → x ↝ y → ∣ x ∣'' ≡ ∣ y ∣''
  ∣_∣₁' a = cong ∣_∣' ∣ a ∣₁

  ∣_∣*' : {x y : Σ₀} (p : x ↝* y) → ∣ x ∣'' ≡ ∣ y ∣''
  ∣ p ∣*' = cong ∣_∣' ∣ p ∣*

  ∣_∣?' : {x y : Σ₀} (p : x ↝? y) → ∣ x ∣'' ≡ ∣ y ∣''
  ∣ p ∣?' = cong ∣_∣' ∣ p ∣?

  ∣∣*'comp : {x y z : Σ₀} (p : x ↝* y) (q : y ↝* z) → ∣ p · q ∣*' ≡ ∣ p ∣*' ∙ ∣ q ∣*'
  ∣∣*'comp p q =
    ∣ p · q ∣*' ≡⟨ refl ⟩
    cong ∣_∣' ∣ p · q ∣* ≡⟨ cong (cong ∣_∣') (mapPathComp ∣_∣₁ p q) ⟩
    cong ∣_∣' (∣ p ∣* ∙ ∣ q ∣*) ≡⟨ congFunct ∣_∣' _ _ ⟩
    cong ∣_∣' ∣ p ∣* ∙ cong ∣_∣' ∣ q ∣* ≡⟨ refl ⟩
    ∣ p ∣*' ∙ ∣ q ∣*' ∎

  ∣∣?'comp : {x y z : Σ₀} (p : x ↝? y) (q : y ↝? z) → ∣ p ·? q ∣?' ≡ ∣ p ∣?' ∙ ∣ q ∣?'
  ∣∣?'comp p [] = rUnit _
  ∣∣?'comp p (q ∷+ a)=
    ∣ p ·? (q ∷+ a) ∣?'                ≡⟨ refl ⟩
    ∣ (p ·? q) ∷+ a ∣?'                ≡⟨ refl ⟩
    cong ∣_∣' ∣ (p ·? q) ∷+ a ∣?       ≡⟨ refl ⟩
    cong ∣_∣' (∣ (p ·? q) ∣? ∙ ∣ a ∣₁) ≡⟨ congFunct ∣_∣' _ _ ⟩
    cong ∣_∣' ∣ (p ·? q) ∣? ∙ ∣ a ∣₁'  ≡⟨ cong (_∙ ∣ a ∣₁') (∣∣?'comp p q) ⟩
    (∣ p ∣?' ∙ ∣ q ∣?') ∙ ∣ a ∣₁'      ≡⟨ sym (GL.assoc _ _ _) ⟩
    ∣ p ∣?' ∙ ∣ q ∣?' ∙ ∣ a ∣₁'        ≡⟨ cong (_∙_ ∣ p ∣?') (sym (congFunct ∣_∣' _ _)) ⟩
    ∣ p ∣?' ∙ ∣ q ∷+ a ∣?'             ∎
  ∣∣?'comp p (q ∷- a) = {!!} -- similar as above

  ∣∣*'comp₃ : {x y z w : Σ₀} (p : x ↝* y) (q : y ↝* z) (r : z ↝* w) → ∣ p · q · r ∣*' ≡ ∣ p ∣*' ∙ ∣ q ∣*' ∙ ∣ r ∣*'
  ∣∣*'comp₃ p q r = ∣∣*'comp p (q · r) ∙ cong (_∙_ ∣ p ∣*') (∣∣*'comp q r)

  ∣∣?'comp₃ : {x y z w : Σ₀} (p : x ↝? y) (q : y ↝? z) (r : z ↝? w) → ∣ p ·? q ·? r ∣?' ≡ ∣ p ∣?' ∙ ∣ q ∣?' ∙ ∣ r ∣?'
  ∣∣?'comp₃ p q r = ∣∣?'comp p (q ·? r) ∙ cong (_∙_ ∣ p ∣?') (∣∣?'comp q r)

  ∣[]∣*' : {x y : Σ₀} (a : x ↝ y) → ∣ [ a ] ∣*' ≡ cong ∣_∣' ∣ a ∣₁
  ∣[]∣*' a = cong (cong ∣_∣') (sym (GL.lUnit _))
    -- ∣ [ a ] ∣*' ≡⟨ refl ⟩
    -- cong ∣_∣' ∣ [] ∷ a ∣* ≡⟨ refl ⟩
    -- cong ∣_∣' (refl ∙ ∣ a ∣₁) ≡⟨ cong (cong ∣_∣') (sym (GL.lUnit _)) ⟩
    -- cong ∣_∣' ∣ a ∣₁ ∎

  |[]|?' : {x y : Σ₀} (a : x ↝ y) → ∣ [ a ]+ ∣?' ≡ cong ∣_∣' ∣ a ∣₁
  |[]|?' a = cong (cong ∣_∣') (sym (GL.lUnit _))

  ∣_∣** : {x y : Σ₀} {p q : x ↝* y} (ϕ : p ⇔* q) → ∣ p ∣*' ≡ ∣ q ∣*'
  ∣ [] ∣** = refl
  ∣ ϕ ∷+ whisk p α r ∣** = ∣ ϕ ∣** ∙ ∣∣*'comp₃ p _ r ∙ cong (λ q → ∣ p ∣*' ∙ q ∙ ∣ r ∣*') ∣ α ∣₂ ∙ sym (∣∣*'comp₃ p _ r)
  ∣ ϕ ∷- whisk p α r ∣** = ∣ ϕ ∣** ∙ ∣∣*'comp₃ p _ r ∙ cong (λ q → ∣ p ∣*' ∙ q ∙ ∣ r ∣*') (sym ∣ α ∣₂) ∙ sym (∣∣*'comp₃ p _ r)

  ∣_∣?* : {x y : Σ₀} {p q : x ↝? y} (ϕ : p ⇔? q) → ∣ p ∣?' ≡ ∣ q ∣?'
  ∣ [] ∣?* = refl
  ∣ ϕ ∷+ whisk? p α r ∣?* = ∣ ϕ ∣?* ∙ {!!} ∙ {!!}
  ∣ ϕ ∷+ whiskUL p a q ∣?* = {!!}
  ∣ ϕ ∷+ whiskUR p a q ∣?* = {!!}
  ∣ ϕ ∷- whisk? p α r ∣?* = {!!}
  ∣ ϕ ∷- whiskUL p a q ∣?* = {!!}
  ∣ ϕ ∷- whiskUR p a q ∣?* = {!!}

  ---
  --- elimination
  ---

  congFunct-dep' : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {x y z : A} (f : (a : A) → B a) (p : x ≡ y) (q : y ≡ z)
                   → cong f (p ∙ q) ≡ compPathP' {B = B} (cong f p) (cong f q)
  congFunct-dep' {A = A} {B = B} f p q = sym (fromPathP (congFunct-dep f p q)) ∙ fromPathP (compPathP'-filler {B = B} {p = p} {q = q} (cong f p) (cong f q))

  -- the induction principle
  elim :
    {ℓ₂ : Level}
    (A : ⟦ P ⟧ → Type ℓ₂)
    (f₀ : (x : Σ₀) → A ∣ ∣ x ∣ ∣')
    (f₁ : {x y : Σ₀} (a : x ↝ y) → PathP (λ i → A ∣ ∣ a ∣₁ i ∣') (f₀ x) (f₀ y))
    (f₂ : {x y : Σ₀} {p q : x ↝* y} (α : p ⇒ q) → PathP (λ i → PathP (λ j → cong (cong A) ∣ α ∣₂ i j) (f₀ x) (f₀ y)) (*P (A ∘ ∣_∣') f₁ p) (*P (A ∘ ∣_∣') f₁ q))
    (x : ⟦ P ⟧) → A x
  elim A f₀ f₁ f₂ ∣ x ∣' = 1Polygraph.elim (A ∘ ∣_∣') f₀ f₁ x
  elim A f₀ f₁ f₂ (∣_∣₂ {x} {y} {p} {q} α i j) = lem i j
    where
    lem' : {x y : Σ₀} (p : x ↝* y) → cong (1Polygraph.elim (A ∘ ∣_∣') f₀ f₁) ∣ p ∣* ≡ *P (A ∘ ∣_∣') f₁ p
    lem' [] = refl
    lem' (p ∷ a) =
      cong (1Polygraph.elim (A ∘ ∣_∣') f₀ f₁) ∣ p ∷ a ∣* ≡⟨ refl ⟩
      cong (1Polygraph.elim (A ∘ ∣_∣') f₀ f₁) (∣ p ∣* ∙ ∣ a ∣₁) ≡⟨ congFunct-dep' (1Polygraph.elim (A ∘ ∣_∣') f₀ f₁) ∣ p ∣* ∣ a ∣₁ ⟩
      compPathP' {B = A ∘ ∣_∣'} (cong (1Polygraph.elim (A ∘ ∣_∣') f₀ f₁) ∣ p ∣*) (cong (1Polygraph.elim (A ∘ ∣_∣') f₀ f₁) ∣ a ∣₁) ≡⟨ cong (λ p → compPathP' {B = A ∘ ∣_∣'} p (cong (1Polygraph.elim (A ∘ ∣_∣') f₀ f₁) ∣ a ∣₁)) (lem' p) ⟩
      compPathP' {B = A ∘ ∣_∣'} (*P (A ∘ ∣_∣') f₁ p) (cong (1Polygraph.elim (A ∘ ∣_∣') f₀ f₁) ∣ a ∣₁) ≡⟨ refl ⟩
      compPathP' {B = A ∘ ∣_∣'} (*P (A ∘ ∣_∣') f₁ p) (f₁ a) ≡⟨ refl ⟩
      *P (A ∘ ∣_∣') f₁ (p ∷ a) ∎
    lem : PathP (λ i → PathP (λ j → cong (cong A) ∣ α ∣₂ i j) (f₀ x) (f₀ y)) (cong (1Polygraph.elim (A ∘ ∣_∣') f₀ f₁) ∣ p ∣*) (cong (1Polygraph.elim (A ∘ ∣_∣') f₀ f₁) ∣ q ∣*)
    lem = subst2 (PathP λ i → PathP (λ j → cong (cong A) ∣ α ∣₂ i j) (f₀ x) (f₀ y)) (sym (lem' p)) (sym (lem' q)) (f₂ α)

  elimSet :
    {ℓ₂ : Level}
    (A : ⟦ P ⟧ → Type ℓ₂)
    (AS : (x : ⟦ P ⟧) → isSet (A x))
    (f₀ : (x : Σ₀) → A ∣ ∣ x ∣ ∣')
    (f₁ : {x y : Σ₀} (a : x ↝ y) → PathP (λ i → A ∣ ∣ a ∣₁ i ∣') (f₀ x) (f₀ y))
    (x : ⟦ P ⟧) → A x
  elimSet A AS f₀ f₁ x = elim A f₀ f₁ (λ α → isSet→SquareP (λ i j → AS _) _ _ _ _) x

  elimProp :
    {ℓ₂ : Level}
    (A : ⟦ P ⟧ → Type ℓ₂)
    (AP : (x : ⟦ P ⟧) → isProp (A x))
    (f₀ : (x : Σ₀) → A ∣ ∣ x ∣ ∣')
    (x : ⟦ P ⟧) → A x
  elimProp A AP f₀ x = elimSet A (λ x → isProp→isSet (AP x)) f₀ (λ a → isProp→PathP (λ _ → AP _) _ _) x

  -- rec :
    -- {ℓ₂ : Level}
    -- {A : Type ℓ₂}
    -- (f₀ : (x : Σ₀) → A)
    -- (f₁ : {x y : Σ₀} (a : x ↝ y) → f₀ x ≡ f₀ y)
    -- (f₂ : {x y : Σ₀} {p q : x ↝* y} (α : p ⇒ q) → ((f₁ *) p) ≡ ((f₁ *) q))
    -- (x : ⟦_⟧) → A
  -- rec {A = A} f₀ f₁ f₂ = elim (λ _ → A) f₀ f₁ test
    -- where
    -- test : {x y : Σ₀} {p q : x ↝* y} (α : p ⇒ q) → PathP (λ i → f₀ x ≡ f₀ y) (*P (λ _ → A) f₁ p) (*P (λ _ → A) f₁ q)
    -- test α = {!!}

  -- I think that this ought to be terminating here
  {-# TERMINATING #-}
  rec :
    {A : Type ℓ₃} →
    (f₀ : Σ₀ → A)
    (f₁ : {x y : Σ₀} → x ↝ y → f₀ x ≡ f₀ y)
    (f₂ : {x y : Σ₀} {p q : x ↝* y} → p ⇒ q → (f₁ *) p ≡ (f₁ *) q) →
    ⟦ P ⟧ → A
  rec f₀ f₁ f₂ ∣ x ∣' = 1Polygraph.rec f₁ x
  rec f₀ f₁ f₂ (∣_∣₂ {x} {y} {p} {q} α i j) = lem i j
    where
    lem' : {x y : Σ₀} (p : x ↝* y) → cong (rec f₀ f₁ f₂) ∣ p ∣*' ≡ (f₁ *) p
    lem' [] = refl
    lem' (p ∷ a) =
      cong (rec f₀ f₁ f₂) ∣ p ∷ a ∣*'                                       ≡⟨ refl ⟩
      cong (rec f₀ f₁ f₂ ∘ ∣_∣') ∣ p ∷ a ∣*                                 ≡⟨ refl ⟩
      cong (rec f₀ f₁ f₂ ∘ ∣_∣') (∣ p ∣* ∙ ∣ a ∣₁)                          ≡⟨ congFunct (rec f₀ f₁ f₂ ∘ ∣_∣') ∣ p ∣* ∣ a ∣₁ ⟩
      cong (rec f₀ f₁ f₂ ∘ ∣_∣') ∣ p ∣* ∙ cong (rec f₀ f₁ f₂ ∘ ∣_∣') ∣ a ∣₁ ≡⟨ cong (_∙ (cong (rec f₀ f₁ f₂ ∘ ∣_∣') ∣ a ∣₁)) (lem' p) ⟩
      (f₁ *) p ∙ f₁ a                                                       ∎
    lem : cong (rec f₀ f₁ f₂) ∣ p ∣*' ≡ cong (rec f₀ f₁ f₂) ∣ q ∣*'
    lem = lem' p ∙ f₂ α ∙ sym (lem' q)

  ---
  --- hom polygraph
  ---

  -- record whiskHom (x y : Σ₀) : Type _ where
    -- field
      -- whx : Σ₀
      -- why : Σ₀
      -- whp : x ↝* whx
      -- whr : why ↝* y
      -- whq : whx ↝* why
      -- whq' : whx ↝* why
      -- whα : whq ⇒ whq'

  -- hom : (x y : Σ₀) → (∣ x ∣'' ≡ ∣ y ∣'') ≃ ⟦ record { Σ₀ = x ↝* y ; _↝_ = {!!} } ⟧₁
  -- hom x y = {!!}
