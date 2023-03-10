{-# OPTIONS --cubical --allow-unsolved-metas  #-}

module 2Polygraph where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sum hiding (rec ; elim)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥ hiding (rec ; elim)
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation as PT hiding (rec ; elim)

open import Graph
open Graph.FreeCategory hiding (elim)
open import 1Polygraph renaming (⟦_⟧ to ⟦_⟧₁) hiding (module Operations ; rec ; elim)

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

module _ (P : 2Polygraph {ℓ₀} {ℓ₁} {ℓ₂}) where
  open Operations P

  data _⇒w_ : {x y : Σ₀} → (x ↝* y) → (x ↝* y) → Type (ℓ-max ℓ₀ (ℓ-max ℓ₁ ℓ₂)) where
    whisk  : {x' x y y' : Σ₀} → (p : x' ↝* x) {q q' : x ↝* y} (α : q ⇒ q') (r : y ↝* y') → (p · q · r) ⇒w (p · q' · r)
    whisk⁻ : {x' x y y' : Σ₀} → (p : x' ↝* x) {q q' : x ↝* y} (α : q ⇒ q') (r : y ↝* y') → (p · q' · r) ⇒w (p · q · r)

  infix 4 _⇔*_

  -- TODO: rather use the groupoid closure
  _⇔*_ : {x y : Σ₀} (p q : x ↝* y) → Type (ℓ-max ℓ₀ (ℓ-max ℓ₁ ℓ₂))
  _⇔*_ = FreeCategory _⇒w_

  whiskAssoc : {x'' x' x y y' y'' : Σ₀} (p' : x'' ↝* x') (p : x' ↝* x) (q : x ↝* y) (r : y ↝* y') (r' : y' ↝* y'') → p' · (p · q · r) · r' ≡ (p' · p) · q · (r · r')
  whiskAssoc p' p q r r' =
    p' · (p · q · r) · r'   ≡⟨ cong (λ p → p' · p) (FreeCategory.assoc p _ r') ⟩
    p' · (p · (q · r) · r') ≡⟨ sym (FreeCategory.assoc p' p _) ⟩
    (p' · p) · (q · r) · r' ≡⟨ cong (λ q → (p' · p) · q) (FreeCategory.assoc q _ r') ⟩
    (p' · p) · q · (r · r') ∎

  whisk* : {x' x y y' : Σ₀} → (p : x' ↝* x) {q q' : x ↝* y} (ϕ : q ⇔* q') (r : y ↝* y') → (p · q · r) ⇔* (p · q' · r)
  whisk* p [] q = []
  whisk* p (ϕ ∷ whisk p' α r') r = whisk* p ϕ r · [≡ whiskAssoc p p' _ r' r ] · [ whisk (p · p') α (r' · r) ] · [≡ sym (whiskAssoc p p' _ r' r) ]
  whisk* p (ϕ ∷ whisk⁻ p' α r') r = whisk* p ϕ r · [≡ whiskAssoc p p' _ r' r ] · [ whisk⁻ (p · p') α (r' · r) ] · [≡ sym (whiskAssoc p p' _ r' r) ]

  -- local confluence
  isLC : (x : Σ₀) → Type _
  isLC x = {y y' : Σ₀} (a : x ↝ y) (b : x ↝ y') →
           Σ[ z ∈ Σ₀ ]
           Σ[ p ∈ y  ↝* z ]
           Σ[ q ∈ y' ↝* z ]
           ([ a ] · p) ⇔* ([ b ] · q)

  hasLC = {x : Σ₀} → isLC x

  -- confluence
  isC : (x : Σ₀) → Type _
  isC x = {y y' : Σ₀} (p : x ↝* y) (q : x ↝* y') →
          Σ[ z ∈ Σ₀ ]
          Σ[ p' ∈ y  ↝* z ]
          Σ[ q' ∈ y' ↝* z ]
          (p · p') ⇔* (q · q')

  hasC = {x : Σ₀} → isC x

  -- Newman's lemma
  newman : isWF Σ' → hasLC → hasC
  newman wf lc {x = x} = induction (WF+ wf) {P = isC} (λ x ih → lem x ih) x
    where
    lem : (x : Σ₀) → ((y : Σ₀) → y ↜+ x → isC y) → isC x
    lem x ih [] q = _ , q , [] , [≡ sym (FreeCategory.lUnit q) ]
    lem x ih (p ∷ a) [] = _ , [] , p ∷ a , [≡ cong (λ p → p ∷ a) (FreeCategory.lUnit p) ]
    lem x ih (p ∷ a) (q ∷ b) = {!!}
    -- lem x ih [] q = _ , q , [] , [≡ sym (·-unitr _) ]
    -- lem x ih (x↝y ∷ p) [] = _ , [] , (x↝y ∷ p) , [≡ cong (λ p → x↝y ∷ p) (·-unitr p) ]
    -- lem x ih (x↝y₁ ∷ y₁↝y₁') (x↝y₂ ∷ y₂↝y₂') with lc x↝y₁ x↝y₂
    -- ... | z , y₁↝z , y₂↝z , x↝y₁↝z⇔x↝y₂↝z with ih _ [ x↝y₁ ]⁺ y₁↝y₁' y₁↝z
    -- ... | z₁ , y₁'↝z₁ , z↝z₁ , y₁↝y₁'↝z₁⇔y₁↝z↝z₁ with ih _ [ x↝y₂ ]⁺ (y₂↝z · z↝z₁) y₂↝y₂'
    -- ... | z' , z₁↝z' , y₂'↝z' , y₂↝z₁↝z'⇔y₂↝y₂'↝z' = z' , y₁'↝z₁ · z₁↝z' , y₂'↝z' ,
      -- ([≡ cong (λ p → x↝y₁ ∷ p) (sym (·-assoc y₁↝y₁' _ _)) ] ·
      -- whisk* [ x↝y₁ ] y₁↝y₁'↝z₁⇔y₁↝z↝z₁ z₁↝z' ·
      -- [≡ cong (λ p → x↝y₁ ∷ p) (·-assoc y₁↝z _ _) ] ·
      -- whisk* [] x↝y₁↝z⇔x↝y₂↝z (z↝z₁ · z₁↝z') ·
      -- [≡ cong (λ p → x↝y₂ ∷ p) (sym (·-assoc y₂↝z _ _) ∙ sym (·-unitr _)) ] ·
      -- whisk* [ x↝y₂ ] y₂↝z₁↝z'⇔y₂↝y₂'↝z' [] ·
      -- [≡ cong (λ p → x↝y₂ ∷ p) (·-unitr _) ])

  -- homotopy basis with normal targets
  hasNHB = {x y : Σ₀} → isNF {P = Σ'} y → (p q : x ↝* y) → p ⇔* q

  -- homotopy basis
  hasHB = {x y : Σ₀} → (p q : x ↝* y) → p ⇔* q

  -- confluence implies homotopy basis with normal targets
  CNHB : isSet Σ₀ → hasC → hasNHB
  CNHB = {!!}
  -- CNHB is confl ny p q with confl p q
  -- ... | z , a ∷ y↝z , y↝z' , p⇔q = ⊥.rec (ny (rt→t a y↝z))
  -- ... | z , [] , y↝z' , p⇔q with ∷-destruct y↝z'
  -- ... | inl (z≡z , y↝z'≡[]) = [≡ sym (·-unitr p) ] · p⇔q · [≡ cong (λ p → q · p) lem' ∙ ·-unitr q ]
    -- where
    -- lem : z≡z ≡ refl
    -- lem = is z z z≡z refl
    -- lem' : y↝z' ≡ []
    -- lem' = subst (λ p → PathP (λ i → p i ↝* z) y↝z' []) lem y↝z'≡[]
  -- ... | inr (_ , a , r , y↝z'≡a∷r) = ⊥.rec (ny (rt→t a r))

  -- local confluence implies coherence
  HB : isSet Σ₀ → isWF Σ' → hasDR Σ' → hasLC → hasHB
  HB is wf dr lc {x} {y} p q = {!!}
    where
    C : hasC
    C = newman wf lc
    NZ : hasNZ Σ'
    NZ = normalize wf dr
    NHB : hasNHB
    NHB = CNHB is C
    z : Σ₀
    z = NZ y .fst
    nz : isNF z
    nz = NZ y .snd .snd
    r : y ↝* z
    r = NZ y .snd .fst
    ϕ : p · r ⇔* q · r
    ϕ = NHB nz (p · r) (q · r)

  -- data ∥_∥ : Type (ℓ-max ℓ₀ (ℓ-max ℓ₁ ℓ₂)) where
    -- ∣_∣ : ∥_∥' → ∥_∥
    -- ∣_∣₂ : {x y : Σ₀} {p q : x ↝* y} → cong ∣_∣ ∣ p ∣* ≡ cong ∣_∣ ∣ q ∣*

  --- TODO: we cannot define the presented category at once because the output
  --- type of ∣_∣* uses constructors from pres...
  -- data pres : Type (ℓ-max ℓ₀ (ℓ-max ℓ₁ ℓ₂))
  -- ∣_∣* : {x y : Σ₀} → (x ↝* y) → ∣ x ∣ ≡ ∣ y ∣

  -- data pres : Type (ℓ-max ℓ₀ (ℓ-max ℓ₁ ℓ₂))
  -- ∣_∣* : {x y : Σ₀} → (x ↝* y) → inj x ≡ inj y

  -- data pres where
    -- inj : Σ₀ → pres

  data ⟦_⟧ : Type (ℓ-max (ℓ-max ℓ₀ ℓ₁) ℓ₂) where
    ∣_∣' : ⟦ Σ' ⟧₁ → ⟦_⟧
    ∣_∣₂ : {x y : Σ₀} {p q : x ↝* y} → p ⇒ q → cong ∣_∣' ∣ p ∣* ≡ cong ∣_∣' ∣ q ∣*

  -- -- I think that this ought to be terminating here (and in fact induction below, is terminating...)
  -- {-# TERMINATING #-}
  -- rec :
    -- {A : Type ℓ₃} →
    -- {f₀ : Σ₀ → A}
    -- (f₁ : {x y : Σ₀} → x ↝ y → f₀ x ≡ f₀ y)
    -- (f₂ : {x y : Σ₀} {p q : x ↝* y} → p ⇒ q → (f₁ *) p ≡ (f₁ *) q) →
    -- ⟦_⟧ → A
  -- rec f₁ f₂ ∣ x ∣' = 1Pol.rec Σ' f₁ x
  -- rec f₁ f₂ (∣_∣₂ {x} {y} {p} {q} α i j) = lem i j
    -- where
    -- lem' : {x y : Σ₀} (p : x ↝* y) → cong (rec f₁ f₂) (cong ∣_∣' ∣ p ∣*) ≡ (f₁ *) p
    -- lem' [] = refl
    -- lem' (a ∷ p) =
      -- cong (rec f₁ f₂) (cong ∣_∣' (∣ a ∣₁ ∙ ∣ p ∣*))                        ≡⟨ refl ⟩
      -- cong (rec f₁ f₂ ∘ ∣_∣') (∣ a ∣₁ ∙ ∣ p ∣*)                             ≡⟨ congFunct (rec f₁ f₂ ∘ ∣_∣') ∣ a ∣₁ ∣ p ∣* ⟩
      -- cong (rec f₁ f₂ ∘ ∣_∣') ∣ a ∣₁ ∙ cong (rec f₁ f₂ ∘ ∣_∣') ∣ p ∣*       ≡⟨ cong (λ p → cong (rec f₁ f₂ ∘ ∣_∣') ∣ a ∣₁ ∙ p) (lem' p) ⟩
      -- cong (rec f₁ f₂ ∘ ∣_∣') ∣ a ∣₁ ∙ (f₁ *) p                             ≡⟨ refl ⟩
      -- cong (1Pol.rec Σ' f₁) ∣ a ∣₁ ∙ (f₁ *) p                         ≡⟨ refl ⟩
      -- f₁ a ∙ (f₁ *) p                                                       ∎
    -- lem : cong (rec f₁ f₂) (cong ∣_∣' ∣ p ∣*) ≡ cong (rec f₁ f₂) (cong ∣_∣' ∣ q ∣*)
    -- lem = lem' p ∙ f₂ α ∙ sym (lem' q)

  congFunct-dep' : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {x y z : A} (f : (a : A) → B a) (p : x ≡ y) (q : y ≡ z) → cong f (p ∙ q) ≡ compPathP' {B = B} (cong f p) (cong f q)
  congFunct-dep' {A = A} {B = B} f p q = J (λ y p → {z : A} (q : y ≡ z) → cong f (p ∙ q) ≡ compPathP' {B = B} (cong f p) (cong f q)) lem p q
    where
    lem : {y z : A} (q : y ≡ z) → cong f (refl ∙ q) ≡ compPathP' {B = B} (cong f refl) (cong f q)
    -- lem {y} {z} q =
      -- cong f (refl ∙ q) ≡⟨ {!!} ⟩
      -- subst (λ p → PathP (λ i → B (p i)) (f y) (f z)) (lUnit q) (cong f q) ≡⟨ {!!} ⟩
      -- compPathP' {B = B} refl (cong f q) ≡⟨ refl ⟩
      -- compPathP' {B = B} (cong f refl) (cong f q) ∎
    lem = J (λ z q → cong f (refl ∙ q) ≡ compPathP' {B = B} (cong f refl) (cong f q)) lem'
      where
      lem' : cong f (refl ∙ refl) ≡ compPathP' {B = B} (cong f refl) (cong f refl)
      lem' =
        cong f (refl ∙ refl) ≡⟨ {!!} ⟩
        compPathP' {B = B} refl refl ≡⟨ refl ⟩
        compPathP' {B = B} (cong f refl) (cong f refl) ∎

  -- the induction principle
  elim :
    {ℓ₂ : Level}
    (A : ⟦_⟧ → Type ℓ₂) →
    (f₀ : (x : Σ₀) → A ∣ ∣ x ∣ ∣')
    (f₁ : {x y : Σ₀} (a : x ↝ y) → PathP (λ i → A ∣ ∣ a ∣₁ i ∣') (f₀ x) (f₀ y))
    (f₂ : {x y : Σ₀} {p q : x ↝* y} (α : p ⇒ q) → PathP (λ i → PathP (λ j → cong (cong A) ∣ α ∣₂ i j) (f₀ x) (f₀ y)) (*P (A ∘ ∣_∣') f₁ p) (*P (A ∘ ∣_∣') f₁ q))
    (x : ⟦_⟧) → A x
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

  -- -- -- in order to show a property about points it is enough to show it on
  -- -- -- constructible ones
  -- -- ∥∥-point : (A : (x : ⟦_⟧) → Type ℓ₂) →
            -- -- ((x : ∥_∥) → isProp (A x)) →
            -- -- ((x : Σ₀) → A ∣ ∣ x ∣ ∣') →
            -- -- (x : ∥_∥) → A x
  -- -- ∥∥-point A P H x = ∥∥-ind A H (λ _ → toPathP (P _ _ _))
    -- -- {!!} -- by (dependent variant of) P
    -- -- x

  -- -- -- in order to show a property about paths it is enough to show it on
  -- -- -- constructible paths
  -- -- ∥∥-path : (A : {x y : ∥_∥} (p : x ≡ y) → Type ℓ₂) →
           -- -- ({x y : ∥_∥} (p : x ≡ y) → isProp (A p)) →
           -- -- ({x y : Σ₀} (p : x ↝* y) → A (cong ∣_∣' ∣ p ∣*)) →
           -- -- {x y : ∥_∥} (p : x ≡ y) → A p
  -- -- ∥∥-path A P H {x} {y} p = {!!}

