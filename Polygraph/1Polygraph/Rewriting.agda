{-# OPTIONS --cubical --allow-unsolved-metas #-}

module 1Polygraph.Rewriting where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma

open import Graph
open import 1Polygraph.Base
open import 1Polygraph.PathElimination

private variable
  ℓ₀ ℓ₁ ℓ₂ ℓ₃ : Level

module _ (P : 1Polygraph {ℓ₀} {ℓ₁}) where
  open Operations P

  -- terminating
  isWF : Type _
  isWF = isWellFounded _↜_

module _ {P : 1Polygraph {ℓ₀} {ℓ₁}} where
  open Operations P

  -- the transitive closure of reduction is well-founded
  WF+ : isWF P → isWellFounded _↜+_
  WF+ wf = subst isWellFounded (FreeSemicategory.onOp _) (WFtrans _↜_ wf)

  -- reducible
  isR : (x : Σ₀) → Type _
  isR x = (Σ Σ₀ λ y → x ↝ y)

  -- decidable reducibility
  isDR : (x : Σ₀) → Type _
  isDR x = Dec (isR x)

  -- normal forms
  isNF : (x : Σ₀) → Type _
  isNF x = {y : Σ₀} → x ↝+ y → ⊥

  -- alternative definitions of normal forms
  isNF' : (x : Σ₀) → Type _
  isNF' x = {y : Σ₀} → x ↝* y → y ↝* x

  module _ where
    open FreeCategory

    isNF→isNF' : {x : Σ₀} → isNF x → isNF' x
    isNF→isNF' NF [] = []
    isNF→isNF' NF (p ∷ a) = ⊥.rec (NF (toSC p a))

    -- This definition is closer to the traditional one but less nice
    isNF'' : (x : Σ₀) → Type _
    isNF'' x = {y : Σ₀} (f : x ↝* y) → Σ (x ≡ y) (λ p → subst (λ x → x ↝* y) p f ≡ [])

    module _ (wf : isWF P) where
      -- well-founded graphs don't have loops
      WFloop+ : {x : Σ₀} → ¬ (x ↝+ x)
      WFloop+ {x} p = lem x p
        where
        lem : (x : Σ₀) → x ↝+ x → ⊥
        lem x = induction (WF+ wf) {P = λ x → x ↝+ x → ⊥} (λ x ih q → ih x q q) x

      WFloop : isSet Σ₀ → {x : Σ₀} (p : x ↝* x) → p ≡ []
      WFloop S₀ {x} p = FreeCategory.elimPath (λ p → p ≡ []) lem (λ p a → ⊥.rec (WFloop+ (toSC p a))) p
        where
        lem : (q : x ≡ x) → subst⁻ (λ y → y ↝* x) q [] ≡ []
        lem q = cong (λ q → subst⁻ (λ y → y ↝* x) q []) (S₀ x x q refl) ∙ substRefl {B = λ y → y ↝* x} []

    -- isNF'→isNF : isWF → {x : Σ₀} → isNF' x → isNF x
    -- isNF'→isNF wf n p = WFloop wf {!!} -- WFloop wf (append p (n (t→rt p)))

    -- isNF'→isNF'' : isWF → (x : Σ₀) → isNF' x → isNF'' x
    -- isNF'→isNF'' wf x n [] = refl , {!!}
    -- isNF'→isNF'' wf x n (a ∷ p) = ⊥.rec (WFloop wf {!rt→t a p!})

  -- uniqueness of normal forms
  -- isNF : isWF → {x : Σ₀} → isNF' x → (y : Σ₀) → x ↝* y → x ≡ y
  -- isNF wf nx ny [] = refl
  -- isNF wf nx ny (a ∷ p) = ⊥.rec (WFloop wf {!!})

  -- normalizing
  isNZ : (x : Σ₀) → Type _
  isNZ x = Σ Σ₀ λ y → x ↝* y × isNF y

module _ (P : 1Polygraph {ℓ₀} {ℓ₁}) where
  open Operations P

  -- every element has decidable reducibility
  hasDR : Type _
  hasDR = (x : Σ₀) → isDR {P = P} x

  -- normalization property
  hasNZ : Type _
  hasNZ = (x : Σ₀) → isNZ {P = P} x

module _ {P : 1Polygraph {ℓ₀} {ℓ₁}} where
  open Operations P
  open FreeSemicategory
  open FreeCategory hiding (rec ; elim)

  -- everybody has a normal form
  normalize : isWF P → hasDR P → hasNZ P
  normalize wf dr x = induction (WF+ wf) {P = isNZ {P = P}} ind x
    where
    ind : (x : Σ₀) (ih : (y : Σ₀) → x ↝+ y → isNZ y) → isNZ x
    ind y ih with dr y
    ... | no ¬red = y , [] , λ {z} y↝*z → ¬red (dh y↝*z)
    ... | yes (y' , y↝y') with ih y' [ y↝y' ]⁺
    ... | z , y'↝z , nz = z , FreeCategory.snoc y↝y' y'↝z , nz
