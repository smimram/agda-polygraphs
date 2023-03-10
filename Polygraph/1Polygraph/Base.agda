{-# OPTIONS --cubical #-}

module 1Polygraph.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function as Fun
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws as GL
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path
open import Cubical.Data.Sum hiding (rec ; elim)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥ hiding (rec ; elim)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation as PT hiding (rec ; elim)
open import Cubical.HITs.SetTruncation as ST hiding (rec ; elim)

open import Graph

private variable
  ℓ₀ ℓ₁ ℓ₂ ℓ₃ : Level

record 1Polygraph : Type (ℓ-suc (ℓ-max ℓ₀ ℓ₁)) where
  field
    Σ₀  : Type ℓ₀
    _↝_ : Graph Σ₀ ℓ₁

module Operations (P : 1Polygraph {ℓ₀} {ℓ₁}) where
  open 1Polygraph P public

  _↝*_ = FreeCategory.FreeCategory _↝_
  _↝+_ = FreeSemicategory.FreeSemicategory _↝_
  -- _↭_  = TransReflClosure (SymClosure _↝_)
  _↭!_ = FreeGroupoid.FreeGroupoid _↝_
  _↜_ = Graph.op _↝_
  _↜+_ = Graph.op _↝+_

module _ (P : 1Polygraph {ℓ₀} {ℓ₁}) where
  open Operations P

  -- terminating
  isWF : Type _
  isWF = isWellFounded _↜_

  -- the transitive closure of reduction is well-founded
  WF+ : isWF → isWellFounded _↜+_
  WF+ wf = subst isWellFounded (FreeSemicategory.onOp _) (WFtrans _↜_ wf)

  -- normal forms

  isNF : (x : Σ₀) → Type _
  isNF x = {y : Σ₀} → x ↝+ y → ⊥

  -- testing alternative definitions of normal forms
  module test-nf where
    isNF' : (x : Σ₀) → Type _
    isNF' x = {y : Σ₀} → x ↝* y → y ↝* x

    -- WFloops : ({x : Σ₀} → x ↝+ x) → Σ₀ → ¬ isWF
    -- WFloops p x wf = induction (WF+ wf) (λ x' ih → ih x' p) x

    -- well-founded graphs don't have loops
    WFloop : isWF → {x : Σ₀} → ¬ (x ↝+ x)
    WFloop wf {x} p = lem x p
      where
      lem : (x : Σ₀) → x ↝+ x → ⊥
      lem x = induction (WF+ wf) {P = λ x → x ↝+ x → ⊥} (λ x ih q → ih x q q) x

    -- isNF'→isNF : isWF → {x : Σ₀} → isNF' x → isNF x
    -- isNF'→isNF wf n p = WFloop wf {!!} -- WFloop wf (append p (n (t→rt p)))

    -- -- This definition is closer to the traditional one but less nice than the
    -- -- above one.
    -- isNF'' : (x : Σ₀) → Type _
    -- isNF'' x = {y : Σ₀} (f : x ↝* y) → Σ (x ≡ y) (λ p → subst (λ x → x ↝* y) p f ≡ [])

    -- isNF'→isNF'' : isWF → (x : Σ₀) → isNF' x → isNF'' x
    -- isNF'→isNF'' wf x n [] = refl , {!!}
    -- isNF'→isNF'' wf x n (a ∷ p) = ⊥.rec (WFloop wf {!rt→t a p!})

  -- normalizing
  isNZ : (x : Σ₀) → Type _
  isNZ x = Σ Σ₀ λ y → x ↝* y × isNF y

  -- normalization property
  hasNZ : Type _
  hasNZ = (x : Σ₀) → isNZ x

  -- reducible
  isR : (x : Σ₀) → Type _
  isR x = (Σ Σ₀ λ y → x ↝ y)

  -- decidable reducibility
  isDR : (x : Σ₀) → Type _
  isDR x = Dec (isR x)

  -- every element has decidable reducibility
  hasDR : Type _
  hasDR = (x : Σ₀) → isDR x

  -- uniqueness of normal forms
  -- isNF : isWF → {x : Σ₀} → isNF' x → (y : Σ₀) → x ↝* y → x ≡ y
  -- isNF wf nx ny [] = refl
  -- isNF wf nx ny (a ∷ p) = ⊥.rec (WFloop wf {!!})

  -- The presented type
  data ⟦_⟧ : Type (ℓ-max ℓ₀ ℓ₁) where
    ∣_∣  : Σ₀ → ⟦_⟧
    ∣_∣₁ : {x y : Σ₀} → x ↝ y → ∣ x ∣ ≡ ∣ y ∣

  rec : {A : Type ℓ₂} {f₀ : Σ₀ → A} (f : {x y : Σ₀} → x ↝ y → f₀ x ≡ f₀ y) → ⟦_⟧ → A
  rec {f₀ = f₀} f ∣ x ∣ = f₀ x
  rec f (∣ a ∣₁ i) = f a i

  rec-comp₁ : {A : Type ℓ₂} {f₀ : Σ₀ → A} (f : {x y : Σ₀} → x ↝ y → f₀ x ≡ f₀ y) {x y : Σ₀} (a : x ↝ y) → cong (rec f) ∣ a ∣₁ ≡ f a
  rec-comp₁ f a = refl

module _ {P : 1Polygraph {ℓ₀} {ℓ₁}} where
  open Operations P

  open FreeSemicategory
  open FreeCategory hiding (elim)

  -- everybody has a normal form
  normalize : isWF P → hasDR P → hasNZ P
  normalize wf dr x = induction (WF+ P wf) {P = isNZ P} ind x
    where
    ind : (x : Σ₀) (ih : (y : Σ₀) → x ↝+ y → isNZ P y) → isNZ P x
    ind y ih with dr y
    ... | no ¬red = y , [] , λ {z} y↝*z → ¬red (dh⁺ y↝*z)
    ... | yes (y' , y↝y') with ih y' [ y↝y' ]⁺
    ... | z , y'↝z , nz = z , snoc y↝y' y'↝z , nz

  elim : (A : ⟦ P ⟧ → Type ℓ₃) (f₀ : (x : Σ₀) → A ∣ x ∣) (f : {x y : Σ₀} (a : x ↝ y) → PathP (λ i → A (∣ a ∣₁ i)) (f₀ x) (f₀ y)) (x : ⟦ P ⟧) → A x
  elim A f₀ f ∣ x ∣ = f₀ x
  elim A f₀ f (∣ a ∣₁ i) = f a i

  eta : (A : ⟦ P ⟧ → Type ℓ₃) (f : (x : ⟦ P ⟧) → A x) → elim A (λ x → f ∣ x ∣) (λ a → cong f ∣ a ∣₁) ≡ f
  eta A f = funExt (elim (λ n → elim A (λ x → f ∣ x ∣) (λ a → cong f ∣ a ∣₁) n ≡ f n) (λ x → refl) (λ {x} {y} a i → refl))

  ∣_∣* : {x y : Σ₀} → (x ↝* y) → ∣ x ∣ ≡ ∣ y ∣
  ∣ [] ∣* = refl
  ∣ p ∷ a ∣* = ∣ p ∣* ∙ ∣ p ∣₁

  _* : {A : Type ℓ₃} {f₀ : Σ₀ → A} (f : {x y : Σ₀} → x ↝ y → f₀ x ≡ f₀ y) {x y : Σ₀} → x ↝* y → f₀ x ≡ f₀ y
  (f *) [] = refl
  (f *) (p ∷ a) = (f *) p ∙ f a

  -- -- dependent version
  -- *P : (A : ⟦ P ⟧ → Type ℓ₃) {f₀ : (x : Σ₀) → A ∣ x ∣} (f : {x y : Σ₀} (α : x ↝ y) → PathP (λ i → A (∣ α ∣₁ i)) (f₀ x) (f₀ y)) {x y : Σ₀} (p : x ↝* y) → PathP (λ i → A (∣ p ∣* i)) (f₀ x) (f₀ y)
  -- *P A f [] = refl
  -- *P A f {x} {y} (a ∷ p) = compPathP' {B = A} (f a) (*P A f p)

-- module _ {ℓ : Level} {P : 1Polygraph {ℓ} {ℓ}} where
  -- open 1Operations P

  -- postulate
    -- path-elim :
      -- {x : Σ₀}
      -- (A : {y : Σ₀} (p : _≡_ {A = ⟦ P ⟧} ∣ x ∣ ∣ y ∣) → Type ℓ) →
      -- A refl →
      -- ({y z : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) (a : y ↝ z) → A p ≃ A (p ∙ ∣ a ∣₁)) →
      -- {y : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) → A p

    -- path-elim-refl :
      -- {x : Σ₀}
      -- (A : {y : Σ₀} (p : _≡_ {A = ⟦ P ⟧} ∣ x ∣ ∣ y ∣) → Type ℓ) →
      -- (Ar : A refl) →
      -- (Aa : {y z : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) (a : y ↝ z) → A p ≃ A (p ∙ ∣ a ∣₁)) →
      -- path-elim A Ar Aa refl ≡ Ar

    -- path-elim-ext :
      -- {x : Σ₀}
      -- (A : {y : Σ₀} (p : _≡_ {A = ⟦ P ⟧} ∣ x ∣ ∣ y ∣) → Type ℓ) →
      -- (Ar : A refl) →
      -- (Aa : {y z : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) (a : y ↝ z) → A p ≃ A (p ∙ ∣ a ∣₁)) →
      -- {y z : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) (a : y ↝ z) →
      -- path-elim A Ar Aa (p ∙ ∣ a ∣₁) ≡ equivFun (Aa p a) (path-elim A Ar Aa p)

  -- Prop≡ : {ℓ : Level} {A B : Type ℓ} → isProp A → isProp B → (A → B) → (B → A) → A ≡ B
  -- Prop≡ {A = A} {B = B} PA PB f g = ua (isoToEquiv e)
    -- where
    -- e : Iso A B
    -- Iso.fun e = f
    -- Iso.inv e = g
    -- Iso.rightInv e _ = PB _ _
    -- Iso.leftInv e _ = PA _ _

  -- -- ∣_∣! : {x y : Σ₀} → (x ↭! y) → ∣ x ∣ ≡ ∣ y ∣
  -- -- ∣ p ∣! = GpdClosure-elim _↝_
    -- -- (λ {x} {y} p → ∣ x ∣ ≡ ∣ y ∣)
    -- -- refl
    -- -- (λ a p → equivFun (e a) p )
    -- -- (λ a p → invEq (e a) p)
    -- -- (λ a p → retEq (e a) p)
    -- -- (λ a p → secEq (e a) p)
    -- -- (λ a p → {!!}) p
    -- -- where
    -- -- e : {x y z : Σ₀} (a : x ↝ y) → (∣ y ∣ ≡ ∣ z ∣) ≃ (∣ x ∣ ≡ ∣ z ∣)
    -- -- e a = compPathlEquiv ∣ a ∣₁

  -- ∣_∣! : {x y : Σ₀} → (x ↭! y) → ∣ x ∣ ≡ ∣ y ∣
  -- ∣_∣! {x} {y} p = GpC-elim _↝_
    -- (λ {y} p → ∣ x ∣ ≡ ∣ y ∣)
    -- refl
    -- (λ p a → equivFun (e a) p)
    -- (λ p a → invEq (e a) p)
    -- (λ p a → secEq (e a) p)
    -- (λ p a → retEq (e a) p)
    -- (λ p a → sym (commPathIsEq (snd (e a)) p))
    -- p
    -- where
    -- e : {x y z : Σ₀} (a : y ↝ z) → (∣ x ∣ ≡ ∣ y ∣) ≃ (∣ x ∣ ≡ ∣ z ∣)
    -- e a = compPathrEquiv ∣ a ∣₁

  -- Path≃GC : {x y : Σ₀} → (∣ x ∣ ≡ ∣ y ∣) ≃ x ↭! y
  -- Path≃GC {x} {y} = isoToEquiv e
    -- where
    -- e : Iso (∣ x ∣ ≡ ∣ y ∣) (x ↭! y)
    -- Iso.fun e p = path-elim (λ {y} p → x ↭! y) [] (λ {y} p a → GpCcompEquivR _↝_ x a) p
    -- Iso.inv e p = ∣ p ∣!
    -- Iso.rightInv e p = GpC-elim _↝_ RI
      -- (path-elim-refl _ _ _ )
      -- (λ {y} {z} {p} ri a → pee ∣ p ∣! a ∙ cong (_∷+ a) ri)
      -- (λ {y} {z} {p} ri a → pee' ∣ p ∣! a ∙ cong (_∷- a) ri)
      -- (λ {y} {z} {p} ri a → toPathP {!!})
      -- {!!}
      -- {!!}
      -- p
      -- where
      -- pe = path-elim (λ {y} p → x ↭! y) [] (λ {y} p a → GpCcompEquivR _↝_ x a)
      -- pee : {y z : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) (a : y ↝ z) → pe (p ∙ ∣ a ∣₁) ≡ pe p ∷+ a
      -- pee = path-elim-ext (λ {y} p → x ↭! y) [] (λ {y} p a → GpCcompEquivR _↝_ x a)
      -- pee' : {y z : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) (a : z ↝ y) → pe (p ∙ sym ∣ a ∣₁) ≡ pe p ∷- a
      -- pee' = {!!}
      -- RI : {y : Σ₀} (p : x ↭! y) → Type _
      -- RI p = pe ∣ p ∣! ≡ p
    -- Iso.leftInv e p = path-elim (λ {y} p → ∣ path-elim (λ {y} p → x ↭! y) [] (λ {y} p → GpCcompEquivR _↝_ x) p ∣! ≡ p) {!!} {!!} p

  -- -- -- zig-zags cover everything
  -- -- -- Note : I think that we could show ∥ Σ (x ↭ y) (λ q → p ≡ ∣ q ∣') ∥₁ if ↭ means quotiented by aa- = id and a-a = id
  -- -- zz-surj : {x y : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) → ∥ Σ (x ↭ y) (λ q → p ≡ ∣ q ∣') ∥₁
  -- -- zz-surj {x = x} = path-elim (λ {y} p → ∥ Σ (x ↭ y) (λ q → p ≡ ∣ q ∣') ∥₁) ∣ [] , refl ∣₁ λ p a → ua (isoToEquiv (e p a))
    -- -- where
    -- -- e : {y z : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) (a : y ↝ z) → Iso ∥ Σ (x ↭ y) (λ q → p ≡ ∣ q ∣') ∥₁ ∥ Σ (x ↭ z) (λ q → p ∙ ∣ a ∣₁ ≡ ∣ q ∣') ∥₁
    -- -- Iso.fun (e {y} p a) = PT.map λ { (q , r) → (q · [ σ+ a ]) , lem q r }
      -- -- where
      -- -- lem : (q : x ↭ y) (r : p ≡ ∣ q ∣') → p ∙ ∣ a ∣₁ ≡ ∣ q · [ σ+ a ] ∣'
      -- -- lem q r =
        -- -- p ∙ ∣ a ∣₁ ≡⟨ cong₂ _∙_ r (rUnit _) ⟩
        -- -- ∣ q ∣' ∙ (∣ a ∣₁ ∙ refl) ≡⟨ refl ⟩
        -- -- ∣ q ∣' ∙ ∣ [ σ+ a ] ∣' ≡⟨ sym (∣∣'· q [ σ+ a ]) ⟩
        -- -- ∣ q · [ σ+ a ] ∣' ∎
    -- -- Iso.inv (e {y} {z} p a) = PT.map λ { (q , r) →  (q · [ σ- a ]) , lem q r }
      -- -- where
      -- -- lem : (q : x ↭ z) (r : p ∙ ∣ a ∣₁ ≡ ∣ q ∣') → p ≡ ∣ q · [ σ- a ] ∣'
      -- -- lem q r =
        -- -- p ≡⟨ rUnit _ ⟩
        -- -- p ∙ refl ≡⟨ cong (_∙_ p) (sym (rCancel _)) ⟩
        -- -- p ∙ (∣ a ∣₁ ∙ sym ∣ a ∣₁) ≡⟨ assoc _ _ _ ⟩
        -- -- (p ∙ ∣ a ∣₁) ∙ sym ∣ a ∣₁ ≡⟨ cong₂ _∙_ r (rUnit _) ⟩
        -- -- ∣ q ∣' ∙ sym ∣ a ∣₁ ∙ refl ≡⟨ refl ⟩
        -- -- ∣ q ∣' ∙ ∣ [ σ- a ] ∣' ≡⟨ sym (∣∣'· q [ σ- a ]) ⟩
        -- -- ∣ q · [ σ- a ] ∣' ∎
    -- -- Iso.rightInv (e p a) _ = isPropPropTrunc _ _
    -- -- Iso.leftInv (e p a) _ = isPropPropTrunc _ _

  -- -- path≡₁ : (x y : Σ₀) → ∥ ∣ x ∣ ≡ ∣ y ∣ ∥₁ ≡ ∥ x ↭ y ∥₁
  -- -- path≡₁ x y =
    -- -- Prop≡ isPropPropTrunc isPropPropTrunc
      -- -- (PT.elim (λ _ → isPropPropTrunc) λ p → PT.elim (λ _ → isPropPropTrunc) (λ { (q , r) → ∣ q ∣₁ }) (zz-surj p))
      -- -- (PT.rec isPropPropTrunc λ p → ∣ ∣ p ∣' ∣₁)

  -- -- path≡₂ : (x y : Σ₀) → ∥ ∣ x ∣ ≡ ∣ y ∣ ∥₂ ≡ ∥ x ↭! y ∥₂
  -- -- path≡₂ x y = ua (isoToEquiv e)
    -- -- where
    -- -- e : Iso ∥ ∣ x ∣ ≡ ∣ y ∣ ∥₂ ∥ x ↭! y ∥₂
    -- -- Iso.fun e = ST.rec isSetSetTrunc λ p → {!!}
    -- -- Iso.inv e = ST.rec isSetSetTrunc λ p → {!!}
    -- -- Iso.rightInv e = {!!}
    -- -- Iso.leftInv e = {!!}

  -- hContr : (ℓ : Level) → Type (ℓ-suc ℓ)
  -- hContr ℓ = Σ (Type ℓ) isContr

  -- -- setTruncUniversal
  -- test : {ℓ : Level} {A : Type} → (A → hProp ℓ) ≃ (∥ A ∥₂ → hProp ℓ)
  -- test {ℓ} {A} = isoToEquiv e
    -- where
    -- e : Iso (A → hProp ℓ) (∥ A ∥₂ → hProp ℓ)
    -- Iso.fun e P a = ST.elim (λ a → isSetHProp) (λ a → P a) a
    -- Iso.inv e P a = P ∣ a ∣₂
    -- Iso.rightInv e P = funExt (ST.elim (λ a → isProp→isSet (isSetHProp _ _)) λ _ → refl)
    -- Iso.leftInv e P = refl

  -- -- test : {ℓ : Level} {A : Type} (P : A → Type ℓ) → ((x : A) → isProp (P a)) → ((a : A) → P a) → ((a : ∥ A 

  -- -- path-elim-Prop :
    -- -- {x : Σ₀}
    -- -- (A : {y : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) → Type ℓ) →
    -- -- ({y : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) → isProp (A p)) →
    -- -- ({y : Σ₀} (p : x ↭ y) → A ∣ p ∣') →
    -- -- {y : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) → A p
  -- -- path-elim-Prop {x = x} A AP Ap {y = y} p = {!!}
  -- -- -- subst {!A''!} (sym (path≡₁ x y)) {!!}
  -- -- -- subst (λ p → {!A'!}) (sym (path≡₁ _ _)) {!!}
    -- -- where
    -- -- A' : ∥ ∣ x ∣ ≡ ∣ y ∣ ∥₁ → hContr ℓ
    -- -- A' = PT.rec isPropHContr λ p → A p , {!!} , AP _ _
    -- -- A'' : ∥ ∣ x ∣ ≡ ∣ y ∣ ∥₁ → Type ℓ
    -- -- A'' p = fst (A' p)
    -- -- E : ∥ x ↭ y ∥₁ ≡ ∥ ∣ x ∣ ≡ ∣ y ∣ ∥₁
    -- -- E = sym (path≡₁ x y)
  -- -- -- path-elim A (Ap []) (λ p a → {!!}) p
    -- -- -- where
    -- -- -- lem : {y z : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) (a : y ↝ z) → A p ≡ A (p ∙ ∣ a ∣₁)
    -- -- -- lem p a = {!!}

    -- -- -- Prop≡ (AP _) (AP _) (λ t → subst A {!!} {!!}) {!!}




      -- -- Prop≡ (AP _) (AP _) {!!} {!!}
      -- -- where
      -- -- f : {y z : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) (a : y ↝ z) → A p → A (p ∙ ∣ a ∣₁)
      -- -- f = {!!}
      -- -- f' : {y z : Σ₀} (p : x ↭ y) (a : y ↝ z) → A ∣ p ∣' → A (∣ p · [ σ+ a ] ∣')
      -- -- f' p a t = {!!}
      -- -- g : A (p ∙ ∣ a ∣₁) → A p
      -- -- g = {!!}

  -- -- -- ∥∥'-ppind :
    -- -- -- -- (P : {x y : ∥_∥} (p q : x ≡ y) → Type ℓ₃) →
    -- -- -- ({x y : ∥_∥} (p q : x ≡ y) → isProp (P p q)) →
    -- -- -- ({x y : Σ₀} (p q : x ↝* y) → P ((∣_∣₁ *) p) ((∣_∣₁ *) q)) →
    -- -- -- {x y : ∥_∥} (p q : x ≡ y) → P p q
  -- -- -- ∥∥'-ppind P prop H p q = {!!}
