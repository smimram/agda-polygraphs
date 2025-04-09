{-# OPTIONS --cubical -W noUnsupportedIndexedMatch --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Unit renaming (Unit* to ⊤*)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation

module 1Polygraph where

import 0Polygraph as 0Pol

private variable
  ℓ : Level

-- A 1-polygraph
record Polygraph {ℓ : Level} : Type (ℓ-suc ℓ) where
  constructor polygraph
  field
    pred : 0Pol.Polygraph {ℓ}
    gen  : 0Pol.sphere pred → Type ℓ

open Polygraph public

0Polygraph = 0Pol.Polygraph

degenerate : 0Polygraph {ℓ} → Polygraph {ℓ}
degenerate P = polygraph P (λ _ → ⊥*)

-- add-gen : (P : Polygraph) → (0Pol.sphere (pred P) → Type ℓ) → Polygraph {ℓ}
-- add-gen P f = polygraph (pred P) (λ s → gen P s ⊎ f s)

-- add-gen-empty : (P : Polygraph {ℓ}) → add-gen (degenerate (pred P)) (gen P) ≡ P
-- add-gen-empty P = cong₂ polygraph refl (funExt λ s → ua ⊎-IdL-⊥*-≃)

-- add-gen-sym : (P : Polygraph {ℓ}) (f g : _) → add-gen (add-gen P f) g ≡ add-gen (add-gen P g) f
-- add-gen-sym P f g = cong₂ polygraph refl (funExt λ s → ua ⊎-assoc-≃ ∙ cong (λ X → gen P s ⊎ X) (ua ⊎-swap-≃) ∙ sym (ua ⊎-assoc-≃))

module _ (P : Polygraph {ℓ}) where

  0sphere = 0Pol.sphere (pred P)
  0sphere-src = 0Pol.sphere-src (pred P)
  0sphere-tgt = 0Pol.sphere-tgt (pred P)
  0sphere-op = 0Pol.sphere-op (pred P)

  -- A cell in the 1-polygraph
  data cell : 0sphere → Type ℓ where
    id   : (x : pred P) → cell (x , x)
    cons : {x y z : pred P} (a : gen P (x , y)) (f : cell (y , z)) → cell (x , z)
    cons' : {x y z : pred P} (a : gen P (y , x)) (f : cell (y , z)) → cell (x , z)

  comp0 : {x y z : pred P} → cell (x , y) → cell (y , z) → cell (x , z)
  comp0 (id _) g = g
  comp0 (cons a f) g = cons a (comp0 f g)
  comp0 (cons' a f) g = cons' a (comp0 f g)

  comp0-assoc : {x y z w : pred P} (f : cell (x , y)) (g : cell (y , z)) (h : cell (z , w)) → comp0 (comp0 f g) h ≡ comp0 f (comp0 g h)
  comp0-assoc (id _) g h = refl
  comp0-assoc (cons a f) g h = cong (cons a) (comp0-assoc f g h)
  comp0-assoc (cons' a f) g h = cong (cons' a) (comp0-assoc f g h)

  comp0-unitl : {x y : pred P} (f : cell (x , y)) → comp0 (id x) f ≡ f
  comp0-unitl f = refl

  comp0-unitr : {x y : pred P} (f : cell (x , y)) → comp0 f (id y) ≡ f
  comp0-unitr (id _) = refl
  comp0-unitr (cons a f) = cong (cons a) (comp0-unitr f)
  comp0-unitr (cons' a f) = cong (cons' a) (comp0-unitr f)

  cell-gen : {s : 0sphere} → gen P s → cell s
  cell-gen a = cons a (id _)

  cell-gen' : {s : 0sphere} → gen P s → cell (0sphere-op s)
  cell-gen' a = cons' a (id _)

  snoc : {x y z : pred P} → gen P (y , z) → cell (x , y) → cell (x , z)
  snoc a (id _) = cell-gen a
  snoc a (cons b f) = cons b (snoc a f)
  snoc a (cons' b f) = cons' b (snoc a f)

  snoc' : {x y z : pred P} → gen P (z , y) → cell (x , y) → cell (x , z)
  snoc' a (id _) = cons' a (id _)
  snoc' a (cons b f) = cons b (snoc' a f)
  snoc' a (cons' b f) = cons' b (snoc' a f)

  -- Opposite of a cell
  cell-op : {s : 0sphere} → cell s → cell (0sphere-op s)
  cell-op (id x) = id x
  cell-op (cons a f) = snoc' a (cell-op f)
  cell-op (cons' a f) = snoc a (cell-op f)

  -- A sphere in the 1-polygraph
  sphere : Type ℓ
  sphere = Σ 0sphere (λ s → cell s × cell s)

  sphere-pred : sphere → 0sphere
  sphere-pred = fst

  sphere-src : (s : sphere) → cell (sphere-pred s)
  sphere-src s = fst (snd s)

  sphere-tgt : (s : sphere) → cell (sphere-pred s)
  sphere-tgt s = snd (snd s)

  context : 0sphere → 0sphere → Type ℓ
  context (x , y) (x' , y') = cell (x' , x) × cell (y , y')

  substitute : {s t : 0sphere} → cell s → context s t → cell t
  substitute g (f , h) = comp0 f (comp0 g h)

  context-id : {s : 0sphere} → context s s
  context-id = id _ , id _

  context-comp : {s t u : 0sphere} → context s t → context t u → context s u
  context-comp (f , g) (f' , g') = comp0 f' f , comp0 g g'

  substitute-id : {s : 0sphere} (f : cell s) → substitute f context-id ≡ f
  substitute-id f = comp0-unitr f

  substitute-comp :
    {s t u : 0sphere} (f : cell s) (c : context s t) (d : context t u) →
    substitute f (context-comp c d) ≡ substitute (substitute f c) d
  substitute-comp g (f , h) (f' , h') =
    comp0 (comp0 f' f) (comp0 g (comp0 h h')) ≡⟨ comp0-assoc f' _ _ ⟩
    comp0 f' (comp0 f (comp0 g (comp0 h h'))) ≡⟨ cong (comp0 f') (cong (comp0 f) (sym (comp0-assoc g h h'))) ⟩
    comp0 f' (comp0 f (comp0 (comp0 g h) h')) ≡⟨ cong (comp0 f') (sym (comp0-assoc f _ _)) ⟩
    comp0 f' (comp0 (comp0 f (comp0 g h)) h') ∎

  -- The presented type (geometric realization)
  data pres : Type ℓ where
    pres-pred : pred P → pres
    disk      : {s : 0sphere} → gen P s → pres-pred (0sphere-src s) ≡ pres-pred (0sphere-tgt s)

  pres-elim :
    {ℓ' : Level} (A : pres → Type ℓ') →
    (p : (x : pred P) → A (pres-pred x)) →
    ({s : 0sphere} (a : gen P s) → PathP (λ i → A (disk a i)) (p (0sphere-src s)) (p (0sphere-tgt s))) →
    (x : pres) → A x
  pres-elim A p q (pres-pred x) = p x
  pres-elim A p q (disk a i) = q a i

  pres-rec :
    {ℓ' : Level} {A : Type ℓ'}
    (p : (pred P) → A) →
    ({s : 0sphere} → (gen P s) → p (0sphere-src s) ≡ p (0sphere-tgt s)) →
    pres → A
  pres-rec {A = A} = pres-elim λ _ → A

  -- Realization of a cell into the presented type
  pres-cell : {s : 0sphere} → cell s → pres-pred (0sphere-src s) ≡ pres-pred (0sphere-tgt s)
  pres-cell (id x) = refl
  pres-cell (cons a f) = disk a ∙ pres-cell f
  pres-cell (cons' a f) = sym (disk a) ∙ pres-cell f

  cell-pres = pres-cell

  -- -- There is a cell between any two elements of the presented set
  -- -- TODO: we would need Kraus-von Raummer for this
  -- coh-cell : {(x , y) : 0sphere} (p : ∣ pres-pred x ∣₂ ≡ ∣ pres-pred y ∣₂) → ∥ cell (x , y) ∥₁
  -- coh-cell p = PT.elim (λ _ → isPropPropTrunc) (λ p → {!!}) (invEq propTrunc≃Trunc1 ((Iso.fun (PathIdTruncIso 1) (cong (equivFun setTrunc≃Trunc2) p))))

  -- Any element of the presented set has a representative
  has-repr : (x : ∥ pres ∥₂) → ∥ Σ (pred P) (λ y → ∣ pres-pred y ∣₂ ≡ x) ∥₁
  has-repr = ST.elim (λ _ → isProp→isSet isPropPropTrunc) (pres-elim (λ x → ∥ Σ (pred P) (λ y → ∣ pres-pred y ∣₂ ≡ ∣ x ∣₂) ∥₁) (λ x → ∣ x , refl ∣₁) λ x → toPathP (isPropPropTrunc _ _))

  ---
  --- Tietze transformations
  ---

  tietze0 : (X : Type ℓ) → (X → pred P) → Polygraph {ℓ}
  tietze0 X f = polygraph (pred P ⊎ X) g
    where
    g : 0Pol.sphere (pred P ⊎ X) → Type ℓ
    g (inl x , inl y) = gen P (x , y)
    g (inl x , inr y) = x ≡ f y
    g (inr x , _) = ⊥*

  -- Canonical 1-genertor associated to an added 0-generator
  tietze0gen : {X : Type ℓ} (f : X → pred P) (x : X) → gen (tietze0 X f) (inl (f x) , inr x)
  tietze0gen f x = refl

  tietze1 : (f : 0sphere → Type ℓ) → ({s : 0sphere} → f s → cell s) → Polygraph {ℓ}
  -- tietze1 f _ = add-gen P f
  tietze1 f g = polygraph (pred P) g'
    where
    g' : 0Pol.sphere (pred P) → Type ℓ
    g' s = gen P s ⊎ f s

data tietze {ℓ : Level} : Polygraph {ℓ} → Polygraph {ℓ} → Type (ℓ-suc ℓ) where
  T0  : (P : Polygraph) (X : Type _) (f : X → pred P) → tietze P (tietze0 P X f)
  T0' : (P : Polygraph) (X : Type _) (f : X → pred P) → tietze (tietze0 P X f) P
  T1  : (P : Polygraph) (f : 0sphere P → Type ℓ) (g : {s : 0sphere P} → f s → cell P s) → tietze P (tietze1 P f g)
  T1' : (P : Polygraph) (f : 0sphere P → Type ℓ) (g : {s : 0sphere P} → f s → cell P s) → tietze (tietze1 P f g) P
  Tr  : {P : Polygraph} → tietze P P
  Tt  : {P Q R : Polygraph} → tietze P Q → tietze Q R → tietze P R

T≡ : {P Q : Polygraph {ℓ}} → P ≡ Q → tietze P Q
T≡ {P = P} p = subst (tietze P) p Tr

module _ (P : Polygraph {ℓ}) where

  tietze0-correct : (X : Type ℓ) (f : X → pred P) → ∥ pres P ∥₂ ≡ ∥ pres (tietze0 P X f) ∥₂
  tietze0-correct X f = ua (isoToEquiv e)
    where
    Q = tietze0 P X f
    F : pres P → pres Q
    F = pres-rec _ (λ x → pres-pred (inl x)) (λ a → disk a)
    G : pres Q → pres P
    G = pres-rec _ p q
      where
      p : pred Q → pres P
      p (inl x) = pres-pred x
      p (inr x) = pres-pred (f x)
      q : {s : 0sphere Q} → gen Q s → p (0sphere-src Q s) ≡ p (0sphere-tgt Q s)
      q {s = inl x , inl y} a = disk a
      q {s = inl x , inr y} a = cong pres-pred a
    open Iso
    e : Iso ∥ pres P ∥₂ ∥ pres Q ∥₂
    F' = ST.map F
    G' = ST.map G
    e .fun = F'
    e .inv = G'
    e .rightInv = ST.elim (λ _ → isProp→isSet (isSetSetTrunc _ _)) (pres-elim Q (λ x → F' (G' ∣ x ∣₂) ≡ ∣ x ∣₂) p (λ _ → toPathP (isSetSetTrunc _ _ _ _)))
      where
      p : (x : pred Q) → F' (G' ∣ pres-pred x ∣₂) ≡ ∣ pres-pred x ∣₂
      p (inl x) = refl
      p (inr x) = cong ∣_∣₂ (disk refl)
    e .leftInv = ST.elim (λ _ → isProp→isSet (isSetSetTrunc _ _)) (pres-elim P (λ x → G' (F' ∣ x ∣₂) ≡ ∣ x ∣₂) (λ _ → refl) λ _ → toPathP (isSetSetTrunc _ _ _ _))

  tietze1-correct : (f : 0sphere P → Type ℓ) → (g : {s : 0sphere P} → f s → cell P s) → ∥ pres P ∥₂ ≡ ∥ pres (tietze1 P f g) ∥₂
  tietze1-correct f g = ua (isoToEquiv e)
    where
    Q = tietze1 P f g
    F : pres P → pres Q
    F = pres-rec P pres-pred (λ a → disk (inl a))
    G : pres Q → pres P
    G = pres-rec Q pres-pred p
      where
      p : {s : 0sphere Q} → gen Q s → pres-pred (0sphere-src Q s) ≡ pres-pred (0sphere-tgt Q s)
      p (inl a) = disk a
      p (inr a) = pres-cell P (g a)
    F' = ST.map F
    G' = ST.map G
    open Iso
    e : Iso ∥ pres P ∥₂ ∥ pres Q ∥₂
    e .fun = F'
    e .inv = G'
    e .rightInv = ST.elim (λ _ → isProp→isSet (isSetSetTrunc _ _)) (pres-elim Q (λ x → F' (G' ∣ x ∣₂) ≡ ∣ x ∣₂) (λ _ → refl) λ _ → toPathP (isSetSetTrunc _ _ _ _))
    e .leftInv = ST.elim (λ _ → isProp→isSet (isSetSetTrunc _ _)) (pres-elim P (λ x → G' (F' ∣ x ∣₂) ≡ ∣ x ∣₂) (λ _ → refl) λ _ → toPathP (isSetSetTrunc _ _ _ _))

-- Correctness of Tietze transformations (see below for another proof)
tietze-correct : {P Q : Polygraph {ℓ}} → tietze P Q → ∥ pres P ∥₂ ≡ ∥ pres Q ∥₂
tietze-correct (T0 P X f) = tietze0-correct P X f
tietze-correct (T1 P f g) = tietze1-correct P f g
tietze-correct (T0' P X f) = sym (tietze0-correct P X f)
tietze-correct (T1' P f g) = sym (tietze1-correct P f g)
tietze-correct Tr = refl
tietze-correct (Tt r s) = tietze-correct r ∙ tietze-correct s

poly≡ : {P Q : Polygraph {ℓ}} (f0 : pred P ≡ pred Q) (f1 : (s : 0sphere P) → gen P s ≡ gen Q (transport f0 (fst s) , transport f0 (snd s))) → P ≡ Q
poly≡ f0 f1 = {!!}

-- T1 under Grothendieck duality
module _ {ℓ : Level} (P : Polygraph {ℓ}) {X : Type ℓ} (f : X → 0sphere P) (g : (x : X) → cell P (f x)) where
  gen1alt : 0sphere P → Type ℓ
  gen1alt s = gen P s ⊎ fiber f s

  tietze1alt : Polygraph {ℓ}
  tietze1alt = polygraph (pred P) gen1alt

  T1alt : tietze P tietze1alt
  T1alt = subst (tietze P) p T1alt'
    where
    g' : {s : 0sphere P} → fiber f s → cell P s
    g' (x , p) = subst (cell P) p (g x)
    T1alt' : tietze P (tietze1 P (fiber f) g')
    T1alt' = T1 P (fiber f) g'
    p : tietze1 P (fiber f) g' ≡ tietze1alt
    p = poly≡ refl lem
      where
      lem : (s : 0sphere (tietze1 P (fiber f) g')) → gen (tietze1 P (fiber f) g') s ≡ gen1alt (transport refl (fst s) , transport refl (snd s))
      lem (x , y) = cong gen1alt (cong₂ {C = λ x y → 0sphere P} (λ x y → x , y) (sym (transportRefl x)) (sym (transportRefl y)))

module _ where
  private
    postulate AC : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} → ((a : A) → ∥ B a ∥₁) → ∥ ((a : A) → B a) ∥₁

  tietze-complete : {P Q : Polygraph {ℓ}} → ∥ pres P ∥₂ ≡ ∥ pres Q ∥₂ → ∥ tietze P Q ∥₁
  tietze-complete {ℓ = ℓ} {P = P} {Q = Q} p = ST-rec-fun isPropPropTrunc (λ f → ST-rec-fun isPropPropTrunc (λ g → ∣ lem ∣₁) g) f
    where
    ST-rec-fun : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → isProp C → ((A → B) → C) → (A → ∥ B ∥₁) → C
    ST-rec-fun PC f f' = PT.rec PC f (AC f')
    pres→pred : {P : Polygraph {ℓ}} → pres P → ∥ pred P ∥₁
    pres→pred = pres-rec _ ∣_∣₁ (λ _ → isPropPropTrunc _ _)
    pres→pred' : {P : Polygraph {ℓ}} → ∥ pres P ∥₂ → ∥ pred P ∥₁
    pres→pred' = ST.rec (isProp→isSet isPropPropTrunc) pres→pred
    
    f'' : pres P → ∥ pres Q ∥₂
    f'' x = transport p ∣ x ∣₂
    f' : pred P → ∥ pres Q ∥₂
    f' x = f'' (pres-pred x)
    f : pred P → ∥ pred Q ∥₁
    -- f x = pres→pred' (f' x)
    f x = pres→pred' (transport p ∣ pres-pred x ∣₂)

    lem : tietze P Q
    lem = Tt
      (T0 P (pred Q) (λ y → fst (G y))) (Tt
      (T1alt P' {X = Q1} f1 g1) (Tt
      (T1 {!!} {!!} {!!}) (Tt
      (T≡ {!!})
      (T0' Q (pred P) λ x → fst (F x)))))
      where
      postulate F : (x : pred P) → Σ (pred Q) (λ y → transport p ∣ pres-pred x ∣₂ ≡ ∣ pres-pred y ∣₂)
      postulate G : (y : pred Q) → Σ (pred P) (λ x → transport (sym p) ∣ pres-pred y ∣₂ ≡ ∣ pres-pred x ∣₂)
      P' = tietze0 P (pred Q) (λ y → fst (G y))
      Q1 = Σ (0sphere Q) (gen Q)
      f1 : Q1 → 0sphere P'
      f1 ((x , y) , _) = inr x , inr y
      g1 : (x : Q1) → cell P' (f1 x)
      g1 ((x , y) , a) =
        comp0 P' {y = inl (fst (G x))}
        (cell-gen' _ refl) (comp0 _ {y = inl (fst (G y))}
        {!!} -- by the second component of G, both are in the same connected component and thus exists is an equality and thus a 1-cell
        (cell-gen _ refl))
      
    g'' : pres Q → ∥ pres P ∥₂
    g'' x = transport (sym p) ∣ x ∣₂
    g' : pred Q → ∥ pres P ∥₂
    g' x = g'' (pres-pred x)
    g : pred Q → ∥ pred P ∥₁
    g x = pres→pred' (g' x)

    -- g''-pres-pred : (x : pred Q) → g'' (pres-pred x) ≡ g' x
    -- g''-pres-pred x = refl

    -- g''-f'' : (x : pres P) → ST.rec isSetSetTrunc g'' (f'' x) ≡ ∣ x ∣₂
    -- g''-f'' x = {!!}

    -- g''-f' : (x : pred P) → ST.rec isSetSetTrunc g'' (f' x) ≡ ∣ pres-pred x  ∣₂
    -- g''-f' x = {!!}

--- Functors between polygraphs
---

-- A functor is a "Kleisli graph morphism" which associates to every 1-generator a 1-cell 
record functor {ℓ : Level} (P Q : Polygraph {ℓ}) : Type ℓ where
  constructor func
  field
    func-pred : 0Pol.functor (pred P) (pred Q)
    func-fun  : {s : 0sphere P} → gen P s → cell Q (0Pol.functor-sphere func-pred s)

open functor public

functor-0sphere : {P Q : Polygraph {ℓ}} → functor P Q → 0sphere P → 0sphere Q
functor-0sphere f = 0Pol.functor-sphere (func-pred f)

-- Identity functor
functor-id : {P : Polygraph {ℓ}} → functor P P
functor-id = func 0Pol.functor-id (cell-gen _)

-- Lifting of functors to 1-cells
functor-bind : {P Q : Polygraph {ℓ}} (f : functor P Q) {s : 0sphere P} → cell P s → cell Q (functor-0sphere f s)
functor-bind f (id x) = id _
functor-bind f (cons a u) = comp0 _ (func-fun f a) (functor-bind f u)
functor-bind f (cons' a u) = comp0 _ (cell-op _ (func-fun f a)) (functor-bind f u)

-- Composition of functors
functor-comp : {P Q R : Polygraph {ℓ}} → functor P Q → functor Q R → functor P R
functor-comp f g = func (0Pol.functor-comp (func-pred f) (func-pred g)) (λ a → functor-bind g (func-fun f a))

-- Application of a functor to a 1-sphere
functor-sphere : {P Q : Polygraph {ℓ}} → functor P Q → sphere P → sphere Q
functor-sphere f (s , x , y) = 0Pol.functor-sphere (func-pred f) s , functor-bind f x , functor-bind f y

-- Application of a functor to a context
functor-context : {P Q : Polygraph {ℓ}} {s t : 0sphere P} (f : functor P Q) → context P s t → context Q (functor-0sphere f s) (functor-0sphere f t)
functor-context f (u , v) = functor-bind f u , functor-bind f v

-- TODO: we could also show that bind id ≡ id (instead of this extensional version bind id f ≡ f)
functor-bind-id : {P : Polygraph {ℓ}} {s : 0sphere P} (f : cell P s) → functor-bind functor-id f ≡ f
functor-bind-id (id x) = refl
functor-bind-id (cons a f) = cong (cons a) (functor-bind-id f)
functor-bind-id (cons' a f) = cong (cons' a) (functor-bind-id f)

-- Map between presented types induced by a functor
functor-pres : {P Q : Polygraph {ℓ}} → functor P Q → pres P → pres Q
functor-pres f = pres-rec _ (λ x → pres-pred (func-pred f x)) (λ a → pres-cell _ (func-fun f a))

-- An explicit equivalence between polygraphs (where we have cells in the polygraph witnessing for the fact that G∘F ∼ id)
record equivalence {ℓ : Level} (P Q : Polygraph {ℓ}) : Type ℓ where
  constructor equiv
  field
    equiv-f : functor P Q
    equiv-g : functor Q P
    equiv-gf : (x : pred P) → cell P (x , func-pred equiv-g (func-pred equiv-f x))
    equiv-fg : (y : pred Q) → cell Q (y , func-pred equiv-f (func-pred equiv-g y))

open equivalence public

equivalence-id : {P : Polygraph {ℓ}} → equivalence P P
equivalence-id = equiv functor-id functor-id id id

equivalence-sym : {P Q : Polygraph {ℓ}} → equivalence P Q → equivalence Q P
equivalence-sym e = equiv (e .equiv-g) (e .equiv-f) (e .equiv-fg) (e .equiv-gf)

equivalence-comp : {P Q R : Polygraph {ℓ}} → equivalence P Q → equivalence Q R → equivalence P R
equivalence-comp {P = P} {R = R} e1 e2 = equiv f g c d
  where
  f1 = equiv-f e1
  f2 = equiv-f e2
  f  = functor-comp f1 f2
  g1 = equiv-g e1
  g2 = equiv-g e2
  g  = functor-comp g2 g1
  c : (x : pred P) → cell P (x , func-pred g (func-pred f x))
  c x = comp0 _ (equiv-gf e1 x) (functor-bind g1 (equiv-gf e2 (func-pred f1 x)))
  d : (y : pred R) → cell R (y , func-pred f (func-pred g y))
  d y = comp0 _ (equiv-fg e2 y) (functor-bind f2 (equiv-fg e1 (func-pred g2 y)))

-- The preservation theorem
preservation : {P Q : Polygraph {ℓ}} → tietze P Q → equivalence P Q
preservation (T0 P X f) = equiv F G id FG
  where
  Q = tietze0 P X f
  F : functor P Q
  F .func-pred = inl
  F .func-fun a = cell-gen _ a
  G : functor Q P
  G .func-pred (inl x) = x
  G .func-pred (inr x) = f x
  G .func-fun {s = inl x , inl y} a = cell-gen _ a
  G .func-fun {s = inl x , inr y} a = subst (λ x' → cell P (x , x')) a (id x) -- a : x ≡ f y , on veut : cell P (x , f y)
  G .func-fun {s = inr x , inl y} ()
  G .func-fun {s = inr x , inr y} ()
  FG : (y : pred Q) → cell Q (y , func-pred F (func-pred G y))
  FG (inl x) = id (inl x)
  FG (inr x) = cell-op Q (cell-gen Q refl)
preservation (T0' P X f) = equivalence-sym (preservation (T0 P X f))
preservation (T1 P f g) = equiv F G id id
  where
  Q = tietze1 P f g
  F : functor P Q
  F .func-pred x = x
  F .func-fun a = cell-gen Q (inl a)
  G : functor Q P
  G .func-pred x = x
  G .func-fun (inl a) = cell-gen P a
  G .func-fun (inr a) = g a
preservation (T1' P f g) = equivalence-sym (preservation (T1 P f g))
preservation Tr = equivalence-id
preservation (Tt T U) = equivalence-comp (preservation T) (preservation U)

-- Equivalent presentations induce the same truncated presented type
equivalence-pres : {P Q : Polygraph {ℓ}} → equivalence P Q → ∥ pres P ∥₂ ≡ ∥ pres Q ∥₂
equivalence-pres {P = P} {Q = Q} E = ua (isoToEquiv e)
  where
  open Iso
  e : Iso ∥ pres P ∥₂ ∥ pres Q ∥₂
  e .fun = ST.map (functor-pres (E .equiv-f))
  e .inv = ST.map (functor-pres (E .equiv-g))
  e .rightInv = ST.elim (λ _ → isProp→isSet (isSetSetTrunc _ _)) (pres-elim _ _ (λ x → sym (cong ∣_∣₂ (cell-pres _ (equiv-fg E x)))) (λ _ → toPathP (isSetSetTrunc _ _ _ _)))
  e .leftInv  = ST.elim (λ _ → isProp→isSet (isSetSetTrunc _ _)) (pres-elim _ _ (λ x → sym (cong ∣_∣₂ (cell-pres _ (equiv-gf E x)))) (λ _ → toPathP (isSetSetTrunc _ _ _ _)))

-- We recover a ("more constructive") proof of correction of tietze equivalences (in fact, we could remove the above one which is the one obtained by "cut elimination")
tietze-correct' : {P Q : Polygraph {ℓ}} → tietze P Q → ∥ pres P ∥₂ ≡ ∥ pres Q ∥₂
tietze-correct' T = equivalence-pres (preservation T)

-- module _ where
  -- private
    -- postulate AC : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} → ((a : A) → ∥ B a ∥₁) → ∥ ((a : A) → B a) ∥₁

  -- AC2 : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {A' : Type ℓ'} {B : A → A' → Type ℓ''} → ((a : A) (a' : A') → ∥ B a a' ∥₁) → ∥ ((a : A) (a' : A') → B a a') ∥₁
  -- AC2 f = AC λ a → AC (f a)

  -- tietze-complete' : {P Q : Polygraph {ℓ}} → ∥ pres P ∥₂ ≡ ∥ pres Q ∥₂ → ∥ equivalence P Q ∥₁
  -- tietze-complete' {P = P} {Q = Q} p = {!!}
    -- -- PT.rec isPropPropTrunc (λ F₀ → {!!}) (AC2 F₀)
    -- where
    -- F₀ : (pres P → pres Q) → pred P → ∥ pred Q ∥₁
    -- F₀ f x = pres-rec _ ∣_∣₁ (λ _ → isPropPropTrunc _ _) (f (pres-pred x))
    -- F₁ : (f : pres P → pres Q) (F₀ : pred P → pred Q) {s : 0sphere P} → gen P s → ∥ gen Q (0Pol.functor-sphere F₀ s) ∥₁
    -- F₁ f F₀ a = {!!}

inl-ret : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → (B → A) → A ⊎ B → A
inl-ret f (inl x) = x
inl-ret f (inr x) = f x

-- Generators for the extension theorem
extension-gen :
  (P : Polygraph {ℓ})
  {Q' : 0Polygraph {ℓ}} →
  0Pol.tietze (pred P) Q' →
  (0Pol.sphere Q' → Type ℓ)
extension-gen P (0Pol.T0 .(pred P) X f) = gen (tietze0 P X f)
extension-gen P {Q' = Q'} (0Pol.T0' _ X f) (x , y) = Σ (Q' ⊎ X) λ x' → Σ (Q' ⊎ X) λ y' → (x ≡ f' x') × gen P (x' , y') × (y ≡ f' y')
  -- gen P (inl x , inl y) ⊎ Σ X λ x' → Σ X λ y' → (x ≡ f x') × gen P (inr x' , inr y') × (y ≡ f y') -- TODO: encore plus de cas (encore 2).................
  where
  -- f' : Q' ⊎ X → Q'
  -- f' (inl x) = x
  -- f' (inr x) = f x
  f' = inl-ret f
extension-gen P 0Pol.Tr = gen P
extension-gen P (0Pol.Tt T T') = extension-gen (polygraph _ (extension-gen P T)) T'

-- The extension function
extension :
  {ℓ : Level}
  (P : Polygraph {ℓ})
  {Q' : 0Polygraph {ℓ}} →
  0Pol.tietze (pred P) Q' →
  Polygraph {ℓ}
extension {ℓ = ℓ} P {Q'} T = polygraph Q' (extension-gen P T)

-- Coherence
coherent : Polygraph {ℓ} → Type ℓ
coherent P = (s : 0sphere P) → cell P s

-- -- The extension function is correct
-- extension-correct :
  -- (P : Polygraph {ℓ})
  -- {Q : 0Polygraph {ℓ}} →
  -- (T : 0Pol.tietze (pred P) Q) →
  -- tietze P (extension P T)
-- extension-correct P (0Pol.T0 .(pred P) X f) = T0 P X f
-- extension-correct P (0Pol.T0' _ X f) = {!T0' ? ? ?!} -- we seem to need the hypothesis that P is coherent here
-- extension-correct P 0Pol.Tr = Tr
-- extension-correct P (0Pol.Tt T T') = Tt (extension-correct P T) (extension-correct (polygraph _ (extension-gen P T)) T')

-- The extension function is correct
extension-correct :
  (P : Polygraph {ℓ})
  {Q : 0Polygraph {ℓ}} →
  coherent P →
  (T : 0Pol.tietze (pred P) Q) →
  tietze P (extension P T)

-- The transfer theorem
transfer :
  {P : Polygraph {ℓ}}
  {Q' : 0Polygraph {ℓ}} →
  coherent P →
  (T' : 0Pol.tietze (pred P) Q') →
  coherent (extension P T')

module _ (Q₀ : 0Polygraph {ℓ}) (X : Type ℓ) (f : X → Q₀) (P₁ : 0Pol.sphere (Q₀ ⊎ X) → Type ℓ) (coh : coherent (polygraph (Q₀ ⊎ X) P₁)) where
  private
    P₀ = Q₀ ⊎ X

    P = polygraph P₀ P₁
    
    -- -- normalize elements of P₀
    -- nf : P₀ → P₀
    -- nf x = inl (inl-ret f x)

    -- -- extension of nf to spheres
    -- nf-sphere : 0sphere P → 0sphere P
    -- nf-sphere = 0Pol.functor-sphere nf

    -- Q = extension P (0Pol.T0' Q₀ X f)
    Q = polygraph Q₀ (λ s → Σ P₀ λ x' → Σ P₀ λ y' → (0Pol.sphere-src _ s ≡ inl-ret f x') × gen P (x' , y') × (0Pol.sphere-tgt _ s ≡ inl-ret f y'))

    P' = tietze0 Q X f

  tietze1' : tietze P P'
  tietze1' = Tt
    (T1 P (gen P') c)
    (Tt (T≡ swap)
    (T1' P' (gen P) d))

    where
    c : {s : 0sphere P} → gen P' s → cell P s
    -- c {inl x , inl y} (x' , y' , p , a , q) = cell-gen _ (subst2 (λ x y → gen P (x , y)) ({!!} ∙ cong inl (sym p)) ({!!} ∙ cong inl (sym q)) a)
    -- c {inl x , inr y} a = comp0 P {y = inl (f y)} {!!} {!!} -- for this second case, we need coh
      -- where
      -- p : x ≡ f y
      -- p = a
    -- c {inr x , inl y} ()
    -- c {inr x , inr y} ()
    c a = coh _

    d : {s : 0sphere P'} → gen P s → cell P' s
    d {inl x , inl y} a = cell-gen _ (inl x , inl y , refl , a , refl)
    d {inl x , inr y} a = cons (inl x , inr y , refl , a , refl) (cell-gen _ (tietze0gen Q f y))
    d {inr x , inl y} a = cons' (tietze0gen Q f x) (cell-gen _ (inr x , inl y , refl , a , refl))
    d {inr x , inr y} a = cons' (tietze0gen Q f x) (cons (inr x , inr y , refl , a , refl) (cell-gen _ (tietze0gen Q f y)))

    -- NOTE: it would work for any polygraphs P and P' with the same underlying 0-polygraph
    swap : tietze1 P (gen P') c ≡ tietze1 P' (gen P) d
    swap = cong₂ polygraph refl (funExt λ s → ua ⊎-swap-≃)

extension-correct P coh (0Pol.T0 .(pred P) X f) = T0 P X f
-- NOTE: we need the hypothesis that P is coherent here
extension-correct P coh T@(0Pol.T0' Q' X f) = Tt lem (T0' Q X f)
  where
  Q : Polygraph
  Q = extension P T
  lem : tietze P (tietze0 Q X f)
  lem = tietze1' Q' X f (gen P) coh
extension-correct P coh 0Pol.Tr = Tr
extension-correct P coh (0Pol.Tt T T') = Tt (extension-correct P coh T) (extension-correct (extension P T) (transfer coh T) T')

transfer {P = P} {Q' = Q'} coh T' (x , y) =
  -- NOTE: this is where we need inverses (op)
  comp0 _ (equiv-fg E x) (comp0 _ (functor-bind F (coh (func-pred G x , func-pred G y))) (cell-op _ (equiv-fg E y)))
  where
  Q = extension P T'

  T : tietze P Q
  T = extension-correct P coh T'

  E : equivalence P Q
  E = preservation T

  F : functor P Q
  F = equiv-f E

  G : functor Q P
  G = equiv-g E
