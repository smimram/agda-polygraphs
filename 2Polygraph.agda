{-# OPTIONS --cubical -W noUnsupportedIndexedMatch --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty

module 2Polygraph where

import 0Polygraph as 0Pol
import 1Polygraph as 1Pol

private variable
  ℓ : Level

-- A 2-polygraph
record Polygraph {ℓ : Level} : Type (ℓ-suc ℓ) where
  constructor polygraph
  field
    pred : 1Pol.Polygraph {ℓ}
    gen  : 1Pol.sphere pred → Type

whisker2 : {A : Type ℓ} {x y z w : A} (f : x ≡ y) {g g' : y ≡ z} (F : g ≡ g') (h : z ≡ w) → f ∙ g ∙ h ≡ f ∙ g' ∙ h
whisker2 f {g = g} F h = J (λ g' F → f ∙ g ∙ h ≡ f ∙ g' ∙ h) refl F

open Polygraph public

module _ (P : Polygraph {ℓ}) where

  0cell = 1Pol.pred (pred P)
  0sphere = 1Pol.0sphere (pred P)
  1sphere = 1Pol.sphere (pred P)
  1sphere-pred = 1Pol.sphere-pred (pred P)
  1sphere-src = 1Pol.sphere-src (pred P)
  1sphere-tgt = 1Pol.sphere-tgt (pred P)
  1cell = 1Pol.cell (pred P)
  1substitute = 1Pol.substitute (pred P)
  1comp0 = 1Pol.comp0 (pred P)
  1context = 1Pol.context (pred P)
  1context-id = 1Pol.context-id (pred P)
  1context-comp = 1Pol.context-comp (pred P)
  1substitute-id = 1Pol.substitute-id (pred P)
  1substitute-comp = 1Pol.substitute-comp (pred P)

  gen-src : {s : 1sphere} → gen P s → 1cell (1sphere-pred s)
  gen-src {s} _ = 1sphere-src s

  gen-tgt : {s : 1sphere} → gen P s → 1cell (1sphere-pred s)
  gen-tgt {s} _ = 1sphere-tgt s

  -- An atom is a 2-generator in a 1-context
  record atom (s : 1sphere) : Type ℓ where
    field
      atom-sphere  : 1sphere
      atom-gen     : gen P atom-sphere
      atom-context : 1context (1sphere-pred atom-sphere) (1sphere-pred s)
      atom-src-eq  : 1sphere-src s ≡ 1substitute (1sphere-src atom-sphere) atom-context
      atom-tgt-eq  : 1sphere-tgt s ≡ 1substitute (1sphere-tgt atom-sphere) atom-context

  open atom public

  -- Internal source of an atom
  atom-src : {s : 1sphere} → atom s → 1cell (1sphere-pred s)
  atom-src a = 1substitute (1sphere-src (atom-sphere a)) (atom-context a)

  -- Internal target of an atom
  atom-tgt : {s : 1sphere} → atom s → 1cell (1sphere-pred s)
  atom-tgt a = 1substitute (1sphere-tgt (atom-sphere a)) (atom-context a)

  atom-generator : {s : 1sphere} → gen P s → atom s
  atom-generator {s = s} a =
    record
     { atom-sphere  = s
     ; atom-gen     = a
     ; atom-context = 1context-id
     ; atom-src-eq  = sym (1substitute-id _)
     ; atom-tgt-eq  = sym (1substitute-id _)
     }

  -- A cell is a composite of atoms
  data cell : 1sphere → Type ℓ where
    id   : {s : 0sphere} (f : 1cell s) → cell (s , (f , f))
    cons : {s : 0sphere} {x y z : 1cell s} (a : atom (s , (x , y))) (f : cell (s , (y , z))) → cell (s , (x , z))
    cons' : {s : 0sphere} {x y z : 1cell s} (a : atom (s , (y , x))) (f : cell (s , (y , z))) → cell (s , (x , z))

  -- Composition of 2-cells in dimension 1
  comp1 : {s : 0sphere} {x y z : 1cell s} → cell (s , (x , y)) → cell (s , (y , z)) → cell (s , (x , z))
  comp1 (id _) g = g
  comp1 (cons a f) g = cons a (comp1 f g)
  comp1 (cons' a f) g = cons' a (comp1 f g)

  cell-atom : {s : 1sphere} → atom s → cell s
  cell-atom a = cons a (id _)

  cell-gen : {s : 1sphere} → gen P s → cell s
  cell-gen a = cell-atom (atom-generator a)

  -- A 2-sphere
  sphere : Type ℓ
  sphere = Σ 1sphere (λ s → cell s × cell s)

  -- Underlying 1-sphere of a 2-sphere
  sphere-pred : sphere → 1sphere
  sphere-pred = fst

  sphere-src : (s : sphere) → cell (sphere-pred s)
  sphere-src s = fst (snd s)

  sphere-tgt : (s : sphere) → cell (sphere-pred s)
  sphere-tgt s = snd (snd s)

  -- A 2-context
  record context (s t : 1sphere) : Type ℓ where
    field
      context-pred : 1context (1sphere-pred s) (1sphere-pred t)
      context-fst  : cell (_ , (1sphere-src t , 1substitute (1sphere-src s) context-pred))
      context-snd  : cell (_ , (1substitute (1sphere-tgt s) context-pred , 1sphere-tgt t))

  open context public

  -- Put a 2-cell in a 1-context
  substitute+ : {s : 1sphere} {t : 0sphere} (f : cell s) (c : 1context (1sphere-pred s) t) → cell (t , (1substitute (1sphere-src s) c , 1substitute (1sphere-tgt s) c))
  substitute+ (id f) c = id (1substitute f c)
  substitute+ (cons {x = x} {y = y} a f) c = cons a' (substitute+ f c)
    where
    u = 1sphere-src (atom-sphere a)
    v = 1sphere-tgt (atom-sphere a)
    c' = atom-context a
    p : 1substitute x c ≡ 1substitute u (1context-comp c' c)
    p =
      1substitute x c                    ≡⟨ cong (λ x → 1substitute x c) (atom-src-eq a) ⟩
      1substitute (atom-src a) c         ≡⟨ refl ⟩
      1substitute (1substitute u c') c   ≡⟨ sym (1substitute-comp _ c' c) ⟩
      1substitute u (1context-comp c' c) ∎
    q : 1substitute y c ≡ 1substitute v (1context-comp c' c)
    q =
      1substitute y c                    ≡⟨ cong (λ y → 1substitute y c) (atom-tgt-eq a) ⟩
      1substitute (1substitute v c') c   ≡⟨ sym (1substitute-comp _ c' c) ⟩
      1substitute v (1context-comp c' c) ∎
    a' : atom (_ , 1substitute x c , 1substitute y c)
    a' = record
          { atom-sphere  = atom-sphere a
          ; atom-gen     = atom-gen a
          ; atom-context = 1Pol.context-comp _ (atom-context a) c
          ; atom-src-eq  = p
          ; atom-tgt-eq  = q
          }
  substitute+ (cons' {x = x} {y = y} a f) c = {!!}

  -- Put a 2-cell in a 2-contexts
  substitute : {s t : 1sphere} → cell s → context s t → cell t
  substitute f c = comp1 (context-fst c) (comp1 (substitute+ f (context-pred c)) (context-snd c))

  1pres = 1Pol.pres (pred P)
  1pres-cell = 1Pol.pres-cell (pred P)

  -- Type presented by a 2-polygraph
  data pres : Type ℓ where
    pres-pred : 1pres → pres
    disk      : {s : 1sphere} → gen P s → cong pres-pred (1pres-cell (1sphere-src s)) ≡ cong pres-pred (1pres-cell (1sphere-tgt s))

  pres-cell : {s : 1sphere} → cell s → cong pres-pred (1pres-cell (1sphere-src s)) ≡ cong pres-pred (1pres-cell (1sphere-tgt s))
  pres-cell (id f) = refl
  pres-cell {s = s , x , z} (cons {y = y} a f) =
    cong pres-pred (1pres-cell (1sphere-src (s , x , z)))                            ≡⟨ cong (λ f → cong pres-pred (1pres-cell f)) (atom-src-eq a) ⟩
    cong pres-pred (1pres-cell (1comp0 u (1comp0 (gen-src (atom-gen a)) v)))         ≡⟨ {!!} ⟩ -- 1pres-cell vs ∙
    cong pres-pred (1pres-cell u ∙ 1pres-cell (gen-src (atom-gen a)) ∙ 1pres-cell v) ≡⟨ {!!} ⟩ -- cong vs ∙
    u' ∙ cong pres-pred (1pres-cell (gen-src (atom-gen a))) ∙ v'                     ≡⟨ whisker2 u' (disk (atom-gen a)) v' ⟩
    u' ∙ cong pres-pred (1pres-cell (gen-tgt (atom-gen a))) ∙ v'                     ≡⟨ {!!} ⟩ -- similar as above
    cong pres-pred (1pres-cell (1sphere-src (s , y , z)))                            ≡⟨ pres-cell f ⟩
    cong pres-pred (1pres-cell (1sphere-tgt (s , x , z)))                            ∎
    where
    u = atom-context a .fst
    v = atom-context a .snd
    u' = cong pres-pred (1pres-cell u)
    v' = cong pres-pred (1pres-cell v)
  pres-cell {s = s , x , z} (cons' a f) = {!!} -- similar as above

  ---
  --- Tietze transformations
  ---

  tietze0 : (X : Type ℓ) → (X → 0cell) → Polygraph {ℓ}
  tietze0 X f = polygraph (1Pol.tietze0 (pred P) X f) g
    where
    g : 1Pol.sphere (1Pol.tietze0 (pred P) X f) → Type
    g ((inl x , inl y) , u , v) = gen P ((x , y) , ({!u!} , {!v!}))
      where

      -- NOTE: this is in fact an equivalence
      lem : {x y : 0cell} → 1Pol.cell (1Pol.tietze0 (pred P) X f) (inl x , inl y) → 1Pol.cell (P .pred) (x , y)
      lem (1Pol.id .(inl _)) = 1Pol.id _
      lem {x = x} {z} (1Pol.cons {y = inl y} a f) = 1Pol.cons a (lem f)
      lem {x = x} {z} (1Pol.cons {y = inr y} a (1Pol.cons () f))
      lem {x = x} {z} (1Pol.cons {y = inr y} a (1Pol.cons' {y = inl y'} b f)) = 1Pol.cons {!!} (1Pol.cons' {!!} (lem f))
      lem (1Pol.cons' a f) = {!!} -- similar
    g ((inl x , inr y) , u , v) = ⊥*
    g ((inr x , y) , u , v) = ⊥*

---
--- Functors between polygraphs
---

record functor {ℓ : Level} (P Q : Polygraph {ℓ}) : Type ℓ where
  constructor func
  field
    func-pred : 1Pol.functor (pred P) (pred Q)
    func-fun  : {s : 1sphere P} → gen P s → cell Q (1Pol.functor-sphere func-pred s)

open functor public

functor-0sphere : {P Q : Polygraph {ℓ}} → functor P Q → 0sphere P → 0sphere Q
functor-0sphere f = 1Pol.functor-0sphere (func-pred f)

functor-1sphere : {P Q : Polygraph {ℓ}} → functor P Q → 1sphere P → 1sphere Q
functor-1sphere f = 1Pol.functor-sphere (func-pred f)

functor-1context : {P Q : Polygraph {ℓ}} {s t : 0sphere P} (f : functor P Q) → 1context P s t → 1context Q (functor-0sphere f s) (functor-0sphere f t)
functor-1context f = 1Pol.functor-context (func-pred f)

functor-id : {P : Polygraph {ℓ}} → functor P P
functor-id {P = P} = func 1Pol.functor-id (λ a → cell-gen _ (subst (gen P) (sym p) a))
  where
  p : {s : 1sphere P} → 1Pol.functor-sphere 1Pol.functor-id s ≡ s
  p = ΣPathP (refl , (ΣPathP (1Pol.functor-bind-id _ , 1Pol.functor-bind-id _)))

functor-bind : {P Q : Polygraph {ℓ}} (f : functor P Q) {s : 1sphere P} → cell P s → cell Q (functor-1sphere f s)
functor-bind f (id x) = id _
functor-bind f (cons a x) = comp1 _ (substitute _ (func-fun f (atom-gen a)) {!functor-1context f (atom-context a)!}) (functor-bind f x)
functor-bind f (cons' a x) = comp1 _ {!!} (functor-bind f x)

functor-comp : {P Q R : Polygraph {ℓ}} → functor P Q → functor Q R → functor P R
functor-comp f g = func (1Pol.functor-comp (func-pred f) (func-pred g)) (λ a → functor-bind g {!func-fun f a!})

-- Coherence
coherent : Polygraph {ℓ} → Type ℓ
coherent P = {s : 0sphere P} (x y : 1cell P s) → cell P (s , x , y)
