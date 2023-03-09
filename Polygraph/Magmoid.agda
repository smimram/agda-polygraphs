{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit renaming (Unit to ⊤)

module Magmoid where

private variable
  ℓ ℓ' : Level

record Magmoid : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    obj : Type ℓ
    hom : obj → obj → Type ℓ'
    id : (x : obj) → hom x x
    _⋆_ : {x y z : obj} → hom x y → hom y z → hom x z

open Magmoid public

isInitial : (C : Magmoid {ℓ} {ℓ'}) → (x : obj C) → Type _
isInitial C x = (y : obj C) → isContr (hom C x y)

isPropIsInitial : {C : Magmoid {ℓ} {ℓ'}} (x : obj C) → isProp (isInitial C x)
isPropIsInitial x = isPropΠ λ y → isPropIsContr
