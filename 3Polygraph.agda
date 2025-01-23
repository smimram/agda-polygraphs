{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

module 3Polygraph where

import 0Polygraph as 0Pol
import 1Polygraph as 1Pol
import 2Polygraph as 2Pol

private variable
  ℓ : Level

-- A 3-polygraph
record Polygraph {ℓ : Level} : Type (ℓ-suc ℓ) where
  field
    pred : 2Pol.Polygraph {ℓ}
    gen  : 2Pol.sphere pred → Type ℓ

open Polygraph public

module _ (P : Polygraph {ℓ}) where

  1sphere = 2Pol.1sphere (pred P)
  2sphere = 2Pol.sphere (pred P)
  2cell = 2Pol.cell (pred P)
  2context = 2Pol.context (pred P)
  2sphere-pred = 2Pol.sphere-pred (pred P)
  2sphere-src = 2Pol.sphere-src (pred P)
  2sphere-tgt = 2Pol.sphere-tgt (pred P)
  2substitute = 2Pol.substitute (pred P)

  record atom (s : 2sphere) : Type ℓ where
    field
      atom-sphere  : 2sphere
      atom-gen     : gen P atom-sphere
      atom-context : 2context (2sphere-pred atom-sphere) (2sphere-pred s)
      atom-src-eq  : 2sphere-src s ≡ 2substitute (2sphere-src atom-sphere) atom-context
      atom-tgt-eq  : 2sphere-tgt s ≡ 2substitute (2sphere-tgt atom-sphere) atom-context

  open atom public

  data cell : 2sphere → Type ℓ where
     id   : {s : 1sphere} (f : 2cell s) → cell (s , (f , f))
     cons : {s : 1sphere} {x y z : 2cell s} (a : atom (s , (x , y))) (f : cell (s , (y , z))) → cell (s , (x , z))

  2pres = 2Pol.pres (pred P)

  data pres : Type ℓ where
    pres-pred : 2pres → pres
    -- disk : 
