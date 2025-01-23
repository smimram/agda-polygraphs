{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

module 0Polygraph where

private variable
  ℓ : Level

Polygraph : Type (ℓ-suc ℓ)
Polygraph {ℓ} = Type ℓ

module _ (P : Polygraph {ℓ}) where

  sphere : Type ℓ
  sphere = P × P

  sphere-src : sphere → P
  sphere-src = fst

  sphere-tgt : sphere → P
  sphere-tgt = snd

  sphere-op : sphere → sphere
  sphere-op (x , y) = y , x

  ---
  --- Tietze transformations
  ---

  tietze0 : (X : Type ℓ) → (X → P) → Polygraph {ℓ}
  tietze0 X f = P ⊎ X

functor : (P Q : Polygraph {ℓ}) → Type _
functor P Q = P → Q

functor-id : {P : Polygraph {ℓ}} → functor P P
functor-id x = x

functor-comp : {P Q R : Polygraph {ℓ}} → functor P Q → functor Q R → functor P R
functor-comp f g x = g (f x)

functor-sphere : {P Q : Polygraph {ℓ}} → functor P Q → sphere P → sphere Q
functor-sphere f (x , y) = f x , f y

data tietze {ℓ : Level} : Polygraph {ℓ} → Polygraph {ℓ} → Type (ℓ-suc ℓ) where
  T0  : (P : Polygraph) (X : Type _) (f : X → P) → tietze P (tietze0 P X f)
  T0' : (P : Polygraph) (X : Type _) (f : X → P) → tietze (tietze0 P X f) P
  Tr  : {P : Polygraph} → tietze P P
  Tt  : {P Q R : Polygraph} → tietze P Q → tietze Q R → tietze P R
