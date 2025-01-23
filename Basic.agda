{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.HITs.SetTruncation as ST

--- Basic facts which ought to be in the standard library

-- STbind : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} → ((x : A) → ∥ B x ∥₂) → (∥ A ∥₂ → ∥ B {!!} ∥₂)
-- STbind f = ST.rec {!!} {!!}
