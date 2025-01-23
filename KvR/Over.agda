{-# OPTIONS --cubical #-}

---
--- Types over a given type
---

module Over where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

Over : (ℓ : Level) {ℓ' : Level} (A : Type ℓ') → Type _
Over ℓ A = TypeWithStr ℓ (λ B → B → A)
