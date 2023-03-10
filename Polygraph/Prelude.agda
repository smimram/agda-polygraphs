{-# OPTIONS --cubical #-}

module Prelude where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.GroupoidLaws

-- characterization of path between functions

funPath : {ℓ ℓ' ℓ'' : Level} {X : Type ℓ} {A : X → Type ℓ'} {B : X → Type ℓ''} {x y : X} (f : A x → B x) (g : A y → B y) (p : x ≡ y)
           → PathP (λ i → A (p i) → B (p i)) f g ≃ ((a : A x) → subst B p (f a) ≡ g (subst A p a))
funPath {X = X} {A = A} {B = B} {x = x} f g p = J (λ y p → (g : A y → B y) → PathP (λ i → A (p i) → B (p i)) f g ≃ ((a : A x) → subst B p (f a) ≡ g (subst A p a)))
  -- (λ g → isoToEquiv
    -- (iso
      -- (λ p a → substRefl {A = A x} {B = λ _ → B x} {x = a} (f a) ∙ funExt⁻ p a ∙ sym (cong g (substRefl {A = A x} {x = a} a)))
      -- (λ q → funExt λ a → sym (substRefl {A = A x} {B = λ _ → B x} {x = a} (f a)) ∙ q a ∙ cong g (substRefl {A = A x} {x = a} a))
      -- (λ q → {!!})
      -- {!!}))
  (λ g → isoToEquiv (e g))
  p g
  where
  e : (g : A x → B x) → Iso (PathP (λ i → A x → B x) f g) ((a : A x) → subst B refl (f a) ≡ g (subst A refl a))
  Iso.fun (e g) q a = substRefl {B = B} (f a) ∙ funExt⁻ q a ∙ cong g (sym (substRefl {B = A} a))
    -- subst B refl (f a) ≡⟨ substRefl {B = B} (f a) ⟩
    -- f a ≡⟨ funExt⁻ q a ⟩
    -- g a ≡⟨ cong g (sym (substRefl {B = A} a)) ⟩
    -- g (subst A refl a) ∎
  Iso.inv (e g) q = funExt λ a → sym (substRefl {B = B} (f a)) ∙ q a ∙ cong g (substRefl {B = A} a)
    -- f a ≡⟨ sym (substRefl {B = B} (f a)) ⟩
    -- subst B refl (f a) ≡⟨ q a ⟩
    -- g (subst A refl a) ≡⟨ cong g (substRefl {B = A} a) ⟩
    -- g a ∎
  Iso.rightInv (e g) q = funExt λ a →
    substRefl {B = B} (f a) ∙ funExt⁻ (funExt (λ a → sym (substRefl {B = B} (f a)) ∙ q a ∙ (cong g (substRefl {B = A} a)))) a ∙ cong g (sym (substRefl {B = A} a)) ≡⟨ refl ⟩
    substRefl {B = B} (f a) ∙ (sym (substRefl {B = B} (f a)) ∙ q a ∙ (cong g (substRefl {B = A} a))) ∙ (cong g (sym (substRefl {B = A} a))) ≡⟨ cong (_∙_ _) (sym (assoc _ _ _)) ⟩
    substRefl {B = B} (f a) ∙ sym (substRefl {B = B} (f a)) ∙ ((q a ∙ (cong g (substRefl {B = A} a))) ∙ (cong g (sym (substRefl {B = A} a)))) ≡⟨ assoc _ _ _ ⟩
    (substRefl {B = B} (f a) ∙ sym (substRefl {B = B} (f a))) ∙ ((q a ∙ (cong g (substRefl {B = A} a))) ∙ (cong g (sym (substRefl {B = A} a)))) ≡⟨ cong (_∙ ((q a ∙ (cong g (substRefl {B = A} a))) ∙ (cong g (sym (substRefl {B = A} a))))) (rCancel _) ⟩
    refl ∙ ((q a ∙ (cong g (substRefl {B = A} a))) ∙ (cong g (sym (substRefl {B = A} a)))) ≡⟨ sym (lUnit _) ⟩
    (q a ∙ (cong g (substRefl {B = A} a))) ∙ (cong g (sym (substRefl {B = A} a))) ≡⟨ sym (assoc _ _ _) ⟩
    q a ∙ (cong g (substRefl {B = A} a) ∙ cong g (sym (substRefl {B = A} a))) ≡⟨ cong (_∙_ _) (rCancel _) ⟩
    q a ∙ refl ≡⟨ sym (rUnit _) ⟩
    q a ∎
  Iso.leftInv (e g) q = cong funExt (funExt lem)
    where
    lem : (a : A x) → (sym (substRefl {B = B} (f a))) ∙ (substRefl {B = B} (f a) ∙ funExt⁻ q a ∙ cong g (sym (substRefl {B = A} a))) ∙ cong g (substRefl {B = A} a) ≡ funExt⁻ q a
    lem a =
      sym (substRefl {B = B} (f a)) ∙ (substRefl {B = B} (f a) ∙ funExt⁻ q a ∙ cong g (sym (substRefl {B = A} a))) ∙ cong g (substRefl {B = A} a) ≡⟨ cong (_∙_ _) (sym (assoc _ _ _)) ⟩
      sym (substRefl {B = B} (f a)) ∙ substRefl {B = B} (f a) ∙ ((funExt⁻ q a ∙ cong g (sym (substRefl {B = A} a))) ∙ cong g (substRefl {B = A} a)) ≡⟨ assoc _ _ _ ⟩
      (sym (substRefl {B = B} (f a)) ∙ substRefl {B = B} (f a)) ∙ ((funExt⁻ q a ∙ cong g (sym (substRefl {B = A} a))) ∙ cong g (substRefl {B = A} a)) ≡⟨ cong (_∙ (funExt⁻ q a ∙ cong g (sym (substRefl {B = A} a))) ∙ cong g (substRefl {B = A} a)) (lCancel _) ⟩
      refl ∙ ((funExt⁻ q a ∙ cong g (sym (substRefl {B = A} a))) ∙ cong g (substRefl {B = A} a)) ≡⟨ sym (lUnit _) ⟩
      (funExt⁻ q a ∙ cong g (sym (substRefl {B = A} a))) ∙ cong g (substRefl {B = A} a) ≡⟨ sym (assoc _ _ _) ⟩
      funExt⁻ q a ∙ (cong g (sym (substRefl {B = A} a)) ∙ cong g (substRefl {B = A} a)) ≡⟨ cong (_∙_ _) (lCancel _) ⟩
      funExt⁻ q a ∙ refl ≡⟨ sym (rUnit _) ⟩
      funExt⁻ q a ∎

-- -- transportFun : {ℓ ℓ' ℓ'' : Level} {X : Type ℓ} {A : X → Type ℓ'} {B : X → Type ℓ''} {x y : X} (f : A x → B x) (p : x ≡ y)
               -- -- → transport (λ i → A (p i) → B (p i)) f ≡ subst B p ∘ f ∘ subst⁻ A p
-- -- transportFun {A = A} {B = B} f p = J (λ y p → transport (λ i → A (p i) → B (p i)) f ≡ subst B p ∘ f ∘ subst⁻ A p) (transportRefl f ∙ funExt λ a → sym (substRefl {B = B} _) ∙ cong (subst B refl) (cong f {!substRefl⁻!})) p

-- funPath2 : {ℓ ℓ' ℓ'' : Level} {X : Type ℓ} {A : X → Type ℓ'} {B : X → Type ℓ''} {x y : X} (f : A x → B x) (g : A y → B y) (p : x ≡ y)
           -- → PathP (λ i → A (p i) → B (p i)) f g ≃ ((a : A x) → subst B p (f a) ≡ g (subst A p a))
-- funPath2 {A = A} {B = B} {x = x} f g p =
  -- PathP (λ i → A (p i) → B (p i)) f g ≃⟨ PathP≃Path (λ i → A (p i) → B (p i)) f g ⟩
  -- transport (λ i → A (p i) → B (p i)) f ≡ g ≃⟨ {!!} ⟩ -- not in the standard library...
  -- (subst B p) ∘ f ∘ (subst⁻ A p) ≡ g ≃⟨ {!!} ⟩
  -- (subst B p) ∘ f ∘ (subst⁻ A p) ∘ subst A p ≡ g ∘ subst A p ≃⟨ {!!} ⟩
  -- (subst B p) ∘ f ≡ g ∘ subst A p ≃⟨ {!!} ⟩
  -- ((a : A x) → subst B p (f a) ≡ g (subst A p a)) ■

-- -- Lemma 12
-- -- TODO: see also funTypeTransp
-- funPath3 : {ℓ ℓ' ℓ'' : Level} {X : Type ℓ} {A : X → Type ℓ'} {B : X → Type ℓ''} {x y : X} (f : A x → B x) (g : A y → B y) (p : x ≡ y)
          -- → PathP (λ i → A (p i) → B (p i)) f g ≃ ((a : A x) → subst B p (f a) ≡ g (subst A p a))
-- funPath3 {A = A} {B = B} {x = x} f g p = isoToEquiv e
  -- where
  -- -- for inspiration...
  -- funTypeTransp' : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} (B : A → Type ℓ') (C : A → Type ℓ'') {x y : A} (p : x ≡ y) (f : B x → C x) → PathP (λ i → B (p i) → C (p i)) f (subst C p ∘ f ∘ subst B (sym p))
  -- -- funTypeTransp' B C {x = x} p f i b = transp (λ j → C (p (j ∧ i))) (~ i) (f (transp (λ j → B (p (i ∧ ~ j))) (~ i) b))
  -- funTypeTransp' B C {x = x} p f i b = transport-filler (λ i → C (p i)) (f (transp (λ j → B (p (i ∧ ~ j))) (~ i) b)) i

  -- e : Iso (PathP (λ i → A (p i) → B (p i)) f g) ((a : A x) → subst B p (f a) ≡ g (subst A p a))

  -- -- Iso.fun e q a i = transp (λ j → B (p (i ∨ j))) i (q i (transp (λ j → A (p (i ∧ j))) (~ i) a))
  -- -- Iso.fun e q a i = transp (λ j → B (p (i ∨ j))) i (q i (transport-filler (λ i → A (p i)) a i))
  -- -- Iso.fun e q a = fromPathP (λ i → q i (toPathP {A = λ i → A (p i)} {x = a} refl i))
  -- Iso.fun e q a = fromPathP (congP (λ i → q i) (toPathP {A = λ i → A (p i)} {x = a} refl))
  -- -- Iso.inv e q i a = transp (λ j → B (p (i ∨ ~ j))) {!i!} (q (transp (λ j → A (p (i ∧ ~ j))) (~ i) a) i) -- toPathP (funExt λ a → {!q (subst A (sym p) a)!})
  -- -- Iso.inv e q = toPathP (funExt λ a → fromPathP {A = λ i → B (p i)} (toPathP (q (subst A (sym p) a)) ▷ cong g (substSubst⁻ A p a)))
  -- Iso.inv e q = toPathP (funExt λ a → q (subst A (sym p) a) ∙ cong g (substSubst⁻ A p a))
  -- -- Iso.inv e q i a = {!transp (λ j → B (p (i ∨ ~ j))) i (q' i)!}
    -- -- where
    -- -- a' : A x
    -- -- a' = transp (λ j → A (p (i ∧ ~ j))) (~ i) a
    -- -- q' : subst B p (f (transp (λ j → A (p (i ∧ ~ j))) (~ i) a)) ≡ g (subst A p (transp (λ j → A (p (i ∧ ~ j))) (~ i) a))
    -- -- q' = q (transp (λ j → A (p (i ∧ ~ j))) (~ i) a)
  -- -- Iso.inv e q i a = transp (λ j → B (p (i ∨ ~ j))) {!i!} (q (transp (λ j → A (p (i ∧ ~ j))) (~ i) a) i)
  -- Iso.rightInv e q = {!!}
  -- -- funExt λ a →
    -- -- fromPathP (λ i → toPathP {A = λ i → A (p i) → B (p i)} {x = f} (funExt (λ a → q (subst A (sym p) a) ∙ (λ i → g (substSubst⁻ A p a i)))) i (toPathP {A = λ i → A (p i)} (λ _ → subst A p a) i)) ≡⟨ {!!} ⟩
    -- -- fromPathP (λ i → toPathP {A = λ i → A (p i) → B (p i)} {x = f} (funExt (λ a → q (subst A (sym p) a) ∙ (λ i → g (substSubst⁻ A p a i)))) i (toPathP {A = λ i → A (p i)} (λ _ → subst A p a) i)) ≡⟨ {!!} ⟩
    -- -- q a ∎
  -- Iso.leftInv e p = {!!}
  -- -- {!toPathP (funExt (λ a → fromPathP (λ i → p i (toPathP (λ _ → transport (λ i₁ → A (p₁ i₁)) (subst A (λ i₁ → p₁ (~ i₁)) a)) i)) ∙ (λ i → g (substSubst⁻ A p₁ a i)))) ≡ p!}
  -- -- e' : Iso (PathP (λ i → A (p i) → B (p i)) f g) ((a : A x) → f a ≡ subst B (sym p) (g (subst A p a)))
  -- -- Iso.fun e' q a i = {!sym (subst-filler B (sym p) ?)!}
     -- -- -- q i (subst-filler A p a i)
  -- -- Iso.inv e' q i a = {!q!}
  -- -- Iso.rightInv e' p = {!!}
  -- -- Iso.leftInv e' p = {!!}
