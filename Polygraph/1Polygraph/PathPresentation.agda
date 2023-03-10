{-# OPTIONS --cubical #-}

-- the presentation of the path space in 1 polygraphs

module 1Polygraph.PathPresentation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function as Fun
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws as GL
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Data.Sum hiding (rec ; elim)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥ hiding (rec ; elim)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation as PT hiding (rec ; elim)
open import Cubical.HITs.SetTruncation as ST hiding (rec ; elim)

open import Graph
open import Magmoid
open import 1Polygraph.Base
open import 1Polygraph.PathElimination

module _ {ℓ : Level} {P : 1Polygraph {ℓ} {ℓ}} {x : 1Polygraph.Σ₀ P} where
  open Operations P
  open FreeGroupoid

  open Magmoids {P = P} x

  private
    H : obj C
    H = (λ y → x ↭! y) , [] , λ a → FreeGroupoid.compEquivR x a

    -- two ways of expressing path composition coincide
    subst≡comp : {ℓ : Level} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → subst (λ y → x ≡ y) q p ≡ p ∙ q
    subst≡comp p q = fromPathP (compPath-filler p q)

    -- TODO: could be derived from equivComp in the stdlib (but less nice computation principle)
    postCompEquivEquiv : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (g : B ≃ C) → (A ≃ B) ≃ (A ≃ C)
    postCompEquivEquiv {A = A} {B = B} {C = C} g = isoToEquiv e
      where
      e : Iso (A ≃ B) (A ≃ C)
      Iso.fun e f = compEquiv f g
      Iso.inv e f = compEquiv f (invEquiv g)
      Iso.rightInv e f = equivEq (funExt λ x → secEq g (equivFun f x))
      Iso.leftInv e f = equivEq (funExt λ x → retEq g (equivFun f x))

    isInitialH : isInitial C H
    isInitialH X@(K , r , e) = F , contr
      where
      eq : {y : Σ₀} (p : x ↭! y) → K x ≃ K y
      eq p = FreeGroupoid.elim≃ (λ {y} p → K x ≃ K y) (idEquiv _) (λ _ a → postCompEquivEquiv (e a)) p
      F : hom C H X
      F = (λ {y} p → equivFun (eq p) r) , refl , λ a k → refl
      contr : (G : hom C H X) → F ≡ G
      contr G@(f , ρ , ϵ) = ΣPathP (implicitFunExt (funExt first) , (ΣPathP (lemr , lema)))
        where
        first : {y : Σ₀} (p : x ↭! y) → fst F p ≡ f p
        first {y} p = FreeGroupoid.elim≃ (λ p → fst F p ≡ f p) lemr lema p
          where
          lemr : r ≡ f []
          lemr = sym ρ
          lema : {y z : Σ₀} (p : x ↭! y) (a : y ↝ z) → (fst F p ≡ f p) ≃ (equivFun (e a) (fst F p) ≡ f (p ∷+ a))
          lema p a = compEquiv lem (compPathrEquiv (ϵ a p))
            where
            lem : (fst F p ≡ f p) ≃ (equivFun (e a) (fst F p) ≡ equivFun (e a) (f p))
            lem = congEquiv {x = fst F p} {y = f p} (e a)
        lemr : PathP (λ i → first [] i ≡ r) (refl {x = r}) ρ
        -- lemr = toPathP lem
        -- where
          -- lem : subst (λ x → x ≡ r) (first []) refl ≡ ρ
          -- lem = substInPathsR (first []) refl ∙ sym (rUnit _)
        lemr i j = ρ (~ i ∨ j)
        lema : PathP
          (λ i → {y z : Σ₀} (a : y ↝ z) (p : x ↭! y) → equivFun (e a) (first p i) ≡ first (p ∷+ a) i)
          (λ a p _ → equivFun (e a) (equivFun (eq p) r))
          ϵ
        lema i a p j = lem' a p i j
          where
          lem' : {y z : Σ₀} (a : y ↝ z) (p : x ↭! y) → PathP (λ i → equivFun (e a) (first p i) ≡ first (p ∷+ a) i) (refl {x = equivFun (e a) (equivFun (eq p) r)}) (ϵ a p)
          lem' a p = toPathP lem''
            where
            gen2 : {ℓ : Level} {A : Type ℓ} {x x' y y' : A} (p : x' ≡ x) (q : y ≡ y') (r : x ≡ y) → transport (λ i → p (~ i) ≡ q i) r ≡ p ∙ r ∙ q
            gen2 p q r = fromPathP (doubleCompPath-filler p r q) ∙ doubleCompPath≡compPath p r q
            gen : {ℓ : Level} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → transport (λ i → p i ≡ (p ∙ q) i) refl ≡ q
            gen p q = gen2 (sym p) (p ∙ q) refl ∙ eqs
              where
              eqs =
                sym p ∙ refl ∙ p ∙ q   ≡⟨ assoc _ _ _ ⟩
                (sym p ∙ refl) ∙ p ∙ q ≡⟨ cong (λ r → r ∙ p ∙ q) (sym (rUnit _)) ⟩
                sym p ∙ p ∙ q          ≡⟨ assoc _ _ _ ⟩
                (sym p ∙ p) ∙ q        ≡⟨ cong (_∙ q) (lCancel p) ⟩
                refl ∙ q               ≡⟨ sym (lUnit q) ⟩
                q                      ∎
            lem'' : transport (λ i → cong (equivFun (e a)) (first p) i ≡ (cong (equivFun (e a)) (first p) ∙ ϵ a p) i) refl ≡ ϵ a p
            lem'' = gen _ _

  pathPresentation : {y : Σ₀} → (∣ x ∣ ≡ ∣ y ∣) ≃ (x ↭! y)
  pathPresentation {y} = isoToEquiv e
    where
    f : hom C CI H
    f = isInitialCI H .fst
    g : hom C H CI
    g = isInitialH CI .fst
    e : Iso (∣ x ∣ ≡ ∣ y ∣) (x ↭! y)
    fg : _⋆_ C {x = CI} {y = H} {z = CI} f g ≡ id C CI
    fg = isContr→isProp (isInitialCI CI) _ (id C CI)
    gf : _⋆_ C {x = H} {y = CI} {z = H} g f ≡ id C H
    gf = isContr→isProp (isInitialH H) _ (id C H)
    Iso.fun e = fst f
    Iso.inv e =  fst g
    Iso.rightInv e p = funExt⁻ (implicitFunExt⁻ (cong fst gf)) p
    Iso.leftInv e p = funExt⁻ (implicitFunExt⁻ (cong fst fg)) p
