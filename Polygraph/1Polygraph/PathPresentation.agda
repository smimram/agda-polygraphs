{-# OPTIONS --cubical --allow-unsolved-metas #-}

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

  H : obj C
  H = (λ y → x ↭! y) , [] , λ a → FreeGroupoid.compEquivR x a

  -- two ways of expressing path composition coincide
  subst≡comp : {ℓ : Level} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → subst (λ y → x ≡ y) q p ≡ p ∙ q
  subst≡comp p q = fromPathP (compPath-filler p q)

  -- H→I : hom C H CI
  -- H→I = (λ {y} p → ∣ p ∣!) , refl , lem
    -- where
    -- lem : {y z : Σ₀} (a : y ↝ z) (p : x ↭! y) → subst (λ n → ∣ x ∣ ≡ n) ∣ a ∣₁ ∣ p ∣! ≡ ∣ p ∣! ∙ ∣ a ∣₁
    -- lem a p = subst≡comp ∣ p ∣! ∣ a ∣₁

  -- H→H : hom C H H
  -- H→H = _⋆_ C {H} {CI} {H} H→I (fst (initCI H))

  -- -- H→H≡id : H→H ≡ id C H
  -- -- H→H≡id = ΣPathP (implicitFunExt (λ {y} → funExt λ p → lem1 p) , (ΣPathP ({!!} , {!!})))
    -- -- where
    -- -- lem1 : {y : Σ₀} (p : x ↭! y) → fst H→H p ≡ p
    -- -- lem1 {y} p = {!refl!}

  -- Hcontr : isContr (hom C H H)
  -- Hcontr = (id C H) , (λ f → ΣPathP (implicitFunExt (λ {y} → funExt λ p → sym (lem1 f p)) , ΣPathP ({!!} , {!!})))
    -- where
    -- lem1 : (f : hom C H H) {y : Σ₀} (p : x ↭! y) → fst f p ≡ p
    -- lem1 f@(ϕ , ρ , ϵ) p = GpC-elim _ (λ {y} p → fst f p ≡ p)
      -- ρ
      -- (λ {y} {z} {p} q a → sym (ϵ a p) ∙ cong (λ p → p ∷+ a) q)
      -- (λ {y} {z} {p} q a → {!!})
      -- {!!}
      -- {!!}
      -- {!!}
      -- {!!}
      -- where
      -- -- the type of ϵ
      -- eps : {y z : Σ₀} (a : y ↝ z) (p : x ↭! y) → ϕ p ∷+ a ≡ ϕ (p ∷+ a)
      -- eps = ϵ

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
        -- lema p a =
          -- fst F p ≡ f p ≃⟨ {!!} ⟩
          -- equivFun (e a) (fst F p) ≡ equivFun (e a) (f p) ≃⟨ {!!} ⟩
          -- equivFun (e a) (fst F p) ≡ f (p ∷+ a) ■
        -- lema p a = isoToEquiv E
          -- where
          -- E : Iso (fst F p ≡ f p) (equivFun (e a) (fst F p) ≡ f (p ∷+ a))
          -- Iso.fun E q = cong (equivFun (e a)) q ∙ ϵ a p
          -- Iso.inv E q = {!!}
          -- Iso.rightInv E = {!!}
          -- Iso.leftInv E = {!!}
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
      -- lema = toPathP (implicitFunExt (implicitFunExt (funExt λ a i p → lem i _ _ a p)))
        -- where
        -- -- bla : {y z : Σ₀} (p : x ↭! y) (a : y ↝ z) → first (p ∷+ a) ≡ cong (equivFun (e a)) (first p) ∙ ϵ a p
        -- -- bla p a = refl
        -- -- Remove implicit arguments
        -- ϵ' : (y z : Σ₀) (a : y ↝ z) (k : fst H y) → equivFun (e a) (f k) ≡ f (equivFun (snd (snd H) a) k)
        -- ϵ' y z a = ϵ {y} {z} a
        -- transportApp : {ℓ ℓ' : Level} {A : Type ℓ} (B : A → I → Type ℓ') (x : A) (f : (x : A) → B x i0) → transport (λ i → (x : A) → B x i) f x ≡ transport (λ i → B x i) (f x)
        -- transportApp {A = A} B x f = {!!} ∙ {!!}
        -- lem : transport (λ i → (y z : Σ₀) (a : y ↝ z) (p : x ↭! y) → equivFun (e a) (first p i) ≡ first (p ∷+ a) i) (λ y z a p _ → equivFun (e a) (equivFun (eq p) r)) ≡ ϵ'
        -- lem = funExt λ y → funExt λ z → {!!}
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
        -- -- testing types
        -- ϵ' : {y z : Σ₀} (a : y ↝ z) (p : x ↭! y) → equivFun (e a) (f p) ≡ f (p ∷+ a)
        -- ϵ' = {!!}
        -- ind : first (p ∷+ a) ≡ cong (equivFun (e a)) (first p) ∙ ϵ a p
        -- ind = refl
        
