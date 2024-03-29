{-# OPTIONS --cubical #-}

module 1Polygraph.PathElimination where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function as Fun
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
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

open import Prelude
open import 1Polygraph.Base
open import Magmoid

module _ {ℓ₀ ℓ₁ : Level} {P : 1Polygraph {ℓ₀} {ℓ₁}} where
  open Operations P

  module Magmoids (x : Σ₀) where
    C : Magmoid
    obj C = Σ (Σ₀ → Type (ℓ-max ℓ₀ ℓ₁)) λ K → K x × ({y z : Σ₀} → (a : y ↝ z) → K y ≃ K z)
    hom C (K , r , e) (K' , r' , e') = Σ ({y : Σ₀} → K y → K' y) λ f → (f r ≡ r') × ({y z : Σ₀} (a : y ↝ z) (k : K y) → equivFun (e' a) (f k) ≡ f (equivFun (e a) k))
    id C (K , r , e) = (λ k → k) , refl , λ a k → refl
    _⋆_ C {K , r , e} {K' , r' , e'} {K'' , r'' , e''} (f , δ , γ) (f' , δ' , γ') = f' ∘ f , cong f' δ ∙ δ' , λ a k → γ' a (f k) ∙ cong f' (γ a k)

    CI : obj C
    CI = (λ y → ∣ x ∣ ≡ ∣ y ∣) , refl {x = ∣ x ∣} , λ a → pathToEquiv (cong (λ n → ∣ x ∣ ≡ n) ∣ a ∣₁) -- compPathrEquiv ∣ a ∣₁

    D : Magmoid
    obj D = Σ (⟦ P ⟧ → Type (ℓ-max ℓ₀ ℓ₁)) (λ L → L ∣ x ∣)
    hom D (L , l) (L' , l') = Σ ({n : ⟦ P ⟧} → L n → L' n) (λ g → g l ≡ l')
    id D (L , l) = (λ l → l) , refl
    _⋆_ D (g , ϵ) (g' , ϵ') = (λ l → g' (g l)) , cong g' ϵ ∙ ϵ'

    DI : obj D
    DI = (λ n → ∣ x ∣ ≡ n) , refl

    -- like sing but with opposite choice of contraction point
    singl' : {ℓ : Level} {A : Type ℓ} (a : A) → Type ℓ
    singl' {A = A} a = Σ A (λ x → x ≡ a)

    isContrSingl' : {ℓ : Level} {A : Type ℓ} (a : A) → isContr (singl' a)
    isContrSingl' a = (a , refl) , lem
      where
      lem : (x : singl' a) → (a , (λ _ → a)) ≡ x
      lem (x , p) = ΣPathP (sym p , (toPathP lem2))
        where
        lem2 : subst (λ x → x ≡ a) (sym p) refl ≡ p
        lem2 = substInPathsR (sym p) refl ∙ sym (rUnit _)

    -- Note: there is no content in initiality since this is a proposition (and
    -- this makes Agda loop for nothing)
    abstract
      isInitialDI : isInitial D DI
      isInitialDI (L , p) = subst isContr (sym lem5 ∙ sym lem2) lem6
        where
        lem : ({n : ⟦ P ⟧} → fst DI n → L n) ≃ (((n , p) : Σ ⟦ P ⟧ λ n → fst DI n) → L n)
        -- curryfication
        -- TODO: there ought to be something like this already in the standard library...
        lem = isoToEquiv e
          where
          e : Iso ({n : ⟦ P ⟧} → fst DI n → L n) (((n , p) : Σ ⟦ P ⟧ λ n → fst DI n) → L n)
          Iso.fun e f (n , p) = f p
          Iso.inv e f {n} p = f (n , p)
          Iso.rightInv e f = refl
          Iso.leftInv e f = refl
        lem2 : Σ ({n : ⟦ P ⟧} → fst DI n → L n) (λ g → g refl ≡ p) ≡ Σ (((n , p) : Σ ⟦ P ⟧ λ n → fst DI n) → L n) (λ g → g (∣ x ∣ , refl) ≡ p)
        lem2 = ua (Σ-cong-equiv lem (λ g → idEquiv _))
        lem3 : isContr (Σ ⟦ P ⟧ λ n → fst DI n)
        lem3 = isContrSingl ∣ x ∣
        lem3' : (Σ ⟦ P ⟧ λ n → fst DI n) ≃ ⊤
        lem3' = isContr→≃Unit lem3
        -- lem4 : (((n , p) : Σ ⟦ P ⟧ (λ n → fst DI n)) → L n) ≃ L ∣ x ∣
        -- lem4 = compEquiv step1 step2
          -- where
          -- step1 : (((n , p) : Σ ⟦ P ⟧ (λ n → fst DI n)) → L n) ≃ (⊤ → L ∣ x ∣)
          -- step1 = equivΠ lem3' λ { (n , p) → subst (λ n → L n ≃ L ∣ x ∣) p (idEquiv _) }
          -- step2 : (⊤ → L ∣ x ∣) ≃ L ∣ x ∣
          -- step2 = isoToEquiv e
            -- where
            -- e : Iso (⊤ → L ∣ x ∣) (L ∣ x ∣)
            -- Iso.fun e f = f tt
            -- Iso.inv e l tt = l
            -- Iso.rightInv e l = refl
            -- Iso.leftInv e f = refl
        --- NOTE: the above proof is not precise enough for us to prove lem5
        --- below, we need to hardcode a simpler one
        lem4 : (((n , p) : Σ ⟦ P ⟧ (λ n → fst DI n)) → L n) ≃ L ∣ x ∣
        lem4 = isoToEquiv e
          where
          e : Iso (((n , p) : Σ ⟦ P ⟧ (λ n → fst DI n)) → L n) (L ∣ x ∣)
          Iso.fun e g = g (∣ x ∣ , refl)
          Iso.inv e l (n , p) = subst L p l
          Iso.rightInv e l = substRefl {B = L} l
          Iso.leftInv e g = funExt λ { (n , p) → li n p }
            where
            -- li'' : (n : ⟦ P ⟧) (p : ∣ x ∣ ≡ n) → (∣ x ∣ , refl) ≡ (n , p)
            -- li'' n p = ΣPathP (p , λ i j → p (i ∧ j))
            -- li' : (n : ⟦ P ⟧) (p : ∣ x ∣ ≡ n) → PathP (λ i → L (p i)) (g (∣ x ∣ , refl)) (g (n , p))
            -- li' n p = cong g (li'' n p)
            -- li : (n : ⟦ P ⟧) (p : ∣ x ∣ ≡ n) → transport (λ i → L (p i)) (g (∣ x ∣ , (λ _ → ∣ x ∣))) ≡ g (n , p)
            -- li n p = fromPathP (li' n p)
            li : (n : ⟦ P ⟧) (p : ∣ x ∣ ≡ n) → transport (λ i → L (p i)) (g (∣ x ∣ , (λ _ → ∣ x ∣))) ≡ g (n , p)
            li n p = fromPathP (cong g (ΣPathP (p , λ i j → p (i ∧ j))))
        lem5 : Σ (((n , p) : Σ ⟦ P ⟧ (λ n → fst DI n)) → L n) (λ g → g (∣ x ∣ , refl) ≡ p) ≡ (Σ (L ∣ x ∣) λ l → l ≡ p)
        lem5 = ua (Σ-cong-equiv lem4 λ g → isoToEquiv (e g))
          where
          e : (g : ((n , p) : Σ ⟦ P ⟧ (λ n → ∣ x ∣ ≡ n)) → L n) → Iso (g (∣ x ∣ , refl) ≡ p) (equivFun lem4 g ≡ p)
          Iso.fun (e g) q = q
          Iso.inv (e g) q = q
          Iso.rightInv (e g) q = refl
          Iso.leftInv (e g) q = refl
        lem6 : isContr (Σ (L ∣ x ∣) λ g → g ≡ p)
        lem6 = isContrSingl' _
  
    -- NB : it's simpler in the direction D ≡ C than C ≡ D because of the
    -- transport in hom≡ along the function
    obj≃ : obj D ≃ obj C
    obj≃ = isoToEquiv e
      where
      e : Iso (Σ (⟦ P ⟧ → Type _) (λ L → L ∣ x ∣)) (Σ (Σ₀ → Type _) (λ K → K x × ({y z : Σ₀} (a : y ↝ z) → K y ≃ K z)))
      Iso.fun e (L , p) = (λ n → L ∣ n ∣) , p , λ a → pathToEquiv (cong L ∣ a ∣₁)
      Iso.inv e (K , r , e) = (rec {f₀ = K} (λ a → ua (e a))) , r
      Iso.rightInv e (K , r , e) = ΣPathP (refl , ΣPathP (refl , implicitFunExt (implicitFunExt (funExt λ a → pathToEquiv-ua (e a)))))
      Iso.leftInv e (L , p) = ΣPathP ((funExt (elim (λ n → rec (λ a → ua (pathToEquiv (cong L ∣ a ∣₁))) n ≡ L n) (λ _ → refl) lem)) , refl)
        where
        lem : {y z : Σ₀} (a : y ↝ z) → PathP (λ i → ua (pathToEquiv (cong L ∣ a ∣₁)) i ≡ L (∣ a ∣₁ i)) (λ _ → L ∣ y ∣) (λ _ → L ∣ z ∣)
        lem {y} {z} a = compPathL→PathP lem'
          where
          lem' =
            sym (λ i → ua (pathToEquiv (cong L ∣ a ∣₁)) i) ∙ (λ _ → L ∣ y ∣) ∙ (cong L ∣ a ∣₁) ≡⟨ cong (_∙_ _) (sym (lUnit _)) ⟩
            sym (λ i → ua (pathToEquiv (cong L ∣ a ∣₁)) i) ∙ (cong L ∣ a ∣₁) ≡⟨ cong (_∙ (cong L ∣ a ∣₁)) (cong sym (ua-pathToEquiv (cong L ∣ a ∣₁))) ⟩
            sym (cong L ∣ a ∣₁) ∙ cong L ∣ a ∣₁ ≡⟨ lCancel _ ⟩
            (λ _ → L ∣ z ∣) ∎

    hom≃ : (x y : obj D) → hom D x y ≃ hom C (equivFun obj≃ x) (equivFun obj≃ y)
    hom≃ (L , l) (L' , l') = isoToEquiv e
      where
      e : Iso
        (Σ ({n : ⟦ P ⟧} → L n → L' n) (λ g → g l ≡ l'))
        (Σ ({x : Σ₀} → L ∣ x ∣ → L' ∣ x ∣) (λ f → (f l ≡ l') × ({y z : Σ₀} (a : y ↝ z) (l : L ∣ y ∣) → subst L' ∣ a ∣₁ (f l) ≡ f (subst L ∣ a ∣₁ l))))
      Iso.fun e (g , ϵ) = g , ϵ , λ a l → equivFun (funPath {A = L} {B = L'} g g ∣ a ∣₁) (cong (λ n → g {n}) ∣ a ∣₁) l
      -- lem L L' ∣ a ∣₁ g l -- λ a → cong (λ n → g {n}) ∣ a ∣₁
        -- where
        -- -- TODO: in the standard library?
        -- lem : {ℓ ℓ' : Level} {A : Type ℓ} (B B' : A → Type ℓ') {x y : A} (p : x ≡ y) (f : {x : A} → B x → B' x) (b : B x)
              -- → subst B' p (f b) ≡ f (subst B p b)
        -- lem B B' p f b = J (λ y p → subst B' p (f b) ≡ f (subst B p b)) (substRefl {B = B'} (f b) ∙ sym (cong f (substRefl {B = B} b))) p
      Iso.inv e (f , ϵ , γ) = (λ {n} → elim (λ n → L n → L' n) (λ _ → f) (λ a → invEq (funPath {A = L} {B = L'} f f ∣ a ∣₁) (γ a)) n) , ϵ -- (λ {n} → elim P (λ n → L n → L' n) (λ _ → f) (λ a → γ a) n) , ϵ
      Iso.rightInv e (f , ϵ , γ) = ΣPathP (refl , (ΣPathP (refl , (implicitFunExt (implicitFunExt (funExt (λ a → secEq (funPath {A = L} {B = L'} f f ∣ a ∣₁) (γ a)))))))) -- ΣPathP (refl , (ΣPathP (refl , refl)))
      Iso.leftInv e (g , ϵ) = ΣPathP (implicitFunExt (λ {n} → funExt⁻ lem n) , toPathP lem'') -- ΣPathP ((implicitFunExt (λ {n} → funExt⁻ lem n)) , refl) -- ΣPathP (implicitFunExt (λ {n} → funExt⁻ lem n) , refl)
        -- dealing with implicit arguments requires some administrative work...
        where
        funExt∙ : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} {f g h : (x : A) → B x} (p : f ≡ g) (q : g ≡ h) (x : A) → funExt⁻ (p ∙ q) x ≡ funExt⁻ p x ∙ funExt⁻ q x
        funExt∙ p q x = refl
        -- lem : elim (λ n → L n → L' n) (λ x → g {∣ x ∣}) (λ a → cong (λ n → g {n}) ∣ a ∣₁) ≡ (λ n → g {n})
        -- lem = eta (λ n → L n → L' n) (λ n → g {n})
        lem : elim (λ n → L n → L' n) (λ x → g {∣ x ∣}) (λ a → invEq (funPath {A = L} {B = L'} g g ∣ a ∣₁) (equivFun (funPath {A = L} {B = L'} g g ∣ a ∣₁) (λ i → g))) ≡ (λ n → g {n})
        lem = cong (elim (λ n → L n → L' n) (λ _ → g)) (implicitFunExt (implicitFunExt (funExt λ a → retEq (funPath {A = L} {B = L'} g g ∣ a ∣₁) _))) ∙ eta (λ n → L n → L' n) λ n → g {n}
        lem' : funExt⁻ (funExt⁻ lem ∣ x ∣) l ≡ refl
        lem' =
          funExt⁻ (funExt⁻ lem ∣ x ∣) l ≡⟨ refl ⟩
          funExt⁻ (funExt⁻ (Q ∙ Q') ∣ x ∣) l ≡⟨ refl ⟩
          funExt⁻ (funExt⁻ Q ∣ x ∣ ∙ funExt⁻ Q' ∣ x ∣) l ≡⟨ refl ⟩
          funExt⁻ (funExt⁻ Q ∣ x ∣) l ∙ funExt⁻ (funExt⁻ Q' ∣ x ∣) l ≡⟨ refl ⟩
          refl ∙ refl ≡⟨ sym (lUnit _) ⟩
          refl ∎
          where
          Q = cong (elim (λ n → L n → L' n) (λ _ → g)) (implicitFunExt (implicitFunExt (funExt λ a → retEq (funPath {A = L} {B = L'} g g ∣ a ∣₁) _)))
          Q' = eta (λ n → L n → L' n) λ n → g {n}
        lem'' : subst (λ l → l ≡ l') (funExt⁻ (funExt⁻ lem ∣ x ∣) l) ϵ ≡ ϵ -- transport (λ i → lem i ∣ x ∣ l ≡ l') ϵ ≡ ϵ
        lem'' =
          subst (λ l → l ≡ l') (funExt⁻ (funExt⁻ lem ∣ x ∣) l) ϵ ≡⟨ substInPathsR (funExt⁻ (funExt⁻ lem ∣ x ∣) l) ϵ ⟩
          sym (funExt⁻ (funExt⁻ lem ∣ x ∣) l) ∙ ϵ ≡⟨ cong (_∙ ϵ) (cong sym lem') ⟩
          sym refl ∙ ϵ ≡⟨ cong (_∙ ϵ) refl ⟩
          refl ∙ ϵ ≡⟨ sym (lUnit _) ⟩
          ϵ ∎

    DCI : equivFun obj≃ DI ≡ CI
    DCI = refl

    isContr≃ : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → A ≃ B → isContr A → isContr B
    isContr≃ e = isOfHLevelRespectEquiv 0 e

    abstract
      isInitialCI : isInitial C CI
      isInitialCI X = subst (λ X → isContr (hom C CI X)) fgX lem
        where
        f : obj D → obj C
        f = equivFun obj≃
        g : obj C → obj D
        g = invEq obj≃
        lem : isContr (hom C CI (f (g X)))
        lem = isOfHLevelRespectEquiv 0 (hom≃ DI (g X)) (isInitialDI (g X))
        fgX : f (g X) ≡ X
        fgX = secEq obj≃ X

  module _
    {x : Σ₀}
    (A : {y : Σ₀} (p : _≡_ {A = ⟦ P ⟧} ∣ x ∣ ∣ y ∣) → Type (ℓ-max ℓ₀ ℓ₁))
    (Ar : A refl)
    (Aa : {y z : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) (a : y ↝ z) → A p ≃ A (p ∙ ∣ a ∣₁))
    -- (Aa : {y z : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) (a : y ↝ z) → A p ≃ A (subst (λ n → ∣ x ∣ ≡ n) ∣ a ∣₁ p))
    where

    open Magmoids x

    private
      -- the two natural variants of Aa are equivalent
      substEquivComp : {ℓ : Level} {A : Type ℓ} {x y z : A} (p : y ≡ z) (q : x ≡ y) → subst (_≡_ x) p q ≡ q ∙ p
      substEquivComp p q = fromPathP (compPath-filler q p)

      -- our arguments, seen as an object of C
      X : obj C
      X = (λ y → Σ (∣ x ∣ ≡ ∣ y ∣) A) , (refl , Ar) , λ {y} {z} a → Σ-cong-equiv (compPathrEquiv ∣ a ∣₁) λ p → Aa p a

      ϕ : hom C CI X
      ϕ = fst (isInitialCI X)

      ϕ₁ = fst ϕ
      ϕ₂ = fst (snd ϕ)
      ϕ₃ = snd (snd ϕ)

      ψ : hom C X CI
      ψ = f , refl , γ
        where
        f : {y : Σ₀} → Σ (∣ x ∣ ≡ ∣ y ∣) A → ∣ x ∣ ≡ ∣ y ∣
        f (p , _) = p
        γ : {y z : Σ₀} (a : y ↝ z) (k : Σ (∣ x ∣ ≡ ∣ y ∣) A) → subst (λ n → ∣ x ∣ ≡ n) ∣ a ∣₁ (f k) ≡ f (equivFun (snd (snd X) a) k)
        γ a (p , n) = substEquivComp ∣ a ∣₁ (f (p , n))

      ϕ⋆ψ : hom C CI CI
      ϕ⋆ψ = _⋆_ C {CI} {X} {CI} ϕ ψ

      ϕ⋆ψ≡id : ϕ⋆ψ ≡ Magmoid.id C CI
      ϕ⋆ψ≡id = isContr→isProp (isInitialCI CI) ϕ⋆ψ (Magmoid.id C CI)

      ψ₁ : {y : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) → fst (ϕ₁ p) ≡ p
      ψ₁ p = lem p
        where
        lem : {y : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) → fst (ϕ₁ p) ≡ p
        lem {y} p = funExt⁻ (implicitFunExt⁻ (cong fst ϕ⋆ψ≡id) {y}) p

      ψ₂ : PathP (λ i → ψ₁ refl i ≡ refl) (cong fst ϕ₂ ∙ refl) refl
      ψ₂ = cong (fst ∘ snd) ϕ⋆ψ≡id

    -- induction for paths
    -- following _Path spaces for inductive types_
    elimPath : {y : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) → A p
    elimPath p = subst A (ψ₁ p) (snd (ϕ₁ p))
      -- where
      -- lem : A (fst (ϕ₁ p))
      -- lem = snd (ϕ₁ p)
      -- lem' : fst (ϕ₁ p) ≡ p
      -- lem' = ψ₁ p

    -- TODO: more elegant way?
    elimPathRefl : elimPath refl ≡ Ar
    elimPathRefl =
      subst A (ψ₁ refl) (snd (ϕ₁ refl)) ≡⟨ funExt⁻ (cong (subst A) (sym lem'')) _ ⟩
      subst A (cong fst ϕ₂) (snd (ϕ₁ refl)) ≡⟨ lem ⟩      
      Ar ∎
      where
      lem : subst A (cong fst ϕ₂) (snd (ϕ₁ refl)) ≡ Ar
      lem = fromPathP (cong snd ϕ₂)
      lem' =
        sym (ψ₁ refl) ∙ cong fst ϕ₂ ≡⟨ sym (substInPathsR (ψ₁ refl) (cong fst ϕ₂)) ⟩ 
        subst (λ p → p ≡ refl) (ψ₁ refl) (cong fst ϕ₂) ≡⟨ cong (subst (_≡ refl) (ψ₁ refl)) (rUnit (cong fst ϕ₂)) ⟩
        subst (λ p → p ≡ refl) (ψ₁ refl) (cong fst ϕ₂ ∙ refl) ≡⟨ fromPathP ψ₂ ⟩
        refl ∎
      lem'' =
        cong fst ϕ₂ ≡⟨ lUnit (cong fst ϕ₂) ⟩
        refl ∙ cong fst ϕ₂ ≡⟨ cong (_∙ (cong fst ϕ₂)) (sym (rCancel (ψ₁ refl))) ⟩
        (ψ₁ refl ∙ sym (ψ₁ refl)) ∙ cong fst ϕ₂ ≡⟨ sym (assoc _ _ _) ⟩
        ψ₁ refl ∙ (sym (ψ₁ refl) ∙ cong fst ϕ₂) ≡⟨ cong (_∙_ (ψ₁ refl)) lem' ⟩
        ψ₁ refl ∙ refl ≡⟨ sym (rUnit _) ⟩
        ψ₁ refl ∎

    -- elimPathExt : {y z : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) (a : y ↝ z) → elimPath (subst (_≡_ ∣ x ∣) ∣ a ∣₁ p) ≡ equivFun (Aa p a) (elimPath p)
    -- elimPathExt p a = {!!}
      -- where
      -- lem : {!!}
      -- lem = {!cong snd (ϕ₃ a)!}

  -- ---
  -- --- The particular case where we are eliminating to a proposition
  -- ---
  -- elimPathProp : {x : Σ₀}
    -- (A : {y : Σ₀} (p : _≡_ {A = ⟦ P ⟧} ∣ x ∣ ∣ y ∣) → Type (ℓ-max ℓ₀ ℓ₁))
    -- (AP : {y : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) → isProp (A p))
    -- (Ap : {y : Σ₀} (p : x ↝? y) → A ∣ p ∣?)
    -- {y : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) → A p
  -- elimPathProp A AP Ap p = elimPath A (Ap []) (λ p a → propBiimpl→Equiv (AP _) (AP _) (λ x → {!!}) {!!}) p
    -- where
    -- open import Graph
    -- open FreePregroupoid
