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

-- The definition of the category C lives in a bigger universe than D because
-- the universe has to be bigger than the one of relations in the first case
-- (and not in the second). For simplicity, we suppose that relations are as
-- high as objects from there on. Similarly, when definining the initial object
-- of C, we get something of level the type of A instead of the level of the
-- objects.
module _ {ℓ : Level} {P : 1Polygraph {ℓ} {ℓ}} where
  open Operations P

  module Magmoids (x : Σ₀) where
    C : Magmoid
    obj C = Σ (Σ₀ → Type ℓ) λ K → K x × ({y z : Σ₀} → (a : y ↝ z) → K y ≃ K z)
    hom C (K , r , e) (K' , r' , e') = Σ ({y : Σ₀} → K y → K' y) λ f → (f r ≡ r') × ({y z : Σ₀} (a : y ↝ z) (k : K y) → equivFun (e' a) (f k) ≡ f (equivFun (e a) k))
    id C (K , r , e) = (λ k → k) , refl , λ a k → refl
    _⋆_ C {K , r , e} {K' , r' , e'} {K'' , r'' , e''} (f , δ , γ) (f' , δ' , γ') = f' ∘ f , cong f' δ ∙ δ' , λ a k → γ' a (f k) ∙ cong f' (γ a k)

    CI : obj C
    CI = (λ y → ∣ x ∣ ≡ ∣ y ∣) , refl {x = ∣ x ∣} , λ a → pathToEquiv (cong (λ n → ∣ x ∣ ≡ n) ∣ a ∣₁) -- compPathrEquiv ∣ a ∣₁

    D : Magmoid
    obj D = Σ (⟦ P ⟧ → Type ℓ) (λ L → L ∣ x ∣)
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
      initDI : isInitial D DI
      initDI (L , p) = subst isContr (sym lem5 ∙ sym lem2) lem6
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
  
    -- Lemma 12
    -- TODO: see also funTypeTransp
    funPath : {ℓ ℓ' ℓ'' : Level} {X : Type ℓ} {A : X → Type ℓ'} {B : X → Type ℓ''} {x y : X} (f : A x → B x) (g : A y → B y) (p : x ≡ y)
              → PathP (λ i → A (p i) → B (p i)) f g ≃ ((a : A x) → subst B p (f a) ≡ g (subst A p a))
    funPath {A = A} {B = B} {x = x} f g p = isoToEquiv e
      where
      -- for inspiration...
      funTypeTransp' : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} (B : A → Type ℓ') (C : A → Type ℓ'') {x y : A} (p : x ≡ y) (f : B x → C x) → PathP (λ i → B (p i) → C (p i)) f (subst C p ∘ f ∘ subst B (sym p))
      -- funTypeTransp' B C {x = x} p f i b = transp (λ j → C (p (j ∧ i))) (~ i) (f (transp (λ j → B (p (i ∧ ~ j))) (~ i) b))
      funTypeTransp' B C {x = x} p f i b = transport-filler (λ i → C (p i)) (f (transp (λ j → B (p (i ∧ ~ j))) (~ i) b)) i

      e : Iso (PathP (λ i → A (p i) → B (p i)) f g) ((a : A x) → subst B p (f a) ≡ g (subst A p a))

      -- Iso.fun e q a i = transp (λ j → B (p (i ∨ j))) i (q i (transp (λ j → A (p (i ∧ j))) (~ i) a))
      -- Iso.fun e q a i = transp (λ j → B (p (i ∨ j))) i (q i (transport-filler (λ i → A (p i)) a i))
      -- Iso.fun e q a = fromPathP (λ i → q i (toPathP {A = λ i → A (p i)} {x = a} refl i))
      Iso.fun e q a = fromPathP (congP (λ i → q i) (toPathP {A = λ i → A (p i)} {x = a} refl))
      -- Iso.inv e q i a = transp (λ j → B (p (i ∨ ~ j))) {!i!} (q (transp (λ j → A (p (i ∧ ~ j))) (~ i) a) i) -- toPathP (funExt λ a → {!q (subst A (sym p) a)!})
      -- Iso.inv e q = toPathP (funExt λ a → fromPathP {A = λ i → B (p i)} (toPathP (q (subst A (sym p) a)) ▷ cong g (substSubst⁻ A p a)))
      Iso.inv e q = toPathP (funExt λ a → q (subst A (sym p) a) ∙ cong g (substSubst⁻ A p a))
      -- Iso.inv e q i a = {!transp (λ j → B (p (i ∨ ~ j))) i (q' i)!}
        -- where
        -- a' : A x
        -- a' = transp (λ j → A (p (i ∧ ~ j))) (~ i) a
        -- q' : subst B p (f (transp (λ j → A (p (i ∧ ~ j))) (~ i) a)) ≡ g (subst A p (transp (λ j → A (p (i ∧ ~ j))) (~ i) a))
        -- q' = q (transp (λ j → A (p (i ∧ ~ j))) (~ i) a)
      -- Iso.inv e q i a = transp (λ j → B (p (i ∨ ~ j))) {!i!} (q (transp (λ j → A (p (i ∧ ~ j))) (~ i) a) i)
      Iso.rightInv e q = {!!}
      -- funExt λ a →
        -- fromPathP (λ i → toPathP {A = λ i → A (p i) → B (p i)} {x = f} (funExt (λ a → q (subst A (sym p) a) ∙ (λ i → g (substSubst⁻ A p a i)))) i (toPathP {A = λ i → A (p i)} (λ _ → subst A p a) i)) ≡⟨ {!!} ⟩
        -- fromPathP (λ i → toPathP {A = λ i → A (p i) → B (p i)} {x = f} (funExt (λ a → q (subst A (sym p) a) ∙ (λ i → g (substSubst⁻ A p a i)))) i (toPathP {A = λ i → A (p i)} (λ _ → subst A p a) i)) ≡⟨ {!!} ⟩
        -- q a ∎
      Iso.leftInv e p = {!!}
      -- {!toPathP (funExt (λ a → fromPathP (λ i → p i (toPathP (λ _ → transport (λ i₁ → A (p₁ i₁)) (subst A (λ i₁ → p₁ (~ i₁)) a)) i)) ∙ (λ i → g (substSubst⁻ A p₁ a i)))) ≡ p!}
      -- e' : Iso (PathP (λ i → A (p i) → B (p i)) f g) ((a : A x) → f a ≡ subst B (sym p) (g (subst A p a)))
      -- Iso.fun e' q a i = {!sym (subst-filler B (sym p) ?)!}
         -- -- q i (subst-filler A p a i)
      -- Iso.inv e' q i a = {!q!}
      -- Iso.rightInv e' p = {!!}
      -- Iso.leftInv e' p = {!!}

    transportFun : {ℓ ℓ' ℓ'' : Level} {X : Type ℓ} {A : X → Type ℓ'} {B : X → Type ℓ''} {x y : X} (f : A x → B x) (p : x ≡ y)
                   → transport (λ i → A (p i) → B (p i)) f ≡ subst B p ∘ f ∘ subst⁻ A p
    transportFun {A = A} {B = B} f p = J (λ y p → transport (λ i → A (p i) → B (p i)) f ≡ subst B p ∘ f ∘ subst⁻ A p) (transportRefl f ∙ funExt λ a → sym (substRefl {B = B} _) ∙ cong (subst B refl) (cong f {!substRefl⁻!})) p

    funPath2 : {ℓ ℓ' ℓ'' : Level} {X : Type ℓ} {A : X → Type ℓ'} {B : X → Type ℓ''} {x y : X} (f : A x → B x) (g : A y → B y) (p : x ≡ y)
               → PathP (λ i → A (p i) → B (p i)) f g ≃ ((a : A x) → subst B p (f a) ≡ g (subst A p a))
    funPath2 {A = A} {B = B} {x = x} f g p =
      PathP (λ i → A (p i) → B (p i)) f g ≃⟨ PathP≃Path (λ i → A (p i) → B (p i)) f g ⟩
      transport (λ i → A (p i) → B (p i)) f ≡ g ≃⟨ {!!} ⟩ -- not in the standard library...
      (subst B p) ∘ f ∘ (subst⁻ A p) ≡ g ≃⟨ {!!} ⟩
      (subst B p) ∘ f ∘ (subst⁻ A p) ∘ subst A p ≡ g ∘ subst A p ≃⟨ {!!} ⟩
      (subst B p) ∘ f ≡ g ∘ subst A p ≃⟨ {!!} ⟩
      ((a : A x) → subst B p (f a) ≡ g (subst A p a)) ■

    -- direct proof using J
    funPath3 : {ℓ ℓ' ℓ'' : Level} {X : Type ℓ} {A : X → Type ℓ'} {B : X → Type ℓ''} {x y : X} (f : A x → B x) (g : A y → B y) (p : x ≡ y)
               → PathP (λ i → A (p i) → B (p i)) f g ≃ ((a : A x) → subst B p (f a) ≡ g (subst A p a))
    funPath3 {X = X} {A = A} {B = B} {x = x} f g p = J (λ y p → (g : A y → B y) → PathP (λ i → A (p i) → B (p i)) f g ≃ ((a : A x) → subst B p (f a) ≡ g (subst A p a)))
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
        substRefl {B = B} (f a) ∙ (sym (substRefl {B = B} (f a)) ∙ q a ∙ (cong g (substRefl {B = A} a))) ∙ (cong g (sym (substRefl {B = A} a))) ≡⟨ {!!} ⟩
        q a ∎
      Iso.leftInv (e g) = {!!}

    -- NB : it's simpler in the direction D ≡ C than C ≡ D because of the
    -- transport in hom≡ along the function
    obj≃ : obj D ≃ obj C
    obj≃ = isoToEquiv e
      where
      e : Iso (Σ (⟦ P ⟧ → Type ℓ) (λ L → L ∣ x ∣)) (Σ (Σ₀ → Type ℓ) (λ K → K x × ({y z : Σ₀} (a : y ↝ z) → K y ≃ K z)))
      Iso.fun e (L , p) = (λ n → L ∣ n ∣) , p , λ a → pathToEquiv (cong L ∣ a ∣₁)
      Iso.inv e (K , r , e) = (rec P {f₀ = K} (λ a → ua (e a))) , r
      Iso.rightInv e (K , r , e) = ΣPathP (refl , ΣPathP (refl , implicitFunExt (implicitFunExt (funExt λ a → pathToEquiv-ua (e a)))))
      Iso.leftInv e (L , p) = ΣPathP ((funExt (elim (λ n → rec P (λ a → ua (pathToEquiv (cong L ∣ a ∣₁))) n ≡ L n) (λ _ → refl) lem)) , refl)
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
      Iso.fun e (g , ϵ) = g , ϵ , λ a l → equivFun (funPath3 {A = L} {B = L'} g g ∣ a ∣₁) (cong (λ n → g {n}) ∣ a ∣₁) l
      -- lem L L' ∣ a ∣₁ g l -- λ a → cong (λ n → g {n}) ∣ a ∣₁
        -- where
        -- -- TODO: in the standard library?
        -- lem : {ℓ ℓ' : Level} {A : Type ℓ} (B B' : A → Type ℓ') {x y : A} (p : x ≡ y) (f : {x : A} → B x → B' x) (b : B x)
              -- → subst B' p (f b) ≡ f (subst B p b)
        -- lem B B' p f b = J (λ y p → subst B' p (f b) ≡ f (subst B p b)) (substRefl {B = B'} (f b) ∙ sym (cong f (substRefl {B = B} b))) p
      Iso.inv e (f , ϵ , γ) = (λ {n} → elim (λ n → L n → L' n) (λ _ → f) (λ a → invEq (funPath3 {A = L} {B = L'} f f ∣ a ∣₁) (γ a)) n) , ϵ -- (λ {n} → elim P (λ n → L n → L' n) (λ _ → f) (λ a → γ a) n) , ϵ
      Iso.rightInv e (f , ϵ , γ) = ΣPathP (refl , (ΣPathP (refl , (implicitFunExt (implicitFunExt (funExt (λ a → secEq (funPath3 {A = L} {B = L'} f f ∣ a ∣₁) (γ a)))))))) -- ΣPathP (refl , (ΣPathP (refl , refl)))
      Iso.leftInv e (g , ϵ) = ΣPathP (implicitFunExt (λ {n} → funExt⁻ lem n) , toPathP lem'') -- ΣPathP ((implicitFunExt (λ {n} → funExt⁻ lem n)) , refl) -- ΣPathP (implicitFunExt (λ {n} → funExt⁻ lem n) , refl)
        -- dealing with implicit arguments requires some administrative work...
        where
        funExt∙ : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} {f g h : (x : A) → B x} (p : f ≡ g) (q : g ≡ h) (x : A) → funExt⁻ (p ∙ q) x ≡ funExt⁻ p x ∙ funExt⁻ q x
        funExt∙ p q x = refl
        -- lem : elim (λ n → L n → L' n) (λ x → g {∣ x ∣}) (λ a → cong (λ n → g {n}) ∣ a ∣₁) ≡ (λ n → g {n})
        -- lem = eta (λ n → L n → L' n) (λ n → g {n})
        lem : elim (λ n → L n → L' n) (λ x → g {∣ x ∣}) (λ a → invEq (funPath3 {A = L} {B = L'} g g ∣ a ∣₁) (equivFun (funPath3 {A = L} {B = L'} g g ∣ a ∣₁) (λ i → g))) ≡ (λ n → g {n})
        lem = cong (elim (λ n → L n → L' n) (λ _ → g)) (implicitFunExt (implicitFunExt (funExt λ a → retEq (funPath3 {A = L} {B = L'} g g ∣ a ∣₁) _))) ∙ eta (λ n → L n → L' n) λ n → g {n}
        lem' : funExt⁻ (funExt⁻ lem ∣ x ∣) l ≡ refl
        lem' =
          funExt⁻ (funExt⁻ lem ∣ x ∣) l ≡⟨ refl ⟩
          funExt⁻ (funExt⁻ (Q ∙ Q') ∣ x ∣) l ≡⟨ refl ⟩
          funExt⁻ (funExt⁻ Q ∣ x ∣ ∙ funExt⁻ Q' ∣ x ∣) l ≡⟨ refl ⟩
          funExt⁻ (funExt⁻ Q ∣ x ∣) l ∙ funExt⁻ (funExt⁻ Q' ∣ x ∣) l ≡⟨ refl ⟩
          refl ∙ refl ≡⟨ sym (lUnit _) ⟩
          refl ∎
          where
          Q = cong (elim (λ n → L n → L' n) (λ _ → g)) (implicitFunExt (implicitFunExt (funExt λ a → retEq (funPath3 {A = L} {B = L'} g g ∣ a ∣₁) _)))
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
      initCI : isInitial C CI
      initCI X = subst (λ X → isContr (hom C CI X)) fgX lem
        where
        f : obj D → obj C
        f = equivFun obj≃
        g : obj C → obj D
        g = invEq obj≃
        lem : isContr (hom C CI (f (g X)))
        lem = isOfHLevelRespectEquiv 0 (hom≃ DI (g X)) (initDI (g X))
        fgX : f (g X) ≡ X
        fgX = secEq obj≃ X

    abstract
      initCI' : (X : obj C) (f : hom C CI X) (g : hom C CI X) → f ≡ g
      initCI' X f g = isContr→isProp (initCI X) f g

  module _
    {x : Σ₀}
    (A : {y : Σ₀}
    (p : _≡_ {A = ⟦ P ⟧} ∣ x ∣ ∣ y ∣) → Type ℓ)
    (Ar : A refl)
    -- (Aa : {y z : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) (a : y ↝ z) → A p ≃ A (p ∙ ∣ a ∣₁))
    (Aa : {y z : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) (a : y ↝ z) → A p ≃ A (subst (λ n → ∣ x ∣ ≡ n) ∣ a ∣₁ p))
    where

    open Magmoids x

    -- the two natural variants of Aa are equivalent
    compPathrEquivEquiv : {ℓ : Level} {A : Type ℓ} {x y z : A} (p : y ≡ z) → pathToEquiv (cong (λ y → x ≡ y) p) ≡ compPathrEquiv p
    compPathrEquivEquiv {x = x} {y = y} p = equivEq (funExt lem)
      where
      lem : (q : x ≡ y) → subst (_≡_ x) p q ≡ q ∙ p
      lem q = fromPathP (compPath-filler q p)

    -- our arguments, seen as an object of C
    X : obj C
    X = (λ y → Σ (∣ x ∣ ≡ ∣ y ∣) A) , (refl , Ar) , λ {y} {z} a → Σ-cong-equiv (pathToEquiv (cong (λ n → ∣ x ∣ ≡ n) ∣ a ∣₁)) λ p → Aa p a

    ϕ : hom C CI X
    ϕ = fst (initCI X)

    ϕ₁ = fst ϕ
    ϕ₂ = fst (snd ϕ)
    ϕ₃ = snd (snd ϕ)

    ψ : hom C X CI
    ψ = f , refl , γ
      where
      f : {y : Σ₀} → Σ (∣ x ∣ ≡ ∣ y ∣) A → ∣ x ∣ ≡ ∣ y ∣
      f (p , _) = p
      γ : {y z : Σ₀} (a : y ↝ z) (k : Σ (∣ x ∣ ≡ ∣ y ∣) A) → subst (λ n → ∣ x ∣ ≡ n) ∣ a ∣₁ (f k) ≡ f (equivFun (snd (snd X) a) k)
      γ a (p , n) = refl

    ϕ⋆ψ : hom C CI CI
    ϕ⋆ψ = _⋆_ C {CI} {X} {CI} ϕ ψ

    ϕ⋆ψ≡id : ϕ⋆ψ ≡ Magmoid.id C CI
    ϕ⋆ψ≡id = initCI' CI _ _

    ψ₁ : {y : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) → fst (ϕ₁ p) ≡ p
    ψ₁ p = lem p
      where
      lem : {y : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) → fst (ϕ₁ p) ≡ p
      lem {y} p = funExt⁻ (implicitFunExt⁻ (cong fst ϕ⋆ψ≡id) {y}) p

    ψ₂ : PathP (λ i → ψ₁ refl i ≡ refl) (cong fst ϕ₂ ∙ refl) refl
    ψ₂ = cong (fst ∘ snd) ϕ⋆ψ≡id

    -- induction for paths
    -- following _Path spaces for inductive types_
    path-elim' : {y : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) → A p
    path-elim' p = subst A (ψ₁ p) (snd (ϕ₁ p))
      -- where
      -- lem : A (fst (ϕ₁ p))
      -- lem = snd (ϕ₁ p)
      -- lem' : fst (ϕ₁ p) ≡ p
      -- lem' = ψ₁ p

    -- TODO: more elegant way?
    path-elim-refl' : path-elim' refl ≡ Ar
    path-elim-refl' =
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

    -- path-elim-ext' : {y z : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) (a : y ↝ z) → path-elim' (subst (_≡_ ∣ x ∣) ∣ a ∣₁ p) ≡ equivFun (Aa p a) (path-elim' p)
    -- path-elim-ext' p a = {!!}
      -- where
      -- lem : {!!}
      -- lem = {!cong snd (ϕ₃ a)!}
