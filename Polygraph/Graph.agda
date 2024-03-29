{-# OPTIONS --allow-unsolved-metas --cubical #-}

module Graph where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws as GL hiding (assoc ; lUnit)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Empty hiding (elim ; rec)
open import Cubical.Data.Sum hiding (elim ; rec)
open import Cubical.Data.Sigma
open import Cubical.Relation.Binary
open import Cubical.Induction.WellFounded renaming
  (
    Acc to isAcc;
    WellFounded to isWellFounded
  ) public

induction = WFI.induction

-- A graph is a relation on a type
Graph : {ℓ : Level} (A : Type ℓ) (ℓ' : Level) → Type _
Graph {ℓ} A ℓ' = Rel A A ℓ'

private variable
  ℓ₀ ℓ₁ ℓ₂ ℓ : Level
  A : Type ℓ₀
  X : Type ℓ₀
  R : Graph A ℓ₁

op : Graph A ℓ₁ → Graph A ℓ₁
op R x y = R y x

op² : (R : Graph A ℓ₁) → op (op R) ≡ R
op² R = funExt λ x → funExt λ y → refl

---
--- The transitive closure
---

module FreeSemicategory where

  infixl 5 _∷⁺_

  data FreeSemicategory {A : Type ℓ₀} (R : Graph A ℓ₁) : Graph A (ℓ-max ℓ₀ ℓ₁) where
    [_]⁺ : {x y : A} → R x y → FreeSemicategory R x y
    _∷⁺_ : {x y z : A} → FreeSemicategory R x y → R y z → FreeSemicategory R x z

  T = FreeSemicategory

  module _ {A : Type ℓ₀} {R : Graph A ℓ₁} where
    private
      _↝_ = R
      _↝+_ = FreeSemicategory R

    snoc : {x y z : A} (a : x ↝ y) (p : y ↝+ z) → x ↝+ z
    snoc a [ b ]⁺ = [ a ]⁺ ∷⁺ b
    snoc a (p ∷⁺ b) = (snoc a p) ∷⁺ b

    dh : {x z : A} (p : x ↝+ z) → Σ A λ y → x ↝ y
    dh [ a ]⁺ = _ , a
    dh (p ∷⁺ a) = dh p

  onOp : (R : Graph A ℓ₁) → FreeSemicategory (op R) ≡ op (FreeSemicategory R)
  onOp {A = A} R = funExt λ x → funExt λ y → ua (isoToEquiv (e x y))
    where
    f : {x y : A} → FreeSemicategory (op R) x y → op (FreeSemicategory R) x y
    f [ a ]⁺ = [ a ]⁺
    f (p ∷⁺ a) = snoc a (f p)
    g : {x y : A} → op (FreeSemicategory R) x y → FreeSemicategory (op R) x y
    g [ a ]⁺ = [ a ]⁺
    g (p ∷⁺ a) = snoc a (g p)
    f-snoc : {x y z : A} (a : R y z) (p : FreeSemicategory (op R) y x) → f (snoc a p) ≡ f p ∷⁺ a
    f-snoc a [ b ]⁺ = refl
    f-snoc a (p ∷⁺ b) = cong (snoc b) (f-snoc a p)
    fg : {x y : A} (p : op (FreeSemicategory R) x y) → f (g p) ≡ p
    fg [ a ]⁺ = refl
    fg (p ∷⁺ a) = f-snoc a (g p) ∙ cong (λ p → p ∷⁺ a) (fg p)
    e : (x y : A) → Iso (FreeSemicategory (op R) x y) (op (FreeSemicategory R) x y)
    g-snoc : {x y z : A} (a : R z y) (p : op (FreeSemicategory R) x y) → g (snoc a p) ≡ g p ∷⁺ a
    g-snoc a [ b ]⁺ = refl
    g-snoc a (p ∷⁺ b) = cong (snoc b) (g-snoc a p)
    gf : {x y : A} (p : FreeSemicategory (op R) x y) → g (f p) ≡ p
    gf [ a ]⁺ = refl
    gf (p ∷⁺ a) = g-snoc a (f p) ∙ cong (λ p → p ∷⁺ a) (gf p)
    Iso.fun (e x y) = f
    Iso.inv (e x y) = g
    Iso.rightInv (e x y) = fg
    Iso.leftInv (e x y) = gf

module _ {ℓ₀ : Level} {A : Type ℓ₀} (_<_ : Graph A ℓ₂) where
  open FreeSemicategory

  _<⁺_ = FreeSemicategory _<_

  WFtrans : isWellFounded _<_ → isWellFounded _<⁺_
  WFtrans wf = induction wf λ x ih → acc λ y y<⁺x → lem ih y<⁺x
    where
    lem : {x z : A} → ((y : A) → y < x → isAcc _<⁺_ y) → z <⁺ x → isAcc _<⁺_ z
    lem ih [ z<x ]⁺ = ih _ z<x
    lem  {x} {z} ih (z<⁺y ∷⁺ y<x) with lem ih [ y<x ]⁺
    ... | acc <z-isAcc = <z-isAcc _ z<⁺y

module FreeCategory where
  infixl 5 _∷_

  -- The reflexive-transitive closure
  data FreeCategory {A : Type ℓ₀} (R : Graph A ℓ₁) : Graph A (ℓ-max ℓ₀ ℓ₁) where
    [] : {x : A} → FreeCategory R x x
    _∷_ : {x y z : A} → FreeCategory R x y → R y z → FreeCategory R x z

  T = FreeCategory

  module _ {X : Type ℓ₀} {_↝_ : Graph X ℓ₁} where
    private
      _↝*_ = FreeCategory _↝_
      _↝+_ = FreeSemicategory.T _↝_

    elim :
      (P : {x y : X} → x ↝* y → Type ℓ₂) →
      ({x : X} → P ([] {x = x})) →
      ({x y z : X} (p : x ↝* y) (a : y ↝ z) → P (p ∷ a)) →
      {x y : X} (p : x ↝* y) → P p
    elim P P[] P∷ [] = P[]
    elim P P[] P∷ (x ∷ p) = P∷ x p

    rec :
      {P : Type ℓ₂} →
      ((x : X) → P) →
      ({x y z : X} → x ↝* y → y ↝ z → P) →
      {x y : X} → x ↝* y → P
    rec {P = P} P[] P∷ = elim (λ {_} {_} _ → P) (λ {x} → P[] x) P∷

    ∷-destruct : {x z : X} (q : x ↝* z) → (Σ (x ≡ z) λ p → subst (λ x → x ↝* z) p q ≡ []) ⊎ Σ X (λ y → Σ (x ↝* y) λ p → Σ (y ↝ z) λ a → q ≡ p ∷ a)
    ∷-destruct {z = z} [] = inl (refl , substRefl {B = λ x → x ↝* z} [])
    ∷-destruct (q ∷ a) = inr (_ , q , a , refl)

    -- eliminate paths with fixed endpoints
    elimPath : {x z : X} {ℓ : Level} (A : x ↝* z → Type ℓ) → ((p : x ≡ z) → A (subst⁻ (λ x → x ↝* z) p [])) → ({y : X} (p : x ↝* y) (a : y ↝ z) → A (p ∷ a)) → (p : x ↝* z) → A p
    elimPath {x = x} {z = z} A A[] A∷ p' with ∷-destruct p'
    ... | inl (p , q) = subst A lem (A[] p)
      where
      lem : subst⁻ (λ x → x ↝* z) p [] ≡ p'
      lem =
        subst⁻ (λ x → x ↝* z) p [] ≡⟨ cong (subst⁻ (λ x → x ↝* z) p) (sym q) ⟩
        subst⁻ (λ x → x ↝* z) p (subst (λ x → x ↝* z) p p') ≡⟨ subst⁻Subst (λ x → x ↝* z) p p' ⟩
        p' ∎
    ... | inr (y , p , a , q) = subst A (sym q) (A∷ p a)

    recPath : {x z : X} {ℓ : Level} {A : Type ℓ} → ((p : x ≡ z) → A) → ({y : X} (p : x ↝* y) (a : y ↝ z) → A) → x ↝* z → A
    recPath {A = A} = elimPath (λ _ → A)

    [_] : {x y : X} → x ↝ y → x ↝* y
    [ a ] = [] ∷ a

    infixr 5 _·_
    _·_ : {x y z : X} → x ↝* y → y ↝* z → x ↝* z
    p · [] = p
    p · (q ∷ a) = (p · q) ∷ a

    snoc : {x y z : X} → x ↝ y → y ↝* z → x ↝* z
    snoc a p = [ a ] · p
    
    [≡_] : {x y : X} → x ≡ y → x ↝* y
    [≡_] {x = x} p = J (λ y _ → x ↝* y) [] p

    assoc : {x y z w : X} (p : x ↝* y) (q : y ↝* z) (r : z ↝* w) → (p · q) · r ≡ p · (q · r)
    assoc p q [] = refl
    assoc p q (r ∷ a) = cong (λ p → p ∷ a) (assoc p q r)

    lUnit : {x y : X} (p : x ↝* y) → p ≡ [] · p
    lUnit [] = refl
    lUnit (p ∷ a) = cong (λ p → p ∷ a) (lUnit p)

    module _ {A : Type ℓ} {f₀ : X → A} (f : {x y : X} → x ↝ y → f₀ x ≡ f₀ y) where
      -- mapping a function to paths to the elements of the list (geometric realization)
      _* : {x y : X} → x ↝* y → f₀ x ≡ f₀ y
      _* [] = refl
      _* (p ∷ a) = _* p ∙ f a

      toPath = _*

      toPath∙ : {x y z : X} (p : x ↝* y) (q : y ↝* z) → toPath (p · q) ≡ toPath p ∙ toPath q
      toPath∙ p [] = rUnit (toPath p)
      toPath∙ p (q ∷ a) =
        toPath ((p · q) ∷ a) ≡⟨ refl ⟩
        toPath (p · q) ∙ f a ≡⟨ cong (_∙ f a) (toPath∙ p q) ⟩
        (toPath p ∙ toPath q) ∙ f a ≡⟨ sym (GL.assoc _ _ _) ⟩
        toPath p ∙ toPath q ∙ f a ≡⟨ cong (_∙_ (toPath p)) refl ⟩
        toPath p ∙ toPath (q ∷ a) ∎

      toPath∙∙ :  {x y z w : X} (p : x ↝* y) (q : y ↝* z) (r : z ↝* w) → toPath (p · q · r) ≡ toPath p ∙∙ toPath q ∙∙ toPath r
      toPath∙∙ p q r = {!!} -- using the above

    toSC : {x y z : X} (p : x ↝* y) (a : y ↝ z) → x ↝+ z
    toSC [] a = [ a ]⁺
      where open FreeSemicategory
    toSC (p ∷ b) a = toSC p b ∷⁺ a
      where open FreeSemicategory

    data isEmpty : {x y : X} → x ↝* y → Type (ℓ-max ℓ₀ ℓ₁) where
      empty[] : {x : X} → isEmpty {x} {x} []

    -- emptyPath : {x y : X} → Σ (x ↝* y) isEmpty ≃ (x ≡ y)
    -- emptyPath {x} {y} = isoToEquiv e
      -- where
      -- f : {y : X} → Σ (x ↝* y) isEmpty → x ≡ y
      -- f (.[] , empty[]) = refl
      -- g : {y : X} → x ≡ y → Σ (x ↝* y) isEmpty
      -- g = J (λ y p → Σ (x ↝* y) isEmpty) ([] , empty[])
      -- e : Iso (Σ (x ↝* y) isEmpty) (x ≡ y)
      -- Iso.fun e = f
      -- Iso.inv e = g
      -- Iso.rightInv e p = J (λ y p → f (g p) ≡ p) {!!} p
      -- Iso.leftInv e = {!!}

---
--- The free -1-groupoid (the correct notion of groupoid on a Prop)
---

module FreePregroupoid where

  infixl 5 _∷+_
  infixl 5 _∷-_

  --  groupoid closure from the right
  data FreePregroupoid {X : Type ℓ₀} (_↝_ : Graph X ℓ₁) : Graph X (ℓ-max ℓ₀ ℓ₁) where
    [] : {x : X} → FreePregroupoid _↝_ x x
    _∷+_ : {x y z : X} → FreePregroupoid _↝_ x y → y ↝ z → FreePregroupoid _ x z
    _∷-_ : {x y z : X} → FreePregroupoid _↝_ x y → z ↝ y → FreePregroupoid _ x z

  T = FreePregroupoid

  module _ {_↝_ : Graph X ℓ₁} where
    private
      _↝?_ = FreePregroupoid _↝_

    [≡_]? : {x y : X} → x ≡ y → x ↝? y
    [≡_]? {x = x} p = J (λ y _ → x ↝? y) [] p

    [_]+ : {x y : X} (a : x ↝ y) → x ↝? y
    [ a ]+ = [] ∷+ a

    [_]- : {y x : X} (a : y ↝ x) → x ↝? y
    [ a ]- = [] ∷- a

    module _ where
      open FreeCategory

      ofFC : {x y : X} → FreeCategory.T _↝_ x y → x ↝? y
      ofFC [] = []
      ofFC (p ∷ a) = ofFC p ∷+ a

    infixr 5 _·?_
    _·?_ : {x y z : X} → x ↝? y → y ↝? z → x ↝? z
    p ·? [] = p
    p ·? (q ∷+ a) = (p ·? q) ∷+ a
    p ·? (q ∷- a) = (p ·? q) ∷- a

    module _ {A : Type ℓ} {f₀ : X → A} (f : {x y : X} → x ↝ y → f₀ x ≡ f₀ y) where
      _*? : {x y : X} → x ↝? y → f₀ x ≡ f₀ y
      _*? [] = refl
      _*? (p ∷+ a) = _*? p ∙ f a
      _*? (p ∷- a) = _*? p ∙ sym (f a)

      toPath = _*?

      toPath∙∙ : {x y z w : X} (p : x ↝? y) (q : y ↝? z) (r : z ↝? w) → toPath (p ·? q ·? r) ≡ toPath p ∙∙ toPath q ∙∙ toPath r
      toPath∙∙ = {!!}

      module _ where
        open FreeCategory
        private
          _↝*_ = FreeCategory _↝_

        toPathOfFC : {x y : X} (p : x ↝* y) → _*? (ofFC p) ≡ (f *) p
        toPathOfFC [] = refl
        toPathOfFC (p ∷ a) = cong (_∙ (f a)) (toPathOfFC p)

    assoc : {x y z w : X} (p : x ↝? y) (q : y ↝? z) (r : z ↝? w) → (p ·? q) ·? r ≡ p ·? (q ·? r)
    assoc p q [] = refl
    assoc p q (r ∷+ a) = cong (λ p → p ∷+ a) (assoc p q r)
    assoc p q (r ∷- a) = cong (λ p → p ∷- a) (assoc p q r)

    lUnit : {x y : X} (p : x ↝? y) → p ≡ [] ·? p
    lUnit [] = refl
    lUnit (p ∷+ a) = cong (λ p → p ∷+ a) (lUnit p)
    lUnit (p ∷- a) = cong (λ p → p ∷- a) (lUnit p)

module FreePregroupoid' where

  infixl 5 _∷+_
  infixl 5 _∷-_

  data FreePregroupoid' {X : Type ℓ₀} (_↝_ : Graph X ℓ₁) : Graph X (ℓ-max ℓ₀ ℓ₁) where
    [] : {x : X} → FreePregroupoid' _↝_ x x
    _∷+_ : {x y z : X} → FreePregroupoid' _↝_ x y → y ↝ z → FreePregroupoid' _ x z
    _∷-_ : {x y z : X} → FreePregroupoid' _↝_ x y → z ↝ y → FreePregroupoid' _ x z
    invl : {x y z : X} (p : FreePregroupoid' _↝_ x y) (a : z ↝ y)  → (p ∷- a) ∷+ a ≡ p
    invr : {x y z : X} (p : FreePregroupoid' _↝_ x y) (a : y ↝ z) → p ∷+ a ∷- a ≡ p

  module _ {_↝_ : Graph X ℓ₁} where
    private
      _↝¿_ = FreePregroupoid' _↝_

    elim :
      {x : X} (A : {y : X} → x ↝¿ y → Type ℓ₂) →
      (f[] : A ([] {x = x}))
      (f∷+ : {y z : X} {p : x ↝¿ y} (_ : A p) (a : y ↝ z) → A (p ∷+ a))
      (f∷- : {y z : X} {p : x ↝¿ y} (_ : A p) (a : z ↝ y) → A (p ∷- a)) →
      (fl : {y z : X} {p : x ↝¿ y} (q : A p) (a : z ↝ y) → PathP (λ i → A (invl p a i)) (f∷+ (f∷- q a) a) q)
      (fr : {y z : X} {p : x ↝¿ y} (q : A p) (a : y ↝ z) → PathP (λ i → A (invr p a i)) (f∷- (f∷+ q a) a) q)
      {y : X} (p : x ↝¿ y) → A p
    elim {x = x} A f[] f∷+ f∷- fl fr = e
      where
      e : {y : X} (p : x ↝¿ y) → A p
      e [] = f[]
      e (p ∷+ a) = f∷+ (e p) a
      e (p ∷- a) = f∷- (e p) a
      e (invl p a i) = fl (e p) a i
      e (invr p a i) = fr (e p) a i

    rec :
      {x : X} {A : Type ℓ₂} →
      (f[] : A)
      (f∷+ : {y z : X} → A → y ↝ z → A)
      (f∷- : {y z : X} → A → z ↝ y → A) →
      (fl : {y z : X} (q : A) (a : z ↝ y) → f∷+ (f∷- q a) a ≡ q)
      (fr : {y z : X} (q : A) (a : y ↝ z) → f∷- (f∷+ q a) a ≡ q)
      {y : X} (p : x ↝¿ y) → A
    rec {x = x} {A} f[] f∷+ f∷- fl fr = elim (λ _ → A) f[] f∷+ f∷- fl fr

    elim≃ :
      {x : X} (A : {y : X} → x ↝¿ y → Type ℓ₂) →
      (f[] : A ([] {x = x}))
      (f≃ : {y z : X} {p : x ↝¿ y} (a : y ↝ z) → A p ≃ A (p ∷+ a))
      {y : X} (p : x ↝¿ y) → A p
    elim≃ {x = x} A f[] f≃ p = elim A f[] (λ x a → equivFun (f≃ a) x) f∷- {!!} {!!} p
      where
      f∷- : {y z : X} {p : x ↝¿ y} (_ : A p) (a : z ↝ y) → A (p ∷- a)
      f∷- x a = invEq (f≃ a) (subst A (sym (invl _ a)) x)

---
--- The free higher groupoid
---

module FreeGroupoid where

  infixl 5 _∷+_
  infixl 5 _∷-_

  --  groupoid closure from the right
  data FreeGroupoid {X : Type ℓ₀} (_↝_ : Graph X ℓ₁) : Graph X (ℓ-max ℓ₀ ℓ₁) where
    [] : {x : X} → FreeGroupoid _↝_ x x
    _∷+_ : {x y z : X} → FreeGroupoid _↝_ x y → y ↝ z → FreeGroupoid _ x z
    _∷-_ : {x y z : X} → FreeGroupoid _↝_ x y → z ↝ y → FreeGroupoid _ x z
    invl : {x y z : X} (p : FreeGroupoid _↝_ x y) (a : z ↝ y)  → (p ∷- a) ∷+ a ≡ p
    invr : {x y z : X} (p : FreeGroupoid _↝_ x y) (a : y ↝ z) → p ∷+ a ∷- a ≡ p
    coh  : {x y z : X} (p : FreeGroupoid _↝_ x y) (a : y ↝ z) → cong (λ p → p ∷+ a) (invr p a) ≡ invl (p ∷+ a) a

  T = FreeGroupoid

  module _ {_↝_ : Graph X ℓ₁} where
    private
      _↝!_ = FreeGroupoid _↝_

    [≡_]! : {x y : X} → x ≡ y → x ↝! y
    [≡_]! {x = x} p = J (λ y _ → x ↝! y) [] p

    -- plain elimination principle
    elim :
      {x : X} (A : {y : X} → x ↝! y → Type ℓ₂) →
      (f[] : A ([] {x = x}))
      (f∷+ : {y z : X} {p : x ↝! y} (_ : A p) (a : y ↝ z) → A (p ∷+ a))
      (f∷- : {y z : X} {p : x ↝! y} (_ : A p) (a : z ↝ y) → A (p ∷- a)) →
      (fl : {y z : X} {p : x ↝! y} (q : A p) (a : z ↝ y) → PathP (λ i → A (invl p a i)) (f∷+ (f∷- q a) a) q)
      (fr : {y z : X} {p : x ↝! y} (q : A p) (a : y ↝ z) → PathP (λ i → A (invr p a i)) (f∷- (f∷+ q a) a) q)
      (fc : {y z : X} {p : x ↝! y} (q : A p) (a : y ↝ z) → PathP (λ i → PathP (λ j → A (coh p a i j)) (f∷+ (f∷- (f∷+ q a) a) a) (f∷+ q a)) (congP (λ _ q → f∷+ q a) (fr q a)) (fl (f∷+ q a) a)) →
      {y : X} (p : x ↝! y) → A p
    elim {x = x} A f[] f∷+ f∷- fl fr fc = e
      where
      e : {y : X} (p : x ↝! y) → A p
      e [] = f[]
      e (p ∷+ a) = f∷+ (e p) a
      e (p ∷- a) = f∷- (e p) a
      e (invl p a i) = fl (e p) a i
      e (invr p a i) = fr (e p) a i
      e (coh p a i j) = fc (e p) a i j

    rec :
      {x : X} {A : Type ℓ₂} →
      (f[] : A)
      (f∷+ : {y z : X} → A → y ↝ z → A)
      (f∷- : {y z : X} → A → z ↝ y → A) →
      (fl : {y z : X} (q : A) (a : z ↝ y) → f∷+ (f∷- q a) a ≡ q)
      (fr : {y z : X} (q : A) (a : y ↝ z) → f∷- (f∷+ q a) a ≡ q)
      (fc : {y z : X} (q : A) (a : y ↝ z) → cong (λ q → f∷+ q a) (fr q a) ≡ fl (f∷+ q a) a) →
      {y : X} (p : x ↝! y) → A
    rec {x = x} {A} f[] f∷+ f∷- fl fr fc = elim (λ _ → A) f[] f∷+ f∷- fl fr fc

    infixr 5 _·!_
    _·!_ : {x y z : X} → x ↝! y → y ↝! z → x ↝! z
    p ·! q = elim (λ {z} q → _ ↝! z) p (λ r a → r ∷+ a) (λ r a → r ∷- a) (λ r a → invl r a) (λ r a → invr r a) (λ r a → coh r a) q

    -- alternative recurrence principle to an equivalence
    recHAEquiv :
      {x : X} {A : Type ℓ₂} →
      (f[] : A)
      (f≃ : HAEquiv A A)
      {y : X} (p : x ↝! y) → A
    recHAEquiv f[] f≃ = rec f[] (λ a _ → fst f≃ a) (λ a _ → snd f≃ .isHAEquiv.g a ) (λ p _ → snd f≃ .isHAEquiv.rinv p) (λ p _ → snd f≃ .isHAEquiv.linv p) (λ p _ → snd f≃ .isHAEquiv.com p)

    rec≃ :
      {x : X} {A : Type ℓ₂} →
      (f[] : A)
      (f≃ : A ≃ A)
      {y : X} (p : x ↝! y) → A
    rec≃ f[] f≃ = recHAEquiv f[] (equiv→HAEquiv f≃)

    compIsoR : (x : X) {y z : X} (a : y ↝ z) → Iso (x ↝! y) (x ↝! z)
    compIsoR x {y} {z} a = e
      where
      e : Iso (x ↝! y) (x ↝! z)
      Iso.fun e p = p ∷+ a
      Iso.inv e p = p ∷- a
      Iso.rightInv e p = invl p a
      Iso.leftInv e p = invr p a

    compEquivR : (x : X) {y z : X} (a : y ↝ z) → x ↝! y ≃ x ↝! z
    compEquivR x {y} {z} a = isoToEquiv (compIsoR x a)

    compHAEquivR : (x : X) {y z : X} (a : y ↝ z) → HAEquiv (x ↝! y) (x ↝! z)
    compHAEquivR x {y} {z} a = f , e
      where
      f : x ↝! y → x ↝! z
      f p = p ∷+ a
      e : isHAEquiv f
      isHAEquiv.g e p = p ∷- a
      isHAEquiv.linv e p = invr p a
      isHAEquiv.rinv e p = invl p a
      isHAEquiv.com e p = coh p a

    compIsoR⁻ : (x : X) {y z : X} (a : z ↝ y) → Iso (x ↝! y) (x ↝! z)
    compIsoR⁻ x {y} {z} a = e
      where
      e : Iso (x ↝! y) (x ↝! z)
      Iso.fun e p = p ∷- a
      Iso.inv e p = p ∷+ a
      Iso.rightInv e p = invr p a
      Iso.leftInv e p = invl p a

    -- packed elimination principle to an equivalence
    module ElimEquiv
      {x : X} (A : {y : X} → x ↝! y → Type ℓ₂)
      (f[] : A ([] {x = x}))
      (f≃ : {y z : X} (p : x ↝! y) (a : y ↝ z) → A p ≃ A (p ∷+ a))
      where

      f : {y z : X} (p : x ↝! y) (a : y ↝ z) → A p → A (p ∷+ a)
      f p a k = equivFun (f≃ p a) k
      f⁻ : {y z : X} (p : x ↝! y) (a : y ↝ z) → A (p ∷+ a) → A p
      f⁻ p a k = invEq (f≃ p a) k
      g : {y z : X} (p : x ↝! y) (a : z ↝ y) → A p → A (p ∷- a)
      g p a k =  f⁻ (p ∷- a) a (subst⁻ A (invl p a) k)
      g⁻ : {y z : X} (p : x ↝! y) (a : z ↝ y) → A (p ∷- a) → A p
      g⁻ p a k = subst A (invl p a) (f (p ∷- a) a k)
      g≃ : {y z : X} (p : x ↝! y) (a : z ↝ y) → A p ≃ A (p ∷- a)
      g≃ p a = isoToEquiv e
        where
        e : Iso (A p) (A (p ∷- a))
        Iso.fun e k = g p a k
        Iso.inv e k = g⁻ p a k
        Iso.rightInv e k =
          g p a (g⁻ p a k) ≡⟨ refl ⟩
          f⁻ (p ∷- a) a (subst⁻ A (invl p a) (subst A (invl p a) (f (p ∷- a) a k))) ≡⟨ cong (f⁻ (p ∷- a) a) (subst⁻Subst A (invl p a) _) ⟩
          f⁻ (p ∷- a) a (f (p ∷- a) a k)                                            ≡⟨ retEq (f≃ (p ∷- a) a) k ⟩
          k ∎
        Iso.leftInv e k =
          g⁻ p a (g p a k) ≡⟨ refl ⟩
          subst A (invl p a) (f (p ∷- a) a (f⁻ (p ∷- a) a (subst⁻ A (invl p a) k))) ≡⟨ cong (subst A (invl p a)) (secEq (f≃ (p ∷- a) a) _) ⟩
          subst A (invl p a) (subst⁻ A (invl p a) k)                                ≡⟨ substSubst⁻ A (invl p a) k ⟩
          k ∎
      fg : {y z : X} (p : x ↝! y) (a : z ↝ y) (k : A p) → subst A (invl p a) (f (p ∷- a) a (g p a k)) ≡ k
      fg p a k = retEq (g≃ p a) k
      gf : {y z : X} (p : x ↝! y) (a : y ↝ z) (k : A p) → subst A (invr p a) (g (p ∷+ a) a (f p a k)) ≡ k
      gf p a k = lem -- secEq f through h- = f-
        where
        nat : {y z : X} (p q : x ↝! y) (P : p ≡ q) (a : y ↝ z) (k : A (p ∷+ a)) → subst A P (f⁻ p a k) ≡ f⁻ q a (subst A (cong (λ p → p ∷+ a) P) k)
        nat p q P a k = J (λ q P → subst A P (f⁻ p a k) ≡ f⁻ q a (subst A (cong (λ p → p ∷+ a) P) k)) (substRefl {B = A} (f⁻ p a k) ∙ cong (f⁻ p a) (sym (substRefl {B = A} k))) P
        zigzag : sym (invl (p ∷+ a) a) ∙ cong (λ p → p ∷+ a) (invr p a) ≡ refl
        zigzag =
          sym (invl (p ∷+ a) a) ∙ cong (λ p → p ∷+ a) (invr p a) ≡⟨ cong (_∙_ (sym (invl (p ∷+ a) a))) (coh p a) ⟩
          sym (invl (p ∷+ a) a) ∙ invl (p ∷+ a) a ≡⟨ lCancel _ ⟩
          refl ∎
        lem : subst A (invr p a) (f⁻ (p ∷+ a ∷- a) a (subst⁻ A (invl (p ∷+ a) a) (f p a k))) ≡ k
        lem =
          subst A (invr p a) (f⁻ (p ∷+ a ∷- a) a (subst⁻ A (invl (p ∷+ a) a) (f p a k))) ≡⟨ nat _ _ _ _ _ ⟩
          f⁻ p a (subst A (cong (λ p → p ∷+ a) (invr p a)) (subst⁻ A (invl (p ∷+ a) a) (f p a k))) ≡⟨ cong (f⁻ p a) (sym (substComposite A _ _ _) ∙ funExt⁻ (cong (subst A) zigzag) (f p a k) ∙ substRefl {B = A} (f p a k)) ⟩
          f⁻ p a (f p a k) ≡⟨ retEq (f≃ p a) k ⟩
          k ∎
      -- fgf : {y z : X} (p : x ↝! y) (a : y ↝ z) (k : A p) → {!gf p a k!} ≡ fg (p ∷+ a) a (f p a k)
      -- fgf p a k = {!!}
  
      fIsoOver : {y z : X} (a : y ↝ z) → IsoOver (compIsoR x a) A A
      IsoOver.fun (fIsoOver a) p k = f p a k
      IsoOver.inv (fIsoOver a) p k = g p a k
      IsoOver.rightInv (fIsoOver {y} {z} a) p k = toPathP (fg p a k)
      IsoOver.leftInv (fIsoOver a) p k = toPathP (gf p a k)
  
      fHAEquivOver0 : {y z : X} (a : y ↝ z) → HAEquivOver A A (iso→HAEquiv (compIsoR x a))
      fHAEquivOver0 a = IsoOver.fun (fIsoOver a) , IsoOver→HAEquivOver (fIsoOver a)

      -- TODO: is there a more direct way to perform this??? (from the above data...)
      fHAEquivOver : {y z : X} (a : y ↝ z) → HAEquivOver A A (compHAEquivR x a)
      fHAEquivOver a = fun , isHAE'
        where
        fun : mapOver (compIsoR x a .Iso.fun) A A
        fun = IsoOver.fun (fIsoOver a)
        isHAE : isHAEquivOver (iso→HAEquiv (compIsoR x a)) A A fun
        isHAE = IsoOver→HAEquivOver (fIsoOver a)
        lem : iso→HAEquiv (compIsoR x a) ≡ compHAEquivR x a
        lem = Σ≡Prop (λ f → isPropIsHAEquiv {f = f}) refl
        lem' : PathP
          (λ i → (fun : mapOver (lem i .fst) A A) → Type _)
          (isHAEquivOver (iso→HAEquiv (compIsoR x a)) A A)
          (isHAEquivOver (compHAEquivR x a) A A)
        lem' = funExt⁻ (funExt⁻ (cong isHAEquivOver lem) A) A
        lem'' : isHAEquivOver (iso→HAEquiv (compIsoR x a)) A A ≡ isHAEquivOver (compHAEquivR x a) A A
        lem'' = sym (transportRefl _) ∙ fromPathP lem'
        abstract
          isHAE' : isHAEquivOver (compHAEquivR x a) A A fun
          isHAE' = transport (funExt⁻ lem'' fun) isHAE

      elim≃ : {y : X} (p : x ↝! y) → A p
      elim≃ = elim (λ {y} p → A p)
        f[]
        (λ {y} {z} {p} k a → fst (fHAEquivOver a) p k)
        (λ {y} {z} {p} k a → isHAEquivOver.inv (snd (fHAEquivOver a)) p k)
        (λ {y} {z} {p} k a → isHAEquivOver.rinv (snd (fHAEquivOver a)) p k)
        (λ {y} {z} {p} k a → isHAEquivOver.linv (snd (fHAEquivOver a)) p k)
        (λ {y} {z} {p} k a → isHAEquivOver.com (snd (fHAEquivOver a)) k)

    open ElimEquiv public using (elim≃)

    -- elimination to a Prop
    elimProp :
      {x : X}
      (A : {y : X} → x ↝! y → Type ℓ₂) →
      (AP : {y : X} (p : x ↝! y) → isProp (A p)) →
      (f[] : A ([] {x = x}))
      (f∷+ : {y z : X} {p : x ↝! y} (_ : A p) (a : y ↝ z) → A (p ∷+ a))
      (f∷- : {y z : X} {p : x ↝! y} (_ : A p) (a : z ↝ y) → A (p ∷- a)) →
      {y : X} (p : x ↝! y) → A p
    elimProp {x = x} A AP f[] f∷+ f∷- = elim A f[] f∷+ f∷- (λ _ _ → toPathP (AP _ _ _)) (λ _ _ → toPathP (AP _ _ _)) (λ _ _ → isProp→SquareP (λ _ _ → AP _) _ _ _ _)

    module _ where
      open FreeSemicategory
      ofSC : {x y : X} → (FreeSemicategory.FreeSemicategory _↝_ x y) → x ↝! y
      ofSC [ a ]⁺ = [] ∷+ a
      ofSC (p ∷⁺ a) = ofSC p ∷+ a

    module _ where
      open FreePregroupoid
      ofPG : {x y : X} → (FreePregroupoid.FreePregroupoid _↝_ x y) → x ↝! y
      ofPG [] = []
      ofPG (p ∷+ x) = ofPG p ∷+ x
      ofPG (p ∷- x) = ofPG p ∷- x

    module _ where
      open import Cubical.HITs.SetTruncation as ST

      private
        _↝?_ = FreeSemicategory.FreeSemicategory _↝_

      setTruncation : (x y : X) → ∥ x ↝! y ∥₂ ≃ x ↝? y
      setTruncation x y = {!!}
