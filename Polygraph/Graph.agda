{-# OPTIONS --allow-unsolved-metas --cubical #-}

module Graph where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Induction.WellFounded renaming
  (
    Rel to Graph;
    Acc to isAcc;
    WellFounded to isWellFounded
  ) public

induction = WFI.induction

private variable
  ℓ₀ ℓ₁ ℓ₂ : Level
  A : Type ℓ₀
  X : Type ℓ₀
  R : Graph A ℓ₁

op : Graph A ℓ₁ → Graph A ℓ₁
op R x y = R y x

op² : (R : Graph A ℓ₁) → op (op R) ≡ R
op² R = funExt λ x → funExt λ y → refl

---
--- Symmetric closure
---

data SymClosure {A : Type ℓ₀} (R : Graph A ℓ₁) : Graph A (ℓ-max ℓ₀ ℓ₁) where
  σ+ : {a b : A} → R a b → SymClosure R a b
  σ- : {a b : A} → R a b → SymClosure R b a

---
--- The transitive closure
---

data TransClosure {A : Type ℓ₀} (R : Graph A ℓ₁) : Graph A (ℓ-max ℓ₀ ℓ₁) where
  [_]⁺ : {a b : A} → R a b → TransClosure R a b
  _∷⁺_ : {a b c : A} → R a b → TransClosure R b c → TransClosure R a c

hd : {a c : A} (p : TransClosure R a c) → Σ A (λ b → R a b)
hd [ x ]⁺ = _ , x
hd (x ∷⁺ p) = _ , x

snoc⁺ : {a b c : A} → TransClosure R a b → R b c → TransClosure R a c
snoc⁺ [ x ]⁺ y = x ∷⁺ [ y ]⁺
snoc⁺ (x ∷⁺ p) y = x ∷⁺ snoc⁺ p y

transOp : (R : Graph A ℓ₁) → TransClosure (op R) ≡ op (TransClosure R)
transOp {A = A} R = funExt λ x → funExt λ y → ua (isoToEquiv (iso F G FG GF))
  where
  F  : {x y : A} → TransClosure (op R) x y → op (TransClosure R) x y
  F [ x ]⁺ = [ x ]⁺
  F (x ∷⁺ p) = snoc⁺ (F p) x
  G : {x y : A} → op (TransClosure R) x y → TransClosure (op R) x y
  G [ x ]⁺ = [ x ]⁺
  G (x ∷⁺ p) = snoc⁺ (G p) x
  F-snoc : {x y z : A} (p : TransClosure (op R) x y) (q : R z y) → F (snoc⁺ p q) ≡ q ∷⁺ (F p)
  F-snoc [ x ]⁺ q = refl
  F-snoc (x ∷⁺ p) q = cong (λ p → snoc⁺ p x) (F-snoc p q)
  G-snoc : {x y z : A} (p : op (TransClosure R) y z) (q : R y x) → G (snoc⁺ p q) ≡ q ∷⁺ G p
  G-snoc [ x ]⁺ q = refl
  G-snoc (x ∷⁺ p) q = cong (λ p → snoc⁺ p x) (G-snoc p q)
  FG : {x y : A} (p : op (TransClosure R) x y) → F (G p) ≡ p
  FG [ x ]⁺ = refl
  FG (x ∷⁺ p) = F-snoc (G p) x ∙ cong (λ p → x ∷⁺ p) (FG p)
  GF : {x y : A} (p : TransClosure (op R) x y) → G (F p) ≡ p
  GF [ x ]⁺ = refl
  GF (x ∷⁺ p) = G-snoc (F p) x ∙ cong (λ p → x ∷⁺ p) (GF p)

module _ {A : Type ℓ₀} (_<_ : Graph A ℓ₂) where
  _<⁺_ = TransClosure _<_

  WFtrans : isWellFounded _<_ → isWellFounded _<⁺_
  WFtrans wf = induction wf (λ a ih → acc (λ c a<⁺c → lem ih a<⁺c))
    where
    lem : {a c : A} → ((b : A) → b < a → isAcc _<⁺_ b) → c <⁺ a → isAcc _<⁺_ c
    lem ih [ a<c ]⁺ = ih _ a<c
    lem ih (c<b ∷⁺ b<⁺a) with lem ih b<⁺a
    ... | acc <b-is-acc = <b-is-acc _ [ c<b ]⁺

infixr 5 _∷_

-- The reflexive-transitive closure
data TransReflClosure {A : Type ℓ₀} (R : Graph A ℓ₁) : Graph A (ℓ-max ℓ₀ ℓ₁) where
  [] : {a : A} → TransReflClosure R a a
  _∷_ : {a b c : A} → R a b → TransReflClosure R b c → TransReflClosure R a c

∷-elim :
  (P : {a b : A} → TransReflClosure R a b → Set ℓ₂) →
  ({a : A} → P ([] {a = a})) →
  ({a b c : A} (x : R a b) (p : TransReflClosure R b c) → P (x ∷ p)) →
  {a b : A} (p : TransReflClosure R a b) → P p
∷-elim P P[] P∷ [] = P[]
∷-elim P P[] P∷ (x ∷ p) = P∷ x p

∷-rec :
  {P : Set ℓ₂} →
  ((a : A) → P) →
  ({a b c : A} → R a b → TransReflClosure R b c → P) →
  {a b : A} → TransReflClosure R a b → P
∷-rec {P = P} P[] P∷ = ∷-elim (λ {_} {_} _ → P) (λ {a} → P[] a) P∷

∷-destruct : {a c : A} (q : TransReflClosure R a c) → (Σ (a ≡ c) (λ p → PathP (λ i → TransReflClosure R (p i) c) q [])) ⊎ Σ A (λ b → Σ (R a b) λ x → Σ (TransReflClosure R b c) λ p → q ≡ x ∷ p)
∷-destruct [] = inl (refl , refl)
∷-destruct (x ∷ q) = inr (_ , x , q , refl)

[_] : {a b : A} → R a b → TransReflClosure R a b
[ p ] = p ∷ []

infixr 5 _·_
_·_ : {a b c : A} → TransReflClosure R a b → TransReflClosure R b c → TransReflClosure R a c
[] · q = q
(x ∷ p) · q = x ∷ (p · q)

[≡_] : {ℓ₀ ℓ₁ : Level} {A : Type ℓ₀} {R : Graph A ℓ₁} {a a' : A} → a ≡ a' → TransReflClosure R a a'
[≡_] {R = R} {a = a} p = J (λ a' _ → TransReflClosure R a a') [] p

·-assoc : {a b c d : A} (p : TransReflClosure R a b) (q : TransReflClosure R b c) (r : TransReflClosure R c d) → (p · q) · r ≡ p · (q · r)
·-assoc [] q r = refl
·-assoc (x ∷ p) q r = cong (λ p → x ∷ p) (·-assoc p q r)

·-unitr : {a b : A} (p : TransReflClosure R a b) → p · [] ≡ p
·-unitr [] = refl
·-unitr (x ∷ p) = cong (λ p → x ∷ p) (·-unitr p)

t→rt : {a b : A} → TransClosure R a b → TransReflClosure R a b
t→rt [ x ]⁺ = x ∷ []
t→rt (x ∷⁺ p) = {!x ∷ (t→rt p)!}

rt→t : {a b c : A} → R a b → TransReflClosure R b c → TransClosure R a c
rt→t a<b [] = [ a<b ]⁺
rt→t a<b (b<b' ∷ b'<*c) = a<b ∷⁺ rt→t b<b' b'<*c

append : {a b c : A} → TransClosure R a b → TransReflClosure R b c → TransClosure R a c
append [ x ]⁺ q = rt→t x q
append (x ∷⁺ p) q = x ∷⁺ append p q

---
--- Path induction
---

module PI (R : Graph X ℓ₁) where
  open import Cubical.Categories.Category.Precategory

  _↝_ = R

  module _ (x₀ : X) where

    C : Precategory _ _
    Precategory.ob C = Σ (X → Type _) (λ K → K x₀ × ({x y : X} → x ↝ y → K x ≃ K y))
    Precategory.Hom[_,_] C (K , r , e) (K' , r' , e') = Σ ((x : X) → K x → K' x) (λ f → (f x₀ r ≡ r') × ({x y : X} (a : x ↝ y) (k : K x) →  equivFun (e' a) (f x k) ≡ f y (equivFun (e a) k)))
    Precategory.id C = (λ x k → k) , refl , λ s k → refl
    Precategory._⋆_ C (f , δ , γ) (f' , δ' , γ') = (λ x k → f' x (f x k)) , cong (f' x₀) δ ∙ δ' , λ s k → {!!}
    Precategory.⋆IdL C = {!!}
    Precategory.⋆IdR C = {!!}
    Precategory.⋆Assoc C = {!!}

    open import Cubical.HITs.TypeQuotients as TQ

    init : Precategory.ob C
    init = (λ x → TQ.[ x₀ ] ≡ TQ.[ x ]) , refl , λ a → isoToEquiv (act a)
      where
      act : {x y : X} (a : x ↝ y) → Iso (TQ.[ x₀ ] ≡ TQ.[ x ]) (TQ.[ x₀ ] ≡ TQ.[ y ])
      Iso.fun (act a) p = p ∙ eq/ _ _ a
      Iso.inv (act a) p = p ∙ sym (eq/ _ _ a)
      Iso.rightInv (act a) p = sym (assoc _ _ _) ∙ cong (λ q → p ∙ q) (lCancel (eq/ _ _ a)) ∙ sym (rUnit p)
      Iso.leftInv (act a) p = sym (assoc _ _ _) ∙ cong (λ q → p ∙ q) (rCancel (eq/ _ _ a)) ∙ sym (rUnit p)

---
--- The free higher groupoid
---

-- data GpdClosure {A : Type ℓ₀} (R : Graph A ℓ₁) : Graph A (ℓ-max ℓ₀ ℓ₁) where
  -- ∣_∣  : {a b : A} → TransReflClosure (SymClosure R) a b → GpdClosure R a b
  -- invl : {a b c : A} (x : R a b) (p : TransReflClosure (SymClosure R) b c) → ∣ σ- x ∷ σ+ x ∷ p ∣ ≡ ∣ p ∣
  -- invr : {a b c : A} (x : R b a) (p : TransReflClosure (SymClosure R) b c) → ∣ σ+ x ∷ σ- x ∷ p ∣ ≡ ∣ p ∣
  -- coh  : {a b c : A} (x : R a b) (p : TransReflClosure (SymClosure R) b c) → {!cong (λ p → σ+ x ∷ p) (invl x p)!}

infixr 5 _+∷_
infixr 5 _-∷_

data GpdClosure {X : Type ℓ₀} (R : Graph X ℓ₁) : Graph X (ℓ-max ℓ₀ ℓ₁) where
  [] : {x : X} → GpdClosure R x x
  _+∷_ : {x y z : X} → R x y → GpdClosure R y z → GpdClosure R x z
  _-∷_ : {x y z : X} → R y x → GpdClosure R y z → GpdClosure R x z
  invl : {x y z : X} (a : R x y) (p : GpdClosure R y z) → a -∷ a +∷ p ≡ p
  invr : {x y z : X} (a : R y x) (p : GpdClosure R y z) → a +∷ a -∷ p ≡ p
  coh  : {x y z : X} (a : R x y) (p : GpdClosure R y z) → cong (a +∷_) (invl a p) ≡ invr a (a +∷ p)

GpdClosure-elim :
  {X : Type ℓ₀} (R : Graph X ℓ₁) (A : {x y : X} → GpdClosure R x y → Type ℓ₂)
  (f[] : {x : X} → A ([] {x = x}))
  (f+∷ : {x y z : X} (a : R x y) {p : GpdClosure R y z} → A p → A (a +∷ p))
  (f-∷ : {x y z : X} (a : R y x) {p : GpdClosure R y z} → A p → A (a -∷ p))
  (fl : {x y z : X} (a : R x y) {p : GpdClosure R y z} (q : A p) → PathP (λ i → A (invl a p i)) (f-∷ a (f+∷ a q)) q)
  (fr : {x y z : X} (a : R y x) {p : GpdClosure R y z} (q : A p) → PathP (λ i → A (invr a p i)) (f+∷ a (f-∷ a q)) q)
  (fc : {x y z : X} (a : R x y) {p : GpdClosure R y z} (q : A p) → SquareP (λ i j → A (coh a p i j)) (congP (λ _ → f+∷ a) (fl a q)) (fr a (f+∷ a q)) (λ _ → f+∷ a (f-∷ a (f+∷ a q))) (λ _ → f+∷ a q)) →
  -- PathP (λ i → PathP (λ j → A (coh a p i j)) (f+∷ a (f-∷ a (f+∷ a q))) (f+∷ a q)) (congP (λ _ q → f+∷ a q) (fl a q)) (fr a (f+∷ a q))
  {x y : X} (p : GpdClosure R x y) → A p
GpdClosure-elim {X = X} R A f[] f+∷ f-∷ fl fr fc = e
  where
  e : {x y : X} (p : GpdClosure R x y) → A p
  e [] = f[]
  e (a +∷ p) = f+∷ a (e p)
  e (a -∷ p) = f-∷ a (e p)
  e (invl a p i) = fl a (e p) i
  e (invr a p i) = fr a (e p) i
  e (coh a p i j) = fc a (e p) i j

-- -- trying to define an elimination principle without dependent paths...
-- GpdClosure-elim2 :
  -- {X : Type ℓ₀} (R : Graph X ℓ₁) (A : {x y : X} → GpdClosure R x y → Type ℓ₂)
  -- (f[] : {x : X} → A ([] {x = x}))
  -- (f+∷ : {x y z : X} (a : R x y) {p : GpdClosure R y z} → A p → A (a +∷ p))
  -- (f-∷ : {x y z : X} (a : R y x) {p : GpdClosure R y z} → A p → A (a -∷ p))
  -- (fl : {x y z : X} (a : R x y) {p : GpdClosure R y z} (q : A p) → subst A (invl a p) (f-∷ a (f+∷ a q)) ≡ q)
  -- (fr : {x y z : X} (a : R y x) {p : GpdClosure R y z} (q : A p) → subst A (invr a p) (f+∷ a (f-∷ a q)) ≡ q)
  -- (fc : {x y z : X} (a : R x y) {p : GpdClosure R y z} (q : A p) → {!!} ≡ {!fr!}) →
  -- {x y : X} (p : GpdClosure R x y) → A p
-- GpdClosure-elim2 {X = X} R A f[] f+∷ f-∷ fl fr fc =
  -- GpdClosure-elim R A f[] f+∷ f-∷ (λ a q → toPathP (fl a q)) (λ a q → toPathP (fr a q)) lem
  -- where
  -- lem : {x y : X} {z : X} (a : R x y) {p : GpdClosure R y z} (q : A p) →
    -- -- PathP
      -- -- (λ i → PathP (λ j → A (coh a p i j)) (f+∷ a (f-∷ a (f+∷ a q))) (f+∷ a q))
      -- -- (congP (λ _ → f+∷ a) (toPathP (fl a q)))
      -- -- (toPathP (fr a (f+∷ a q)))
    -- SquareP (λ i j → A (coh a p i j))
      -- (congP (λ _ → f+∷ a) (toPathP (fl a q)))
      -- (toPathP (fr a (f+∷ a q)))
      -- (λ _ → f+∷ a (f-∷ a (f+∷ a q)))
      -- (λ _ → f+∷ a q)
  -- lem a q = toPathP ({!!} ∙ cong toPathP {!!})

GpdClosure-rec :
  {X : Type ℓ₀} (R : Graph X ℓ₁) {A : Type ℓ₂} →
  (f[] : {x : X} → A)
  (f+∷ : {x y z : X} → R x y → GpdClosure R y z → A → A)
  (f-∷ : {x y z : X} → R y x → GpdClosure R y z → A → A) →
  (fl : {x y z : X} (a : R x y) (p : GpdClosure R y z) (q : A) → f-∷ a (a +∷ p) (f+∷ a p q) ≡ q)
  (fr : {x y z : X} (a : R y x) (p : GpdClosure R y z) (q : A) → f+∷ a (a -∷ p) (f-∷ a p q) ≡ q)
  (fc : {x y z : X} (a : R x y) (p : GpdClosure R y z) (q : A) → congP (λ i q → f+∷ a (invl a p i) q) (fl a p q) ≡ fr a (a +∷ p) (f+∷ a p q)) →
  {x y : X} (p : GpdClosure R x y) → A
GpdClosure-rec R {A} f[] f+∷ f-∷ fl fr fc p =
  GpdClosure-elim R (λ _ → A) (λ {x} → f[] {x}) (λ a {p} α → f+∷ a p α) (λ a {p} α → f-∷ a p α) (λ a q → fl a _ q) (λ a q → fr a _ q) (λ a q → fc a _ q) p

infixl 5 _∷+_
infixl 5 _∷-_

--  groupoid closure from the right
data GpC {X : Type ℓ₀} (R : Graph X ℓ₁) : Graph X (ℓ-max ℓ₀ ℓ₁) where
  [] : {x : X} → GpC R x x
  _∷+_ : {x y z : X} → GpC R x y → R y z → GpC R x z
  _∷-_ : {x y z : X} → GpC R x y → R z y → GpC R x z
  invl : {x y z : X} (p : GpC R x y) (a : R z y)  → (p ∷- a) ∷+ a ≡ p
  invr : {x y z : X} (p : GpC R x y) (a : R y z) → p ∷+ a ∷- a ≡ p
  coh  : {x y z : X} (p : GpC R x y) (a : R y z) → cong (λ p → p ∷+ a) (invr p a) ≡ invl (p ∷+ a) a

-- plain elimination principle
GpC-elim :
  {X : Type ℓ₀} {x : X} (R : Graph X ℓ₁) (A : {y : X} → GpC R x y → Type ℓ₂) →
  (f[] : A ([] {x = x}))
  (f∷+ : {y z : X} {p : GpC R x y} (_ : A p) (a : R y z) → A (p ∷+ a))
  (f∷- : {y z : X} {p : GpC R x y} (_ : A p) (a : R z y) → A (p ∷- a)) →
  (fl : {y z : X} {p : GpC R x y} (q : A p) (a : R z y) → PathP (λ i → A (invl p a i)) (f∷+ (f∷- q a) a) q)
  (fr : {y z : X} {p : GpC R x y} (q : A p) (a : R y z) → PathP (λ i → A (invr p a i)) (f∷- (f∷+ q a) a) q)
  (fc : {y z : X} {p : GpC R x y} (q : A p) (a : R y z) → PathP (λ i → PathP (λ j → A (coh p a i j)) (f∷+ (f∷- (f∷+ q a) a) a) (f∷+ q a)) (congP (λ _ q → f∷+ q a) (fr q a)) (fl (f∷+ q a) a)) →
  {y : X} (p : GpC R x y) → A p
GpC-elim {X = X} {x = x} R A f[] f+∷ f-∷ fl fr fc = e
  where
  e : {y : X} (p : GpC R x y) → A p
  e [] = f[]
  e (p ∷+ a) = f+∷ (e p) a
  e (p ∷- a) = f-∷ (e p) a
  e (invl p a i) = fl (e p) a i
  e (invr p a i) = fr (e p) a i
  e (coh p a i j) = fc (e p) a i j

GpC-rec :
  {X : Type ℓ₀} {x : X} (R : Graph X ℓ₁) {A : Type ℓ₂} →
  (f[] : A)
  (f+∷ : {y z : X} → A → R y z → A)
  (f-∷ : {y z : X} → A → R z y → A) →
  (fl : {y z : X} (q : A) (a : R z y) → f+∷ (f-∷ q a) a ≡ q)
  (fr : {y z : X} (q : A) (a : R y z) → f-∷ (f+∷ q a) a ≡ q)
  (fc : {y z : X} (q : A) (a : R y z) → cong (λ q → f+∷ q a) (fr q a) ≡ fl (f+∷ q a) a) →
  {y : X} (p : GpC R x y) → A
GpC-rec {X = X} {x = x} R {A} f[] f+∷ f-∷ fl fr fc = GpC-elim R (λ _ → A) f[] f+∷ f-∷ fl fr fc

-- alternative recurrence principle to an equivalence
GpC-recHAEquiv : 
  {X : Type ℓ₀} {x : X} (R : Graph X ℓ₁) {A : Type ℓ₂} →
  (f[] : A)
  (f≃ : HAEquiv A A)
  {y : X} (p : GpC R x y) → A
GpC-recHAEquiv R f[] f≃ = GpC-rec R f[] (λ a _ → fst f≃ a) (λ a _ → snd f≃ .isHAEquiv.g a ) (λ p _ → snd f≃ .isHAEquiv.rinv p) (λ p _ → snd f≃ .isHAEquiv.linv p) (λ p _ → snd f≃ .isHAEquiv.com p)

GpC-rec≃ :
  {X : Type ℓ₀} {x : X} (R : Graph X ℓ₁) {A : Type ℓ₂} →
  (f[] : A)
  (f≃ : A ≃ A)
  {y : X} (p : GpC R x y) → A
GpC-rec≃ R f[] f≃ = GpC-recHAEquiv R f[] (equiv→HAEquiv f≃)

GpCcompIsoR : {X : Type ℓ₀} (R : Graph X ℓ₁) (x : X) {y z : X} (a : R y z) → Iso (GpC R x y) (GpC R x z)
GpCcompIsoR R x {y} {z} a = e
  where
  e : Iso (GpC R x y) (GpC R x z)
  Iso.fun e p = p ∷+ a
  Iso.inv e p = p ∷- a
  Iso.rightInv e p = invl p a
  Iso.leftInv e p = invr p a

GpCcompEquivR : {X : Type ℓ₀} (R : Graph X ℓ₁) (x : X) {y z : X} (a : R y z) → GpC R x y ≃ GpC R x z
GpCcompEquivR R x {y} {z} a = isoToEquiv (GpCcompIsoR R x a)

GpCcompHAEquivR : {X : Type ℓ₀} (R : Graph X ℓ₁) (x : X) {y z : X} (a : R y z) → HAEquiv (GpC R x y) (GpC R x z)
GpCcompHAEquivR R x {y} {z} a = f , e
  where
  f : GpC R x y → GpC R x z
  f p = p ∷+ a
  e : isHAEquiv f
  isHAEquiv.g e p = p ∷- a
  isHAEquiv.linv e p = invr p a
  isHAEquiv.rinv e p = invl p a
  isHAEquiv.com e p = coh p a

GpCcompIsoR⁻ : {X : Type ℓ₀} (R : Graph X ℓ₁) (x : X) {y z : X} (a : R z y) → Iso (GpC R x y) (GpC R x z)
GpCcompIsoR⁻ R x {y} {z} a = e
  where
  e : Iso (GpC R x y) (GpC R x z)
  Iso.fun e p = p ∷- a
  Iso.inv e p = p ∷+ a
  Iso.rightInv e p = invr p a
  Iso.leftInv e p = invl p a

-- packed elimination principle to an equivalence
module ElimEq
  {X : Type ℓ₀} {x : X} (R : Graph X ℓ₁) (A : {y : X} → GpC R x y → Type ℓ₂)
  (f[] : A ([] {x = x}))
  (f≃ : {y z : X} (p : GpC R x y) (a : R y z) → A p ≃ A (p ∷+ a))
  where

  f : {y z : X} (p : GpC R x y) (a : R y z) → A p → A (p ∷+ a)
  f p a k = equivFun (f≃ p a) k
  f⁻ : {y z : X} (p : GpC R x y) (a : R y z) → A (p ∷+ a) → A p
  f⁻ p a k = invEq (f≃ p a) k
  g : {y z : X} (p : GpC R x y) (a : R z y) → A p → A (p ∷- a)
  g p a k =  f⁻ (p ∷- a) a (subst⁻ A (invl p a) k)
  g⁻ : {y z : X} (p : GpC R x y) (a : R z y) → A (p ∷- a) → A p
  g⁻ p a k = subst A (invl p a) (f (p ∷- a) a k)
  g≃ : {y z : X} (p : GpC R x y) (a : R z y) → A p ≃ A (p ∷- a)
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
  -- h : {y z : X} (p : GpC R x y) (a : R y z) → A p → A (p ∷+ a)
  -- h p a k = g⁻ (p ∷+ a) a (subst⁻ A (invr p a) k)
  -- h⁻ : {y z : X} (p : GpC R x y) (a : R y z) → A (p ∷+ a) → A p
  -- h⁻ p a k = subst A (invr p a) (g (p ∷+ a) a k)
  -- h≃ : {y z : X} (p : GpC R x y) (a : R y z) → A p ≃ A (p ∷+ a)
  -- h≃ p a = isoToEquiv e
    -- where
    -- e : Iso (A p) (A (p ∷+ a))
    -- Iso.fun e k = h p a k
    -- Iso.inv e k = h⁻ p a k
    -- Iso.rightInv e k = cong (g⁻ (p ∷+ a) a) (subst⁻Subst A (invr p a) _) ∙ retEq (g≃ (p ∷+ a) a) k
    -- Iso.leftInv e k = cong (subst A (invr p a)) (secEq (g≃ (p ∷+ a) a) _) ∙ substSubst⁻ A (invr p a) k
  -- h≡f : {y z : X} (p : GpC R x y) (a : R y z) → h p a ≡ f p a
  -- h≡f p a = funExt λ k →
    -- h p a k ≡⟨ refl ⟩
    -- subst A (invl (p ∷+ a) a) (f (p ∷+ a ∷- a) a (subst⁻ A (invr p a) k)) ≡⟨ cong (subst A (invl (p ∷+ a) a)) (sym {!!}) ⟩
    -- subst A (invl (p ∷+ a) a) (subst⁻ A (invl (p ∷+ a) a) (f p a k)) ≡⟨ substSubst⁻ A (invl (p ∷+ a) a) _ ⟩
    -- f p a k ∎
  fg : {y z : X} (p : GpC R x y) (a : R z y) (k : A p) → subst A (invl p a) (f (p ∷- a) a (g p a k)) ≡ k
  fg p a k = retEq (g≃ p a) k
  gf : {y z : X} (p : GpC R x y) (a : R y z) (k : A p) → subst A (invr p a) (g (p ∷+ a) a (f p a k)) ≡ k
  gf p a k = lem -- secEq f through h- = f-
    where
    nat : {y z : X} (p q : GpC R x y) (P : p ≡ q) (a : R y z) (k : A (p ∷+ a)) → subst A P (f⁻ p a k) ≡ f⁻ q a (subst A (cong (λ p → p ∷+ a) P) k)
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
  -- fgf : {y z : X} (p : GpC R x y) (a : R y z) (k : A p) → {!gf p a k!} ≡ fg (p ∷+ a) a (f p a k)
  -- fgf p a k = {!!}

  fIsoOver : {y z : X} (a : R y z) → IsoOver (GpCcompIsoR R x a) A A
  IsoOver.fun (fIsoOver a) p k = f p a k
  IsoOver.inv (fIsoOver a) p k = g p a k
  IsoOver.rightInv (fIsoOver {y} {z} a) p k = toPathP (fg p a k)
  IsoOver.leftInv (fIsoOver a) p k = toPathP (gf p a k)

  fHAEquivOver0 : {y z : X} (a : R y z) → HAEquivOver A A (iso→HAEquiv (GpCcompIsoR R x a))
  fHAEquivOver0 a = IsoOver.fun (fIsoOver a) , IsoOver→HAEquivOver (fIsoOver a)

  -- TODO: is there a more direct way to perform this??? (from the above data...)
  fHAEquivOver : {y z : X} (a : R y z) → HAEquivOver A A (GpCcompHAEquivR R x a)
  fHAEquivOver a = fun , isHAE'
    where
    fun : mapOver (GpCcompIsoR R x a .Iso.fun) A A
    fun = IsoOver.fun (fIsoOver a)
    isHAE : isHAEquivOver (iso→HAEquiv (GpCcompIsoR R x a)) A A fun
    isHAE = IsoOver→HAEquivOver (fIsoOver a)
    lem : iso→HAEquiv (GpCcompIsoR R x a) ≡ GpCcompHAEquivR R x a
    lem = Σ≡Prop (λ f → isPropIsHAEquiv {f = f}) refl
    lem' : PathP
      (λ i → (fun : mapOver (lem i .fst) A A) → Type (ℓ-max (ℓ-max ℓ₀ ℓ₁) ℓ₂))
      (isHAEquivOver (iso→HAEquiv (GpCcompIsoR R x a)) A A)
      (isHAEquivOver (GpCcompHAEquivR R x a) A A)
    lem' = funExt⁻ (funExt⁻ (cong isHAEquivOver lem) A) A
    lem'' : isHAEquivOver (iso→HAEquiv (GpCcompIsoR R x a)) A A ≡ isHAEquivOver (GpCcompHAEquivR R x a) A A
    lem'' = sym (transportRefl _) ∙ fromPathP lem'
    abstract
      isHAE' : isHAEquivOver (GpCcompHAEquivR R x a) A A fun
      isHAE' = transport (funExt⁻ lem'' fun) isHAE

  -- fHAEquivOver' : {y z : X} (a : R y z) → HAEquivOver A A (GpCcompHAEquivR R x a)
  -- fHAEquivOver' a = (λ p k → f p a k) , e
    -- where
    -- e : isHAEquivOver (GpCcompHAEquivR R x a) A A (λ p k → f p a k)
    -- isHAEquivOver.inv e p k = g p a k
    -- isHAEquivOver.rinv e p k = lem
      -- where
      -- lem : PathP (λ i → A (invl p a i)) (f (p ∷- a) a (g p a k)) k
      -- lem = {!!}
    -- isHAEquivOver.linv e p k = {!!}
    -- isHAEquivOver.com e p = {!!}

  GpC-elim' : {y : X} (p : GpC R x y) → A p
  GpC-elim' = GpC-elim R (λ {y} p → A p)
    f[]
    (λ {y} {z} {p} k a → fst (fHAEquivOver a) p k)
    (λ {y} {z} {p} k a → isHAEquivOver.inv (snd (fHAEquivOver a)) p k)
    (λ {y} {z} {p} k a → isHAEquivOver.rinv (snd (fHAEquivOver a)) p k)
    (λ {y} {z} {p} k a → isHAEquivOver.linv (snd (fHAEquivOver a)) p k)
    (λ {y} {z} {p} k a → isHAEquivOver.com (snd (fHAEquivOver a)) k)

  -- -- TODO: for the direct version , it seems difficult to define the coherence directly...
  -- GpC-elim'' : {y : X} (p : GpC R x y) → A p
  -- GpC-elim'' = GpC-elim R (λ {y} p → A p)
    -- f[]
    -- (λ {y} {z} {p} k a → f p a k) -- equivFun (f≃ p a) k
    -- (λ {y} {z} {p} k a → g p a k) -- invEq (f≃ (p ∷- a) a) (subst⁻ A (invl p a) k)
    -- (λ {y} {z} {p} k a → toPathP (fg p a k)) -- toPathP (cong (subst A (invl p a)) (secEq (f≃ (p ∷- a) a) _) ∙ substSubst⁻ A (invl p a) k))
    -- (λ {y} {z} {p} k a → toPathP (gf p a k))
    -- (λ {y} {z} {p} k a → toPathP {!!})
      -- where

      -- lem : {y z : X} (p : GpC R x y) (a : R y z) (k : A p) →
        -- transport (λ i → PathP (λ j → A (coh p a i j)) (f (p ∷+ a ∷- a) a (g (p ∷+ a) a (f p a k))) (f p a k))
        -- (congP (λ k q → f (invr p a k) a q) (toPathP (gf p a k)))
        -- ≡
        -- toPathP (fg (p ∷+ a) a (f p a k))
      -- lem p a k = {!!}

open ElimEq public using (GpC-elim')
