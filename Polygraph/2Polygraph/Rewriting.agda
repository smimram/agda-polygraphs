{-# OPTIONS --cubical --allow-unsolved-metas #-}

module 2Polygraph.Rewriting where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws as GL
open import Cubical.Data.Sum hiding (rec ; elim)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥ hiding (rec ; elim)

open import Graph
open Graph.FreeCategory hiding (elim ; rec)
open Graph.FreePregroupoid
open import 1Polygraph renaming (⟦_⟧ to ⟦_⟧₁) hiding (module Operations ; rec ; elim ; elimPath)
open import 2Polygraph.Base

private variable
  ℓ ℓ₀ ℓ₁ ℓ₂ ℓ₃ : Level

module _ (P : 2Polygraph {ℓ₀} {ℓ₁} {ℓ₂}) where
  open Operations P

  -- local confluence
  isLC : (x : Σ₀) → Type _
  isLC x = {y y' : Σ₀} (a : x ↝ y) (b : x ↝ y') →
           Σ[ z ∈ Σ₀ ]
           Σ[ p ∈ y  ↝* z ]
           Σ[ q ∈ y' ↝* z ]
           ([ a ] · p ⇔* [ b ] · q)

  hasLC = {x : Σ₀} → isLC x

  -- confluence
  isC : (x : Σ₀) → Type _
  isC x = {y y' : Σ₀} (p : x ↝* y) (q : x ↝* y') →
          Σ[ z ∈ Σ₀ ]
          Σ[ p' ∈ y  ↝* z ]
          Σ[ q' ∈ y' ↝* z ]
          (p · p') ⇔* (q · q')

  hasC = {x : Σ₀} → isC x

  -- Newman's lemma
  newman : isWF Σ' → hasLC → hasC
  newman wf lc {x = x} = induction (WF+ wf) {P = isC} lem x
    where
    open Graph.FreePregroupoid
    lem : (x : Σ₀) → ((y : Σ₀) → x ↝+ y → isC y) → isC x
    lem x ih [] q = _ , q , [] , [≡ sym (FreeCategory.lUnit q) ]?
    lem x ih (p ∷ a) [] = _ , [] , p ∷ a , [≡ cong (λ p → p ∷ a) (FreeCategory.lUnit p) ]?
    lem x ih ([] ∷ a) ([] ∷ b) = lc a b
    lem x ih ([] ∷ a) (q ∷ b' ∷ b) with lem _ ih [ a ] (q ∷ b')
    ... | _ , p' , q' , ap'⇔qq' with ih _ (toSC q b') q' [ b ]
    ... | _ , p'' , q'' , q'p''⇔bq'' = _ , p' · p'' , q'' , [≡ sym (FreeCategory.assoc [ a ] p' p'') ∙ FreeCategory.lUnit _ ]? ·? whisk* [] ap'⇔qq' p'' ·? [≡ sym (FreeCategory.lUnit _) ∙ FreeCategory.assoc (q ∷ b') q' p'' ]? ·? whisk* (q · [ b' ]) q'p''⇔bq'' [] ·? [≡ sym (FreeCategory.assoc (q ∷ b') [ b ] q'') ]?
    lem x ih (p ∷ a' ∷ a) ([] ∷ b) = {!!}
    lem x ih (p ∷ a' ∷ a) (q ∷ b' ∷ b) = {!!}
    -- -- lem x ih (x↝y₁ ∷ y₁↝y₁') (x↝y₂ ∷ y₂↝y₂') with lc x↝y₁ x↝y₂
    -- -- ... | z , y₁↝z , y₂↝z , x↝y₁↝z⇔x↝y₂↝z with ih _ [ x↝y₁ ]⁺ y₁↝y₁' y₁↝z
    -- -- ... | z₁ , y₁'↝z₁ , z↝z₁ , y₁↝y₁'↝z₁⇔y₁↝z↝z₁ with ih _ [ x↝y₂ ]⁺ (y₂↝z · z↝z₁) y₂↝y₂'
    -- -- ... | z' , z₁↝z' , y₂'↝z' , y₂↝z₁↝z'⇔y₂↝y₂'↝z' = z' , y₁'↝z₁ · z₁↝z' , y₂'↝z' ,
      -- -- ([≡ cong (λ p → x↝y₁ ∷ p) (sym (·-assoc y₁↝y₁' _ _)) ] ·
      -- -- whisk* [ x↝y₁ ] y₁↝y₁'↝z₁⇔y₁↝z↝z₁ z₁↝z' ·
      -- -- [≡ cong (λ p → x↝y₁ ∷ p) (·-assoc y₁↝z _ _) ] ·
      -- -- whisk* [] x↝y₁↝z⇔x↝y₂↝z (z↝z₁ · z₁↝z') ·
      -- -- [≡ cong (λ p → x↝y₂ ∷ p) (sym (·-assoc y₂↝z _ _) ∙ sym (·-unitr _)) ] ·
      -- -- whisk* [ x↝y₂ ] y₂↝z₁↝z'⇔y₂↝y₂'↝z' [] ·
      -- -- [≡ cong (λ p → x↝y₂ ∷ p) (·-unitr _) ])

  -- homotopy basis with normal targets
  hasNHB = {x y : Σ₀} → isNF {P = Σ'} y → (p q : x ↝* y) → p ⇔* q

  -- confluence implies homotopy basis with normal targets
  CNHB : isSet Σ₀ → hasC → hasNHB
  CNHB S C ny p q with C p q
  ... | z , p' ∷ a , q' , p⇔q = ⊥.rec (ny (toSC p' a))
  ... | z , [] , q' , p⇔q with ∷-destruct q'
  ... | inr (_ , q'' , a , _) = ⊥.rec (ny (toSC q'' a))
  ... | inl (pq , q'≡[]) = p⇔q ·? [≡ cong (λ q' → q · q') lem' ]?
    where
    lem : pq ≡ refl
    lem = S _ _ pq refl
    lem' : q' ≡ []
    lem' = sym (substRefl {B = λ x → x ↝* z} q') ∙ transport (λ i → subst (λ x → x ↝* z) (lem i) q' ≡ []) q'≡[]

  ---
  --- homotopy basis
  ---

  hasHB : Type _
  hasHB = {x y : Σ₀} (p q : x ↝* y) → _≡_ {A = _≡_ {A = ⟦ P ⟧} ∣ x ∣'' ∣ y ∣''} ∣ p ∣*' ∣ q ∣*'


  -- Church-Rosser for parallel zig-zags
  hasPCR : Type _
  hasPCR = {x y : Σ₀} (p q : x ↝? y) → ∣ p ∣?' ≡ ∣ q ∣?'

  -- local confluence implies coherence
  module _ (S₀ : isSet Σ₀) (WF : isWF Σ') (DR : hasDR Σ') (LC : hasLC) where
    private
      C : hasC
      C = newman WF LC

      NZ : hasNZ Σ'
      NZ = normalize WF DR

      NF : Σ₀ → Σ₀
      NF x = NZ x .fst

      NFisNF : (x : Σ₀) → isNF (NF x)
      NFisNF x = NZ x .snd .snd

      NFisNF' : {x : Σ₀} → isNF' (NF x)
      NFisNF' {x} = isNF→isNF' (NFisNF x)

      -- morphism to the normal form
      NFmor : (x : Σ₀) → x ↝* NF x
      NFmor x = NZ x .snd .fst

      -- path to the normal form (TODO: remove and rename the above one)
      NFpath : (x : Σ₀) → _≡_ {A = ⟦ P ⟧} ∣ x ∣'' ∣ NF x ∣''
      NFpath x = ∣ NFmor x ∣*'

      -- path between normal forms corresponding to a path
      NFmap : {x y : Σ₀} (p : x ↝* y) → NF x ↝* NF y
      NFmap {x} {y} p = nxr · nyl⁻
        where
        confl = C (NFmor x) (p · NFmor y)
        nxr : NF x ↝* fst confl
        nxr = confl .snd .fst
        nyl : NF y ↝* fst confl
        nyl = confl .snd .snd .fst
        nyl⁻ : fst confl ↝* NF y
        nyl⁻ = NFisNF' nyl

      -- NFindep : {x y : Σ₀} (p : ∣ x ∣ ≡ ∣ y ∣) → NF x ≡ NF y
      -- NFindep p = {!ua ?!}

      NHB : hasNHB
      NHB = CNHB S₀ C

    HB : hasHB
    HB {x} {y} p q =
      ∣ p ∣*'                           ≡⟨ rUnit _ ⟩
      ∣ p ∣*' ∙ refl                    ≡⟨ cong (_∙_ ∣ p ∣*') (sym (rCancel _)) ⟩
      ∣ p ∣*' ∙ ∣ r ∣*' ∙ sym ∣ r ∣*'   ≡⟨ GL.assoc _ _ _ ⟩
      (∣ p ∣*' ∙ ∣ r ∣*') ∙ sym ∣ r ∣*' ≡⟨ cong (_∙ sym ∣ r ∣*') (sym (∣∣*'comp p r)) ⟩
      ∣ p · r ∣*' ∙ sym ∣ r ∣*'         ≡⟨ cong (_∙ sym ∣ r ∣*') ∣ ϕ ∣** ⟩
      ∣ q · r ∣*' ∙ sym ∣ r ∣*'         ≡⟨ cong (_∙ sym ∣ r ∣*') (∣∣*'comp q r) ⟩
      (∣ q ∣*' ∙ ∣ r ∣*') ∙ sym ∣ r ∣*' ≡⟨ sym (GL.assoc _ _ _) ⟩
      ∣ q ∣*' ∙ ∣ r ∣*' ∙ sym ∣ r ∣*'   ≡⟨ cong (_∙_ ∣ q ∣*') (rCancel _) ⟩
      ∣ q ∣*' ∙ refl                    ≡⟨ sym (rUnit _) ⟩
      ∣ q ∣*'                           ∎
      where
      z : Σ₀
      z = NF y
      r : y ↝* z
      r = NZ y .snd .fst
      ϕ : p · r ⇔* q · r
      ϕ = NHB (NFisNF y) (p · r) (q · r)

    private
      CRpath : {x y : Σ₀} (p : x ↝* y) → ∣ NFmor x ∣*' ∙ ∣ NFmap p ∣*' ≡ ∣ p ∣*' ∙ ∣ NFmor y ∣*'
      CRpath {x} {y} p =
        ∣ nx ∣*' ∙ ∣ NFmap p ∣*'                ≡⟨ cong (_∙_ ∣ nx ∣*') refl  ⟩
        ∣ nx ∣*' ∙ ∣ nxr · nyl⁻ ∣*'             ≡⟨ cong (_∙_ ∣ nx ∣*') (∣∣*'comp nxr nyl⁻) ⟩
        ∣ nx ∣*' ∙ ∣ nxr ∣*' ∙ ∣ nyl⁻ ∣*'       ≡⟨ GL.assoc _ _ _ ⟩
        (∣ nx ∣*' ∙ ∣ nxr ∣*') ∙ ∣ nyl⁻ ∣*'     ≡⟨ cong (_∙ ∣ nyl⁻ ∣*') (sym (∣∣*'comp nx nxr)) ⟩
        ∣ nx · nxr ∣*' ∙ ∣ nyl⁻ ∣*'             ≡⟨ cong (_∙ ∣ nyl⁻ ∣*') ∣ c ∣** ⟩
        ∣ (p · ny) · nyl ∣*' ∙ ∣ nyl⁻ ∣*'       ≡⟨ cong (_∙ ∣ nyl⁻ ∣*') (∣∣*'comp (p · ny) nyl) ⟩
        (∣ p · ny ∣*' ∙ ∣ nyl ∣*') ∙ ∣ nyl⁻ ∣*' ≡⟨ sym (GL.assoc _ _ _) ⟩
        ∣ p · ny ∣*' ∙ ∣ nyl ∣*' ∙ ∣ nyl⁻ ∣*'   ≡⟨ cong (_∙_ ∣ p · ny ∣*') (sym (∣∣*'comp nyl nyl⁻)) ⟩
        ∣ p · ny ∣*' ∙ ∣ nyl · nyl⁻ ∣*'         ≡⟨ cong (_∙_ ∣ p · ny ∣*') (cong ∣_∣*' (WFloop WF S₀ (nyl · nyl⁻))) ⟩
        ∣ p · ny ∣*' ∙ ∣ [] ∣*'                 ≡⟨ sym (rUnit _) ⟩
        ∣ p · ny ∣*'                            ≡⟨ ∣∣*'comp p ny ⟩
        ∣ p ∣*' ∙ ∣ ny ∣*'                      ∎
        where
        nx : x ↝* NF x
        nx = NFmor x
        ny : y ↝* NF y
        ny = NFmor y
        confl = C nx (p · ny)
        nxr : NF x ↝* fst confl
        nxr = confl .snd .fst
        nyl : NF y ↝* fst confl
        nyl = confl .snd .snd .fst
        nyl⁻ : fst confl ↝* NF y
        nyl⁻ = NFisNF' nyl
        c : nx · nxr ⇔* (p · ny) · nyl
        c = confl .snd .snd .snd

    -- Church-Rosser
    CR : {x y : Σ₀} (p : x ↝? y) → Σ (NF x ↝* NF y) (λ n → ∣ NFmor x ∣*' ∙ ∣ n ∣*' ≡ ∣ p ∣?' ∙ ∣ NFmor y ∣*')
    CR [] =  [] , sym (GL.rUnit _) ∙ GL.lUnit _
    CR (_∷+_ {x} {y} {z} p a)= n · n' , (
      ∣ nx ∣*' ∙ ∣ n · n' ∣*'             ≡⟨ cong (_∙_ ∣ nx ∣*') (∣∣*'comp n n') ⟩
      ∣ nx ∣*' ∙ ∣ n ∣*' ∙ ∣ n' ∣*'       ≡⟨ GL.assoc _ _ _ ⟩
      (∣ nx ∣*' ∙ ∣ n ∣*') ∙ ∣ n' ∣*'     ≡⟨ cong (_∙ ∣ n' ∣*') c ⟩
      (∣ p ∣?' ∙ ∣ ny ∣*') ∙ ∣ n' ∣*'     ≡⟨ sym (GL.assoc _ _ _) ⟩
      ∣ p ∣?' ∙ ∣ ny ∣*' ∙ ∣ n' ∣*'       ≡⟨ cong (_∙_ ∣ p ∣?') (CRpath [ a ]) ⟩
      ∣ p ∣?' ∙ ∣ [ a ] ∣*' ∙ ∣ nz ∣*'    ≡⟨ cong (_∙_ ∣ p ∣?') (cong (_∙ ∣ nz ∣*') (∣[]∣*' a)) ⟩
      ∣ p ∣?' ∙ ∣ a ∣₁' ∙ ∣ nz ∣*'        ≡⟨ GL.assoc _ _ _ ⟩
      (∣ p ∣?' ∙ ∣ a ∣₁') ∙ ∣ nz ∣*'      ≡⟨ cong (_∙ ∣ nz ∣*') (cong (_∙_ ∣ p ∣?') (sym (|[]|?' a))) ⟩
      (∣ p ∣?' ∙ ∣ [ a ]+ ∣?') ∙ ∣ nz ∣*' ≡⟨ cong (_∙ ∣ nz ∣*') (sym (∣∣?'comp p [ a ]+)) ⟩
      (∣ p ·? [ a ]+ ∣?') ∙ ∣ nz ∣*'      ≡⟨ cong (_∙ ∣ nz ∣*') refl ⟩
      ∣ p ∷+ a ∣?' ∙ ∣ nz ∣*'             ∎)
      where
      n : NF x ↝* NF y
      n = CR p .fst

      n' : NF y ↝* NF z
      n' = NFmap [ a ]

      c = CR p .snd

      nx : x ↝* NF x
      nx = NFmor x

      ny : y ↝* NF y
      ny = NFmor y

      nz : z ↝* NF z
      nz = NFmor z
    CR (_∷-_ {x} {y} {z} p a) = n · n' , (
      ∣ nx ∣*' ∙ ∣ n · n' ∣*'              ≡⟨ cong (_∙_ ∣ nx ∣*') (∣∣*'comp n n') ⟩
      ∣ nx ∣*' ∙ ∣ n ∣*' ∙ ∣ n' ∣*'        ≡⟨ GL.assoc _ _ _ ⟩
      (∣ nx ∣*' ∙ ∣ n ∣*') ∙ ∣ n' ∣*'      ≡⟨ cong (_∙ ∣ n' ∣*') c ⟩
      (∣ p ∣?' ∙ ∣ ny ∣*') ∙ ∣ n' ∣*'      ≡⟨ sym (GL.assoc _ _ _) ⟩
      ∣ p ∣?' ∙ ∣ ny ∣*' ∙ ∣ n' ∣*'        ≡⟨ cong (_∙_ ∣ p ∣?') c' ⟩
      ∣ p ∣?' ∙ sym ∣ [ a ] ∣*' ∙ ∣ nz ∣*' ≡⟨ cong (_∙_ ∣ p ∣?') (cong (_∙ ∣ nz ∣*') (cong sym (∣[]∣*' a))) ⟩
      ∣ p ∣?' ∙ sym ∣ a ∣₁' ∙ ∣ nz ∣*'     ≡⟨ GL.assoc _ _ _ ⟩
      (∣ p ∣?' ∙ sym ∣ a ∣₁') ∙ ∣ nz ∣*'   ≡⟨ cong (_∙ ∣ nz ∣*') (cong (_∙_ ∣ p ∣?') (sym (|[]|?'- a))) ⟩
      (∣ p ∣?' ∙ ∣ [ a ]- ∣?') ∙ ∣ nz ∣*'  ≡⟨ cong (_∙ ∣ nz ∣*') (sym (∣∣?'comp p [ a ]-)) ⟩
      (∣ p ·? [ a ]- ∣?') ∙ ∣ nz ∣*'       ≡⟨ cong (_∙ ∣ nz ∣*') refl ⟩
      ∣ p ∷- a ∣?' ∙ ∣ nz ∣*'              ∎)
      where
      |[]|?'- : {x y : Σ₀} (a : x ↝ y) → ∣ [ a ]- ∣?' ≡ sym ∣ a ∣₁'
      |[]|?'- a = cong (cong ∣_∣') (sym (GL.lUnit _))

      n : NF x ↝* NF y
      n = CR p .fst

      n' : NF y ↝* NF z
      n' = NFisNF' (NFmap [ a ])

      c = CR p .snd

      nx : x ↝* NF x
      nx = NFmor x

      ny : y ↝* NF y
      ny = NFmor y

      nz : z ↝* NF z
      nz = NFmor z

      c' : ∣ ny ∣*' ∙ ∣ n' ∣*' ≡ sym ∣ [ a ] ∣*' ∙ ∣ nz ∣*'
      c' =
        ∣ ny ∣*' ∙ ∣ n' ∣*'                                   ≡⟨ GL.lUnit _ ⟩
        refl ∙ ∣ ny ∣*' ∙ ∣ n' ∣*'                            ≡⟨ cong (_∙ ∣ ny ∣*' ∙ ∣ n' ∣*' ) (sym (GL.lCancel _)) ⟩
        (sym ∣ [ a ] ∣*' ∙ ∣ [ a ] ∣*') ∙ ∣ ny ∣*' ∙ ∣ n' ∣*' ≡⟨ sym (GL.assoc _ _ _) ⟩
        sym ∣ [ a ] ∣*' ∙ (∣ [ a ] ∣*' ∙ ∣ ny ∣*' ∙ ∣ n' ∣*') ≡⟨ cong (_∙_ (sym ∣ [ a ] ∣*')) lem ⟩
        sym ∣ [ a ] ∣*' ∙ ∣ nz ∣*'                            ∎
        where
        confl = C nz ([ a ] · ny)
        nzr = confl .snd .fst
        nyl = confl .snd .snd .fst
        nyl⁻ = NFisNF' nyl
        lem' : ∣ NFmap [ a ] ∣*' ≡ sym ∣ n' ∣*'
        lem' =
          ∣ NFmap [ a ] ∣*'                             ≡⟨ GL.rUnit _ ⟩
          ∣ NFmap [ a ] ∣*' ∙ refl                      ≡⟨ cong (_∙_ ∣ NFmap [ a ] ∣*') (sym (rCancel _)) ⟩
          ∣ NFmap [ a ] ∣*' ∙ ∣ n' ∣*' ∙ sym ∣ n' ∣*'   ≡⟨ GL.assoc _ _ _ ⟩
          (∣ NFmap [ a ] ∣*' ∙ ∣ n' ∣*') ∙ sym ∣ n' ∣*' ≡⟨ cong (_∙ (sym ∣ n' ∣*')) (sym (∣∣*'comp (NFmap [ a ]) n')) ⟩
          ∣ NFmap [ a ] · n' ∣*' ∙ sym ∣ n' ∣*'         ≡⟨ cong (_∙ (sym ∣ n' ∣*')) (cong ∣_∣*' (WFloop WF S₀ (NFmap [ a ] · n'))) ⟩
          ∣ [] ∣*' ∙ sym ∣ n' ∣*'                       ≡⟨ sym (GL.lUnit _) ⟩
          sym ∣ n' ∣*'                                  ∎
        lem =
          ∣ [ a ] ∣*' ∙ ∣ ny ∣*' ∙ ∣ n' ∣*'         ≡⟨ GL.assoc _ _ _ ⟩
          (∣ [ a ] ∣*' ∙ ∣ ny ∣*') ∙ ∣ n' ∣*'       ≡⟨ cong (_∙ ∣ n' ∣*') (sym (CRpath [ a ])) ⟩
          (∣ nz ∣*' ∙ ∣ NFmap [ a ] ∣*') ∙ ∣ n' ∣*' ≡⟨ sym (GL.assoc _ _ _) ⟩
          ∣ nz ∣*' ∙ (∣ NFmap [ a ] ∣*' ∙ ∣ n' ∣*') ≡⟨ cong (_∙_ ∣ nz ∣*') (cong (_∙ ∣ n' ∣*') lem') ⟩
          ∣ nz ∣*' ∙ (sym ∣ n' ∣*' ∙ ∣ n' ∣*')      ≡⟨ cong (_∙_ ∣ nz ∣*') (lCancel _) ⟩
          ∣ nz ∣*' ∙ refl                           ≡⟨ sym (rUnit _) ⟩
          ∣ nz ∣*'                                  ∎

    -- TODO: CR implies this more natural variant
    PCR : hasPCR
    PCR = ?
