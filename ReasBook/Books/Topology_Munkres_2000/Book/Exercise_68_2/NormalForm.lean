module

public import Mathlib.Algebra.Group.ULift
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.CoprodI

public section

universe u v

namespace Monoid.Coprod

open MulEquiv Monoid.CoprodI

/-- The two factors of a binary coproduct, lifted to a common universe. -/
abbrev LiftedFactors (G₁ : Type u) (G₂ : Type v) : Bool → Type (max u v)
  | false => ULift.{max u v, u} G₁
  | true => ULift.{max u v, v} G₂

/-- The canonical monoid structures on the lifted factors. -/
instance instMonoidLiftedFactors (G₁ : Type u) (G₂ : Type v) [Monoid G₁] [Monoid G₂] :
    (i : Bool) → Monoid (LiftedFactors G₁ G₂ i)
  | false => inferInstance
  | true => inferInstance

/-- The canonical group structures on the lifted factors. -/
instance instGroupLiftedFactors (G₁ : Type u) (G₂ : Type v) [Group G₁] [Group G₂] :
    (i : Bool) → Group (LiftedFactors G₁ G₂ i)
  | false =>
      let base : Group (LiftedFactors G₁ G₂ false) := inferInstance
      { base with
        toDivInvMonoid :=
          { base.toDivInvMonoid with
            toMonoid := instMonoidLiftedFactors G₁ G₂ false } }
  | true =>
      let base : Group (LiftedFactors G₁ G₂ true) := inferInstance
      { base with
        toDivInvMonoid :=
          { base.toDivInvMonoid with
            toMonoid := instMonoidLiftedFactors G₁ G₂ true } }

/-- The canonical map from a binary coproduct to its indexed-coproduct model. -/
def toIndexed {G₁ : Type u} {G₂ : Type v} [Monoid G₁] [Monoid G₂] :
    Monoid.Coprod G₁ G₂ →* Monoid.CoprodI (LiftedFactors G₁ G₂) :=
  lift
    ((of : LiftedFactors G₁ G₂ false →* Monoid.CoprodI (LiftedFactors G₁ G₂)).comp
      (ulift.symm : G₁ ≃* LiftedFactors G₁ G₂ false).toMonoidHom)
    ((of : LiftedFactors G₁ G₂ true →* Monoid.CoprodI (LiftedFactors G₁ G₂)).comp
      (ulift.symm : G₂ ≃* LiftedFactors G₁ G₂ true).toMonoidHom)

/-- Helper for Exercise 68.2: `toIndexed` sends a left-factor letter to its lifted letter. -/
@[simp]
lemma toIndexed_apply_inl {G₁ : Type u} {G₂ : Type v} [Monoid G₁] [Monoid G₂]
    (a : G₁) :
    toIndexed (inl a : Monoid.Coprod G₁ G₂) =
      @of Bool (LiftedFactors G₁ G₂) (instMonoidLiftedFactors G₁ G₂) false (ULift.up a) := by
  -- Reduce the binary universal map before simplifying the lifted generator.
  rw [toIndexed, lift_apply_inl]
  rfl

/-- Helper for Exercise 68.2: `toIndexed` sends a right-factor letter to its lifted letter. -/
@[simp]
lemma toIndexed_apply_inr {G₁ : Type u} {G₂ : Type v} [Monoid G₁] [Monoid G₂]
    (b : G₂) :
    toIndexed (inr b : Monoid.Coprod G₁ G₂) =
      @of Bool (LiftedFactors G₁ G₂) (instMonoidLiftedFactors G₁ G₂) true (ULift.up b) := by
  -- Reduce the binary universal map before simplifying the lifted generator.
  rw [toIndexed, lift_apply_inr]
  rfl

/-- The canonical map from the indexed-coproduct model back to the binary coproduct. -/
def fromIndexed {G₁ : Type u} {G₂ : Type v} [Monoid G₁] [Monoid G₂] :
    Monoid.CoprodI (LiftedFactors G₁ G₂) →* Monoid.Coprod G₁ G₂ :=
  Monoid.CoprodI.lift fun i ↦ match i with
    | false => (inl : G₁ →* Monoid.Coprod G₁ G₂).comp
        (ulift : LiftedFactors G₁ G₂ false ≃* G₁).toMonoidHom
    | true => (inr : G₂ →* Monoid.Coprod G₁ G₂).comp
        (ulift : LiftedFactors G₁ G₂ true ≃* G₂).toMonoidHom

/-- The binary coproduct is canonically equivalent to the indexed coproduct of its two factors. -/
def equivIndexed {G₁ : Type u} {G₂ : Type v} [Monoid G₁] [Monoid G₂] :
    Monoid.Coprod G₁ G₂ ≃* Monoid.CoprodI (LiftedFactors G₁ G₂) where
  toFun := toIndexed
  invFun := fromIndexed
  map_mul' := map_mul toIndexed
  left_inv := by
    intro x
    change (fromIndexed.comp toIndexed) x = x
    have h : fromIndexed.comp toIndexed = MonoidHom.id (Monoid.Coprod G₁ G₂) := hom_ext (by
      apply MonoidHom.ext
      intro g
      simp [fromIndexed, toIndexed]) (by
      apply MonoidHom.ext
      intro g
      simp [fromIndexed, toIndexed])
    exact DFunLike.congr_fun h x
  right_inv := by
    intro x
    change (toIndexed.comp fromIndexed) x = x
    have h : toIndexed.comp fromIndexed =
        MonoidHom.id (Monoid.CoprodI (LiftedFactors G₁ G₂)) :=
      Monoid.CoprodI.ext_hom _ _ fun i ↦ by
        cases i
        · apply MonoidHom.ext
          intro g
          simp [fromIndexed, toIndexed]
        · apply MonoidHom.ext
          intro g
          simp [fromIndexed, toIndexed]
    exact DFunLike.congr_fun h x


/-- Helper for Exercise 68.2: the canonical equivalence sends a left-factor letter to its lift. -/
@[simp]
lemma equivIndexed_apply_inl {G₁ : Type u} {G₂ : Type v} [Monoid G₁] [Monoid G₂]
    (a : G₁) :
    equivIndexed (inl a : Monoid.Coprod G₁ G₂) =
      @of Bool (LiftedFactors G₁ G₂) (instMonoidLiftedFactors G₁ G₂) false (ULift.up a) := by
  -- The equivalence uses `toIndexed` as its forward map.
  exact toIndexed_apply_inl a

/-- Helper for Exercise 68.2: the canonical equivalence sends a right-factor letter to its lift. -/
@[simp]
lemma equivIndexed_apply_inr {G₁ : Type u} {G₂ : Type v} [Monoid G₁] [Monoid G₂]
    (b : G₂) :
    equivIndexed (inr b : Monoid.Coprod G₁ G₂) =
      @of Bool (LiftedFactors G₁ G₂) (instMonoidLiftedFactors G₁ G₂) true (ULift.up b) := by
  -- The equivalence uses `toIndexed` as its forward map.
  exact toIndexed_apply_inr b
/-- The canonical reduced-word normal form for a binary coproduct. -/
noncomputable def normalForm {G₁ : Type u} {G₂ : Type v} [Monoid G₁] [Monoid G₂] :
    Monoid.Coprod G₁ G₂ ≃ Monoid.CoprodI.Word (LiftedFactors G₁ G₂) :=
  open scoped Classical in equivIndexed.toEquiv.trans Word.equiv

/-- Helper for Exercise 68.2: the binary normal form represents the indexed image. -/
lemma normalForm_prod {G₁ : Type u} {G₂ : Type v} [Monoid G₁] [Monoid G₂]
    (x : Monoid.Coprod G₁ G₂) :
    (normalForm x).prod = equivIndexed x := by
  classical
  -- Unfold the owner definition once and use the reduced-word equivalence inverse law.
  exact Word.equiv.symm_apply_apply (equivIndexed x)

/-- Helper for Exercise 68.2: with decidable factor equality, the normal form is `Word.equiv`. -/
lemma normalForm_eq_wordEquiv {G₁ : Type u} {G₂ : Type v} [Monoid G₁] [Monoid G₂]
    [∀ i, DecidableEq (LiftedFactors G₁ G₂ i)] (x : Monoid.Coprod G₁ G₂) :
    normalForm x = Word.equiv (equivIndexed x) := by
  -- Compare products; reduced words are uniquely determined by the represented element.
  apply Word.equiv.symm.injective
  change (normalForm x).prod = (Word.equiv (equivIndexed x)).prod
  rw [normalForm_prod]
  exact (Word.equiv.symm_apply_apply (equivIndexed x)).symm

/-- The length of the canonical reduced word representing an element of a binary coproduct. -/
noncomputable def wordLength {G₁ : Type u} {G₂ : Type v} [Monoid G₁] [Monoid G₂]
    (x : Monoid.Coprod G₁ G₂) : ℕ :=
  (normalForm x).toList.length

/-- Helper for Exercise 68.2: word length is the list length of the canonical normal form. -/
lemma wordLength_apply {G₁ : Type u} {G₂ : Type v} [Monoid G₁] [Monoid G₂]
    (x : Monoid.Coprod G₁ G₂) :
    wordLength x = (normalForm x).toList.length := by
  -- This is the public pointwise specification of `wordLength`.
  rfl

end Monoid.Coprod
