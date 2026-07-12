import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import StacksProject_2024.Chap04.Definition_4_27_20
import StacksProject_2024.Chap13.Definition_13_14_10
import StacksProject_2024.Chap13.Proposition_13_14_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty.IsStableUnderRetracts

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section Stability

/- Domain-style sampling for Lemma 13.14.13:
- primary domain: object properties on a triangulated category which are stable under retracts,
  applied to the source-facing predicates `Functor.ComputesRightDerivedAt` and
  `Functor.ComputesLeftDerivedAt`;
- inspected owner declarations:
  `ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_left`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_right`,
  `rightDerivedDefinedObjectProperty`,
  `leftDerivedDefinedObjectProperty`,
  `rightDerivedDefinedObjectProperty_isStableUnderRetracts`,
  `leftDerivedDefinedObjectProperty_isStableUnderRetracts`,
  `Functor.ComputesRightDerivedAt`,
  `Functor.ComputesLeftDerivedAt`;
- best owner abstraction: the core/canonical owner is
  `ObjectProperty.IsStableUnderRetracts`, first for the pointwise-definedness object properties
  from `Proposition_13_14_8`, then for the stronger source-facing computation predicates in the
  present file; the biproduct consequences should therefore be derived from the generic retract
  lemmas `of_biprod_left` and `of_biprod_right`, not stated only as ad hoc conjunction theorems;
- primitive data: the object properties `fun X ↦ F.ComputesRightDerivedAt S X` and
  `fun X ↦ F.ComputesLeftDerivedAt S X`;
- derived API: the left/right direct-summand consequences and the conjunction theorem packaging
  them together.

Source/core/bridge triage:
- `source-facing`: the textbook claim that if `X ⊞ Y` computes the right or left derived functor,
  then both summands do;
- `core/canonical`: `ObjectProperty.IsStableUnderRetracts` for the relevant object properties,
  together with `of_biprod_left` and `of_biprod_right`;
- `bridge/view`: the conjunction theorems `computesRightDerivedAt_of_biprod` and
  `computesLeftDerivedAt_of_biprod`, now demoted to thin wrappers around the owner-level API.
-/

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D)
  [S.ContainsIdentities]
  {X Y : D}

-- Proof sketch: the source-facing computation predicate extends the pointwise-definedness
-- predicate, whose retract stability is already owned upstream. For the isomorphism part, the
-- identity leg
-- `F.obj X ⟶ rightDerivedValue S F X` is a retract, in the arrow category, of the corresponding
-- identity leg for any retract ambient object `Y`; retracts of isomorphisms are isomorphisms.
/-- Objects which compute the right derived functor of `F` form a retract-stable object
property. -/
instance computesRightDerivedAt_isStableUnderRetracts [IsIdempotentComplete D'] :
    (F.computesRightDerivedObjectProperty S).IsStableUnderRetracts := by
  refine ⟨?_⟩
  intro X Y r hY
  letI : F.ComputesRightDerivedAt S Y := hY
  have hX :
      rightDerivedDefinedObjectProperty F S X :=
    (rightDerivedDefinedObjectProperty F S).prop_of_retract r
      (show rightDerivedDefinedObjectProperty F S Y from inferInstance)
  letI : F.HasPointwiseRightDerivedFunctorAt S X := hX
  refine { isIso_rightDerivedValueLeg := ?_ }
  let X' : rightDerivedDefinedSubcategory F S := ⟨X, hX⟩
  let Y' : rightDerivedDefinedSubcategory F S :=
    ⟨Y, show rightDerivedDefinedObjectProperty F S Y from inferInstance⟩
  let i' : X' ⟶ Y' := ObjectProperty.homMk r.i
  let r' : Y' ⟶ X' := ObjectProperty.homMk r.r
  let uX : F.obj X ⟶ rightDerivedValue S F X :=
    rightDerivedValueLeg S F (𝟙 X) (S.id_mem X)
  let uY : F.obj Y ⟶ rightDerivedValue S F Y :=
    rightDerivedValueLeg S F (𝟙 Y) (S.id_mem Y)
  let Ri : rightDerivedValue S F X ⟶ rightDerivedValue S F Y :=
    (rightDerivedDefinedFunctor F S).map i'
  let Rr : rightDerivedValue S F Y ⟶ rightDerivedValue S F X :=
    (rightDerivedDefinedFunctor F S).map r'
  have h_i :
      F.map r.i ≫ uY = uX ≫ Ri := by
    simpa [uX, uY, Ri, i'] using
      (show CommSq uX (F.map r.i) Ri uY from
        rightDerivedValueMap_comp_of_square S F r.i
          (𝟙 X) (𝟙 Y) (S.id_mem X) (S.id_mem Y) r.i
          ⟨by simp⟩).w.symm
  have h_r :
      F.map r.r ≫ uX = uY ≫ Rr := by
    simpa [uX, uY, Rr, r'] using
      (show CommSq uY (F.map r.r) Rr uX from
        rightDerivedValueMap_comp_of_square S F r.r
          (𝟙 Y) (𝟙 X) (S.id_mem Y) (S.id_mem X) r.r
          ⟨by simp⟩).w.symm
  have hR : Ri ≫ Rr = 𝟙 _ := by
    have hi' : i' ≫ r' = 𝟙 X' := by
      ext
      simpa [i', r'] using r.retract
    simpa [Ri, Rr, Functor.map_comp] using
      congrArg ((rightDerivedDefinedFunctor F S).map) hi'
  have hF : F.map r.i ≫ F.map r.r = 𝟙 _ := by
    rw [← F.map_comp, r.retract, F.map_id]
  let hArrow : RetractArrow uX uY :=
    { i := Arrow.homMk' (F.map r.i) Ri h_i
      r := Arrow.homMk' (F.map r.r) Rr h_r
      retract := by
        ext
        · exact hF
        · exact hR }
  exact MorphismProperty.of_retract hArrow inferInstance

-- Proof sketch: dually, pointwise left-derived-definedness already descends along retracts, and
-- the identity projection `leftDerivedValue S F X ⟶ F.obj X` is a retract of the corresponding
-- projection for `Y`; retracts of isomorphisms are isomorphisms.
/-- Objects which compute the left derived functor of `F` form a retract-stable object
property. -/
instance computesLeftDerivedAt_isStableUnderRetracts [IsIdempotentComplete D'] :
    (F.computesLeftDerivedObjectProperty S).IsStableUnderRetracts := by
  refine ⟨?_⟩
  intro X Y r hY
  letI : F.ComputesLeftDerivedAt S Y := hY
  have hX :
      leftDerivedDefinedObjectProperty F S X :=
    (leftDerivedDefinedObjectProperty F S).prop_of_retract r
      (show leftDerivedDefinedObjectProperty F S Y from inferInstance)
  letI : F.HasPointwiseLeftDerivedFunctorAt S X := hX
  refine { isIso_leftDerivedValueProjection := ?_ }
  let X' : leftDerivedDefinedSubcategory F S := ⟨X, hX⟩
  let Y' : leftDerivedDefinedSubcategory F S :=
    ⟨Y, show leftDerivedDefinedObjectProperty F S Y from inferInstance⟩
  let i' : X' ⟶ Y' := ObjectProperty.homMk r.i
  let r' : Y' ⟶ X' := ObjectProperty.homMk r.r
  let uX : leftDerivedValue S F X ⟶ F.obj X :=
    leftDerivedValueProjection S F (𝟙 X) (S.id_mem X)
  let uY : leftDerivedValue S F Y ⟶ F.obj Y :=
    leftDerivedValueProjection S F (𝟙 Y) (S.id_mem Y)
  let Li : leftDerivedValue S F X ⟶ leftDerivedValue S F Y :=
    (leftDerivedDefinedFunctor F S).map i'
  let Lr : leftDerivedValue S F Y ⟶ leftDerivedValue S F X :=
    (leftDerivedDefinedFunctor F S).map r'
  have h_i :
      Li ≫ uY = uX ≫ F.map r.i := by
    simpa [uX, uY, Li, i'] using
      (show CommSq Li uX uY (F.map r.i) from
        leftDerivedValueMap_comp_of_square S F r.i
          (𝟙 X) (𝟙 Y) (S.id_mem X) (S.id_mem Y) r.i
          ⟨by simp⟩).w
  have h_r :
      Lr ≫ uX = uY ≫ F.map r.r := by
    simpa [uX, uY, Lr, r'] using
      (show CommSq Lr uY uX (F.map r.r) from
        leftDerivedValueMap_comp_of_square S F r.r
          (𝟙 Y) (𝟙 X) (S.id_mem Y) (S.id_mem X) r.r
          ⟨by simp⟩).w
  have hL : Li ≫ Lr = 𝟙 _ := by
    have hi' : i' ≫ r' = 𝟙 X' := by
      ext
      simpa [i', r'] using r.retract
    simpa [Li, Lr, Functor.map_comp] using
      congrArg ((leftDerivedDefinedFunctor F S).map) hi'
  have hF : F.map r.i ≫ F.map r.r = 𝟙 _ := by
    rw [← F.map_comp, r.retract, F.map_id]
  let hArrow : RetractArrow uX uY :=
    { i := Arrow.homMk' Li (F.map r.i) h_i
      r := Arrow.homMk' Lr (F.map r.r) h_r
      retract := by
        ext
        · exact hL
        · exact hF }
  exact MorphismProperty.of_retract hArrow inferInstance

end Stability

section Biproduct

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [HasZeroMorphisms D]
  (F : D ⥤ D') (S : MorphismProperty D)
  [S.ContainsIdentities]
  {X Y : D}

/-- Lemma 13.14.13 (1): if `X ⊞ Y` computes the right derived functor of `F`, then `X` does. -/
@[stacks 05T0]
theorem computesRightDerivedAt_left_of_biprod
    [(F.computesRightDerivedObjectProperty S).IsStableUnderRetracts]
    [HasBinaryBiproduct X Y]
    (hXY : F.ComputesRightDerivedAt S (X ⊞ Y)) :
    F.ComputesRightDerivedAt S X :=
  of_biprod_left (F.computesRightDerivedObjectProperty S) hXY

/-- Lemma 13.14.13 (2): if `X ⊞ Y` computes the right derived functor of `F`, then `Y` does. -/
@[stacks 05T0]
theorem computesRightDerivedAt_right_of_biprod
    [(F.computesRightDerivedObjectProperty S).IsStableUnderRetracts]
    [HasBinaryBiproduct X Y]
    (hXY : F.ComputesRightDerivedAt S (X ⊞ Y)) :
    F.ComputesRightDerivedAt S Y :=
  of_biprod_right (F.computesRightDerivedObjectProperty S) hXY

/-- If `X ⊞ Y` computes the right derived functor of `F`, then both summands do. -/
theorem computesRightDerivedAt_of_biprod
    [(F.computesRightDerivedObjectProperty S).IsStableUnderRetracts]
    [HasBinaryBiproduct X Y]
    (hXY : F.ComputesRightDerivedAt S (X ⊞ Y)) :
    F.ComputesRightDerivedAt S X ∧
      F.ComputesRightDerivedAt S Y :=
  ⟨computesRightDerivedAt_left_of_biprod F S hXY,
    computesRightDerivedAt_right_of_biprod F S hXY⟩

/-- Lemma 13.14.13 (3): if `X ⊞ Y` computes the left derived functor of `F`, then `X` does. -/
@[stacks 05T0]
theorem computesLeftDerivedAt_left_of_biprod
    [(F.computesLeftDerivedObjectProperty S).IsStableUnderRetracts]
    [HasBinaryBiproduct X Y]
    (hXY : F.ComputesLeftDerivedAt S (X ⊞ Y)) :
    F.ComputesLeftDerivedAt S X :=
  of_biprod_left (F.computesLeftDerivedObjectProperty S) hXY

/-- Lemma 13.14.13 (4): if `X ⊞ Y` computes the left derived functor of `F`, then `Y` does. -/
@[stacks 05T0]
theorem computesLeftDerivedAt_right_of_biprod
    [(F.computesLeftDerivedObjectProperty S).IsStableUnderRetracts]
    [HasBinaryBiproduct X Y]
    (hXY : F.ComputesLeftDerivedAt S (X ⊞ Y)) :
    F.ComputesLeftDerivedAt S Y :=
  of_biprod_right (F.computesLeftDerivedObjectProperty S) hXY

/-- The left-derived analogue of `computesRightDerivedAt_of_biprod`. -/
theorem computesLeftDerivedAt_of_biprod
    [(F.computesLeftDerivedObjectProperty S).IsStableUnderRetracts]
    [HasBinaryBiproduct X Y]
    (hXY : F.ComputesLeftDerivedAt S (X ⊞ Y)) :
    F.ComputesLeftDerivedAt S X ∧
      F.ComputesLeftDerivedAt S Y :=
  ⟨computesLeftDerivedAt_left_of_biprod F S hXY,
    computesLeftDerivedAt_right_of_biprod F S hXY⟩

end Biproduct

end CategoryTheory
