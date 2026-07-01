import Mathlib
import stacks_project.Chap13.Lemma_13_14_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒟 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']
  (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟)

/-- The object property on `𝒟` consisting of those objects at which the pointwise right derived
functor of `F` with respect to `S` is defined. -/
abbrev rightDerivedDefinedObjectProperty : ObjectProperty 𝒟 :=
  fun X ↦ F.HasPointwiseRightDerivedFunctorAt S X

/-- The object property on `𝒟` consisting of those objects at which the pointwise left derived
functor of `F` with respect to `S` is defined. -/
abbrev leftDerivedDefinedObjectProperty : ObjectProperty 𝒟 :=
  fun X ↦ F.HasPointwiseLeftDerivedFunctorAt S X

end

section

variable {𝒟 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']
  (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟)

/- Domain-style sampling for Lemma 13.14.5:
- primary domain: pointwise left/right derived functors on a localization, together with shift
  compatibility;
- inspected owner declarations:
  `rightDerivedDefinedObjectProperty`,
  `leftDerivedDefinedObjectProperty`,
  `Functor.HasPointwiseRightDerivedFunctorAt`,
  `Functor.HasPointwiseLeftDerivedFunctorAt`,
  `Functor.IsPointwiseLeftKanExtensionAt.isoColimit`,
  `Functor.IsPointwiseRightKanExtensionAt.isoLimit`;
- best owner abstraction: the source-facing pointwise derived values are already owned in this
  chapter by `rightDerivedValue`, `leftDerivedValue`, and the owner object properties
  `rightDerivedDefinedObjectProperty` / `leftDerivedDefinedObjectProperty`, built on top of the
  core/canonical mathlib predicates `Functor.HasPointwiseRightDerivedFunctorAt` and
  `Functor.HasPointwiseLeftDerivedFunctorAt`; the reusable closure API for those predicates should
  live at the owner level `ObjectProperty.IsClosedUnderIsomorphisms` and
  `ObjectProperty.IsStableUnderShift`;
- primitive data: the pointwise derived-definedness predicates at a fixed object;
- derived API: the owner-level closure instances, the shift-invariance equivalences for those
  predicates, and the canonical shift comparison isomorphisms for the pointwise derived values.

Source/core/bridge triage:
- `source-facing`: the four shift-compatibility statements in Lemma 13.14.5;
- `core/canonical`: `ObjectProperty.IsClosedUnderIsomorphisms`,
  `ObjectProperty.IsStableUnderShift`, `Functor.HasPointwiseRightDerivedFunctorAt`,
  `Functor.HasPointwiseLeftDerivedFunctorAt`, `rightDerivedValue`, and `leftDerivedValue`;
- `bridge/view`: the direct typeclass transport instances from `X` to `X⟦n⟧`, derived from the
  owner-level object-property API. -/

/-- The predicate `X ↦ F.HasPointwiseRightDerivedFunctorAt S X` is invariant under isomorphism of
objects. -/
instance rightDerivedDefinedObjectProperty_isClosedUnderIsomorphisms :
    IsClosedUnderIsomorphisms (rightDerivedDefinedObjectProperty F S) := by
  sorry

/-- The predicate `X ↦ F.HasPointwiseLeftDerivedFunctorAt S X` is invariant under isomorphism of
objects. -/
instance leftDerivedDefinedObjectProperty_isClosedUnderIsomorphisms :
    IsClosedUnderIsomorphisms (leftDerivedDefinedObjectProperty F S) := by
  sorry

end

section RightShift

variable {𝒟 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']
  (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟)

/-- The predicate `X ↦ F.HasPointwiseRightDerivedFunctorAt S X` is stable under shifts. -/
instance rightDerivedDefinedObjectProperty_isStableUnderShift
    [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ] :
    IsStableUnderShift (rightDerivedDefinedObjectProperty F S) ℤ := by
  sorry

end RightShift

section RightShiftAPI

variable {𝒟 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']
  (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟)

-- Proof sketch: the localization functor `S.Q` commutes with shifts under
-- the shift-compatibility hypotheses from Situation 13.14.1. Packaging this as an
-- `ObjectProperty.IsStableUnderShift` instance gives the source-facing `↔` statement immediately.
/-- Lemma 13.14.5 (1): the right derived functor of `F` is defined at `X` if and only if it is
defined at the shifted object `X⟦n⟧`. -/
theorem hasPointwiseRightDerivedFunctorAt_iff_shift
    [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : 𝒟) (n : ℤ) :
    F.HasPointwiseRightDerivedFunctorAt S X ↔
      F.HasPointwiseRightDerivedFunctorAt S (X⟦n⟧) := by
  simpa using
    ((rightDerivedDefinedObjectProperty F S).prop_shift_iff_of_isStableUnderShift X n).symm

instance pointwiseRightDerivedFunctorAt_shift
    [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : 𝒟) (n : ℤ)
    [F.HasPointwiseRightDerivedFunctorAt S X] :
    F.HasPointwiseRightDerivedFunctorAt S (X⟦n⟧) := by
  exact (hasPointwiseRightDerivedFunctorAt_iff_shift F S X n).mp inferInstance

end RightShiftAPI

section RightShiftIso

variable {𝒟 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']
  (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟)

-- Proof sketch: clause (1) already recovers the shifted pointwise right-derived value from the
-- single source-facing assumption at `X`; the shift-compatibility hypotheses then canonically
-- identify the diagrams computing `RF(X⟦n⟧)` and `RF(X)⟦n⟧`, and `isoColimit` packages the
-- resulting universal-property uniqueness as the comparison isomorphism.
/-- Lemma 13.14.5 (2): when the right derived functor of `F` is defined at `X`, the derived
value at `X⟦n⟧` is canonically isomorphic to the shift `RF(X)⟦n⟧`. -/
noncomputable def rightDerivedValueShiftIso
    [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : 𝒟) (n : ℤ)
    [F.HasPointwiseRightDerivedFunctorAt S X] :
    rightDerivedValue S F (X⟦n⟧) ≅ ((rightDerivedValue S F X)⟦n⟧) := by
  sorry

end RightShiftIso

section LeftShift

variable {𝒟 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']
  (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟)

/-- The predicate `X ↦ F.HasPointwiseLeftDerivedFunctorAt S X` is stable under shifts. -/
instance leftDerivedDefinedObjectProperty_isStableUnderShift
    [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ] :
    IsStableUnderShift (leftDerivedDefinedObjectProperty F S) ℤ := by
  sorry

end LeftShift

section LeftShiftAPI

variable {𝒟 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']
  (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟)

-- Proof sketch: this is the dual of the right-derived statement, again exposed first through the
-- owner-level shift-stability API on the underlying object property.
/-- Lemma 13.14.5 (3): the left derived functor of `F` is defined at `X` if and only if it is
defined at the shifted object `X⟦n⟧`. -/
theorem hasPointwiseLeftDerivedFunctorAt_iff_shift
    [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : 𝒟) (n : ℤ) :
    F.HasPointwiseLeftDerivedFunctorAt S X ↔
      F.HasPointwiseLeftDerivedFunctorAt S (X⟦n⟧) := by
  simpa using
    ((leftDerivedDefinedObjectProperty F S).prop_shift_iff_of_isStableUnderShift X n).symm

instance pointwiseLeftDerivedFunctorAt_shift
    [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : 𝒟) (n : ℤ)
    [F.HasPointwiseLeftDerivedFunctorAt S X] :
    F.HasPointwiseLeftDerivedFunctorAt S (X⟦n⟧) := by
  exact (hasPointwiseLeftDerivedFunctorAt_iff_shift F S X n).mp inferInstance

end LeftShiftAPI

section LeftShiftIso

variable {𝒟 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']
  (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟)

-- Proof sketch: clause (3) supplies the shifted pointwise left-derived value from the single
-- source-facing assumption at `X`, and the localization-shift compatibility then identifies the
-- diagrams computing `LF(X⟦n⟧)` and `LF(X)⟦n⟧`, with `isoLimit` providing the canonical
-- uniqueness isomorphism.
/-- Lemma 13.14.5 (4): when the left derived functor of `F` is defined at `X`, the derived
value at `X⟦n⟧` is canonically isomorphic to the shift `LF(X)⟦n⟧`. -/
noncomputable def leftDerivedValueShiftIso
    [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : 𝒟) (n : ℤ)
    [F.HasPointwiseLeftDerivedFunctorAt S X] :
    leftDerivedValue S F (X⟦n⟧) ≅ ((leftDerivedValue S F X)⟦n⟧) := by
  sorry

end LeftShiftIso

end CategoryTheory
