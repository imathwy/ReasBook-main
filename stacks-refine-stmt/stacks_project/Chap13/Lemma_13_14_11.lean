import stacks_project.Chap13.Definition_13_14_10
import stacks_project.Chap13.Lemma_13_14_5

open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

/- Domain-style sampling for Lemma 13.14.11:
- primary domain: shift compatibility for the source-facing computation conditions for pointwise
  left/right derived functors on a localization;
- inspected owner declarations:
  `ObjectProperty.IsStableUnderShift`,
  `ObjectProperty.prop_shift_iff_of_isStableUnderShift`,
  `Functor.ComputesRightDerivedAt`,
  `Functor.ComputesLeftDerivedAt`,
  `Functor.computesRightDerivedObjectProperty`,
  `Functor.computesLeftDerivedObjectProperty`,
  `hasPointwiseRightDerivedFunctorAt_iff_shift`,
  `hasPointwiseLeftDerivedFunctorAt_iff_shift`;
- best owner abstraction: the canonical closure owner
  `ObjectProperty.IsStableUnderShift ℤ` applied to the Chapter `13` owner object properties
  `F.computesRightDerivedObjectProperty S` and `F.computesLeftDerivedObjectProperty S`;
- primitive data: the source-facing predicates `Functor.ComputesRightDerivedAt` and
  `Functor.ComputesLeftDerivedAt`, whose content is pointwise derived-definedness together with
  invertibility of the canonical unit/counit comparison map from `Definition_13_14_10`;
- derived API: the owner object properties from `Definition_13_14_10`, the closure instances
  below, and the source-facing `↔` lemmas whose proofs reuse that internal owner abstraction.

Source/core/bridge triage:
- `source-facing`: the textbook statements that `X` computes the derived functor if and only if
  `X⟦n⟧` does, under compatibility of `S` and `F` with shift;
- `core/canonical`: `ObjectProperty.IsStableUnderShift ℤ` for the owner object properties
  `F.computesRightDerivedObjectProperty S` and `F.computesLeftDerivedObjectProperty S`;
- `bridge/view`: the companion pointwise `↔` lemmas below, proved via the owner-level
  shift-stability API. -/

section

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [HasShift D ℤ] [HasShift D' ℤ]
  (F : D ⥤ D') (S : MorphismProperty D)
  [S.ContainsIdentities] [S.IsCompatibleWithShift ℤ] [F.CommShift ℤ]
  {X : D} (n : ℤ)

/-- Objects which compute the right derived functor of `F` are closed under ambient
isomorphisms. -/
instance computesRightDerivedAt_isClosedUnderIsomorphisms :
    IsClosedUnderIsomorphisms (F.computesRightDerivedObjectProperty S) := by
  sorry

/-- Objects which compute the left derived functor of `F` are closed under ambient
isomorphisms. -/
instance computesLeftDerivedAt_isClosedUnderIsomorphisms :
    IsClosedUnderIsomorphisms (F.computesLeftDerivedObjectProperty S) := by
  sorry

/-- Objects which compute the right derived functor of `F` form a shift-stable object property. -/
instance computesRightDerivedAt_isStableUnderShift :
    IsStableUnderShift (F.computesRightDerivedObjectProperty S) ℤ := by
  sorry

/-- Objects which compute the left derived functor of `F` form a shift-stable object property. -/
instance computesLeftDerivedAt_isStableUnderShift :
    IsStableUnderShift (F.computesLeftDerivedObjectProperty S) ℤ := by
  sorry

end

section

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [HasShift D ℤ]
  (F : D ⥤ D') (S : MorphismProperty D)
  [S.ContainsIdentities]
  {X : D} (n : ℤ)

-- Proof sketch: combine the shift invariance of pointwise right-derived existence from
-- `hasPointwiseRightDerivedFunctorAt_iff_shift` with the canonical shift comparison for the
-- pointwise derived values from `Lemma_13_14_5 (2)`, which transports invertibility of the unit
-- map `F.obj X ⟶ RF(X)` exactly to the unit map at `X⟦n⟧`.
/-- Lemma 13.14.11 (1): if the morphism property `S` and the functor `F` are compatible with
shifts, then `X` computes the right derived functor of `F` with respect to `S` if and only if
`X⟦n⟧` does. -/
theorem computesRightDerivedAt_iff_shift
    [HasShift D' ℤ] [S.IsCompatibleWithShift ℤ] [F.CommShift ℤ]
    : F.ComputesRightDerivedAt S X ↔
      F.ComputesRightDerivedAt S (X⟦n⟧) := by
  simpa using
    ((F.computesRightDerivedObjectProperty S).prop_shift_iff_of_isStableUnderShift X n).symm

-- Proof sketch: this is the dual argument, using
-- `hasPointwiseLeftDerivedFunctorAt_iff_shift` together with the shift comparison for the
-- pointwise left-derived values to transport invertibility of the canonical counit map.
/-- Lemma 13.14.11 (2): if the morphism property `S` and the functor `F` are compatible with
shifts, then `X` computes the left derived functor of `F` with respect to `S` if and only if
`X⟦n⟧` does. -/
theorem computesLeftDerivedAt_iff_shift
    [HasShift D' ℤ] [S.IsCompatibleWithShift ℤ] [F.CommShift ℤ]
    : F.ComputesLeftDerivedAt S X ↔
      F.ComputesLeftDerivedAt S (X⟦n⟧) := by
  simpa using
    ((F.computesLeftDerivedObjectProperty S).prop_shift_iff_of_isStableUnderShift X n).symm

end

end CategoryTheory
