import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import stacks_project.Chap04.Definition_4_27_20
import stacks_project.Chap13.Definition_13_14_10
import stacks_project.Chap13.Lemma_13_14_6
import stacks_project.Chap13.Lemma_13_14_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

/-
Domain-style sampling for Lemma 13.14.12:
- primary domain: pointwise computation of right/left derived functors in a triangulated
  localization situation, with closure under distinguished triangles;
- sampled owner declarations:
  `Functor.ComputesRightDerivedAt`,
  `Functor.ComputesLeftDerivedAt`,
  `Functor.computesRightDerivedObjectProperty`,
  `Functor.computesLeftDerivedObjectProperty`,
  `ObjectProperty.IsTriangulatedClosed₃`,
  `ObjectProperty.ext_of_isTriangulatedClosed₃`;
- best owner abstraction: the source-facing predicates
  `Functor.ComputesRightDerivedAt` / `Functor.ComputesLeftDerivedAt` are already organized by the
  Chapter 13 owner object properties `F.computesRightDerivedObjectProperty S` and
  `F.computesLeftDerivedObjectProperty S`; this file should therefore record the third-vertex
  distinguished-triangle closure first as the canonical owner instances
  `IsTriangulatedClosed₃` for those object properties, and only then keep the textbook `obj₃`
  statements as thin wrappers;
- primitive data: a distinguished triangle in `D` and computation hypotheses on its first two
  vertices, where `ComputesRightDerivedAt` / `ComputesLeftDerivedAt` already package the needed
  pointwise derived-definedness together with invertibility of the canonical identity
  leg/projection;
- derived API: the owner-level closure instances and the pointwise `obj₃` consequences.

Source/core/bridge triage:
- `source-facing`: the two textbook `obj₃` closure statements for objects computing the
  right/left derived functor in a distinguished triangle;
- `core/canonical`: the object-property owners
  `F.computesRightDerivedObjectProperty S` / `F.computesLeftDerivedObjectProperty S` together
  with `ObjectProperty.IsTriangulatedClosed₃`;
- `bridge/view`: the two theorem wrappers below, which simply restate the owner-level closure in
  the textbook pointwise form.
-/
variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [Limits.HasZeroObject D] [hasZeroObjectD' : Limits.HasZeroObject D']
  [HasShift D ℤ] [hasShiftD' : HasShift D' ℤ]
  [Preadditive D] [preadditiveD' : Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [shiftAdditiveD' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [pretriangulatedD' : Pretriangulated D']
  [triangulatedD' : IsTriangulated D']
  (F : D ⥤ D') (S : MorphismProperty D)
  [commShiftF : F.CommShift ℤ] [triangulatedF : F.IsTriangulated]
  [satS : IsSaturatedMultiplicativeSystem S] [compatS : S.IsCompatibleWithTriangulation]

section Right

include hasZeroObjectD' hasShiftD' preadditiveD' shiftAdditiveD' pretriangulatedD'
  triangulatedD' commShiftF triangulatedF satS compatS

-- Proof sketch: the underlying pointwise right-derived-definedness already satisfies the
-- third-vertex closure by Lemma `13.14.6`. To upgrade from definedness to computation, compare
-- the `F`-image triangle with the induced triangle on pointwise right-derived values; the first
-- two vertical maps are isomorphisms by the hypotheses on `X` and `Y`, so
-- `Pretriangulated.isIso₃_of_isIso₁₂` gives the third one and hence the required unit
-- isomorphism at `Z`.
/-- Objects computing the right derived functor of `F` form an object property closed under the
third vertex of a distinguished triangle. -/
instance computesRightDerivedObjectProperty_isTriangulatedClosed₃
    : IsTriangulatedClosed₃ (F.computesRightDerivedObjectProperty S) := by
  refine .mk' ?_
  intro T hT h₁ h₂
  sorry

end Right

section Left

include hasZeroObjectD' hasShiftD' preadditiveD' shiftAdditiveD' pretriangulatedD'
  triangulatedD' commShiftF triangulatedF satS compatS

-- Proof sketch: this is the dual owner-level closure statement. Lemma `13.14.6` gives
-- pointwise left-derived existence at the third vertex, and the comparison morphism of
-- distinguished triangles has isomorphic first two components by the hypotheses that `X` and
-- `Y` compute `LF`; two-out-of-three gives the third component, i.e. the identity projection at
-- `Z`.
/-- Objects computing the left derived functor of `F` form an object property closed under the
third vertex of a distinguished triangle. -/
instance computesLeftDerivedObjectProperty_isTriangulatedClosed₃
    : IsTriangulatedClosed₃ (F.computesLeftDerivedObjectProperty S) := by
  refine .mk' ?_
  intro T hT h₁ h₂
  sorry

end Left

end

section SourceFacing

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [Limits.HasZeroObject D] [Limits.HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  (F : D ⥤ D') (S : MorphismProperty D)
  [IsSaturatedMultiplicativeSystem S]

/-- Lemma 13.14.12 (1): if `T` is a distinguished triangle of `D` and its first two vertices
compute the right derived functor of `F` with respect to `S`, then so does its third vertex. -/
theorem computesRightDerivedAt_obj₃_of_distinguished_triangle
    [IsTriangulated D']
    [F.CommShift ℤ] [F.IsTriangulated]
    [S.IsCompatibleWithTriangulation]
    (T : Triangle D) (hT : T ∈ distTriang D)
    (h₁ : F.ComputesRightDerivedAt S T.obj₁)
    (h₂ : F.ComputesRightDerivedAt S T.obj₂) :
    F.ComputesRightDerivedAt S T.obj₃ := by
  exact (F.computesRightDerivedObjectProperty S).ext_of_isTriangulatedClosed₃ T hT h₁ h₂

/-- Lemma 13.14.12 (2): if `T` is a distinguished triangle of `D` and its first two vertices
compute the left derived functor of `F` with respect to `S`, then so does its third vertex. -/
theorem computesLeftDerivedAt_obj₃_of_distinguished_triangle
    [IsTriangulated D']
    [F.CommShift ℤ] [F.IsTriangulated]
    [S.IsCompatibleWithTriangulation]
    (T : Triangle D) (hT : T ∈ distTriang D)
    (h₁ : F.ComputesLeftDerivedAt S T.obj₁)
    (h₂ : F.ComputesLeftDerivedAt S T.obj₂) :
    F.ComputesLeftDerivedAt S T.obj₃ := by
  exact (F.computesLeftDerivedObjectProperty S).ext_of_isTriangulatedClosed₃ T hT h₁ h₂

end SourceFacing

end CategoryTheory
