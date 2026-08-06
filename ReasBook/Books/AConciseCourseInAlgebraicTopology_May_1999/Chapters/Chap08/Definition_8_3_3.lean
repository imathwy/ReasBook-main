import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Convention_5_2_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Lemma_8_3_2

open CategoryTheory ConcreteCategory

universe u w

noncomputable section

-- Semantic recall via `lean_leansearch` surfaced only the model-categorical cofibration class in
-- mathlib, not a canonical owner for well-pointed compactly generated spaces. This item therefore
-- keeps the source-facing unbased cofibration predicate on the distinguished point, and bridges it
-- to the canonical structure map of `X.toBasedSpace` from the terminal based space.

/-- The inclusion of the distinguished basepoint of a based compactly generated space into its
underlying unbased space. -/
abbrev basepointInclusion (X : PointedCompactlyGenerated.{u, w}) :
    C((⊤_ TopCat.{w}), X.toBasedSpace.right) :=
  hom X.toBasedSpace.hom

/-- The basepoint inclusion evaluates to the distinguished point of `X`. -/
@[simp] theorem basepointInclusion_apply
    (X : PointedCompactlyGenerated.{u, w}) (x : (⊤_ TopCat.{w})) :
    basepointInclusion X x = X.point := by
  change
    (ContinuousMap.const PUnit.{w + 1} X.point) (TopCat.terminalIsoPUnit.hom x) = X.point
  rfl

/-- The canonical based map from the terminal based space to `X.toBasedSpace`. -/
def toBasedSpaceBasepointMap (X : PointedCompactlyGenerated.{u, w}) :
    Under.mk (𝟙 (⊤_ TopCat.{w})) ⟶ X.toBasedSpace :=
  Under.homMk (TopCat.ofHom (basepointInclusion X)) (by
    rfl)

/-- The canonical based map from the terminal based space to `X.toBasedSpace` has underlying
continuous map the source basepoint inclusion of `X`. -/
theorem toBasedSpaceBasepointMap_hom (X : PointedCompactlyGenerated.{u, w}) :
    (toBasedSpaceBasepointMap X).right.hom = basepointInclusion X := by
  rfl

/-- Definition 8.3.3. A based compactly generated space is nondegenerately based, or well
pointed, when the inclusion of its distinguished basepoint into the underlying unbased space is
an unbased cofibration. -/
class WellPointedSpace (X : PointedCompactlyGenerated.{u, w}) : Prop where
  /-- The inclusion of the distinguished basepoint of `X` is an unbased cofibration. -/
  isCofibration : IsCofibration.{w, w, w} (basepointInclusion X)

/-- The proposition `WellPointedSpace X` is subsingleton. -/
instance wellPointedSpaceSubsingleton (X : PointedCompactlyGenerated.{u, w}) :
    Subsingleton (WellPointedSpace X) :=
  inferInstance

/-- A based compactly generated space is well pointed exactly when its basepoint inclusion is an
unbased cofibration. -/
theorem wellPointedSpace_iff (X : PointedCompactlyGenerated.{u, w}) :
    WellPointedSpace X ↔ IsCofibration.{w, w, w} (basepointInclusion X) := by
  constructor
  · intro hX
    exact hX.isCofibration
  · intro hX
    exact ⟨hX⟩

/-- The source well-pointedness condition agrees with the unbased cofibration condition on the
canonical based map from the terminal based space to `PointedCompactlyGenerated.toBasedSpace X`. -/
theorem wellPointedSpace_iff_isCofibration_toBasedSpace (X : PointedCompactlyGenerated.{u, w}) :
    WellPointedSpace X ↔
      IsCofibration.{w, w, w} (toBasedSpaceBasepointMap X).right.hom := by
  simpa [toBasedSpaceBasepointMap_hom X] using wellPointedSpace_iff X

/-- A well-pointed compactly generated space makes the canonical based map from the terminal based
space to `PointedCompactlyGenerated.toBasedSpace X` into a based cofibration. -/
theorem WellPointedSpace.isBasedCofibration_toBasedSpace
    {X : PointedCompactlyGenerated.{u, w}} (hX : WellPointedSpace X) :
    IsBasedCofibration (toBasedSpaceBasepointMap X) :=
  IsCofibration.isBasedCofibration
    ((wellPointedSpace_iff_isCofibration_toBasedSpace X).mp hX)
