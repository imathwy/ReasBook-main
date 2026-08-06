import Mathlib.Topology.Homotopy.HomotopyGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Convention_5_2_7

open scoped ContinuousMapZero Topology.Homotopy

-- Semantic recall: `HomotopyGroup.group` and `HomotopyGroup.commGroup` give the canonical
-- algebraic structures on `π₁` and `π₂`. This item records `[Σ X, Y]` and `[Σ² X, Y]` through
-- the standard mapping-space interpretation `π₁(F(X, Y), 0)` and `π₂(F(X, Y), 0)`.

noncomputable section

universe u v w

namespace PointedCompactlyGenerated

/-- The underlying compactly generated space of a based compactly generated space uses the
distinguished point as its zero. -/
instance instZeroToCompactlyGenerated (X : PointedCompactlyGenerated.{u, w}) :
    Zero X.toCompactlyGenerated :=
  ⟨X.point⟩

/-- The Chapter 8 based mapping space between pointed compactly generated spaces, expressed via
the canonical owner `F(X, Y)` for based maps of zero-pointed spaces. -/
abbrev basedMappingSpace (X : PointedCompactlyGenerated.{u, w})
    (Y : PointedCompactlyGenerated.{v, w}) :=
  F(X.toCompactlyGenerated, Y.toCompactlyGenerated)

end PointedCompactlyGenerated

/-- Lean notation for the suspension homotopy classes `[Σ X, Y]`, formalized by
`π₁(PointedCompactlyGenerated.basedMappingSpace X Y, 0)`. -/
notation "[Σ " X ", " Y "]" =>
  HomotopyGroup.Pi 1 (PointedCompactlyGenerated.basedMappingSpace X Y)
    (0 : PointedCompactlyGenerated.basedMappingSpace X Y)

/-- Lean notation for the double-suspension homotopy classes `[Σ² X, Y]`, formalized by
`π₂(PointedCompactlyGenerated.basedMappingSpace X Y, 0)`. -/
notation "[Σ² " X ", " Y "]" =>
  HomotopyGroup.Pi 2 (PointedCompactlyGenerated.basedMappingSpace X Y)
    (0 : PointedCompactlyGenerated.basedMappingSpace X Y)

/-- Lemma 8.2.8 (1): the suspension classes `[Σ X, Y]` carry the usual group structure. -/
instance suspensionHomotopyClassesGroup
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w}) :
    Group ([Σ X, Y]) :=
  inferInstance

/-- Lemma 8.2.8 (2): the double suspension classes `[Σ² X, Y]` carry the usual commutative group
structure. -/
instance doubleSuspensionHomotopyClassesCommGroup
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w}) :
    CommGroup ([Σ² X, Y]) :=
  inferInstance
