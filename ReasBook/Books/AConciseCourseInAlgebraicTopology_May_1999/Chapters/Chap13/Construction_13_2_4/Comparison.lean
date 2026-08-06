import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.UnitInterval
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Construction_13_2_4.Quotient

open scoped unitInterval

universe u

noncomputable section

/-- The generating relation for the cofiber model of the inclusion `Xⁿ⁻¹ ↪ Xⁿ`: points of
`Xⁿ⁻¹` are identified with the base of their cone, and all cone-top points are identified. -/
def topologicalBoundaryCofiberRel {X : Type u} [TopologicalSpace X]
    (Xnm1 : Set X) :
    X ⊕ (Xnm1 × I) → X ⊕ (Xnm1 × I) → Prop
  | Sum.inl x, Sum.inr (a, t) => x = a.1 ∧ t = 0
  | Sum.inr (a, t), Sum.inl x => x = a.1 ∧ t = 0
  | Sum.inr (_, s), Sum.inr (_, t) => s = 1 ∧ t = 1
  | _, _ => False

/-- The setoid presenting the cofiber-model domain for `Xⁿ⁻¹ ↪ Xⁿ`. -/
def topologicalBoundaryCofiberSetoid {X : Type u} [TopologicalSpace X]
    (Xnm1 : Set X) : Setoid (X ⊕ (Xnm1 × I)) :=
  Relation.EqvGen.setoid (topologicalBoundaryCofiberRel Xnm1)

/-- The quotient-model cofiber carrier for the inclusion `Xⁿ⁻¹ ↪ Xⁿ`. -/
abbrev topologicalBoundaryCofiberType {X : Type u} [TopologicalSpace X]
    (Xnm1 : Set X) :=
  Quotient (topologicalBoundaryCofiberSetoid Xnm1)

/-- The cofiber-model carrier of `Xⁿ⁻¹ ↪ Xⁿ` carries the compactly generated replacement of its
quotient topology. -/
instance topologicalBoundaryCofiberTypeTopologicalSpace {X : Type u} [TopologicalSpace X]
    (Xnm1 : Set X) :
    TopologicalSpace (topologicalBoundaryCofiberType Xnm1) :=
  TopologicalSpace.compactlyGenerated.{u, u} (topologicalBoundaryCofiberType Xnm1)

/-- A chosen comparison from the quotient `Xⁿ / Xⁿ⁻¹` to the cofiber model of `Xⁿ⁻¹ ↪ Xⁿ`. -/
abbrev topologicalBoundaryQuotientToCofiber {X : Type u} [TopologicalSpace X]
    (Xnm1 : Set X) :=
  C(collapseSubsetType X Xnm1, topologicalBoundaryCofiberType Xnm1)

/-- A chosen quotient/cofiber comparison for the inclusion `Xⁿ⁻¹ ↪ Xⁿ`, using the canonical
quotient model `collapseSubsetType X Xnm1` and the canonical cofiber model
`topologicalBoundaryCofiberType Xnm1`. Besides the chosen map `Xⁿ / Xⁿ⁻¹ ⟶ cofiber(Xⁿ⁻¹ ↪ Xⁿ)`,
the structure records a chosen comparison back to the quotient and the homotopies witnessing that
these comparisons are inverse up to homotopy. -/
structure TopologicalBoundaryComparison {X : Type u} [TopologicalSpace X] (Xnm1 : Set X) where
  /-- The chosen comparison from the quotient model to the cofiber model. -/
  quotientToCofiber : topologicalBoundaryQuotientToCofiber Xnm1
  /-- The chosen comparison from the cofiber model back to the quotient model. -/
  cofiberToQuotient : C(topologicalBoundaryCofiberType Xnm1, collapseSubsetType X Xnm1)
  /-- The chosen quotient-to-cofiber comparison is a right homotopy inverse. -/
  quotientToCofiber_right :
    ContinuousMap.Homotopic
      (cofiberToQuotient.comp quotientToCofiber)
      (ContinuousMap.id (collapseSubsetType X Xnm1))
  /-- The chosen quotient-to-cofiber comparison is a left homotopy inverse. -/
  quotientToCofiber_left :
    ContinuousMap.Homotopic
      (quotientToCofiber.comp cofiberToQuotient)
      (ContinuousMap.id (topologicalBoundaryCofiberType Xnm1))
