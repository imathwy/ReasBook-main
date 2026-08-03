module

public import Topology_Munkres_2000.Book.Remark_74_2.Vertices
public import Topology_Munkres_2000.Book.Example_74_1.Presentation
public import Topology_Munkres_2000.Book.Example_74_2.Presentation
public import Topology_Munkres_2000.Book.Example_74_3
import all Topology_Munkres_2000.Book.Remark_74_2.Vertices
import all Topology_Munkres_2000.Book.Example_74_1.Presentation
import all Topology_Munkres_2000.Book.Example_74_2.Presentation
import all Topology_Munkres_2000.Book.Example_74_2.UnitSquare
import all Topology_Munkres_2000.Book.Example_74_3
import all Topology_Munkres_2000.Book.Proposition_76_1.Realization

public section

/- The condition that all polygon vertices have one quotient image is the following
map-level predicate, specialized by edge pastings below. -/
#check PolygonVertices.Identified
#check PolygonVertices.identified_iff_exists
#check CyclicPolygon.EdgePasting.VerticesIdentified
#check CyclicPolygon.EdgePasting.verticesIdentified_iff_exists

universe u

/-- Helper for Remark 74.2: a singleton labelling scheme has only its head occurrence. -/
private lemma occurrence_eq_consHead {α : Type u} (word : PolygonWord α)
    (r : LabellingScheme.Occurrence (word ::ₘ 0)) :
    r = (LabellingScheme.consOccurrenceEquiv word 0).symm none := by
  -- Under the cons-occurrence equivalence, the alternative would index the empty remainder.
  apply (LabellingScheme.consOccurrenceEquiv word 0).injective
  rw [Equiv.apply_symm_apply]
  cases h : LabellingScheme.consOccurrenceEquiv word 0 r with
  | none => rfl
  | some remaining =>
      exact (Nat.not_lt_zero remaining.2 remaining.2.isLt).elim

namespace TriangleDisk

/-- Helper for Remark 74.2: every point carrier in the triangular presentation is the standard
triangle. -/
private lemma pointType_eq (r : LabellingScheme.Occurrence scheme) :
    regions.Point r = standardTriangle := by
  -- The presentation uses the same standard triangle for its unique occurrence.
  unfold regions
  rfl

/-- Helper for Remark 74.2: the unique triangular occurrence carries the displayed boundary
word. -/
private lemma region_word : region.1 = boundaryWord := by
  -- The inverse occurrence equivalence selects the head word.
  rfl

/-- Helper for Remark 74.2: the coordinate-sum invariant on the triangular presentation. -/
private def coordinateSum (x : regions.Source) : ℝ :=
  let point : standardTriangle := cast (pointType_eq x.1) x.2
  point.1 0 + point.1 1

/-- Helper for Remark 74.2: the coordinate sum of a parametrized triangle edge is computed by
`edgeCoordinates`. -/
private lemma coordinateSum_edge (r : LabellingScheme.Occurrence scheme)
    (edge : Fin r.1.1.length) (t : unitInterval) :
    coordinateSum ⟨r, regions.edge r edge t⟩ =
      edgeCoordinates (Fin.cast (occurrence_length r) edge) t 0 +
        edgeCoordinates (Fin.cast (occurrence_length r) edge) t 1 := by
  -- Unfold the carrier transport once and reduce it to the concrete edge parametrization.
  unfold coordinateSum regions edgePoint
  rfl

/-- Helper for Remark 74.2: the coordinate sum at a named triangle vertex is computed by its
edge parametrization. -/
private lemma coordinateSum_vertex (i : Fin 3) :
    coordinateSum (vertex i) = edgeCoordinates i 0 0 + edgeCoordinates i 0 1 := by
  -- The named vertex is the initial point of its corresponding edge.
  unfold coordinateSum vertex regions edgePoint
  rfl

/-- Helper for Remark 74.2: directly paired triangle-edge points have the same coordinate sum. -/
private lemma edgeRelated_coordinateSum {x y : regions.Source}
    (hxy : regions.EdgeRelated x y) :
    coordinateSum x = coordinateSum y := by
  -- Normalize to the unique triangular region, then check the nine possible edge pairs.
  unfold LabellingScheme.PolygonalRegions.EdgeRelated at hxy
  rcases hxy with ⟨region₁, region₂, edge₁, edge₂, t, hlabel, rfl, rfl⟩
  rw [coordinateSum_edge, coordinateSum_edge]
  have hregion₁ : region₁ = region := occurrence_eq_consHead boundaryWord region₁
  have hregion₂ : region₂ = region := occurrence_eq_consHead boundaryWord region₂
  subst region₁
  subst region₂
  fin_cases edge₁
  all_goals fin_cases edge₂
  all_goals
    simp [region_word, boundaryWord, boundaryLetters, edgeCoordinates,
      unitInterval.coe_symm_eq] at hlabel ⊢

end TriangleDisk

namespace SphereSquare

/-- Helper for Remark 74.2: every point carrier in the sphere-square presentation is the unit
square. -/
private lemma pointType_eq (r : LabellingScheme.Occurrence scheme) :
    regions.Point r = (unitInterval × unitInterval) := by
  -- The presentation uses the same unit square for its unique occurrence.
  unfold regions
  rfl

/-- Helper for Remark 74.2: the unique sphere-square occurrence carries the displayed boundary
word. -/
private lemma region_word : region.1 = boundaryWord := by
  -- The inverse occurrence equivalence selects the head word.
  rfl

/-- Helper for Remark 74.2: the coordinate-difference invariant on the sphere-square
presentation. -/
private def coordinateDifference (x : regions.Source) : ℝ :=
  let point : unitInterval × unitInterval := cast (pointType_eq x.1) x.2
  (point.1 : ℝ) - (point.2 : ℝ)

/-- Helper for Remark 74.2: the coordinate difference of a parametrized square edge is computed
by `UnitSquare.edge`. -/
private lemma coordinateDifference_edge (r : LabellingScheme.Occurrence scheme)
    (edge : Fin r.1.1.length) (t : unitInterval) :
    coordinateDifference ⟨r, regions.edge r edge t⟩ =
      ((UnitSquare.edge edge t).1 : ℝ) - ((UnitSquare.edge edge t).2 : ℝ) := by
  -- Unfold the carrier transport once and reduce it to the concrete square parametrization.
  unfold coordinateDifference regions
  rfl

/-- Helper for Remark 74.2: the coordinate difference at a named square vertex is computed by
its edge parametrization. -/
private lemma coordinateDifference_vertex (i : Fin 4) :
    coordinateDifference (vertex i) =
      ((UnitSquare.edge i 0).1 : ℝ) - ((UnitSquare.edge i 0).2 : ℝ) := by
  -- The named vertex is the initial point of its corresponding edge.
  unfold coordinateDifference vertex regions
  rfl

/-- Helper for Remark 74.2: directly paired sphere-square edge points have equal coordinate
difference. -/
private lemma edgeRelated_coordinateDifference {x y : regions.Source}
    (hxy : regions.EdgeRelated x y) :
    coordinateDifference x = coordinateDifference y := by
  -- Normalize to the unique square region, then check the sixteen possible edge pairs.
  unfold LabellingScheme.PolygonalRegions.EdgeRelated at hxy
  rcases hxy with ⟨region₁, region₂, edge₁, edge₂, t, hlabel, rfl, rfl⟩
  rw [coordinateDifference_edge, coordinateDifference_edge]
  have hregion₁ : region₁ = region := occurrence_eq_consHead boundaryWord region₁
  have hregion₂ : region₂ = region := occurrence_eq_consHead boundaryWord region₂
  subst region₁
  subst region₂
  fin_cases edge₁
  all_goals fin_cases edge₂
  all_goals
    simp [region_word, boundaryWord, boundaryLetters, UnitSquare.edge,
      unitInterval.coe_symm_eq] at hlabel ⊢

end SphereSquare

/-- Remark 74.2 (1): The four vertices of the torus square have one common image in
the quotient. -/
theorem torusSquareVerticesIdentified :
    PolygonVertices.Identified TorusSquare.regions.quotientMap TorusSquare.vertex := by
  -- Quotient equality reduces to coordinatewise identification of interval endpoints.
  unfold PolygonVertices.Identified
  intro i j
  apply (TorusSquare.regions.quotientMap_realizes.fibers _ _).mpr
  rw [TorusSquare.identified_projection_iff, TorusSquare.identified_iff]
  -- Every square vertex has only endpoint coordinates, so all sixteen pairs are related.
  fin_cases i
  all_goals fin_cases j
  all_goals
    simp [TorusSquare.vertex, UnitSquare.edge, unitInterval.endpointSetoid_iff]

/-- Remark 74.2 (2): The three vertices of the triangular ball presentation do not
all have one common image in the quotient. -/
theorem triangleDiskVerticesNotIdentified :
    ¬ PolygonVertices.Identified
      TriangleDisk.regions.quotientMap TriangleDisk.vertex := by
  -- Equality of the first two vertex classes would place them in the generated edge relation.
  intro hall
  unfold PolygonVertices.Identified at hall
  have hquotient := hall (0 : Fin 3) (1 : Fin 3)
  have hidentified : TriangleDisk.regions.Identified.r
      (TriangleDisk.vertex 0) (TriangleDisk.vertex 1) :=
    (TriangleDisk.regions.quotientMap_realizes.fibers _ _).mp hquotient
  -- The direct coordinate-sum invariant extends through reflexivity, symmetry, and transitivity.
  have hsum : (Setoid.ker TriangleDisk.coordinateSum)
      (TriangleDisk.vertex 0) (TriangleDisk.vertex 1) := by
    exact Relation.EqvGen.eqvGen_le
      (r' := Setoid.ker TriangleDisk.coordinateSum)
      (fun hxy ↦ TriangleDisk.edgeRelated_coordinateSum hxy) hidentified
  -- The invariant has values `0` and `1` at these two concrete vertices.
  rw [Setoid.ker_def] at hsum
  rw [TriangleDisk.coordinateSum_vertex, TriangleDisk.coordinateSum_vertex] at hsum
  norm_num [TriangleDisk.edgeCoordinates] at hsum

/-- Remark 74.2 (3): The four vertices of the sphere square do not all have one
common image in the quotient. -/
theorem sphereSquareVerticesNotIdentified :
    ¬ PolygonVertices.Identified
      SphereSquare.regions.quotientMap SphereSquare.vertex := by
  -- Equality of the first two vertex classes would place them in the generated edge relation.
  intro hall
  unfold PolygonVertices.Identified at hall
  have hquotient := hall (0 : Fin 4) (1 : Fin 4)
  have hidentified : SphereSquare.regions.Identified.r
      (SphereSquare.vertex 0) (SphereSquare.vertex 1) :=
    (SphereSquare.regions.quotientMap_realizes.fibers _ _).mp hquotient
  -- The direct coordinate-difference invariant extends to the full equivalence closure.
  have hdifference : (Setoid.ker SphereSquare.coordinateDifference)
      (SphereSquare.vertex 0) (SphereSquare.vertex 1) := by
    exact Relation.EqvGen.eqvGen_le
      (r' := Setoid.ker SphereSquare.coordinateDifference)
      (fun hxy ↦ SphereSquare.edgeRelated_coordinateDifference hxy) hidentified
  -- The invariant has values `0` and `1` at these two concrete vertices.
  rw [Setoid.ker_def] at hdifference
  rw [SphereSquare.coordinateDifference_vertex,
    SphereSquare.coordinateDifference_vertex] at hdifference
  norm_num [UnitSquare.edge] at hdifference
