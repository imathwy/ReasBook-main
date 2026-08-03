module

public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
public import Mathlib.Topology.Algebra.Affine
public import Mathlib.Topology.Homeomorph.Defs

public section

open Set
open scoped Affine

universe u

/-- A curved triangle in a topological space, modeled on a closed affine triangle in the plane. -/
structure CurvedTriangle (X : Type u) [TopologicalSpace X] where
  /-- The closed affine triangle serving as the planar model. -/
  model : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))
  /-- The subset of the ambient space occupied by the curved triangle. -/
  carrier : Set X
  /-- The homeomorphism from the closed planar model onto the carrier. -/
  chart : model.closedInterior ≃ₜ carrier

namespace CurvedTriangle

noncomputable section

variable {X : Type u} [TopologicalSpace X]

/-- Construct a curved triangle from its planar model, carrier, and chart. -/
def ofModel (model : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (carrier : Set X)
    (chart : model.closedInterior ≃ₜ carrier) : CurvedTriangle X :=
  { model, carrier, chart }

/-- The `i`th closed edge of the planar model. -/
@[expose]
def modelEdge (triangle : CurvedTriangle X) (i : Fin 3) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  (triangle.model.faceOpposite i).closedInterior

/-- A model edge is the closed interior of the corresponding opposite face. -/
theorem modelEdge_def (triangle : CurvedTriangle X) (i : Fin 3) :
    triangle.modelEdge i = (triangle.model.faceOpposite i).closedInterior := rfl

/-- The chart maps the closed planar model onto the carrier. -/
theorem chart_range (triangle : CurvedTriangle X) :
    Set.range (fun x : triangle.model.closedInterior ↦ (triangle.chart x : X)) =
      triangle.carrier := by
  -- Compare the ambient range with the carrier pointwise.
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    -- Every chart value carries its carrier-membership certificate.
    exact (triangle.chart y).property
  · intro hx
    -- Surjectivity of the homeomorphism supplies a preimage of the carrier point.
    obtain ⟨y, hy⟩ := triangle.chart.surjective ⟨x, hx⟩
    refine ⟨y, ?_⟩
    exact congrArg Subtype.val hy

/-- The planar affine interpolation point on the `i`th model edge. -/
def modelEdgeValue (triangle : CurvedTriangle X) (i : Fin 3) (t : unitInterval) :
    EuclideanSpace ℝ (Fin 2) :=
  AffineMap.lineMap ((triangle.model.faceOpposite i).points 0)
    ((triangle.model.faceOpposite i).points 1) (t : ℝ)

/-- Every affine interpolation point on a model edge lies in the closed model triangle. -/
theorem modelEdgeValue_mem_region (triangle : CurvedTriangle X) (i : Fin 3)
    (t : unitInterval) :
    triangle.modelEdgeValue i t ∈ triangle.model.closedInterior := by
  apply triangle.model.closedInterior_faceOpposite_subset_closedInterior i
  rw [Affine.Simplex.mem_closedInterior_iff_wbtw]
  change Wbtw ℝ _ (AffineMap.lineMap _ _ (t : ℝ)) _
  rw [wbtw_lineMap_iff]
  exact Or.inr t.property

/-- Helper for Theorem 78.3: affine parametrization of a model edge is continuous. -/
theorem continuous_modelEdgeValue (triangle : CurvedTriangle X) (i : Fin 3) :
    Continuous (triangle.modelEdgeValue i) := by
  -- Compose continuity of the affine line map with the unit-interval inclusion.
  unfold modelEdgeValue
  exact AffineMap.lineMap_continuous.comp continuous_subtype_val

/-- The point of the closed model triangle on edge `i` with affine parameter `t`. -/
@[expose]
def modelEdgePoint (triangle : CurvedTriangle X) (i : Fin 3) (t : unitInterval) :
    triangle.model.closedInterior :=
  ⟨triangle.modelEdgeValue i t, triangle.modelEdgeValue_mem_region i t⟩

/-- The underlying point of `modelEdgePoint` is its affine interpolation value. -/
theorem modelEdgePoint_apply (triangle : CurvedTriangle X) (i : Fin 3)
    (t : unitInterval) :
    (triangle.modelEdgePoint i t : EuclideanSpace ℝ (Fin 2)) =
      triangle.modelEdgeValue i t := rfl

/-- Helper for Theorem 78.3: the model-edge parametrization is continuous into
the closed model triangle. -/
theorem continuous_modelEdgePoint (triangle : CurvedTriangle X) (i : Fin 3) :
    Continuous (triangle.modelEdgePoint i) := by
  -- Lift the ambient affine map using its established closed-triangle membership.
  exact Continuous.subtype_mk (triangle.continuous_modelEdgeValue i)
    (triangle.modelEdgeValue_mem_region i)

/-- The `i`th vertex of a curved triangle. -/
def vertex (triangle : CurvedTriangle X) (i : Fin 3) : X :=
  triangle.chart ⟨triangle.model.points i, triangle.model.point_mem_closedInterior i⟩

/-- Every curved-triangle vertex belongs to its carrier. -/
theorem vertex_mem (triangle : CurvedTriangle X) (i : Fin 3) :
    triangle.vertex i ∈ triangle.carrier := by
  -- A vertex is a chart value, so its subtype value records the desired membership.
  exact (triangle.chart
    ⟨triangle.model.points i, triangle.model.point_mem_closedInterior i⟩).property

/-- The `i`th edge of a curved triangle, parametrized by the unit interval. -/
def edge (triangle : CurvedTriangle X) (i : Fin 3) : Set X :=
  Set.range (fun t : unitInterval ↦ (triangle.chart (triangle.modelEdgePoint i t) : X))

/-- Membership in a curved edge is characterized by its affine unit-interval parameter. -/
theorem mem_edge_iff (triangle : CurvedTriangle X) (i : Fin 3) (x : X) :
    x ∈ triangle.edge i ↔
      ∃ t : unitInterval, x = (triangle.chart (triangle.modelEdgePoint i t) : X) := by
  -- Unfold the edge range and reverse the witness equality in each direction.
  unfold edge
  constructor
  · rintro ⟨t, htx⟩
    exact ⟨t, htx.symm⟩
  · rintro ⟨t, hxt⟩
    exact ⟨t, hxt.symm⟩

/-- Every curved edge is contained in the curved triangle. -/
theorem edge_subset (triangle : CurvedTriangle X) (i : Fin 3) :
    triangle.edge i ⊆ triangle.carrier := by
  -- Expose an edge parameter and reduce carrier membership to the chart codomain.
  intro x hx
  obtain ⟨t, rfl⟩ := (triangle.mem_edge_iff i x).mp hx
  exact (triangle.chart (triangle.modelEdgePoint i t)).property

/-- Two curved triangles meet in a vertex of each. -/
def SharesVertex (first second : CurvedTriangle X) : Prop :=
  ∃ i j : Fin 3,
    first.carrier ∩ second.carrier = {first.vertex i} ∧ first.vertex i = second.vertex j

/-- Shared-vertex intersections are witnessed by vertices of both curved triangles. -/
theorem sharesVertex_iff (first second : CurvedTriangle X) :
    first.SharesVertex second ↔
      ∃ i j : Fin 3,
        first.carrier ∩ second.carrier = {first.vertex i} ∧
          first.vertex i = second.vertex j := Iff.rfl

/-- Two curved triangles meet in an edge of each. -/
def SharesEdge (first second : CurvedTriangle X) : Prop :=
  ∃ i j : Fin 3,
    first.carrier ∩ second.carrier = first.edge i ∧ first.edge i = second.edge j

/-- Shared-edge intersections are witnessed by edges of both curved triangles. -/
theorem sharesEdge_iff (first second : CurvedTriangle X) :
    first.SharesEdge second ↔
      ∃ i j : Fin 3,
        first.carrier ∩ second.carrier = first.edge i ∧
          first.edge i = second.edge j := Iff.rfl

/-- Two selected curved edges have affine-compatible chart parameterizations. -/
def EdgesCompatible (first second : CurvedTriangle X) (i j : Fin 3) : Prop :=
  ∃ reverse : Bool, ∀ t : unitInterval,
    (first.chart (first.modelEdgePoint i t) : X) =
      (second.chart
        (second.modelEdgePoint j (if reverse then unitInterval.symm t else t)) : X)

/-- Edge compatibility means agreement after preserving or reversing affine parameters. -/
theorem edgesCompatible_iff (first second : CurvedTriangle X) (i j : Fin 3) :
    first.EdgesCompatible second i j ↔
      ∃ reverse : Bool, ∀ t : unitInterval,
        (first.chart (first.modelEdgePoint i t) : X) =
          (second.chart
            (second.modelEdgePoint j (if reverse then unitInterval.symm t else t)) : X) := Iff.rfl


end

end CurvedTriangle

/-- A finite triangulation of a topological space by compatible curved triangles. -/
structure Triangulation (X : Type u) [TopologicalSpace X] where
  /-- The number of curved triangles in the triangulation. -/
  card : ℕ
  /-- The finite family of curved triangles. -/
  triangle : Fin card → CurvedTriangle X
  /-- The curved triangles cover the ambient space. -/
  cover : ⋃ i, (triangle i).carrier = Set.univ
  /-- Distinct curved triangles meet only in the permitted ways. -/
  intersections (i j : Fin card) (hij : i ≠ j) :
    Disjoint (triangle i).carrier (triangle j).carrier ∨
      (triangle i).SharesVertex (triangle j) ∨ (triangle i).SharesEdge (triangle j)
  /-- Every pair of selected edges realizing a shared intersection has affine-compatible charts. -/
  sharedEdge_compatible (i j : Fin card) (hij : i ≠ j) (edgeI edgeJ : Fin 3)
    (hi : (triangle i).carrier ∩ (triangle j).carrier = (triangle i).edge edgeI)
    (hj : (triangle i).carrier ∩ (triangle j).carrier = (triangle j).edge edgeJ) :
    (triangle i).EdgesCompatible (triangle j) edgeI edgeJ

namespace Triangulation

variable {X : Type u} [TopologicalSpace X]

/-- Construct a triangulation from a finite family of curved triangles and its compatibility
conditions. -/
def ofFamily {n : ℕ} (triangle : Fin n → CurvedTriangle X)
    (cover : ⋃ i, (triangle i).carrier = Set.univ)
    (intersections : (i j : Fin n) → i ≠ j →
      Disjoint (triangle i).carrier (triangle j).carrier ∨
        (triangle i).SharesVertex (triangle j) ∨ (triangle i).SharesEdge (triangle j))
    (sharedEdge_compatible : (i j : Fin n) → i ≠ j → (edgeI edgeJ : Fin 3) →
      (triangle i).carrier ∩ (triangle j).carrier = (triangle i).edge edgeI →
      (triangle i).carrier ∩ (triangle j).carrier = (triangle j).edge edgeJ →
      (triangle i).EdgesCompatible (triangle j) edgeI edgeJ) : Triangulation X :=
  { card := n, triangle, cover, intersections, sharedEdge_compatible }

/-- The family of carriers of the curved triangles in a triangulation. -/
def carriers (triangulation : Triangulation X) : Fin triangulation.card → Set X :=
  fun i ↦ (triangulation.triangle i).carrier

/-- The carriers of the curved triangles in a triangulation cover the ambient space. -/
theorem iUnion_carrier (triangulation : Triangulation X) :
    ⋃ i, triangulation.carriers i = Set.univ := triangulation.cover

/-- Distinct curved triangles are disjoint or share a vertex or an edge. -/
theorem intersection_spec (triangulation : Triangulation X) (i j : Fin triangulation.card)
    (hij : i ≠ j) :
    Disjoint (triangulation.triangle i).carrier (triangulation.triangle j).carrier ∨
      (triangulation.triangle i).SharesVertex (triangulation.triangle j) ∨
        (triangulation.triangle i).SharesEdge (triangulation.triangle j) :=
  triangulation.intersections i j hij

/-- Edges realizing a common intersection have affine-compatible chart parameterizations. -/
theorem sharedEdgeCompatible (triangulation : Triangulation X)
    (i j : Fin triangulation.card) (hij : i ≠ j) (edgeI edgeJ : Fin 3)
    (hi : (triangulation.triangle i).carrier ∩ (triangulation.triangle j).carrier =
      (triangulation.triangle i).edge edgeI)
    (hj : (triangulation.triangle i).carrier ∩ (triangulation.triangle j).carrier =
      (triangulation.triangle j).edge edgeJ) :
    (triangulation.triangle i).EdgesCompatible (triangulation.triangle j) edgeI edgeJ :=
  triangulation.sharedEdge_compatible i j hij edgeI edgeJ hi hj


end Triangulation

/-- A topological space is triangulable when it admits a finite triangulation. -/
def Triangulable (X : Type u) [TopologicalSpace X] : Prop :=
  Nonempty (Triangulation X)

/-- Triangulability is equivalent to the existence of a finite triangulation. -/
theorem triangulable_iff (X : Type u) [TopologicalSpace X] :
    Triangulable X ↔ Nonempty (Triangulation X) := Iff.rfl
