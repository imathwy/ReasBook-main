module

public import Topology_Munkres_2000.Book.Definition_78_1.Triangulation
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

import all Topology_Munkres_2000.Book.Definition_78_1.Triangulation

public section

universe u

namespace Affine.Simplex

/-- Helper for Theorem 78.1: the algebraic interior of a positive-dimensional
full-dimensional real simplex is the topological interior of its closed interior. -/
theorem interior_eq_topologicalInterior_closedInterior
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : ℕ} [NeZero n] (simplex : Affine.Simplex ℝ V n)
    (hspan : affineSpan ℝ (Set.range simplex.points) = ⊤) :
    simplex.interior = interior simplex.closedInterior := by
  let basis : AffineBasis (Fin (n + 1)) ℝ V :=
    ⟨simplex.points, simplex.independent, hspan⟩
  -- Both interiors are described by strict positivity of the same barycentric coordinates.
  rw [← simplex.convexHull_eq_closedInterior]
  change simplex.interior = interior (convexHull ℝ (Set.range (basis : Fin (n + 1) → V)))
  rw [basis.interior_convexHull]
  ext x
  constructor
  · rintro ⟨weights, hsum, hweights, rfl⟩
    intro i
    have hcoord :
        basis.coord i (Finset.univ.affineCombination ℝ simplex.points weights) = weights i :=
      basis.coord_apply_combination_of_mem (Finset.mem_univ i) hsum
    rw [hcoord]
    exact (hweights i).1
  · intro hpositive
    let weights : Fin (n + 1) → ℝ := fun i ↦ basis.coord i x
    have hsum : ∑ i, weights i = 1 := basis.sum_coord_apply_eq_one x
    refine ⟨weights, hsum, ?_, ?_⟩
    · intro i
      have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
      obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card
        (by simpa using Nat.succ_lt_succ hn) i
      have hjmem : j ∈ (Finset.univ.erase i : Finset (Fin (n + 1))) := by
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        exact hji
      have hnonnegative :
          ∀ q ∈ (Finset.univ.erase i : Finset (Fin (n + 1))), 0 ≤ weights q := by
        intro q _
        exact (hpositive q).le
      have hremainingPositive : 0 < ∑ q ∈ Finset.univ.erase i, weights q :=
        (Finset.sum_pos_iff_of_nonneg hnonnegative).mpr ⟨j, hjmem, hpositive j⟩
      have hsplit : (∑ q ∈ Finset.univ.erase i, weights q) + weights i = 1 := by
        exact (Finset.sum_erase_add _ _ (Finset.mem_univ i)).trans hsum
      exact ⟨hpositive i, by linarith⟩
    · exact basis.affineCombination_coord_eq_self x

end Affine.Simplex

namespace CurvedTriangle

noncomputable section

variable {X : Type u} [TopologicalSpace X]

/-- Helper for Theorem 78.1: the open cell of a curved triangle is the chart
image of the algebraic interior of its planar model. -/
def openCell (triangle : CurvedTriangle X) : Set X :=
  {x | ∃ y : triangle.model.closedInterior,
    (y : EuclideanSpace ℝ (Fin 2)) ∈ triangle.model.interior ∧
      (triangle.chart y : X) = x}

/-- Helper for Theorem 78.1: open-cell membership is witnessed by an interior
model point with the prescribed chart value. -/
theorem mem_openCell_iff (triangle : CurvedTriangle X) (x : X) :
    x ∈ triangle.openCell ↔
      ∃ y : triangle.model.closedInterior,
        (y : EuclideanSpace ℝ (Fin 2)) ∈ triangle.model.interior ∧
          (triangle.chart y : X) = x := Iff.rfl

/-- Helper for Theorem 78.1: every open-cell point lies in the curved triangle. -/
theorem openCell_subset_carrier (triangle : CurvedTriangle X) :
    triangle.openCell ⊆ triangle.carrier := by
  -- An open-cell witness is a chart value, hence belongs to the chart codomain.
  rintro x ⟨y, _, rfl⟩
  exact (triangle.chart y).property

/-- Helper for Theorem 78.1: the planar model interior is open in the subtype
of the closed model triangle. -/
theorem isOpen_modelInterior_preimage (triangle : CurvedTriangle X) :
    IsOpen (Subtype.val ⁻¹' triangle.model.interior :
      Set triangle.model.closedInterior) := by
  have hspan :
      affineSpan ℝ (Set.range triangle.model.points) = ⊤ :=
    triangle.model.span_eq_top (by simp)
  have hinterior :
      triangle.model.interior = interior triangle.model.closedInterior :=
    triangle.model.interior_eq_topologicalInterior_closedInterior hspan
  -- Restrict the ambient topological interior to the closed-triangle subtype.
  rw [hinterior]
  exact isOpen_interior.preimage continuous_subtype_val

/-- Helper for Theorem 78.1: pulling the open cell back to the carrier subtype
is the chart image of the model interior. -/
theorem preimage_openCell_eq_chart_image_modelInterior
    (triangle : CurvedTriangle X) :
    (Subtype.val ⁻¹' triangle.openCell : Set triangle.carrier) =
      triangle.chart ''
        (Subtype.val ⁻¹' triangle.model.interior :
          Set triangle.model.closedInterior) := by
  -- Chart injectivity identifies the witness in the definition of the open cell.
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hchart : triangle.chart y = x := Subtype.ext hyx
    exact ⟨y, hy, hchart⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

/-- Helper for Theorem 78.1: the open cell is relatively open in its curved
triangle carrier. -/
theorem isOpen_openCell_preimage_carrier (triangle : CurvedTriangle X) :
    IsOpen (Subtype.val ⁻¹' triangle.openCell : Set triangle.carrier) := by
  -- A homeomorphism sends the relatively open model interior to a relatively open cell.
  rw [triangle.preimage_openCell_eq_chart_image_modelInterior]
  exact triangle.chart.isOpenMap _ triangle.isOpen_modelInterior_preimage

/-- Helper for Theorem 78.1: every curved-triangle carrier is compact. -/
theorem isCompact_carrier (triangle : CurvedTriangle X) :
    IsCompact triangle.carrier := by
  letI : CompactSpace triangle.model.closedInterior :=
    isCompact_iff_compactSpace.mp triangle.model.isCompact_closedInterior
  -- Compactness transports across the defining chart.
  exact isCompact_iff_compactSpace.mpr triangle.chart.compactSpace

/-- Helper for Theorem 78.1: in a Hausdorff ambient space every curved-triangle
carrier is closed. -/
theorem isClosed_carrier [T2Space X] (triangle : CurvedTriangle X) :
    IsClosed triangle.carrier := by
  -- Compact subsets of a Hausdorff space are closed.
  exact triangle.isCompact_carrier.isClosed

/-- Helper for Theorem 78.1: a set cut out inside a containing subtype is
homeomorphic to the same set viewed directly in the ambient space. -/
private def nestedSubtypeHomeomorph
    {Z : Type*} [TopologicalSpace Z] (containing inner : Set Z)
    (hinner : inner ⊆ containing) :
    (Subtype.val ⁻¹' inner : Set containing) ≃ₜ inner :=
  { toFun := fun x ↦ ⟨x.1.1, x.2⟩
    invFun := fun x ↦ ⟨⟨x.1, hinner x.2⟩, x.2⟩
    left_inv := fun _ ↦ Subtype.ext rfl
    right_inv := fun _ ↦ Subtype.ext rfl
    continuous_toFun :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk fun x ↦ x.2
    continuous_invFun :=
      (continuous_subtype_val.subtype_mk fun x ↦ hinner x.2).subtype_mk fun x ↦ x.2 }

/-- Helper for Theorem 78.1: a chart value belongs to the open cell exactly
when its model point belongs to the algebraic simplex interior. -/
theorem chart_mem_openCell_iff (triangle : CurvedTriangle X)
    (y : triangle.model.closedInterior) :
    (triangle.chart y : X) ∈ triangle.openCell ↔
      (y : EuclideanSpace ℝ (Fin 2)) ∈ triangle.model.interior := by
  -- Injectivity of the defining chart makes the open-cell witness unique.
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hmodel : z = y := by
      apply triangle.chart.injective
      exact Subtype.ext hzy
    rwa [← hmodel]
  · intro hy
    exact ⟨y, hy, rfl⟩

/-- Helper for Theorem 78.1: the open cell of a curved triangle is
homeomorphic to the interior of its planar model. -/
def openCellHomeomorph (triangle : CurvedTriangle X) :
    triangle.openCell ≃ₜ triangle.model.interior :=
  (nestedSubtypeHomeomorph triangle.carrier triangle.openCell
      triangle.openCell_subset_carrier).symm.trans
    ((triangle.chart.subtype fun y ↦ (triangle.chart_mem_openCell_iff y).symm).symm.trans
      (nestedSubtypeHomeomorph triangle.model.closedInterior triangle.model.interior
        triangle.model.interior_subset_closedInterior))

/-- Helper for Theorem 78.1: model-edge points range over the full closed
opposite face. -/
theorem range_modelEdgePoint_val (triangle : CurvedTriangle X) (i : Fin 3) :
    Set.range (fun t : unitInterval ↦
      (triangle.modelEdgePoint i t : EuclideanSpace ℝ (Fin 2))) =
      triangle.modelEdge i := by
  -- A one-simplex is exactly the affine segment traced by its line map.
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    rw [modelEdge_def, Affine.Simplex.mem_closedInterior_iff_wbtw]
    unfold modelEdgePoint modelEdgeValue
    rw [wbtw_lineMap_iff]
    exact Or.inr t.property
  · intro hx
    rw [modelEdge_def, Affine.Simplex.mem_closedInterior_iff_wbtw, Wbtw,
      affineSegment] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    refine ⟨⟨t, ht⟩, ?_⟩
    unfold modelEdgePoint modelEdgeValue
    rfl

/-- Helper for Theorem 78.1: a model-edge parameter is in the open interval
exactly when the corresponding point is in the relative interior of the edge. -/
theorem modelEdgePoint_mem_faceOpposite_interior_iff
    (triangle : CurvedTriangle X) (i : Fin 3) (t : unitInterval) :
    (triangle.modelEdgePoint i t : EuclideanSpace ℝ (Fin 2)) ∈
        (triangle.model.faceOpposite i).interior ↔
      (t : ℝ) ∈ Set.Ioo 0 1 := by
  -- Reduce relative interior membership to strict betweenness of the two
  -- face vertices, then read off the affine line-map parameter.
  rw [Affine.Simplex.mem_interior_iff_sbtw]
  unfold modelEdgePoint modelEdgeValue
  rw [sbtw_lineMap_iff]
  simp only [and_iff_right_iff_imp]
  intro _
  exact (triangle.model.faceOpposite i).independent.injective.ne (by decide)

/-- Helper for Theorem 78.1: affine parametrization of a model edge is
injective. -/
theorem injective_modelEdgeValue (triangle : CurvedTriangle X) (i : Fin 3) :
    Function.Injective (triangle.modelEdgeValue i) := by
  -- The two vertices of the opposite one-simplex are distinct, so its line
  -- map has a unique scalar parameter.
  unfold modelEdgeValue
  exact (AffineMap.lineMap_injective ℝ
    ((triangle.model.faceOpposite i).independent.injective.ne (by decide))).comp
      Subtype.coe_injective

/-- Helper for Theorem 78.1: the curved edge is the chart image of its full
closed model edge. -/
theorem edge_eq_chart_image_modelEdge (triangle : CurvedTriangle X) (i : Fin 3) :
    triangle.edge i =
      (fun y : triangle.model.closedInterior ↦ (triangle.chart y : X)) ''
        (Subtype.val ⁻¹' triangle.modelEdge i) := by
  -- Replace edge parameters by the range description of the model edge.
  ext x
  constructor
  · intro hx
    obtain ⟨t, hxt⟩ := (triangle.mem_edge_iff i x).mp hx
    subst x
    refine ⟨triangle.modelEdgePoint i t, ?_, rfl⟩
    exact (Set.ext_iff.mp (triangle.range_modelEdgePoint_val i)
      (triangle.modelEdgePoint i t)).mp ⟨t, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨t, ht⟩ :=
      (Set.ext_iff.mp (triangle.range_modelEdgePoint_val i) y).mpr hy
    apply (triangle.mem_edge_iff i _).mpr
    exact ⟨t, congrArg Subtype.val (congrArg triangle.chart (Subtype.ext ht.symm))⟩


end

end CurvedTriangle
