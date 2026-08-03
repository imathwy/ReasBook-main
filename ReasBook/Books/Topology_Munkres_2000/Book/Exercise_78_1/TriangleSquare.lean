module

public import Topology_Munkres_2000.Book.Example_74_1.Presentation
public import Topology_Munkres_2000.Book.Example_74_2.UnitSquare
public import Topology_Munkres_2000.Book.Exercise_55_3

public section

namespace FourTrianglePasting

/-- Helper for Exercise 78.1: both coordinates of the lower triangle chart lie in the unit
interval. -/
lemma lowerTriangleChart_mem (point : standardTriangle) :
    point.1 0 + point.1 1 ∈ Set.Icc (0 : ℝ) 1 ∧ point.1 1 ∈ Set.Icc (0 : ℝ) 1 := by
  -- The triangle inequalities give nonnegativity and the common upper bound directly.
  have hpoint := point.property
  rw [mem_standardTriangle] at hpoint
  constructor
  · exact ⟨add_nonneg hpoint.1 hpoint.2.1, hpoint.2.2⟩
  · exact ⟨hpoint.2.1, (le_add_of_nonneg_left hpoint.1).trans hpoint.2.2⟩

/-- Helper for Exercise 78.1: both coordinates of the upper triangle chart lie in the unit
interval. -/
lemma upperTriangleChart_mem (point : standardTriangle) :
    point.1 0 ∈ Set.Icc (0 : ℝ) 1 ∧ point.1 0 + point.1 1 ∈ Set.Icc (0 : ℝ) 1 := by
  -- The same inequalities, with the two output coordinates exchanged, prove this chart lands.
  have hpoint := point.property
  rw [mem_standardTriangle] at hpoint
  constructor
  · exact ⟨hpoint.1, (le_add_of_nonneg_right hpoint.2.1).trans hpoint.2.2⟩
  · exact ⟨add_nonneg hpoint.1 hpoint.2.1, hpoint.2.2⟩

/-- Helper for Exercise 78.1: the affine chart onto the lower-right half of the unit square. -/
def lowerTriangleChart (point : standardTriangle) : unitInterval × unitInterval :=
  (⟨point.1 0 + point.1 1, (lowerTriangleChart_mem point).1⟩,
    ⟨point.1 1, (lowerTriangleChart_mem point).2⟩)

/-- Helper for Exercise 78.1: the affine chart onto the upper-left half of the unit square. -/
def upperTriangleChart (point : standardTriangle) : unitInterval × unitInterval :=
  (⟨point.1 0, (upperTriangleChart_mem point).1⟩,
    ⟨point.1 0 + point.1 1, (upperTriangleChart_mem point).2⟩)

/-- Helper for Exercise 78.1: the lower affine triangle chart is continuous. -/
lemma continuous_lowerTriangleChart : Continuous lowerTriangleChart := by
  -- Continuity reduces to the two affine coordinate formulas after forgetting subtype proofs.
  apply Continuous.prodMk
  · exact Continuous.subtype_mk (by fun_prop) _
  · exact Continuous.subtype_mk (by fun_prop) _

/-- Helper for Exercise 78.1: the upper affine triangle chart is continuous. -/
lemma continuous_upperTriangleChart : Continuous upperTriangleChart := by
  -- Continuity reduces to the two affine coordinate formulas after forgetting subtype proofs.
  apply Continuous.prodMk
  · exact Continuous.subtype_mk (by fun_prop) _
  · exact Continuous.subtype_mk (by fun_prop) _

/-- Helper for Exercise 78.1: the lower chart sends the triangle's third edge to the square
diagonal, with reversed parameter. -/
lemma lowerTriangleChart_edge_two (t : unitInterval) :
    lowerTriangleChart (TriangleDisk.edgePoint 2 t) =
      (unitInterval.symm t, unitInterval.symm t) := by
  -- Expand the third triangle edge and compare the two square coordinates.
  apply Prod.ext <;> apply Subtype.ext <;>
    simp [lowerTriangleChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates]

/-- Helper for Exercise 78.1: the upper chart sends the triangle's first edge to the square
diagonal. -/
lemma upperTriangleChart_edge_zero (t : unitInterval) :
    upperTriangleChart (TriangleDisk.edgePoint 0 t) = (t, t) := by
  -- Expand the first triangle edge and compare the two square coordinates.
  apply Prod.ext <;> apply Subtype.ext <;>
    simp [upperTriangleChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates]

/-- Helper for Exercise 78.1: the lower affine chart is injective. -/
lemma lowerTriangleChart_injective : Function.Injective lowerTriangleChart := by
  intro point point' hpoints
  apply Subtype.ext
  ext coordinate
  fin_cases coordinate
  · have hfirst := congrArg (fun square ↦ (square.1 : ℝ)) hpoints
    have hsecond := congrArg (fun square ↦ (square.2 : ℝ)) hpoints
    simp only [lowerTriangleChart] at hfirst hsecond
    change point.1 0 = point'.1 0
    linarith
  · exact congrArg (fun square ↦ (square.2 : ℝ)) hpoints

/-- Helper for Exercise 78.1: the upper affine chart is injective. -/
lemma upperTriangleChart_injective : Function.Injective upperTriangleChart := by
  intro point point' hpoints
  apply Subtype.ext
  ext coordinate
  fin_cases coordinate
  · exact congrArg (fun square ↦ (square.1 : ℝ)) hpoints
  · have hfirst := congrArg (fun square ↦ (square.1 : ℝ)) hpoints
    have hsecond := congrArg (fun square ↦ (square.2 : ℝ)) hpoints
    simp only [upperTriangleChart] at hfirst hsecond
    change point.1 1 = point'.1 1
    linarith

/-- Helper for Exercise 78.1: equality between the two chart images occurs exactly along the
common diagonal edges. -/
lemma lowerTriangleChart_eq_upperTriangleChart_iff (point point' : standardTriangle) :
    lowerTriangleChart point = upperTriangleChart point' ↔
      ∃ t : unitInterval,
        point = TriangleDisk.edgePoint 2 (unitInterval.symm t) ∧
          point' = TriangleDisk.edgePoint 0 t := by
  constructor
  · intro hpoints
    have hpoint := point.property
    have hpoint' := point'.property
    rw [mem_standardTriangle] at hpoint hpoint'
    let t : unitInterval := (upperTriangleChart point').1
    refine ⟨t, ?_, ?_⟩
    · apply Subtype.ext
      ext coordinate
      fin_cases coordinate
      · have hfirst := congrArg (fun square ↦ (square.1 : ℝ)) hpoints
        have hsecond := congrArg (fun square ↦ (square.2 : ℝ)) hpoints
        simp [lowerTriangleChart, upperTriangleChart, t, TriangleDisk.edgePoint,
          TriangleDisk.edgeCoordinates] at hfirst hsecond ⊢
        linarith [hpoint.1, hpoint'.2.1]
      · have hfirst := congrArg (fun square ↦ (square.1 : ℝ)) hpoints
        have hsecond := congrArg (fun square ↦ (square.2 : ℝ)) hpoints
        simp [lowerTriangleChart, upperTriangleChart, t, TriangleDisk.edgePoint,
          TriangleDisk.edgeCoordinates] at hfirst hsecond ⊢
        linarith [hpoint.1, hpoint'.2.1]
    · apply Subtype.ext
      ext coordinate
      fin_cases coordinate
      · simp [t, upperTriangleChart, TriangleDisk.edgePoint, TriangleDisk.edgeCoordinates]
      · have hfirst := congrArg (fun square ↦ (square.1 : ℝ)) hpoints
        have hsecond := congrArg (fun square ↦ (square.2 : ℝ)) hpoints
        simp [lowerTriangleChart, upperTriangleChart, t, TriangleDisk.edgePoint,
          TriangleDisk.edgeCoordinates] at hfirst hsecond ⊢
        linarith [hpoint.1, hpoint'.2.1]
  · rintro ⟨t, rfl, rfl⟩
    -- The two named edge formulas agree after the involutive parameter reversal.
    rw [lowerTriangleChart_edge_two, upperTriangleChart_edge_zero,
      unitInterval.symm_symm]

/-- Helper for Exercise 78.1: the two affine triangle charts cover the unit square. -/
lemma lower_upper_triangleChart_surjective :
    Function.Surjective (Sum.elim lowerTriangleChart upperTriangleChart) := by
  intro point
  rcases point with ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  by_cases hyx : y ≤ x
  · let coordinates : EuclideanSpace ℝ (Fin 2) := !₂[x - y, y]
    have coordinates_mem : coordinates ∈ standardTriangle := by
      rw [mem_standardTriangle]
      simp only [coordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      exact ⟨sub_nonneg.mpr hyx, hy0, by linarith⟩
    refine ⟨Sum.inl ⟨coordinates, coordinates_mem⟩, ?_⟩
    -- In the lower half, subtracting the second coordinate gives the inverse chart.
    apply Prod.ext <;> apply Subtype.ext
    · simp [lowerTriangleChart, coordinates]
    · simp [lowerTriangleChart, coordinates]
  · have hxy : x ≤ y := le_of_not_ge hyx
    let coordinates : EuclideanSpace ℝ (Fin 2) := !₂[x, y - x]
    have coordinates_mem : coordinates ∈ standardTriangle := by
      rw [mem_standardTriangle]
      simp only [coordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      exact ⟨hx0, sub_nonneg.mpr hxy, by linarith⟩
    refine ⟨Sum.inr ⟨coordinates, coordinates_mem⟩, ?_⟩
    -- In the upper half, subtracting the first coordinate gives the inverse chart.
    apply Prod.ext <;> apply Subtype.ext
    · simp [upperTriangleChart, coordinates]
    · simp [upperTriangleChart, coordinates]

/-- Helper for Exercise 78.1: the two-chart map from the disjoint union of triangles onto the
unit square is a quotient map. -/
lemma twoTrianglesToSquare_isQuotientMap :
    Topology.IsQuotientMap (Sum.elim lowerTriangleChart upperTriangleChart) := by
  -- A continuous surjection from this compact finite sum to the Hausdorff square is quotient.
  have hclosed : IsClosed standardTriangle := by
    have htriangle : standardTriangle =
        {point | 0 ≤ point 0 ∧ 0 ≤ point 1 ∧ point 0 + point 1 ≤ 1} := by
      ext point
      exact mem_standardTriangle point
    rw [htriangle]
    have hcoord0 : Continuous (fun point : EuclideanSpace ℝ (Fin 2) ↦ point 0) := by
      fun_prop
    have hcoord1 : Continuous (fun point : EuclideanSpace ℝ (Fin 2) ↦ point 1) := by
      fun_prop
    exact (isClosed_le continuous_const hcoord0).inter
      ((isClosed_le continuous_const hcoord1).inter
        (isClosed_le (hcoord0.add hcoord1) continuous_const))
  letI : CompactSpace standardTriangle := isCompact_iff_compactSpace.mp
    (Metric.isCompact_of_isClosed_isBounded hclosed isBounded_standardTriangle)
  refine Topology.IsQuotientMap.of_surjective_continuous lower_upper_triangleChart_surjective ?_
  exact continuous_lowerTriangleChart.sumElim continuous_upperTriangleChart

end FourTrianglePasting
