module

public import Mathlib.Topology.Constructions.SumProd
public import Topology_Munkres_2000.Book.Exercise_17_20.RealPlane

public section

namespace HalfPlaneAxisProjection

open Set

/-- The half-plane together with the horizontal axis in `ℝ × ℝ`. -/
def domain : Set (ℝ × ℝ) := {p | 0 ≤ p.1} ∪ {p | p.2 = 0}

/-- The restriction of the first-coordinate projection to `domain`. -/
def map : domain → ℝ := fun p ↦ p.1.1

/-- Helper for Exercise 22.3: every point on the horizontal axis belongs to `domain`. -/
lemma axisPoint_mem_domain (x : ℝ) : (x, 0) ∈ domain := by
  -- The horizontal-axis component of the union contains the point directly.
  right
  rfl

/-- Helper for Exercise 22.3: the horizontal axis gives a section of `map`. -/
def axisSection (x : ℝ) : domain :=
  ⟨(x, 0), axisPoint_mem_domain x⟩

/-- Helper for Exercise 22.3: the horizontal-axis section is continuous. -/
lemma continuous_axisSection : Continuous axisSection := by
  -- Continuity is inherited from the continuous product map into the subtype.
  exact (continuous_id.prodMk continuous_const).subtype_mk _

/-- Helper for Exercise 22.3: a point with nonnegative first coordinate belongs to `domain`. -/
lemma rightHalfPlanePoint_mem_domain {x y : ℝ} (hx : 0 ≤ x) : (x, y) ∈ domain := by
  -- The right-half-plane component of the union contains the point.
  left
  exact hx

/-- Helper for Exercise 22.3: a canonical point in the open upper slice over `x`. -/
def upperSlicePoint (x : ℝ) (hx : 0 ≤ x) : domain :=
  ⟨(x, 1), rightHalfPlanePoint_mem_domain hx⟩

/-- Helper for Exercise 22.3: a canonical point on the positive unit hyperbola over `x`. -/
noncomputable def positiveHyperbolaPoint (x : ℝ) (hx : 0 < x) : domain :=
  ⟨(x, x⁻¹), rightHalfPlanePoint_mem_domain hx.le⟩

/-- Helper for Exercise 22.3: the upper slice of `domain` maps exactly onto `Ici 0`. -/
lemma image_upperSlice : map '' {p : domain | 0 < p.1.2} = Ici 0 := by
  -- Compare membership on both sides and expose an explicit subtype witness.
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    simp only [mem_setOf_eq] at hp
    rcases p.property with hpRight | hpAxis
    · exact hpRight
    · simp only [mem_setOf_eq] at hpAxis
      linarith
  · intro hx
    refine ⟨upperSlicePoint x hx, ?_, ?_⟩
    · norm_num [upperSlicePoint]
    · rfl

/-- Helper for Exercise 22.3: the unit-hyperbola slice maps exactly onto `Ioi 0`. -/
lemma image_unitHyperbola : map '' {p : domain | p.1.1 * p.1.2 = 1} = Ioi 0 := by
  -- The domain removes the negative branch, leaving precisely positive first coordinates.
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    simp only [mem_setOf_eq] at hp
    rcases p.property with hpRight | hpAxis
    · simp only [mem_setOf_eq] at hpRight
      have hpFirst_ne : p.1.1 ≠ 0 := by
        intro hpFirst
        rw [hpFirst, zero_mul] at hp
        norm_num at hp
      exact lt_of_le_of_ne hpRight (Ne.symm hpFirst_ne)
    · simp only [mem_setOf_eq] at hpAxis
      rw [hpAxis, mul_zero] at hp
      norm_num at hp
  · intro hx
    refine ⟨positiveHyperbolaPoint x hx, ?_, ?_⟩
    · simp only [positiveHyperbolaPoint, Set.mem_setOf_eq]
      exact mul_inv_cancel₀ hx.ne'
    · rfl

/-- The restricted first-coordinate projection is a quotient map. -/
theorem isQuotientMap : Topology.IsQuotientMap map := by
  -- The continuous horizontal-axis section is a left inverse to the projection.
  apply Topology.IsQuotientMap.of_inverse continuous_axisSection continuous_subtype_val.fst
  intro x
  rfl

/-- The restricted first-coordinate projection is not an open map. -/
theorem not_isOpenMap : ¬ IsOpenMap map := by
  -- The open upper slice has the non-open image `Ici 0`.
  intro hopen
  have hUpperOpen : IsOpen {p : domain | 0 < p.1.2} := by
    exact isOpen_lt continuous_const continuous_subtype_val.snd
  have hIciOpen : IsOpen (Ici (0 : ℝ)) := by
    rw [← image_upperSlice]
    exact hopen _ hUpperOpen
  have hIioClosed : IsClosed (Iio (0 : ℝ)) := by
    simpa only [compl_Ici] using hIciOpen.isClosed_compl
  have hClosure : closure (Iio (0 : ℝ)) = Iio 0 := hIioClosed.closure_eq
  rw [closure_Iio] at hClosure
  have hZero : (0 : ℝ) ∈ Iio 0 := hClosure ▸ self_mem_Iic
  have hImpossible : (0 : ℝ) < 0 := by
    simpa only [mem_Iio] using hZero
  exact (lt_irrefl 0) hImpossible

/-- The restricted first-coordinate projection is not a closed map. -/
theorem not_isClosedMap : ¬ IsClosedMap map := by
  -- The closed unit-hyperbola slice has the non-closed image `Ioi 0`.
  intro hclosed
  have hHyperbolaClosed : IsClosed {p : domain | p.1.1 * p.1.2 = 1} := by
    exact isClosed_eq (continuous_subtype_val.fst.mul continuous_subtype_val.snd) continuous_const
  have hIoiClosed : IsClosed (Ioi (0 : ℝ)) := by
    rw [← image_unitHyperbola]
    exact hclosed _ hHyperbolaClosed
  have hClosure : closure (Ioi (0 : ℝ)) = Ioi 0 := hIoiClosed.closure_eq
  rw [closure_Ioi] at hClosure
  have hZero : (0 : ℝ) ∈ Ioi 0 := hClosure ▸ self_mem_Ici
  have hImpossible : (0 : ℝ) < 0 := by
    simpa only [mem_Ioi] using hZero
  exact (lt_irrefl 0) hImpossible

/-- Exercise 22.3: The restricted first-coordinate projection is a quotient map that is neither
open nor closed. -/
theorem quotient_not_open_not_closed :
    Topology.IsQuotientMap map ∧ ¬ IsOpenMap map ∧ ¬ IsClosedMap map :=
  ⟨isQuotientMap, not_isOpenMap, not_isClosedMap⟩

end HalfPlaneAxisProjection

end
