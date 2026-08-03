module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Algebra.BigOperators.Field

public section

open Set

namespace Remark50_2.SimplexGrid

/-- Helper for Remark 50.2: a denominator-`q` grid vertex is a bounded weak
composition of `q` into `d + 1` coordinates. -/
@[expose] def Vertex (d q : ℕ) :=
  {a : Fin (d + 1) → Fin (q + 1) // ∑ i, (a i : ℕ) = q}

/-- Helper for Remark 50.2: weak-composition grid vertices admit the canonical finite
enumeration inherited from their bounded coordinate functions. -/
noncomputable instance vertexFintype (d q : ℕ) : Fintype (Vertex d q) :=
  @Subtype.fintype (Fin (d + 1) → Fin (q + 1))
    (fun a ↦ ∑ i, (a i : ℕ) = q) (Classical.decPred _) inferInstance

/-- Helper for Remark 50.2: the real barycentric coordinates of a positive-denominator
grid vertex are nonnegative. -/
lemma coordinate_nonneg {d q : ℕ} (a : Vertex d q) (i : Fin (d + 1)) :
    0 ≤ (a.1 i : ℝ) / (q : ℝ) := by
  -- Both the numerator and the positive-denominator-free division operation preserve order.
  positivity

/-- Helper for Remark 50.2: normalizing a positive-denominator grid vertex gives
barycentric coordinates summing to one. -/
lemma coordinate_sum {d q : ℕ} (hq : 0 < q) (a : Vertex d q) :
    ∑ i, (a.1 i : ℝ) / (q : ℝ) = 1 := by
  -- Pull the common denominator outside the finite sum and use the weak-composition equation.
  rw [← Finset.sum_div]
  rw [← Nat.cast_sum, a.2]
  exact div_self (Nat.cast_ne_zero.mpr hq.ne')

/-- Helper for Remark 50.2: normalized grid coordinates lie in the real standard simplex. -/
lemma toPoint_mem {d q : ℕ} (hq : 0 < q) (a : Vertex d q) :
    (fun i ↦ (a.1 i : ℝ) / (q : ℝ)) ∈ stdSimplex ℝ (Fin (d + 1)) := by
  -- The two defining simplex conditions are coordinate nonnegativity and total mass one.
  exact ⟨coordinate_nonneg a, coordinate_sum hq a⟩

/-- Helper for Remark 50.2: realize a positive-denominator grid vertex as a point of the
real standard simplex. -/
noncomputable def toPoint {d q : ℕ} (hq : 0 < q) :
    Vertex d q → stdSimplex ℝ (Fin (d + 1)) :=
  fun a ↦ ⟨fun i ↦ (a.1 i : ℝ) / (q : ℝ), toPoint_mem hq a⟩

/-- Helper for Remark 50.2: the realization has the expected coordinate formula. -/
@[simp] lemma toPoint_apply {d q : ℕ} (hq : 0 < q) (a : Vertex d q)
    (i : Fin (d + 1)) :
    (toPoint hq a : Fin (d + 1) → ℝ) i = (a.1 i : ℝ) / (q : ℝ) := by
  -- This is the defining projection of the realization.
  rfl

/-- Helper for Remark 50.2: normalization by a positive denominator does not identify
distinct weak compositions. -/
lemma toPoint_injective {d q : ℕ} (hq : 0 < q) :
    Function.Injective (toPoint (d := d) hq) := by
  -- Compare each real coordinate, cancel the common denominator, and cast back to naturals.
  intro a b hab
  apply Subtype.ext
  funext i
  apply Fin.ext
  have hcoordinate : (a.1 i : ℝ) / (q : ℝ) = (b.1 i : ℝ) / (q : ℝ) := by
    exact congrFun (congrArg Subtype.val hab) i
  have hq_real : (q : ℝ) ≠ 0 := by
    positivity
  have hcast : (a.1 i : ℝ) = (b.1 i : ℝ) := (div_left_inj' hq_real).mp hcoordinate
  exact_mod_cast hcast

/-- Helper for Remark 50.2: a label belongs to the barycentric support of a realized grid
vertex exactly when its integer coordinate is nonzero. -/
lemma toPoint_support_iff {d q : ℕ} (hq : 0 < q) (a : Vertex d q)
    (i : Fin (d + 1)) :
    i ∈ Function.support ((toPoint hq a : stdSimplex ℝ (Fin (d + 1))) :
      Fin (d + 1) → ℝ) ↔ a.1 i ≠ 0 := by
  -- Unfold support and cancel the nonzero real denominator.
  have hq_real : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  simp [Function.mem_support, toPoint_apply, hq_real]

/-- Helper for Remark 50.2: two grid vertices are coordinate-close when each integer
coordinate changes by at most one in either direction. -/
def CoordinateClose {d q : ℕ} (a b : Vertex d q) : Prop :=
  ∀ i, (a.1 i : ℕ) ≤ (b.1 i : ℕ) + 1 ∧ (b.1 i : ℕ) ≤ (a.1 i : ℕ) + 1

/-- Helper for Remark 50.2: coordinate closeness is symmetric. -/
lemma coordinateClose_comm {d q : ℕ} {a b : Vertex d q} :
    CoordinateClose a b ↔ CoordinateClose b a := by
  -- Swap the two component inequalities at each coordinate.
  constructor
  · intro h i
    exact ⟨(h i).2, (h i).1⟩
  · intro h i
    exact ⟨(h i).2, (h i).1⟩

/-- Helper for Remark 50.2: coordinate-close vertices remain at most `1 / q` apart in
each normalized real coordinate. -/
lemma coordinate_dist_le_one_div {d q : ℕ} (hq : 0 < q) {a b : Vertex d q}
    (hab : CoordinateClose a b) (i : Fin (d + 1)) :
    dist ((toPoint hq a : Fin (d + 1) → ℝ) i)
      ((toPoint hq b : Fin (d + 1) → ℝ) i) ≤ 1 / (q : ℝ) := by
  -- Cast the two integer bounds, turn them into an absolute-value estimate, and divide by `q`.
  have hab_real : (a.1 i : ℝ) ≤ (b.1 i : ℝ) + 1 := by
    exact_mod_cast (hab i).1
  have hba_real : (b.1 i : ℝ) ≤ (a.1 i : ℝ) + 1 := by
    exact_mod_cast (hab i).2
  have hdifference : |(a.1 i : ℝ) - (b.1 i : ℝ)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hq_real : 0 < (q : ℝ) := by
    exact_mod_cast hq
  rw [toPoint_apply, toPoint_apply, Real.dist_eq, div_sub_div_same, abs_div,
    abs_of_pos hq_real]
  exact (div_le_div_iff_of_pos_right hq_real).2 hdifference

/-- Helper for Remark 50.2: coordinate-close grid vertices are at sup distance at most
`1 / q` after realization. -/
lemma dist_toPoint_le_one_div {d q : ℕ} (hq : 0 < q) {a b : Vertex d q}
    (hab : CoordinateClose a b) :
    dist (toPoint hq a) (toPoint hq b) ≤ 1 / (q : ℝ) := by
  -- The product metric is controlled by the coordinatewise estimate.
  have hbound : 0 ≤ 1 / (q : ℝ) := by
    positivity
  exact (dist_pi_le_iff hbound).2 (coordinate_dist_le_one_div hq hab)

/-- Helper for Remark 50.2: a candidate top grid cell has `d + 1` vertices and all of
its vertices are coordinate-close. -/
def IsCell {d q : ℕ} (cell : Finset (Vertex d q)) : Prop :=
  cell.card = d + 1 ∧
    ∀ a ∈ cell, ∀ b ∈ cell, CoordinateClose a b

/-- Helper for Remark 50.2: all weak-composition vertices form a finite grid. -/
noncomputable def vertices (d q : ℕ) : Finset (Vertex d q) :=
  Finset.univ

/-- Helper for Remark 50.2: membership in the finite vertex enumeration is automatic. -/
@[simp] lemma mem_vertices {d q : ℕ} (a : Vertex d q) : a ∈ vertices d q := by
  -- The enumeration is the universal finset of the finite weak-composition type.
  exact Finset.mem_univ a

/-- Helper for Remark 50.2: enumerate all cardinality-correct coordinate-close candidate
cells before the incidence argument selects the cumulative-coordinate triangulation. -/
noncomputable def candidateCells (d q : ℕ) : Finset (Finset (Vertex d q)) :=
  @Finset.filter _ IsCell (Classical.decPred IsCell) Finset.univ

/-- Helper for Remark 50.2: the candidate-cell enumeration has exactly the intended
cardinality and coordinate-closeness specification. -/
@[simp] lemma mem_candidateCells {d q : ℕ} (cell : Finset (Vertex d q)) :
    cell ∈ candidateCells d q ↔ IsCell cell := by
  -- Filtering the universal finite family leaves precisely the cells satisfying `IsCell`.
  simp only [candidateCells, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Helper for Remark 50.2: every candidate grid cell has mesh at most `1 / q`. -/
lemma cellDiameter_le_one_div {d q : ℕ} (hq : 0 < q) {cell : Finset (Vertex d q)}
    (hcell : IsCell cell) {a b : Vertex d q} (ha : a ∈ cell) (hb : b ∈ cell) :
    dist (toPoint hq a) (toPoint hq b) ≤ 1 / (q : ℝ) := by
  -- Extract coordinate closeness from the cell predicate and apply the global metric bridge.
  exact dist_toPoint_le_one_div hq (hcell.2 a ha b hb)

end Remark50_2.SimplexGrid
