import Mathlib
import BauschkeLean.Chap01.Text_1_0_10
import BauschkeLean.Chap20.Definition_20_1
import BauschkeLean.Chap25.Definition_25_29

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u}

section AddCommGroup

variable [AddCommGroup H]

-- Semantic recall note: this item uses the Chapter 25 owner `A □ B`, the Chapter 1 APIs `dom`
-- and `range`, and the Chapter 20 API `IsMonotone`.

/-- Proposition 25.30 (1): the value of the parallel sum is the union of the intersections
`A y ∩ B (x - y)` over all decompositions `x = y + (x - y)`. -/
theorem parallelSum_apply_eq_iUnion_inter
    (A B : SetValuedOperator H H) (x : H) :
    (A □ B) x = ⋃ y : H, A y ∩ B (x - y) := by
  ext u
  rw [mem_parallelSum_iff]
  change x ∈ A⁻¹ u + B⁻¹ u ↔ u ∈ ⋃ y : H, A y ∩ B (x - y)
  constructor
  · intro hu
    rcases Set.mem_add.1 hu with ⟨y, hy, z, hz, hEq⟩
    refine Set.mem_iUnion.2 ⟨y, ?_⟩
    have hz' : x - y = z := by
      rw [sub_eq_iff_eq_add']
      exact hEq.symm
    rw [Set.mem_inter_iff, hz']
    exact ⟨
      (SetValuedOperator.mem_inverse_iff A u y).1 hy,
      (SetValuedOperator.mem_inverse_iff B u z).1 hz⟩
  · intro hu
    rcases Set.mem_iUnion.1 hu with ⟨y, hy⟩
    rw [Set.mem_inter_iff] at hy
    exact Set.mem_add.2 ⟨
      y,
      (SetValuedOperator.mem_inverse_iff A u y).2 hy.1,
      x - y,
      (SetValuedOperator.mem_inverse_iff B u (x - y)).2 hy.2,
      by abel_nf⟩

/-- Proposition 25.30 (2): membership in the parallel sum at `x` is equivalent to the existence
of `y` such that `y ∈ A⁻¹ u` and `x - y ∈ B⁻¹ u`. -/
theorem mem_parallelSum_iff_exists_mem_inverse
    (A B : SetValuedOperator H H) (x u : H) :
    u ∈ (A □ B) x ↔ ∃ y : H, y ∈ A⁻¹ u ∧ x - y ∈ B⁻¹ u := by
  rw [mem_parallelSum_iff]
  change x ∈ A⁻¹ u + B⁻¹ u ↔ ∃ y : H, y ∈ A⁻¹ u ∧ x - y ∈ B⁻¹ u
  constructor
  · rintro ⟨y, hy, z, hz, hEq⟩
    refine ⟨y, hy, ?_⟩
    have hz' : x - y = z := by
      rw [sub_eq_iff_eq_add']
      exact hEq.symm
    simpa [hz'] using hz
  · rintro ⟨y, hy, hz⟩
    exact ⟨y, hy, x - y, hz, by abel_nf⟩

/-- Proposition 25.30 (3): the domain of the parallel sum is the range of the sum of the inverse
operators. -/
theorem dom_parallelSum_eq_range_inverse_add_inverse
    (A B : SetValuedOperator H H) :
    dom (A □ B) = range (A⁻¹ + B⁻¹) := by
  ext x
  constructor
  · intro hx
    rcases (SetValuedOperator.mem_dom_iff _ x).1 hx with ⟨u, hu⟩
    rcases (mem_parallelSum_iff_exists_mem_inverse A B x u).1 hu with ⟨y, hy, hz⟩
    exact (SetValuedOperator.mem_range_iff _ x).2 ⟨u, Set.mem_add.2 ⟨y, hy, x - y, hz, by
      abel_nf⟩⟩
  · intro hx
    rcases (SetValuedOperator.mem_range_iff _ x).1 hx with ⟨u, hu⟩
    rcases Set.mem_add.1 hu with ⟨y, hy, z, hz, rfl⟩
    exact (SetValuedOperator.mem_dom_iff _ (y + z)).2 ⟨u,
      (mem_parallelSum_iff_exists_mem_inverse A B (y + z) u).2 ⟨y, hy, by simpa⟩⟩

/-- Proposition 25.30 (4): the range of the parallel sum is the intersection of the ranges of
`A` and `B`. -/
theorem range_parallelSum_eq_range_inter
    (A B : SetValuedOperator H H) :
    range (A □ B) = range A ∩ range B := by
  ext u
  constructor
  · intro hu
    rcases (SetValuedOperator.mem_range_iff _ u).1 hu with ⟨x, hx⟩
    rcases (mem_parallelSum_iff_exists_mem_inverse A B x u).1 hx with ⟨y, hy, hz⟩
    rw [Set.mem_inter_iff]
    exact ⟨
      (SetValuedOperator.mem_range_iff _ u).2 ⟨y,
        (SetValuedOperator.mem_inverse_iff A u y).1 hy⟩,
      (SetValuedOperator.mem_range_iff _ u).2 ⟨x - y,
        (SetValuedOperator.mem_inverse_iff B u (x - y)).1 hz⟩⟩
  · intro hu
    rw [Set.mem_inter_iff] at hu
    rcases hu with ⟨huA, huB⟩
    rcases (SetValuedOperator.mem_range_iff _ u).1 huA with ⟨y, hy⟩
    rcases (SetValuedOperator.mem_range_iff _ u).1 huB with ⟨z, hz⟩
    exact (SetValuedOperator.mem_range_iff _ u).2 ⟨y + z,
      (mem_parallelSum_iff_exists_mem_inverse A B (y + z) u).2 ⟨
        y,
        (SetValuedOperator.mem_inverse_iff A u y).2 hy,
        by simpa [SetValuedOperator.mem_inverse_iff] using hz⟩⟩

end AddCommGroup

section InnerProductSpace

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Proposition 25.30 (5): the parallel sum of two monotone operators is monotone. -/
theorem IsMonotone.parallelSum
    {A B : SetValuedOperator H H} (hA : A.IsMonotone) (hB : B.IsMonotone) :
    (A □ B).IsMonotone := by
  rw [SetValuedOperator.isMonotone_iff]
  have hA_pt := (SetValuedOperator.isMonotone_iff A).1 hA
  have hB_pt := (SetValuedOperator.isMonotone_iff B).1 hB
  have hA_inv :
      ∀ {x u y v : H}, u ∈ ((A⁻¹) x) → v ∈ ((A⁻¹) y) →
        0 ≤ inner ℝ (x - y) (u - v) := by
    intro x u y v hx hy
    rw [SetValuedOperator.mem_inverse_iff] at hx hy
    simpa [real_inner_comm] using hA_pt hx hy
  have hB_inv :
      ∀ {x u y v : H}, u ∈ ((B⁻¹) x) → v ∈ ((B⁻¹) y) →
        0 ≤ inner ℝ (x - y) (u - v) := by
    intro x u y v hx hy
    rw [SetValuedOperator.mem_inverse_iff] at hx hy
    simpa [real_inner_comm] using hB_pt hx hy
  have hsum :
      ∀ {x u y v : H}, u ∈ ((A⁻¹ + B⁻¹) x) → v ∈ ((A⁻¹ + B⁻¹) y) →
        0 ≤ inner ℝ (x - y) (u - v) := by
    intro x u y v hu hv
    rcases Set.mem_add.1 hu with ⟨ux, hux, bx, hbx, rfl⟩
    rcases Set.mem_add.1 hv with ⟨uy, huy, vy, hvy, rfl⟩
    have hpair := add_nonneg (hA_inv hux huy) (hB_inv hbx hvy)
    have hdecomp : (ux + bx) - (uy + vy) = (ux - uy) + (bx - vy) := by
      abel_nf
    simpa [hdecomp, inner_add_right] using hpair
  intro x u y v hx hy
  have hx' : x ∈ (A⁻¹ + B⁻¹) u := (mem_parallelSum_iff A B x u).1 hx
  have hy' : y ∈ (A⁻¹ + B⁻¹) v := (mem_parallelSum_iff A B y v).1 hy
  have hxy : 0 ≤ inner ℝ (u - v) (x - y) := hsum hx' hy'
  simpa [real_inner_comm] using hxy

end InnerProductSpace

end SetValuedOperator
