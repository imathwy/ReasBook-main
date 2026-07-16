import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_6

-- Declarations for this item will be appended below by the statement pipeline.

open Metric
open scoped Pointwise Rockafellar

/-- Membership in the interior of a subset of a pseudo-metric space is equivalent to containing a
positive-radius closed ball around the point. -/
theorem Metric.mem_interior_iff_exists_pos_closedBall_subset
    {P : Type*} [PseudoMetricSpace P] {C : Set P} {x : P} :
    x ∈ interior C ↔ ∃ ε : ℝ, 0 < ε ∧ closedBall x ε ⊆ C := by
  rw [mem_interior_iff_mem_nhds, Metric.nhds_basis_closedBall.mem_iff]

-- Proof sketch: start from the canonical owner theorem
-- `Metric.closure_eq_iInter_thickening`, rewrite each thickening as the existential witness set
-- `{x | ∃ y ∈ C, dist x y < ε}` via `Metric.mem_thickening_iff`, and then pass from `< ε` to
-- `≤ ε` inside the intersection using the standard halving argument.
theorem Metric.closure_eq_iInter_points_within_distance_le
    {P : Type*} [PseudoMetricSpace P] (C : Set P) :
    closure C = ⋂ (ε : ℝ) (_ : 0 < ε), {x : P | ∃ y ∈ C, dist x y ≤ ε} := by
  rw [Set.ext_iff]
  intro x
  rw [Metric.closure_eq_iInter_thickening]
  simp only [Set.mem_iInter, Metric.mem_thickening_iff]
  constructor
  · intro hx ε hε
    rcases hx ε hε with ⟨y, hyC, hxy⟩
    exact ⟨y, hyC, hxy.le⟩
  · intro hx ε hε
    rcases hx (ε / 2) (half_pos hε) with ⟨y, hyC, hxy⟩
    exact ⟨y, hyC, hxy.trans_lt (half_lt_self hε)⟩

section

variable {E : Type*} [PseudoMetricSpace E] [AddGroup E] [IsIsometricVAdd E E]

/-- Intrinsic Text 6.7 (1): the closure of a subset is the intersection of all translates
`C + closedBall 0 ε` with `ε > 0`. -/
theorem closure_eq_iInter_add_closedBall_zero (C : Set E) :
    closure C = ⋂ (ε : ℝ) (_ : 0 < ε), C + closedBall (0 : E) ε := by
  rw [Metric.closure_eq_iInter_points_within_distance_le]
  ext x
  simp only [Set.mem_iInter]
  constructor <;> intro hx ε hε <;>
    simpa [← points_within_distance_le_eq_add_closedBall_zero (C := C) (ε := ε)] using
      hx ε hε

/-- Intrinsic Text 6.7 (2): a point lies in the interior of `C` iff some positive-radius translate
`{x} + closedBall 0 ε` is contained in `C`. -/
theorem mem_interior_iff_exists_pos_add_closedBall_zero_subset {C : Set E} {x : E} :
    x ∈ interior C ↔ ∃ ε : ℝ, 0 < ε ∧ {x} + closedBall (0 : E) ε ⊆ C := by
  rw [Metric.mem_interior_iff_exists_pos_closedBall_subset]
  constructor <;> rintro ⟨ε, hε, hεC⟩ <;> refine ⟨ε, hε, ?_⟩
  · have hEq : {x} + closedBall (0 : E) ε = closedBall x ε := by
      simpa [← vadd_eq_add, Set.singleton_vadd] using
        (closedBall_eq_vadd_closedBall_zero (a := x) (ε := ε)).symm
    exact hEq.symm ▸ hεC
  · have hEq : {x} + closedBall (0 : E) ε = closedBall x ε := by
      simpa [← vadd_eq_add, Set.singleton_vadd] using
        (closedBall_eq_vadd_closedBall_zero (a := x) (ε := ε)).symm
    exact hEq ▸ hεC

/-- Intrinsic Text 6.7 (2): interior as the set of points admitting a positive-radius translate
`{x} + closedBall 0 ε` inside `C`. -/
theorem interior_eq_setOf_exists_add_closedBall_zero_subset (C : Set E) :
    interior C = {x : E | ∃ ε : ℝ, 0 < ε ∧ {x} + closedBall (0 : E) ε ⊆ C} := by
  ext x
  simpa using
    (mem_interior_iff_exists_pos_add_closedBall_zero_subset (C := C) (x := x))

end

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [Module 𝕜 E] [NormSMulClass 𝕜 E]

/-
Source/core/bridge triage:
- `source-facing`: Text 6.7 gives formulas for the closure and interior of a subset, written
  through the closed unit ball `B`.
- `core/canonical`: this file first records the intrinsic owner layer using translates
  `C + closedBall 0 ε` and `{x} + closedBall 0 ε`.
- `bridge/view`: this section rewrites those intrinsic owners into the scalar-generic textbook view
  `C + c • B` and `{x} + c • B`, with primitive nonzero scalar witnesses `c ≠ 0`.
- Primitive data vs derived API: this item introduces no new data, only source-facing
  reformulations of the existing topological operators.
- Domain-style sampling used here: `points_within_distance_le_eq_iUnion_closedBall`,
  `closedBall_eq_add_smul_unitClosedBall_of_ne_zero`, `mem_closure_iff`,
  `nhds_basis_closedBall.mem_iff`, and mathlib's `Metric.closure_eq_iInter_cthickening`, sampled
  as the canonical closure owner but not adopted because the source-facing formula keeps the
  explicit Minkowski-sum neighborhoods.
- Layer target: both declarations are `source-facing` bridge theorems on the owner operators
  `closure` and `interior`.
- Ambient-space refinement: the formulas only use seminormed additive structure together with the
  scalar action assumptions needed for `c • B`, so the public API is stated at that owner level
  rather than concrete finite-coordinate Euclidean models.
-/

/-- Text 6.7 (1): the closure of a subset is the intersection of all sets
`C + c • B` with primitive nonzero radius witness `c ≠ 0`,
where `B` is the closed unit ball centered at the origin. -/
theorem closure_eq_iInter_add_smul_B (C : Set E) :
    closure C = ⋂ (c : 𝕜) (_ : c ≠ 0), C + c • B := by
  rw [closure_eq_iInter_add_closedBall_zero (C := C)]
  ext x
  simp only [Set.mem_iInter]
  constructor
  · intro hx c hc
    have h0 : closedBall (0 : E) ‖c‖ = c • B := by
      simpa using
        (closedBall_eq_add_smul_unitClosedBall_of_ne_zero
          (a := (0 : E)) (c := c) hc)
    have hcNorm : 0 < ‖c‖ := norm_pos_iff.mpr hc
    simpa [h0] using hx ‖c‖ hcNorm
  · intro hx ε hε
    obtain ⟨c, hc, hcε⟩ := NormedField.exists_norm_lt 𝕜 hε
    have hc0 : c ≠ 0 := norm_pos_iff.mp hc
    have h0 : closedBall (0 : E) ‖c‖ = c • B := by
      simpa using
        (closedBall_eq_add_smul_unitClosedBall_of_ne_zero (a := (0 : E)) (c := c) hc0)
    have hx' : x ∈ C + c • B := by
      exact hx c hc0
    have hx'' : x ∈ C + closedBall (0 : E) ‖c‖ := by
      simpa [h0] using hx'
    have hsubset_ball : closedBall (0 : E) ‖c‖ ⊆ closedBall (0 : E) ε := by
      intro y hy
      exact Metric.mem_closedBall.2 ((Metric.mem_closedBall.1 hy).trans hcε.le)
    exact (Set.add_subset_add subset_rfl hsubset_ball) hx''

/-- Text 6.7 (2): the interior of a subset consists of the points `x` for which some translate
`x + c • B` with primitive nonzero witness `c ≠ 0` is contained in `C`, where `B` is the closed unit
ball. -/
theorem mem_interior_iff_exists_add_smul_B_subset {C : Set E} {x : E} :
    x ∈ interior C ↔ ∃ c : 𝕜, c ≠ 0 ∧ {x} + c • B ⊆ C := by
  rw [mem_interior_iff_exists_pos_add_closedBall_zero_subset]
  constructor
  · rintro ⟨ε, hε, hεC⟩
    obtain ⟨c, hc, hcε⟩ := NormedField.exists_norm_lt 𝕜 hε
    have hc0 : c ≠ 0 := norm_pos_iff.mp hc
    have h0 : closedBall (0 : E) ‖c‖ = c • B := by
      simpa using
        (closedBall_eq_add_smul_unitClosedBall_of_ne_zero (a := (0 : E)) (c := c) hc0)
    have hsubset_ball : c • (B : Set E) ⊆ closedBall (0 : E) ε := by
      intro y hy
      have hy' : y ∈ closedBall (0 : E) ‖c‖ := by simpa [h0] using hy
      exact Metric.mem_closedBall.2 ((Metric.mem_closedBall.1 hy').trans hcε.le)
    have hsubset : {x} + c • B ⊆ C :=
      (Set.add_subset_add subset_rfl hsubset_ball).trans hεC
    exact ⟨c, hc0, hsubset⟩
  · rintro ⟨c, hc0, hcC⟩
    refine ⟨‖c‖, norm_pos_iff.mpr hc0, ?_⟩
    have h0 : closedBall (0 : E) ‖c‖ = c • B := by
      simpa using
        (closedBall_eq_add_smul_unitClosedBall_of_ne_zero
          (a := (0 : E)) (c := c) hc0)
    have hεx : ({x} : Set E) + closedBall (0 : E) ‖c‖ = {x} + c • B :=
      congrArg (fun s : Set E => ({x} : Set E) + s) h0
    exact hεx ▸ hcC

/-- Text 6.7 (2): the interior of a subset consists of the points `x` for which some translate
`x + c • B` with primitive nonzero witness `c ≠ 0` is contained in `C`, where `B` is the closed unit
ball. -/
theorem interior_eq_setOf_exists_add_smul_B_subset (C : Set E) :
    interior C = {x : E | ∃ c : 𝕜, c ≠ 0 ∧ {x} + c • B ⊆ C} := by
  ext x
  simpa using
    (mem_interior_iff_exists_add_smul_B_subset (C := C) (x := x))

end
