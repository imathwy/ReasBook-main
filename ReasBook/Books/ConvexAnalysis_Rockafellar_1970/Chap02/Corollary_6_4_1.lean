import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_4
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_7
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_12

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace Set

/-- If `z` is an interior point of `C`, then every direction `y` admits a nonzero scalar step
from `z` that remains in `C`. This primitive bridge only uses the scalar norm, not an order on the
scalar field. -/
theorem forall_exists_ne_zero_add_smul_mem_of_mem_interior
    {C : Set E} {z : E} (hz : z ∈ interior C) :
    ∀ y : E, ∃ ε : 𝕜, ε ≠ 0 ∧ z + ε • y ∈ C := by
  intro y
  by_cases hy : y = 0
  · refine ⟨1, one_ne_zero, ?_⟩
    simpa [hy] using interior_subset hz
  · rcases (Metric.mem_interior_iff_exists_pos_closedBall_subset).1 hz with ⟨δ, hδ, hball⟩
    let r : ℝ := δ / (2 * ‖y‖)
    have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hr : 0 < r := by
      dsimp [r]
      positivity
    obtain ⟨c, hc0, hcr⟩ := NormedField.exists_norm_lt 𝕜 (lt_min zero_lt_one hr)
    let ε : 𝕜 := c ^ 2
    have hε : 0 < ‖ε‖ := by
      dsimp [ε]
      exact norm_pos_iff.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mp hc0.ne'))
    have hεnorm : ‖ε‖ < r := by
      have hcr' : ‖c‖ < r := lt_of_lt_of_le hcr (min_le_right _ _)
      calc
        ‖ε‖ = ‖c‖ * ‖c‖ := by
          dsimp [ε]
          rw [pow_two, norm_mul]
        _ < ‖c‖ := by
          nlinarith [lt_of_lt_of_le hcr (min_le_left _ _)]
        _ < r := hcr'
    refine ⟨ε, norm_ne_zero_iff.mp hε.ne', ?_⟩
    apply hball
    rw [Metric.mem_closedBall, dist_eq_norm]
    rw [show z + ε • y - z = ε • y by abel_nf, norm_smul]
    have hbound : ‖ε‖ * ‖y‖ < δ / 2 := by
      have hεnorm' : ‖ε‖ < δ / (2 * ‖y‖) := by
        simpa [r] using hεnorm
      have htmp : ‖ε‖ * (2 * ‖y‖) < δ := by
        have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * ‖y‖)).mp hεnorm'
        simpa [mul_assoc, mul_left_comm, mul_comm] using this
      nlinarith
    linarith

end Set

end

section

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-
Source/core/bridge triage:
- `source-facing`: Corollary 6.4.1 characterizes ordinary interior points of a convex subset of
  a finite-dimensional ordered normed-field space by the existence of a positive
  step in every direction from the point.
- `core/canonical`: the owner notions are `Convex 𝕜`, `interior`, and the chapter owner theorem
  `Convex.mem_intrinsicInterior_iff_forall_exists_gt_one_lineMap_mem` for relative interior,
  together with the full-dimensional bridge
  `intrinsicInterior_eq_interior_of_affineSpan_eq_top`.
- `bridge/view`: this item upgrades the relative-interior segment-prolongation criterion to the
  ordinary interior criterion by using the full-dimensionality forced by directional extension in
  every ambient direction.
- Domain-style sampling used here: `Metric.mem_interior_iff_exists_pos_closedBall_subset`,
  `Convex.mem_intrinsicInterior_iff_forall_exists_gt_one_lineMap_mem`,
  `intrinsicInterior_eq_interior_of_affineSpan_eq_top`, and the algebraic bridge
  `Set.affineSpan_eq_top_of_forall_exists_ne_zero_lineMap_mem`.
- Primitive data vs derived API: the full-dimensionality bridge is stated from the primitive
  nonzero-step data, while the source-facing positive-step criterion is derived API over ordered
  scalars; the public criterion therefore belongs under the `Convex` owner abstraction rather than
  as a parallel global theorem.
- Layer target: this item stays `source-facing`, refined to owner-style `Convex` API.
-/

namespace Set

/-- If `z` is an interior point of `C`, then every direction `y` admits a positive scalar step
from `z` that remains in `C`. -/
theorem forall_exists_pos_add_smul_mem_of_mem_interior
    {C : Set E} {z : E} (hz : z ∈ interior C) :
    ∀ y : E, ∃ ε > (0 : 𝕜), z + ε • y ∈ C := by
  intro y
  by_cases hy : y = 0
  · refine ⟨1, by positivity, ?_⟩
    simpa [hy] using interior_subset hz
  · rcases (Metric.mem_interior_iff_exists_pos_closedBall_subset).1 hz with ⟨δ, hδ, hball⟩
    let r : ℝ := δ / (2 * ‖y‖)
    have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hr : 0 < r := by
      dsimp [r]
      positivity
    obtain ⟨c, hc0, hcr⟩ := NormedField.exists_norm_lt 𝕜 (lt_min zero_lt_one hr)
    let ε : 𝕜 := c ^ 2
    have hε : 0 < ε := by
      dsimp [ε]
      exact sq_pos_iff.mpr (norm_ne_zero_iff.mp hc0.ne')
    have hεnorm : ‖ε‖ < r := by
      have hcr' : ‖c‖ < r := lt_of_lt_of_le hcr (min_le_right _ _)
      calc
        ‖ε‖ = ‖c‖ * ‖c‖ := by
          dsimp [ε]
          rw [pow_two, norm_mul]
        _ < ‖c‖ := by
          nlinarith [lt_of_lt_of_le hcr (min_le_left _ _)]
        _ < r := hcr'
    refine ⟨ε, hε, ?_⟩
    apply hball
    rw [Metric.mem_closedBall, dist_eq_norm]
    rw [show z + ε • y - z = ε • y by abel_nf, norm_smul]
    have hbound : ‖ε‖ * ‖y‖ < δ / 2 := by
      have hεnorm' : ‖ε‖ < δ / (2 * ‖y‖) := by
        simpa [r] using hεnorm
      have htmp : ‖ε‖ * (2 * ‖y‖) < δ := by
        have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * ‖y‖)).mp hεnorm'
        simpa [mul_assoc, mul_left_comm, mul_comm] using this
      nlinarith
    linarith

end Set

end

section

variable {𝕜 V P : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [AddTorsor V P]

namespace Set

open AffineMap

/-- If every ambient direction from `z` admits a nonzero scalar step that stays in `C`, then
`C` is full-dimensional in the ambient affine space. -/
theorem affineSpan_eq_top_of_forall_exists_ne_zero_lineMap_mem
    (C : Set P) (z : P) (hz : ∀ x : P, ∃ μ : 𝕜, μ ≠ 0 ∧ lineMap z x μ ∈ C) :
    affineSpan 𝕜 C = ⊤ := by
  have hzC : z ∈ C := by
    rcases hz z with ⟨μ, hμ, hmem⟩
    simpa using hmem
  apply top_unique
  intro x _
  rcases hz x with ⟨μ, hμ, hp⟩
  have hzA : z ∈ affineSpan 𝕜 C := subset_affineSpan 𝕜 C hzC
  have hpA : lineMap z x μ ∈ affineSpan 𝕜 C := subset_affineSpan 𝕜 C hp
  have hxA : lineMap z (lineMap z x μ) μ⁻¹ ∈ affineSpan 𝕜 C :=
    AffineMap.lineMap_mem μ⁻¹ hzA hpA
  simpa [lineMap_lineMap_right, inv_mul_cancel₀ hμ] using hxA

end Set

end

section

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

namespace Convex

open AffineMap

/-- If every direction from `z` can be prolonged by a positive scalar while staying in a convex
set `C`, then `z` lies in `interior C`. -/
private theorem mem_interior_of_forall_exists_pos_add_smul_mem
    {C : Set E} {z : E} (hC : Convex 𝕜 C)
    (hz : ∀ y : E, ∃ ε > (0 : 𝕜), z + ε • y ∈ C) :
    z ∈ interior C := by
  have hzC : z ∈ C := by
    rcases hz 0 with ⟨ε, hε, hmem⟩
    simpa using hmem
  have hseg : ∀ x ∈ C, ∃ μ > (1 : 𝕜), lineMap x z μ ∈ C := by
    intro x hx
    rcases hz (z - x) with ⟨ε, hε, hmem⟩
    refine ⟨ε + 1, by linarith, ?_⟩
    rw [lineMap_apply_module']
    have hline : (ε + 1) • (z - x) + x = z + ε • (z - x) := by
      rw [sub_eq_add_neg, add_smul, one_smul]
      abel_nf
    simpa [hline] using hmem
  have hzri : z ∈ intrinsicInterior 𝕜 C :=
    (hC.mem_intrinsicInterior_iff_forall_exists_gt_one_lineMap_mem).2 ⟨⟨z, hzC⟩, hseg⟩
  have hspan : affineSpan 𝕜 C = ⊤ := by
    refine Set.affineSpan_eq_top_of_forall_exists_ne_zero_lineMap_mem C z ?_
    intro x
    rcases hz (x - z) with ⟨ε, hε, hmem⟩
    refine ⟨ε, hε.ne', ?_⟩
    simpa [lineMap_apply_module', add_comm, add_left_comm, add_assoc] using hmem
  simpa [intrinsicInterior_eq_interior_of_affineSpan_eq_top hspan] using hzri

/-- Corollary 6.4.1: a point `z` of a convex set `C` lies in `interior C` if and only if, for
every direction `y`, some positive field-valued step `z + ε • y` still lies in `C`. -/
theorem mem_interior_iff_forall_exists_pos_add_smul_mem
    {C : Set E} {z : E} (hC : Convex 𝕜 C) :
    z ∈ interior C ↔ ∀ y : E, ∃ ε > (0 : 𝕜), z + ε • y ∈ C := by
  constructor
  · exact Set.forall_exists_pos_add_smul_mem_of_mem_interior
  · exact hC.mem_interior_of_forall_exists_pos_add_smul_mem

end Convex

end
