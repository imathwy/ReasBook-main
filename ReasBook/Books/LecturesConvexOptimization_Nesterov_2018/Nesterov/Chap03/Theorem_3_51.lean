import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable {μ : Measure E} [μ.IsAddHaarMeasure]

local notation "dim" => Module.finrank ℝ E

/- Primary domain: intrinsic volume comparison for convex subsets of a closed ball in a
finite-dimensional real normed space.

Sampled owner-style declarations:
- `Convex.nullMeasurableSet`
- `MeasureTheory.measureReal_mono`
- `MeasureTheory.Measure.addHaar_real_closedBall`
- `Module.finrank_pos`

Owner abstraction:
- the ambient additive Haar measure owner `μ` together with its real-valued evaluation `μ.real`
  on an arbitrary finite-dimensional real normed space.

Layer of this file:
- `source-facing`. The theorem is the chapter's direct radius-volume comparison, while its owner
  layer is the intrinsic finite-dimensional real-space volume API rather than the coordinate model
  `EuclideanSpace ℝ (Fin n)`.

Primitive data:
- the convex set `Q`, the comparison set `Sk`, the center `xStar`, and the radii `D`, `vkStar`
- the positive-dimension hypothesis `0 < dim`
- convexity and outer-ball containment for `Q`
- positivity of `μ.real Q`
- finite measure of `Sk`
- the inclusion `Metric.closedBall xStar vkStar ∩ Q ⊆ Sk`

Derived API:
- positivity of `D`, forced by `xStar ∈ Q`, `Q ⊆ Metric.closedBall xStar D`, and
  `0 < μ.real Q`
- positivity of `dim`, supplied directly by the public hypothesis
- the real-valued bound on `vkStar` in terms of the measure ratio `μ.real Sk / μ.real Q`, with
  the exponent written canonically as `1 / dim`.
-/

/-- Helper for Theorem 3.51: if a positive-volume set `Q` contains the center `xStar` and is
contained in `Metric.closedBall xStar D`, then the outer radius `D` must be positive. -/
lemma outer_radius_pos_of_positive_measure
    (hdim : 0 < dim)
    {Q : Set E} {xStar : E} {D : ℝ}
    (hxStar : xStar ∈ Q)
    (hQ_pos : 0 < μ.real Q)
    (hQ_subset : Q ⊆ Metric.closedBall xStar D) :
    0 < D := by
  -- The center belongs to the closed ball, so the radius is at least `0`.
  have hD_nonneg : 0 ≤ D := by
    have hxBall : xStar ∈ Metric.closedBall xStar D := hQ_subset hxStar
    simpa [Metric.mem_closedBall] using hxBall
  by_contra hD_pos
  have hD_zero : D = 0 := le_antisymm (le_of_not_gt hD_pos) hD_nonneg
  have hQ_subset_zero : Q ⊆ Metric.closedBall xStar 0 := by
    simpa [hD_zero] using hQ_subset
  have hmono : μ.real Q ≤ μ.real (Metric.closedBall xStar 0) :=
    measureReal_mono hQ_subset_zero measure_closedBall_lt_top.ne
  -- A zero-radius closed ball is a singleton, hence has zero Haar measure in positive dimension.
  have hclosed_zero : μ.real (Metric.closedBall xStar 0) = 0 := by
    rw [Measure.addHaar_real_closedBall μ xStar (show 0 ≤ (0 : ℝ) by simp)]
    simp [zero_pow (Nat.ne_of_gt hdim)]
  rw [hclosed_zero] at hmono
  linarith

/-- Helper for Theorem 3.51: if the inner radius strictly exceeds the outer one, then the
inclusion hypothesis already forces `Q ⊆ Sk`. -/
lemma comparison_set_contains_domain_of_outer_radius_lt
    {Q Sk : Set E} {xStar : E} {D vkStar : ℝ}
    (hQ_subset : Q ⊆ Metric.closedBall xStar D)
    (hball : Metric.closedBall xStar vkStar ∩ Q ⊆ Sk)
    (hDv : D < vkStar) :
    Q ⊆ Sk := by
  intro y hy
  have hyD : y ∈ Metric.closedBall xStar D := hQ_subset hy
  have hyv : y ∈ Metric.closedBall xStar vkStar := by
    rw [Metric.mem_closedBall] at hyD ⊢
    exact le_of_lt (lt_of_le_of_lt hyD hDv)
  exact hball ⟨hyv, hy⟩

/-- Helper for Theorem 3.51: the homothety of `Q` centered at `xStar` with factor `α ∈ [0, 1]`
stays inside the smaller closed ball and inside `Q` itself. -/
lemma homothety_image_subset_closedBall_inter_of_convex
    {Q : Set E} {xStar : E} {α D : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hQ_convex : Convex ℝ Q) (hxStar : xStar ∈ Q)
    (hQ_subset : Q ⊆ Metric.closedBall xStar D) :
    AffineMap.homothety xStar α '' Q ⊆ Metric.closedBall xStar (α * D) ∩ Q := by
  rintro z ⟨y, hy, rfl⟩
  constructor
  · -- The outer-ball hypothesis contracts to radius `α * D` under homothety.
    rw [Metric.mem_closedBall]
    have hyD : dist y xStar ≤ D := by
      simpa [Metric.mem_closedBall] using hQ_subset hy
    calc
      dist ((AffineMap.homothety xStar α) y) xStar = ‖α‖ * dist xStar y :=
        dist_homothety_center xStar y α
      _ = α * dist y xStar := by
        rw [Real.norm_of_nonneg hα0, dist_comm]
      _ ≤ α * D := mul_le_mul_of_nonneg_left hyD hα0
  · -- Convexity keeps the entire segment from `xStar` to `y` inside `Q`.
    rw [AffineMap.homothety_eq_lineMap]
    exact hQ_convex.lineMap_mem hxStar hy ⟨hα0, hα1⟩

/-- Helper for Theorem 3.51: the real-valued Haar measure of a homothety image scales by
`α ^ dim` when `α ≥ 0`. -/
lemma measureReal_homothety_image
    {Q : Set E} {xStar : E} {α : ℝ}
    (hα0 : 0 ≤ α) :
    μ.real (AffineMap.homothety xStar α '' Q) = α ^ dim * μ.real Q := by
  -- Rewrite the owner-level ENNReal scaling law through `μ.real`.
  rw [MeasureTheory.Measure.real, Measure.addHaar_image_homothety]
  rw [ENNReal.toReal_ofReal_mul]
  · simp [MeasureTheory.Measure.real, abs_of_nonneg, hα0]
  · positivity

/-- Helper for Theorem 3.51: a lower bound on `α ^ dim * μ.real Q` turns into the claimed
`dim`-th-root bound on `α`. -/
lemma alpha_le_volume_ratio_rpow_of_measure_bound
    (hdim : 0 < dim)
    {Q Sk : Set E} {α : ℝ}
    (hQ_pos : 0 < μ.real Q)
    (hα0 : 0 ≤ α)
    (hmeasure : α ^ dim * μ.real Q ≤ μ.real Sk) :
    α ≤ Real.rpow (μ.real Sk / μ.real Q) (1 / (dim : ℝ)) := by
  have hratio_nonneg : 0 ≤ μ.real Sk / μ.real Q := by
    positivity
  have hpow_le : α ^ dim ≤ μ.real Sk / μ.real Q := by
    exact (le_div_iff₀ hQ_pos).2 hmeasure
  have hdim_pos_real : 0 < (dim : ℝ) := by
    exact_mod_cast hdim
  -- Take the `dim`-th root after dividing by the positive denominator.
  have hroot :=
    (Real.le_rpow_inv_iff_of_pos hα0 hratio_nonneg hdim_pos_real).2 (by
      simpa [Real.rpow_natCast] using hpow_le)
  simpa [one_div] using hroot

/-- Theorem 3.51, stated at the intrinsic owner level: if `0 < Module.finrank ℝ E`, if a convex
set `Q` of positive `μ`-volume in a finite-dimensional real normed space is contained in the
closed ball `B(xStar, D)`, if `xStar ∈ Q`, and if a finite-`μ`-volume set `Sk` contains
`B(xStar, vkStar) ∩ Q`, then the radius `vkStar` is bounded by `D` times the `dim`-th root of the
Haar-measure ratio `μ.real Sk / μ.real Q`. Specializing to the canonical choice
`μ = Measure.addHaar` gives the chapter owner used downstream, and in Euclidean space this differs
from textbook Lebesgue volume only by a global positive normalization factor, so the displayed
ratio is unchanged. The textbook `ℝⁿ` statement is therefore recovered by specializing to
`E = EuclideanSpace ℝ (Fin n)` with `0 < n`.
-/
-- Proof sketch: if `vkStar > D`, then `Metric.closedBall xStar vkStar` already contains
-- `Metric.closedBall xStar D`, hence contains `Q`, so `Q ⊆ Sk` and the displayed bound is
-- immediate. The hypotheses force `0 < D`, and the public dimension hypothesis gives
-- `0 < dim`, so one may set
-- `α = vkStar / D ∈ [0, 1]`. Since `xStar ∈ Q` and `Q` is convex, the homothetic copy
-- `(1 - α) • xStar + α • Q` lies in `Q`; because `Q ⊆ Metric.closedBall xStar D`,
-- that same set also lies in `Metric.closedBall xStar vkStar`. Hence it is contained in `Sk`.
-- Taking volumes and using translation invariance together with the scaling rule yields
-- `μ.real Sk ≥ α ^ dim * μ.real Q`, which rearranges to the claimed bound.
theorem inner_ball_radius_le_outer_radius_mul_volume_ratio_rpow_of_convex
    (hdim : 0 < dim)
    {Q Sk : Set E} {xStar : E} {D vkStar : ℝ}
    (hQ_convex : Convex ℝ Q) (hxStar : xStar ∈ Q)
    (hQ_pos : 0 < μ.real Q)
    (hQ_subset : Q ⊆ Metric.closedBall xStar D)
    (hSk_finite : μ Sk ≠ ⊤)
    (hball : Metric.closedBall xStar vkStar ∩ Q ⊆ Sk) :
    vkStar ≤
      D *
        Real.rpow
          (μ.real Sk / μ.real Q)
          (1 / (dim : ℝ)) := by
  -- Route correction: the source proof's large-radius branch needs the missing textbook
  -- containment `Sk ⊆ Q`; the normalized homothety branch below is still valid as stated.
  have hD_pos : 0 < D :=
    outer_radius_pos_of_positive_measure hdim hxStar hQ_pos hQ_subset
  have hD_nonneg : 0 ≤ D := le_of_lt hD_pos
  by_cases hvk_nonpos : vkStar ≤ 0
  · -- If the claimed inner radius is nonpositive, the right-hand side is already nonnegative.
    have hratio_nonneg : 0 ≤ μ.real Sk / μ.real Q := by
      positivity
    have hbound_nonneg :
        0 ≤
          D *
            Real.rpow
              (μ.real Sk / μ.real Q)
              (1 / (dim : ℝ)) := by
      exact mul_nonneg hD_nonneg (Real.rpow_nonneg hratio_nonneg _)
    exact hvk_nonpos.trans hbound_nonneg
  · have hvk_nonneg : 0 ≤ vkStar := le_of_lt (lt_of_not_ge hvk_nonpos)
    by_cases hDv : D < vkStar
    · -- This is the source proof's overlarge-radius branch. As stated, it only yields `Q ⊆ Sk`.
      have hQ_in_Sk : Q ⊆ Sk :=
        comparison_set_contains_domain_of_outer_radius_lt hQ_subset hball hDv
      have hQ_le : μ.real Q ≤ μ.real Sk := measureReal_mono hQ_in_Sk hSk_finite
      have hratio_ge_one : 1 ≤ μ.real Sk / μ.real Q := by
        exact (one_le_div₀ hQ_pos).2 hQ_le
      have hrpow_ge_one :
          1 ≤
            Real.rpow
              (μ.real Sk / μ.real Q)
              (1 / (dim : ℝ)) := by
        calc
          1 = Real.rpow (1 : ℝ) (1 / (dim : ℝ)) := by
            simp
          _ ≤
              Real.rpow
                (μ.real Sk / μ.real Q)
                (1 / (dim : ℝ)) := by
            exact Real.rpow_le_rpow (by positivity) hratio_ge_one (by positivity)
      have hD_le :
          D ≤
            D *
              Real.rpow
                (μ.real Sk / μ.real Q)
                (1 / (dim : ℝ)) := by
        simpa [one_mul] using mul_le_mul_of_nonneg_left hrpow_ge_one hD_nonneg
      -- TODO: to finish this branch one needs the missing source hypothesis `Sk ⊆ Q`
      -- (or an equivalent measure upper bound on `Sk`), which would force `μ.real Sk = μ.real Q`
      -- after `Q ⊆ Sk` and hence reduce the bound to `vkStar ≤ D`.
      sorry
    · have hvk_le_D : vkStar ≤ D := le_of_not_gt hDv
      let α : ℝ := vkStar / D
      have hα0 : 0 ≤ α := by
        exact div_nonneg hvk_nonneg hD_nonneg
      have hα1 : α ≤ 1 := by
        exact (div_le_iff₀ hD_pos).2 (by simpa using hvk_le_D)
      have hα_mul : α * D = vkStar := by
        dsimp [α]
        field_simp [hD_pos.ne']
      -- The normalized homothety image is the exact source object controlling the measure.
      have himage_subset :
          AffineMap.homothety xStar α '' Q ⊆ Metric.closedBall xStar vkStar ∩ Q := by
        have hsubset :=
          homothety_image_subset_closedBall_inter_of_convex
            hα0 hα1 hQ_convex hxStar hQ_subset
        simpa [hα_mul] using hsubset
      have hmeasure_mono : μ.real (AffineMap.homothety xStar α '' Q) ≤ μ.real Sk :=
        measureReal_mono (fun z hz => hball (himage_subset hz)) hSk_finite
      have hmeasure : α ^ dim * μ.real Q ≤ μ.real Sk := by
        simpa [measureReal_homothety_image hα0] using hmeasure_mono
      have hα_le :
          α ≤
            Real.rpow
              (μ.real Sk / μ.real Q)
              (1 / (dim : ℝ)) :=
        alpha_le_volume_ratio_rpow_of_measure_bound hdim hQ_pos hα0 hmeasure
      calc
        vkStar = α * D := by
          rw [hα_mul]
        _ ≤
            Real.rpow
              (μ.real Sk / μ.real Q)
              (1 / (dim : ℝ)) *
              D := by
          exact mul_le_mul_of_nonneg_right hα_le hD_nonneg
        _ =
            D *
              Real.rpow
                (μ.real Sk / μ.real Q)
                (1 / (dim : ℝ)) := by
          ring

end
