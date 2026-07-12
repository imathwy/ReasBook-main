import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.Instances.Real

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Manifold ContDiff

-- Domain sampling pass: this item sits in the real normed-space / smooth-manifold interface.
-- Sampled owner declarations:
-- * `contDiffOn_const`
-- * `contMDiff_iff`
-- * `contMDiff_iff_contDiff`
-- * `ContMDiff.continuous`
-- The source-facing owner is `realHeavisideStep`; the local-coordinate theorem below is a
-- bridge/view statement expressed with the canonical `ContDiffOn` neighborhood API.

/-- The real Heaviside step function, equal to `1` on `[0, ∞)` and `0` on `(-∞, 0)`. -/
noncomputable def realHeavisideStep : ℝ → ℝ :=
  fun x ↦ if 0 ≤ x then 1 else 0

-- Proof sketch: unfold `realHeavisideStep` and simplify the defining `if` using `hx`.
/-- The real Heaviside step function takes the value `1` at every nonnegative real number. -/
theorem realHeavisideStep_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    realHeavisideStep x = 1 := by
  simp [realHeavisideStep, hx]

/-- The real Heaviside step function takes the value `0` at every negative real number. -/
theorem realHeavisideStep_of_neg {x : ℝ} (hx : x < 0) :
    realHeavisideStep x = 0 := by
  simp [realHeavisideStep, show ¬ 0 ≤ x by linarith]

-- Proof sketch: if `x < 0`, choose an open neighborhood `U` on which `realHeavisideStep` is
-- constantly `0`; if `x ≥ 0`, choose an open neighborhood `V` of `1` and take `U = univ`, so the
-- relevant restriction is constantly `1` on `U ∩ realHeavisideStep ⁻¹' V`. For the identity
-- charts on open subsets of `ℝ`, this is exactly a `ContDiffOn` statement for the restricted map.
/-- Problem 2-1 (1): this records only the chartwise `ContDiffOn` clause appearing in the canonical
smoothness criterion `contMDiff_iff`; it is a local bridge theorem rather than a second smoothness
owner. With identity charts on open subsets of `ℝ`, this is the existence of open neighborhoods
`U` of `x` and `V` of `realHeavisideStep x` such that `realHeavisideStep` is `ContDiffOn` on
`U ∩ realHeavisideStep ⁻¹' V`. -/
theorem realHeavisideStep_has_local_smooth_coordinate_representatives (x : ℝ) :
    ∃ U : TopologicalSpace.Opens ℝ, x ∈ (U : Set ℝ) ∧
      ∃ V : TopologicalSpace.Opens ℝ, realHeavisideStep x ∈ (V : Set ℝ) ∧
        ContDiffOn ℝ ∞ realHeavisideStep ((U : Set ℝ) ∩ realHeavisideStep ⁻¹' (V : Set ℝ)) := by
  by_cases hx : x < 0
  · refine ⟨⟨Iio 0, isOpen_Iio⟩, hx, ⟨⟨Iio (1 / 2 : ℝ), isOpen_Iio⟩, ?_, ?_⟩⟩
    · norm_num [realHeavisideStep_of_neg hx]
    · refine (contDiffOn_const :
        ContDiffOn ℝ ∞ (fun _ : ℝ ↦ (0 : ℝ))
          ((Iio 0 : Set ℝ) ∩ realHeavisideStep ⁻¹' (Iio (1 / 2 : ℝ)))).congr ?_
      intro y hy
      exact realHeavisideStep_of_neg hy.1
  · have hx_nonneg : 0 ≤ x := le_of_not_gt hx
    refine ⟨⊤, by simp, ⟨⟨Ioi (1 / 2 : ℝ), isOpen_Ioi⟩, ?_, ?_⟩⟩
    · norm_num [realHeavisideStep_of_nonneg hx_nonneg]
    · refine (contDiffOn_const :
        ContDiffOn ℝ ∞ (fun _ : ℝ ↦ (1 : ℝ))
          ((((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ) ∩
            realHeavisideStep ⁻¹' (Ioi (1 / 2 : ℝ))))).congr ?_
      intro y hy
      have hy_nonneg : 0 ≤ y := by
        by_contra hy_neg
        have hzero : realHeavisideStep y = 0 :=
          realHeavisideStep_of_neg (lt_of_not_ge hy_neg)
        exact (by simp : ¬ (0 : ℝ) ∈ Ioi (1 / 2 : ℝ))
          (by simpa [Set.mem_preimage, hzero] using hy.2)
      exact realHeavisideStep_of_nonneg hy_nonneg

/-- The real Heaviside step function has a jump discontinuity at `0`. -/
theorem realHeavisideStep_not_continuousAt_zero :
    ¬ ContinuousAt realHeavisideStep 0 := by
  intro hcont
  have hpre : realHeavisideStep ⁻¹' Ioi (1 / 2 : ℝ) ∈ nhds (0 : ℝ) := by
    have hV : Ioi (1 / 2 : ℝ) ∈ nhds (realHeavisideStep 0) := by
      simpa [realHeavisideStep_of_nonneg (show (0 : ℝ) ≤ 0 by rfl)] using
        Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)
    exact hcont.preimage_mem_nhds hV
  rcases Metric.mem_nhds_iff.1 hpre with ⟨ε, hε_pos, hε_subset⟩
  have hε_half_pos : 0 < ε / 2 := by
    linarith
  have hball : -(ε / 2) ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg, abs_of_pos hε_half_pos]
    linarith
  have hmem : -(ε / 2) ∈ realHeavisideStep ⁻¹' Ioi (1 / 2 : ℝ) := hε_subset hball
  have hzero : realHeavisideStep (-(ε / 2)) = 0 := by
    apply realHeavisideStep_of_neg
    linarith
  exact (by simp : ¬ (0 : ℝ) ∈ Ioi (1 / 2 : ℝ)) (by simpa [Set.mem_preimage, hzero] using hmem)

-- Problem 2-1 (2) is a derived `ContMDiff` consequence of the jump discontinuity above via the
-- canonical owner theorem `ContMDiff.continuous`.
/-- Problem 2-1 (2): the real Heaviside step function is not smooth as a map `ℝ → ℝ` in the
sense of this chapter; smoothness would force continuity. -/
theorem realHeavisideStep_not_smooth :
    ¬ ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ realHeavisideStep := by
  intro hsmooth
  exact realHeavisideStep_not_continuousAt_zero hsmooth.continuous.continuousAt
