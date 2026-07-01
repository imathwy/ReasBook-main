import Mathlib
import cartan.III.section10.«frozen_0011_Theorem_III_4_extra_9»

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Metric Set

open scoped Topology

-- Proof sketch: `z ↦ 1 / z` is analytic on `{z : ℂ | z ≠ 0}`, and `Complex.exp` is entire; the
-- composition is therefore analytic on the punctured complex plane.
/-- The function `z ↦ exp (1 / z)` is analytic on the punctured complex plane. -/
theorem analyticOnNhd_exp_one_div_punctured_plane :
    AnalyticOnNhd ℂ (fun z : ℂ ↦ Complex.exp (1 / z)) ({0} : Set ℂ)ᶜ := by
  simpa [one_div] using
    (analyticOnNhd_inv.cexp :
      AnalyticOnNhd ℂ (fun z : ℂ ↦ Complex.exp z⁻¹) ({0} : Set ℂ)ᶜ)

/-- Helper for Example III.4-extra-10: restricting punctured-plane analyticity to a punctured ball
shows that `z ↦ exp (1 / z)` has an isolated singularity at the origin. -/
lemma hasIsolatedSingularityAt_exp_one_div_zero :
    HasIsolatedSingularityAt (fun z : ℂ ↦ Complex.exp (1 / z)) 0 := by
  -- Restrict the global punctured-plane analyticity to the unit punctured ball around `0`.
  refine (HasIsolatedSingularityAt.iff_exists_analyticOnNhd_punctured_ball).2 ?_
  refine ⟨1, zero_lt_one, ?_⟩
  refine analyticOnNhd_exp_one_div_punctured_plane.mono ?_
  intro z hz
  simpa using hz.2

/-- Helper for Example III.4-extra-10: the reciprocal of the positive real sequence `n + 1`
approaches `0` through nonzero complex numbers. -/
lemma tendsto_natCast_inv_succ_nhdsNE_zero :
    Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℂ)⁻¹)) atTop (𝓝[≠] (0 : ℂ)) := by
  -- We first show convergence to `0`, then record that every term stays away from `0`.
  rw [tendsto_nhdsWithin_iff]
  constructor
  · convert
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)).comp (Filter.tendsto_add_atTop_nat 1) using 1
  · exact Filter.Eventually.of_forall fun n ↦ by
      have h : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero n
      simpa using inv_ne_zero h

/-- Helper for Example III.4-extra-10: along the positive real ray approaching `0`, the values of
`exp (1 / z)` have norms growing like `exp (n + 1)`, so they cannot converge to a finite limit. -/
lemma exp_one_div_not_tendsto_nhds_at_zero (c : ℂ) :
    ¬ Tendsto (fun z : ℂ ↦ Complex.exp (1 / z)) (𝓝[≠] (0 : ℂ)) (𝓝 c) := by
  intro h
  -- Compose the punctured-neighborhood limit with the explicit positive approach sequence.
  have hseq :
      Tendsto (fun n : ℕ ↦ Complex.exp ((n + 1 : ℂ))) atTop (𝓝 c) := by
    convert h.comp tendsto_natCast_inv_succ_nhdsNE_zero using 1
    ext n
    simp [Nat.cast_add, Nat.cast_one]
  have hnorm_atTop :
      Tendsto (fun n : ℕ ↦ ‖Complex.exp ((n + 1 : ℂ))‖) atTop atTop := by
    -- On the positive real axis, the complex exponential has norm `exp`.
    convert
      (Real.tendsto_exp_atTop.comp
        (Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)) using 1
    ext n
    simp [Complex.norm_exp]
  -- A sequence with finite limit cannot simultaneously have norm tending to `+∞`.
  apply not_tendsto_atTop_of_tendsto_nhds hseq.norm
  exact hnorm_atTop

/-- Helper for Example III.4-extra-10: along the negative real ray approaching `0`, the values of
`exp (1 / z)` tend to `0`, so they cannot tend to infinity. -/
lemma exp_one_div_not_tendsto_cobounded_at_zero :
    ¬ Tendsto (fun z : ℂ ↦ Complex.exp (1 / z)) (𝓝[≠] (0 : ℂ)) (Bornology.cobounded ℂ) := by
  intro h
  have hneg_seq :
      Tendsto (fun n : ℕ ↦ -(((n + 1 : ℕ) : ℂ)⁻¹)) atTop (𝓝[≠] (0 : ℂ)) := by
    -- Negation preserves the ordinary limit to `0` and still avoids the puncture.
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hzero :
          Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℂ)⁻¹)) atTop (𝓝 (0 : ℂ)) :=
        (tendsto_nhdsWithin_iff.mp tendsto_natCast_inv_succ_nhdsNE_zero).1
      simpa using hzero.neg
    · filter_upwards [(tendsto_nhdsWithin_iff.mp tendsto_natCast_inv_succ_nhdsNE_zero).2] with n hn
      simpa using neg_ne_zero.mpr hn
  have hnorm_atTop :
      Tendsto (fun n : ℕ ↦ ‖Complex.exp (1 / (-(((n + 1 : ℕ) : ℂ)⁻¹)))‖) atTop atTop := by
    -- Cobounded convergence is equivalent to the norm tending to `+∞`.
    rw [tendsto_norm_atTop_iff_cobounded]
    convert h.comp hneg_seq using 1
  have hnorm_zero :
      Tendsto (fun n : ℕ ↦ ‖Complex.exp (1 / (-(((n + 1 : ℕ) : ℂ)⁻¹)))‖) atTop (𝓝 0) := by
    -- Along the negative real axis, the reciprocals are `-(n + 1)`, and `exp (-(n + 1)) → 0`.
    convert
      (Real.tendsto_exp_atBot.comp
        (Filter.tendsto_neg_atBot_iff.mpr
          (Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop))) using 1
    ext n
    simp [Complex.norm_exp]
  -- A sequence converging to `0` cannot have norm tending to `+∞`.
  apply not_tendsto_atTop_of_tendsto_nhds hnorm_zero
  exact hnorm_atTop

-- Proof sketch: combine punctured-plane analyticity with the Laurent expansion of `exp (1 / z)`
-- at `0`; since every negative-power coefficient is nonzero, the singularity cannot be
-- meromorphic, hence it is essential.
/-- Example III.4-extra-10: the function `z ↦ exp (1 / z)` has an isolated essential singularity
at the origin. -/
theorem exp_one_div_hasEssentialSingularityAt_zero :
    HasEssentialSingularityAt (fun z : ℂ ↦ Complex.exp (1 / z)) 0 := by
  -- The source proof splits into punctured analyticity plus failure of meromorphy.
  refine ⟨hasIsolatedSingularityAt_exp_one_div_zero, ?_⟩
  intro hmero
  -- A meromorphic germ either has nonnegative order and finite limit, or negative order and
  -- tends to infinity. The two explicit radial sequences rule out both behaviors.
  rcases lt_or_ge (meromorphicOrderAt (fun z : ℂ ↦ Complex.exp (1 / z)) 0) 0 with hneg | hnonneg
  · exact exp_one_div_not_tendsto_cobounded_at_zero
      (tendsto_cobounded_of_meromorphicOrderAt_neg hneg)
  · rcases tendsto_nhds_of_meromorphicOrderAt_nonneg hmero hnonneg with ⟨c, hc⟩
    exact (exp_one_div_not_tendsto_nhds_at_zero c) hc

-- Proof sketch: the complex exponential never vanishes, so every point of the punctured plane is
-- sent to a nonzero complex number.
/-- The function `z ↦ exp (1 / z)` never takes the value `0` on the punctured complex plane. -/
theorem mapsTo_exp_one_div_punctured_plane_nonzero :
    MapsTo (fun z : ℂ ↦ Complex.exp (1 / z)) ({0} : Set ℂ)ᶜ ({0} : Set ℂ)ᶜ := by
  intro z hz
  simp [Complex.exp_ne_zero]

-- Proof sketch: apply the chapter's Picard-type image theorem to the essential singularity at `0`.
-- The image of each punctured ball is either all of `ℂ` or the complement of one point; the
-- preceding nonvanishing theorem shows that the omitted point must be `0`.
/-- Every nonzero complex number is attained by `z ↦ exp (1 / z)` in each punctured disc around
the origin. -/
theorem exists_mem_punctured_ball_exp_one_div_eq {w : ℂ} (hw : w ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ), Complex.exp (1 / z) = w := by
  have hanalytic :
      AnalyticOnNhd ℂ (fun z : ℂ ↦ Complex.exp (1 / z)) (ball (0 : ℂ) ε \ ({0} : Set ℂ)) :=
    analyticOnNhd_exp_one_div_punctured_plane.mono <| by
      intro z hz
      simpa using hz.2
  have himage :=
    punctured_ball_image_eq_univ_or_compl_singleton_of_essential_singularity
      exp_one_div_hasEssentialSingularityAt_zero hε hanalytic
  rcases himage with himage | ⟨a, himage⟩
  · have hw_image :
        w ∈ (fun z : ℂ ↦ Complex.exp (1 / z)) '' (ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
      rw [himage]
      exact mem_univ w
    rcases hw_image with ⟨z, hz, hzw⟩
    exact ⟨z, hz, hzw⟩
  · have hzero_not_mem :
        0 ∉ (fun z : ℂ ↦ Complex.exp (1 / z)) '' (ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
      rintro ⟨z, hz, hz0⟩
      have hz' : z ∈ ({0} : Set ℂ)ᶜ := by
        simpa using hz.2
      have hnonzero : Complex.exp (1 / z) ≠ 0 := by
        simpa only [mem_compl_iff, mem_singleton_iff] using
          mapsTo_exp_one_div_punctured_plane_nonzero hz'
      exact hnonzero hz0
    have ha_zero : a = 0 := by
      have : 0 ∉ ({a} : Set ℂ)ᶜ := by rwa [himage] at hzero_not_mem
      have ha_zero : 0 = a := by simpa using this
      exact ha_zero.symm
    have hw_image :
        w ∈ (fun z : ℂ ↦ Complex.exp (1 / z)) '' (ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
      rw [himage]
      simpa [ha_zero] using hw
    rcases hw_image with ⟨z, hz, hzw⟩
    exact ⟨z, hz, hzw⟩
