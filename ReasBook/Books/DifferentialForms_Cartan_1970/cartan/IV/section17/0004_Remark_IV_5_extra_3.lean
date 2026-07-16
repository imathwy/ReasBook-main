import DifferentialForms_Cartan_1970.cartan.IV.section17.«0003_Proposition_2_1»

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: the dedicated `lean_leansearch` tool was unavailable in this runner, so
-- the statement surface was matched against the local bidisc Cauchy formula in
-- `IV/section17/0003_Proposition_2_1.lean` and the several-variable `AnalyticOnNhd` precedent in
-- `IV/section14/0002_Definition_IV_2_extra_2.lean`.

open Set
open scoped Topology

noncomputable section

/-- The Hartogs inner tube `|z₁| < ρ₁`, `|z₂| < ε` in `ℂ²`. -/
def hartogs_inner_tube (ρ₁ ε : ℝ) : Set (ℂ × ℂ) :=
  {z | ‖z.1‖ < ρ₁ ∧ ‖z.2‖ < ε}

/-- Membership in the Hartogs inner tube is the pair of corresponding norm inequalities. -/
@[simp] theorem mem_hartogs_inner_tube {ρ₁ ε : ℝ} {z : ℂ × ℂ} :
    z ∈ hartogs_inner_tube ρ₁ ε ↔ ‖z.1‖ < ρ₁ ∧ ‖z.2‖ < ε := by
  -- This is just the defining pair of strict inequalities.
  rfl

/-- The Hartogs outer shell `ρ₁ - ε < |z₁| < ρ₁`, `|z₂| < ρ₂` in `ℂ²`. -/
def hartogs_outer_shell (ρ₁ ρ₂ ε : ℝ) : Set (ℂ × ℂ) :=
  {z | ρ₁ - ε < ‖z.1‖ ∧ ‖z.1‖ < ρ₁ ∧ ‖z.2‖ < ρ₂}

/-- Membership in the Hartogs outer shell is the corresponding annulus-disc condition. -/
@[simp] theorem mem_hartogs_outer_shell {ρ₁ ρ₂ ε : ℝ} {z : ℂ × ℂ} :
    z ∈ hartogs_outer_shell ρ₁ ρ₂ ε ↔
      ρ₁ - ε < ‖z.1‖ ∧ ‖z.1‖ < ρ₁ ∧ ‖z.2‖ < ρ₂ := by
  -- This is just the defining annulus-disc condition.
  rfl

/-- The Hartogs cross is the union of the inner tube and the outer shell. -/
def hartogs_cross (ρ₁ ρ₂ ε : ℝ) : Set (ℂ × ℂ) :=
  hartogs_inner_tube ρ₁ ε ∪ hartogs_outer_shell ρ₁ ρ₂ ε

/-- Membership in the Hartogs cross is membership in either the inner tube or the outer shell. -/
@[simp] theorem mem_hartogs_cross {ρ₁ ρ₂ ε : ℝ} {z : ℂ × ℂ} :
    z ∈ hartogs_cross ρ₁ ρ₂ ε ↔
      (‖z.1‖ < ρ₁ ∧ ‖z.2‖ < ε) ∨
        (ρ₁ - ε < ‖z.1‖ ∧ ‖z.1‖ < ρ₁ ∧ ‖z.2‖ < ρ₂) := by
  -- Unfolding the union reduces the claim to the two defining membership lemmas above.
  simp [hartogs_cross]

/-- Helper for Remark IV.5-extra-3: the Hartogs cross lies inside the ambient bidisc. -/
theorem hartogs_cross_subset_bidisc {ρ₁ ρ₂ ε : ℝ} (hερ₂ : ε < ρ₂) :
    hartogs_cross ρ₁ ρ₂ ε ⊆ bidisc ρ₁ ρ₂ := by
  intro z hz
  rcases (mem_hartogs_cross.mp hz) with hz | hz
  · -- On the inner tube, only the `z₂` bound needs to be enlarged from `ε` to `ρ₂`.
    exact mem_bidisc.mpr ⟨hz.1, lt_trans hz.2 hερ₂⟩
  · -- On the outer shell, the defining inequalities already place `z` in the bidisc.
    exact mem_bidisc.mpr ⟨hz.2.1, hz.2.2⟩

/-- Helper for Remark IV.5-extra-3: admissible intermediate radii exist between the Hartogs
cross and the ambient bidisc. -/
theorem exists_admissible_hartogs_radii {ρ₁ ρ₂ ε : ℝ}
    (hε : 0 < ε) (_hερ₁ : ε < ρ₁) (hερ₂ : ε < ρ₂) :
    ∃ r₁ r₂ : ℝ, ρ₁ - ε < r₁ ∧ r₁ < ρ₁ ∧ ε < r₂ ∧ r₂ < ρ₂ := by
  refine ⟨ρ₁ - ε / 2, (ε + ρ₂) / 2, ?_, ?_, ?_, ?_⟩
  · -- The midpoint `ρ₁ - ε/2` stays strictly above the inner annulus threshold.
    linarith
  · -- The same midpoint remains strictly inside the outer radius `ρ₁`.
    linarith
  · -- The average of `ε` and `ρ₂` is strictly larger than `ε`.
    linarith
  · -- The same average stays strictly below `ρ₂`.
    linarith

/-- Helper for Remark IV.5-extra-3: the source-faithful local extension is the double Cauchy
transform on the distinguished torus of radii `r₁` and `r₂`. -/
def hartogs_cauchy_extension (f : (ℂ × ℂ) → ℂ) (r₁ r₂ : ℝ) : (ℂ × ℂ) → ℂ :=
  fun z ↦
    (((2 * Real.pi * Complex.I : ℂ) ^ (2 : ℕ))⁻¹ *
      ∮ ζ₁ in C(0, r₁), ∮ ζ₂ in C(0, r₂),
        f (ζ₁, ζ₂) / ((ζ₁ - z.1) * (ζ₂ - z.2)))

/-- Helper for Remark IV.5-extra-3: every point of the ambient bidisc lies in some admissible
smaller Hartogs bidisc. -/
theorem exists_admissible_hartogs_radii_at_point {ρ₁ ρ₂ ε : ℝ} {z : ℂ × ℂ}
    (hε : 0 < ε) (_hερ₁ : ε < ρ₁) (hερ₂ : ε < ρ₂) (hz : z ∈ bidisc ρ₁ ρ₂) :
    ∃ r₁ r₂ : ℝ,
      ρ₁ - ε < r₁ ∧ r₁ < ρ₁ ∧ ε < r₂ ∧ r₂ < ρ₂ ∧ ‖z.1‖ < r₁ ∧ ‖z.2‖ < r₂ := by
  rcases mem_bidisc.mp hz with ⟨hz₁, hz₂⟩
  let a : ℝ := max ‖z.1‖ (ρ₁ - ε)
  let b : ℝ := max ‖z.2‖ ε
  have ha_lt : a < ρ₁ := by
    refine max_lt hz₁ ?_
    linarith
  have hb_lt : b < ρ₂ := by
    refine max_lt hz₂ hερ₂
  have hρ₁a : ρ₁ - ε ≤ a := by
    exact le_max_right ‖z.1‖ (ρ₁ - ε)
  have hz₁a : ‖z.1‖ ≤ a := by
    exact le_max_left ‖z.1‖ (ρ₁ - ε)
  have hεb : ε ≤ b := by
    exact le_max_right ‖z.2‖ ε
  have hz₂b : ‖z.2‖ ≤ b := by
    exact le_max_left ‖z.2‖ ε
  refine ⟨(a + ρ₁) / 2, (b + ρ₂) / 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The midpoint between `a` and `ρ₁` stays above the Hartogs annulus threshold.
    linarith
  · -- The same midpoint remains inside the ambient first radius.
    linarith
  · -- The midpoint between `b` and `ρ₂` stays above `ε`.
    linarith
  · -- The same midpoint remains inside the ambient second radius.
    linarith
  · -- The first coordinate norm is strictly smaller than the chosen local first radius.
    linarith
  · -- The second coordinate norm is strictly smaller than the chosen local second radius.
    linarith

/-- Helper for Remark IV.5-extra-3: one can choose local radii for every point, and the full
admissibility package is required only when the point lies in the ambient bidisc. -/
theorem exists_total_local_hartogs_radii {ρ₁ ρ₂ ε : ℝ} (hε : 0 < ε) (hερ₁ : ε < ρ₁)
    (hερ₂ : ε < ρ₂) (z : ℂ × ℂ) :
    ∃ r₁ r₂ : ℝ,
      z ∈ bidisc ρ₁ ρ₂ →
        ρ₁ - ε < r₁ ∧ r₁ < ρ₁ ∧ ε < r₂ ∧ r₂ < ρ₂ ∧ ‖z.1‖ < r₁ ∧ ‖z.2‖ < r₂ := by
  by_cases hz : z ∈ bidisc ρ₁ ρ₂
  · rcases exists_admissible_hartogs_radii_at_point hε hερ₁ hερ₂ hz with
      ⟨r₁, r₂, hr₁low, hr₁high, hr₂low, hr₂high, hz₁, hz₂⟩
    exact ⟨r₁, r₂, fun _ ↦ ⟨hr₁low, hr₁high, hr₂low, hr₂high, hz₁, hz₂⟩⟩
  · exact ⟨0, 0, fun hz' ↦ (hz hz').elim⟩

/-- Helper for Remark IV.5-extra-3: first coordinate radius chosen for the local Cauchy extension
through a point of the ambient bidisc. -/
noncomputable def chosen_local_r₁
    (ρ₁ ρ₂ ε : ℝ) (hε : 0 < ε) (hερ₁ : ε < ρ₁) (hερ₂ : ε < ρ₂) (z : ℂ × ℂ) : ℝ :=
  Classical.choose (exists_total_local_hartogs_radii hε hερ₁ hερ₂ z)

/-- Helper for Remark IV.5-extra-3: second coordinate radius chosen for the local Cauchy
extension through a point of the ambient bidisc. -/
noncomputable def chosen_local_r₂
    (ρ₁ ρ₂ ε : ℝ) (hε : 0 < ε) (hερ₁ : ε < ρ₁) (hερ₂ : ε < ρ₂) (z : ℂ × ℂ) : ℝ :=
  Classical.choose
    (Classical.choose_spec (exists_total_local_hartogs_radii hε hερ₁ hερ₂ z))

/-- Helper for Remark IV.5-extra-3: the chosen local radii are admissible and contain the base
point. -/
theorem chosen_local_radii_spec {ρ₁ ρ₂ ε : ℝ} (hε : 0 < ε) (hερ₁ : ε < ρ₁) (hερ₂ : ε < ρ₂)
    {z : ℂ × ℂ} (hz : z ∈ bidisc ρ₁ ρ₂) :
    ρ₁ - ε < chosen_local_r₁ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z ∧
      chosen_local_r₁ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z < ρ₁ ∧
      ε < chosen_local_r₂ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z ∧
      chosen_local_r₂ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z < ρ₂ ∧
      ‖z.1‖ < chosen_local_r₁ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z ∧
      ‖z.2‖ < chosen_local_r₂ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z := by
  have h₁ :
      z ∈ bidisc ρ₁ ρ₂ →
        ρ₁ - ε < chosen_local_r₁ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z ∧
          chosen_local_r₁ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z < ρ₁ ∧
          ε < chosen_local_r₂ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z ∧
          chosen_local_r₂ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z < ρ₂ ∧
          ‖z.1‖ < chosen_local_r₁ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z ∧
          ‖z.2‖ < chosen_local_r₂ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z := by
    -- The second `Classical.choose_spec` removes the remaining existential for `r₂`.
    simpa [chosen_local_r₁, chosen_local_r₂] using
      (Classical.choose_spec
        (Classical.choose_spec (exists_total_local_hartogs_radii hε hερ₁ hερ₂ z)))
  exact h₁ hz

/-- Helper for Remark IV.5-extra-3: the globally glued extension uses the chosen local Cauchy
transform attached to each point. -/
noncomputable def pointwise_hartogs_extension
    (f : (ℂ × ℂ) → ℂ) (ρ₁ ρ₂ ε : ℝ) (hε : 0 < ε) (hερ₁ : ε < ρ₁) (hερ₂ : ε < ρ₂) :
    (ℂ × ℂ) → ℂ :=
  fun z ↦
    hartogs_cauchy_extension f
      (chosen_local_r₁ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z)
      (chosen_local_r₂ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z) z

/-- Helper for Remark IV.5-extra-3: evaluating the inner `ζ₂`-integral on the distinguished torus
rewrites the local double Cauchy transform as a single Cauchy integral in `ζ₁`. -/
lemma hartogs_cauchy_extension_left_slice_formula
    {f : (ℂ × ℂ) → ℂ} {ρ₁ ρ₂ ε r₁ r₂ : ℝ}
    (hhol₂ :
      ∀ w : ℂ, ρ₁ - ε < ‖w‖ → ‖w‖ < ρ₁ →
        DifferentiableOn ℂ (fun z ↦ f (w, z)) (Metric.ball (0 : ℂ) ρ₂))
    (hr₁low : ρ₁ - ε < r₁) (hr₁high : r₁ < ρ₁) (hr₂high : r₂ < ρ₂)
    {z₁ w₂ : ℂ} (hz₁ : ‖z₁‖ < r₁) (hw₂ : ‖w₂‖ < r₂) :
    hartogs_cauchy_extension f r₁ r₂ (z₁, w₂) =
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ∮ ζ₁ in C(0, r₁), f (ζ₁, w₂) / (ζ₁ - z₁)) := by
  have hr₁pos : 0 < r₁ := lt_of_le_of_lt (norm_nonneg z₁) hz₁
  have hr₂pos : 0 < r₂ := lt_of_le_of_lt (norm_nonneg w₂) hw₂
  have hw₂_ball : w₂ ∈ Metric.ball (0 : ℂ) r₂ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw₂
  have hinner_boundary :
      Set.EqOn
        (fun ζ₁ ↦
          ∮ ζ₂ in C(0, r₂), f (ζ₁, ζ₂) / ((ζ₁ - z₁) * (ζ₂ - w₂)))
        (fun ζ₁ ↦ (2 * Real.pi * Complex.I : ℂ) * (f (ζ₁, w₂) / (ζ₁ - z₁)))
        (Metric.sphere (0 : ℂ) r₁) := by
    intro ζ₁ hζ₁
    have hζ₁_norm : ‖ζ₁‖ = r₁ := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hζ₁
    have hζ₁_low : ρ₁ - ε < ‖ζ₁‖ := by
      rw [hζ₁_norm]
      exact hr₁low
    have hζ₁_high : ‖ζ₁‖ < ρ₁ := by
      rw [hζ₁_norm]
      exact hr₁high
    have hright_slice :
        DifferentiableOn ℂ (fun ζ₂ ↦ f (ζ₁, ζ₂)) (Metric.closedBall (0 : ℂ) r₂) :=
      (hhol₂ ζ₁ hζ₁_low hζ₁_high).mono fun ζ₂ hz₂ ↦ by
        have hz₂_le : ‖ζ₂‖ ≤ r₂ := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hz₂
        simpa [Metric.mem_ball, dist_eq_norm] using lt_of_le_of_lt hz₂_le hr₂high
    have hinner_cauchy :
        (∮ ζ₂ in C(0, r₂), (ζ₂ - w₂)⁻¹ * f (ζ₁, ζ₂)) =
          (2 * Real.pi * Complex.I : ℂ) * f (ζ₁, w₂) := by
      -- The outer-shell hypothesis makes the inner `ζ₂`-slice holomorphic on the smaller disc.
      simpa [smul_eq_mul] using
        (hright_slice.circleIntegral_sub_inv_smul (c := 0) (R := r₂) (w := w₂) hw₂_ball)
    -- This is the source step `(2.4)` inserted into the double Cauchy kernel.
    calc
      ∮ ζ₂ in C(0, r₂), f (ζ₁, ζ₂) / ((ζ₁ - z₁) * (ζ₂ - w₂))
          = ∮ ζ₂ in C(0, r₂), (ζ₁ - z₁)⁻¹ * ((ζ₂ - w₂)⁻¹ * f (ζ₁, ζ₂)) := by
              apply circleIntegral.integral_congr hr₂pos.le
              intro ζ₂ hζ₂
              simpa using
                (two_variable_cauchy_integrand_eq_inv_mul_inv
                  (f := f) (ζ₁ := ζ₁) (ζ₂ := ζ₂) (z₁ := z₁) (z₂ := w₂))
      _ = (ζ₁ - z₁)⁻¹ * ∮ ζ₂ in C(0, r₂), (ζ₂ - w₂)⁻¹ * f (ζ₁, ζ₂) := by
            rw [circleIntegral.integral_const_mul]
      _ = (ζ₁ - z₁)⁻¹ * ((2 * Real.pi * Complex.I : ℂ) * f (ζ₁, w₂)) := by
            rw [hinner_cauchy]
      _ = (2 * Real.pi * Complex.I : ℂ) * (f (ζ₁, w₂) / (ζ₁ - z₁)) := by
            rw [div_eq_mul_inv]
            ac_rfl
  have hdouble :
      (∮ ζ₁ in C(0, r₁), ∮ ζ₂ in C(0, r₂),
        f (ζ₁, ζ₂) / ((ζ₁ - z₁) * (ζ₂ - w₂))) =
        (2 * Real.pi * Complex.I : ℂ) *
          (∮ ζ₁ in C(0, r₁), f (ζ₁, w₂) / (ζ₁ - z₁)) := by
    -- After the inner evaluation, only the one-variable Cauchy transform in `ζ₁` remains.
    calc
      (∮ ζ₁ in C(0, r₁), ∮ ζ₂ in C(0, r₂),
        f (ζ₁, ζ₂) / ((ζ₁ - z₁) * (ζ₂ - w₂))) =
          ∮ ζ₁ in C(0, r₁), (2 * Real.pi * Complex.I : ℂ) * (f (ζ₁, w₂) / (ζ₁ - z₁)) := by
            apply circleIntegral.integral_congr hr₁pos.le
            intro ζ₁ hζ₁
            exact hinner_boundary hζ₁
      _ = (2 * Real.pi * Complex.I : ℂ) *
            (∮ ζ₁ in C(0, r₁), f (ζ₁, w₂) / (ζ₁ - z₁)) := by
            rw [circleIntegral.integral_const_mul]
  have htwo_pi_i_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    have htwo_pi_ne : (2 * Real.pi : ℂ) ≠ 0 := by
      refine mul_ne_zero ?_ ?_
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero htwo_pi_ne Complex.I_ne_zero
  have hprefactor :
      hartogs_cauchy_extension f r₁ r₂ (z₁, w₂) =
        (((2 * Real.pi * Complex.I : ℂ) ^ (2 : ℕ))⁻¹ *
          ((2 * Real.pi * Complex.I : ℂ) *
            (∮ ζ₁ in C(0, r₁), f (ζ₁, w₂) / (ζ₁ - z₁)))) := by
    simp [hartogs_cauchy_extension, hdouble]
  -- Cancel one Cauchy factor from the defining prefactor `((2πi)^2)⁻¹`.
  calc
    hartogs_cauchy_extension f r₁ r₂ (z₁, w₂) =
        (((2 * Real.pi * Complex.I : ℂ) ^ (2 : ℕ))⁻¹ *
          ((2 * Real.pi * Complex.I : ℂ) *
            (∮ ζ₁ in C(0, r₁), f (ζ₁, w₂) / (ζ₁ - z₁)))) := hprefactor
    _ = ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
          ∮ ζ₁ in C(0, r₁), f (ζ₁, w₂) / (ζ₁ - z₁)) := by
          rw [pow_two, mul_inv_rev]
          calc
            ((2 * Real.pi * Complex.I : ℂ)⁻¹ * (2 * Real.pi * Complex.I : ℂ)⁻¹) *
                ((2 * Real.pi * Complex.I : ℂ) *
                  (∮ ζ₁ in C(0, r₁), f (ζ₁, w₂) / (ζ₁ - z₁))) =
                (2 * Real.pi * Complex.I : ℂ)⁻¹ *
                  (((2 * Real.pi * Complex.I : ℂ)⁻¹ * (2 * Real.pi * Complex.I : ℂ)) *
                    (∮ ζ₁ in C(0, r₁), f (ζ₁, w₂) / (ζ₁ - z₁))) := by
                  ac_rfl
            _ = ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
                  ∮ ζ₁ in C(0, r₁), f (ζ₁, w₂) / (ζ₁ - z₁)) := by
                  rw [inv_mul_cancel₀ htwo_pi_i_ne, one_mul]

/-- Helper for Remark IV.5-extra-3: for a fixed second coordinate inside the smaller second disc,
the boundary values on `|ζ₁| = r₁` lie in the Hartogs outer shell, so the corresponding `ζ₁`-slice
is continuous on that circle. -/
lemma hartogs_outer_boundary_left_section_continuousOn
    {f : (ℂ × ℂ) → ℂ} {ρ₁ ρ₂ ε r₁ r₂ : ℝ}
    (hcont : ContinuousOn f (hartogs_cross ρ₁ ρ₂ ε))
    (hr₁low : ρ₁ - ε < r₁) (hr₁high : r₁ < ρ₁) (hr₂high : r₂ < ρ₂)
    {w₂ : ℂ} (hw₂ : ‖w₂‖ < r₂) :
    ContinuousOn (fun ζ₁ : ℂ ↦ f (ζ₁, w₂)) (Metric.sphere (0 : ℂ) r₁) := by
  have hmap :
      MapsTo (fun ζ₁ : ℂ ↦ (ζ₁, w₂)) (Metric.sphere (0 : ℂ) r₁) (hartogs_cross ρ₁ ρ₂ ε) := by
    intro ζ₁ hζ₁
    have hζ₁_norm : ‖ζ₁‖ = r₁ := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hζ₁
    -- Every boundary point on `|ζ₁| = r₁` belongs to the outer shell because `w₂` stays in the
    -- smaller second disc and `r₁` lies in the Hartogs annulus.
    exact mem_hartogs_cross.mpr <| Or.inr <| by
      constructor
      · simpa [hζ₁_norm] using hr₁low
      constructor
      · simpa [hζ₁_norm] using hr₁high
      · exact lt_trans hw₂ hr₂high
  have hslice :
      ContinuousOn (fun ζ₁ : ℂ ↦ (ζ₁, w₂)) (Metric.sphere (0 : ℂ) r₁) := by
    simpa using
      (continuousOn_id.prodMk
        (continuousOn_const : ContinuousOn (fun _ : ℂ ↦ w₂) (Metric.sphere (0 : ℂ) r₁)))
  -- Restrict the ambient Hartogs-cross continuity along the fixed-`w₂` boundary slice.
  simpa using hcont.comp hslice hmap

/-- Helper for Remark IV.5-extra-3: for a fixed first coordinate inside the smaller first disc, the
outer-boundary transform in `ζ₂` is continuous on `|ζ₂| = r₂`. -/
lemma hartogs_outer_boundary_transform_continuousOn
    {f : (ℂ × ℂ) → ℂ} {ρ₁ ρ₂ ε r₁ r₂ : ℝ}
    (hcont : ContinuousOn f (hartogs_cross ρ₁ ρ₂ ε))
    (hr₁low : ρ₁ - ε < r₁) (hr₁high : r₁ < ρ₁) (hr₂high : r₂ < ρ₂)
    {w₁ : ℂ} (hw₁ : ‖w₁‖ < r₁) :
    ContinuousOn
      (fun ζ₂ : ℂ ↦
        ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
          ∮ ζ₁ in C(0, r₁), f (ζ₁, ζ₂) / (ζ₁ - w₁)))
      (Metric.sphere (0 : ℂ) r₂) := by
  let S : Set ℂ := Metric.sphere (0 : ℂ) r₂
  have hr₁pos : 0 < r₁ := lt_of_le_of_lt (norm_nonneg w₁) hw₁
  have hw₁_ball : w₁ ∈ Metric.ball (0 : ℂ) r₁ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw₁
  rw [continuousOn_iff_continuous_restrict]
  let K : S × ℝ → ℂ := fun p ↦
    deriv (circleMap (0 : ℂ) r₁) p.2 *
      (f (circleMap (0 : ℂ) r₁ p.2, (p.1 : ℂ)) / (circleMap (0 : ℂ) r₁ p.2 - w₁))
  have hmap :
      MapsTo
        (fun p : S × ℝ ↦ (circleMap (0 : ℂ) r₁ p.2, (p.1 : ℂ)))
        Set.univ (hartogs_cross ρ₁ ρ₂ ε) := by
    intro p hp
    have hζ₁_mem : circleMap (0 : ℂ) r₁ p.2 ∈ Metric.sphere (0 : ℂ) r₁ := by
      exact circleMap_mem_sphere (0 : ℂ) hr₁pos.le p.2
    have hζ₁_norm : ‖circleMap (0 : ℂ) r₁ p.2‖ = r₁ := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hζ₁_mem
    have hζ₂_norm : ‖((p.1 : S) : ℂ)‖ = r₂ := by
      have hp₁ : ((p.1 : S) : ℂ) ∈ Metric.sphere (0 : ℂ) r₂ := (p.1 : S).property
      rw [Metric.mem_sphere, dist_eq_norm] at hp₁
      simpa only [sub_zero] using hp₁
    -- Every parameter point lies on the Hartogs outer shell because `|ζ₁| = r₁` sits in the
    -- annulus and `|ζ₂| = r₂` stays below `ρ₂`.
    exact mem_hartogs_cross.mpr <| Or.inr <| by
      constructor
      · simpa [hζ₁_norm] using hr₁low
      constructor
      · simpa [hζ₁_norm] using hr₁high
      · simpa [hζ₂_norm] using hr₂high
  have hbase_cont :
      Continuous fun p : S × ℝ ↦ (circleMap (0 : ℂ) r₁ p.2, (p.1 : ℂ)) := by
    fun_prop
  have hnum_cont :
      Continuous fun p : S × ℝ ↦ f (circleMap (0 : ℂ) r₁ p.2, (p.1 : ℂ)) := by
    simpa using hcont.comp hbase_cont.continuousOn hmap
  have hden_inv_cont :
      Continuous fun p : S × ℝ ↦ (circleMap (0 : ℂ) r₁ p.2 - w₁)⁻¹ := by
    simpa using (continuous_circleMap_inv hw₁_ball).comp continuous_snd
  have hquot_cont :
      Continuous fun p : S × ℝ ↦
        f (circleMap (0 : ℂ) r₁ p.2, (p.1 : ℂ)) /
          (circleMap (0 : ℂ) r₁ p.2 - w₁) := by
    -- The denominator never vanishes on `|ζ₁| = r₁`, so division is continuous there.
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hnum_cont.mul hden_inv_cont
  have hkernel_cont :
      Continuous K := by
    -- The interval integrand is continuous in both the boundary parameter `ζ₂` and the angle `θ`.
    have hderiv_cont :
        Continuous fun p : S × ℝ ↦ deriv (circleMap (0 : ℂ) r₁) p.2 := by
      simpa [deriv_circleMap] using
        (((continuous_circleMap (0 : ℂ) r₁).comp continuous_snd).mul continuous_const)
    exact hderiv_cont.mul hquot_cont
  have hparam_cont :
      Continuous fun x : S ↦ ∫ θ in (0 : ℝ)..2 * Real.pi, K (x, θ) := by
    -- View the circle integral as a parametric interval integral over the angle variable.
    let K' : S → ℝ → ℂ := fun x θ ↦ K (x, θ)
    have hkernel_cont' : Continuous (Function.uncurry K') := by
      simpa [K'] using hkernel_cont
    simpa [K'] using
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        hkernel_cont' (0 : ℝ) (2 * Real.pi))
  -- Rewrite the restricted function as a scalar multiple of that parametric interval integral.
  have hscaled_cont :
      Continuous fun x : S ↦
        ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
          ∫ θ in (0 : ℝ)..2 * Real.pi, K (x, θ)) :=
    continuous_const.mul hparam_cont
  convert hscaled_cont using 1

/-- Helper for Remark IV.5-extra-3: after parametrizing both circles, the double Cauchy kernel for
the fixed-`w₁` right slice is integrable on the angular square, so the two interval integrals can
be swapped in the source proof. -/
lemma hartogs_right_slice_kernel_integrable
    {f : (ℂ × ℂ) → ℂ} {ρ₁ ρ₂ ε r₁ r₂ : ℝ}
    (hcont : ContinuousOn f (hartogs_cross ρ₁ ρ₂ ε))
    (hr₁low : ρ₁ - ε < r₁) (hr₁high : r₁ < ρ₁) (hr₂high : r₂ < ρ₂)
    {w₁ z₂ : ℂ} (hw₁ : ‖w₁‖ < r₁) (hz₂ : ‖z₂‖ < r₂) :
    let K : ℝ → ℝ → ℂ := fun θ₁ θ₂ ↦
      deriv (circleMap (0 : ℂ) r₁) θ₁ *
        deriv (circleMap (0 : ℂ) r₂) θ₂ *
          (f (circleMap (0 : ℂ) r₁ θ₁, circleMap (0 : ℂ) r₂ θ₂) /
            ((circleMap (0 : ℂ) r₁ θ₁ - w₁) * (circleMap (0 : ℂ) r₂ θ₂ - z₂)))
    MeasureTheory.Integrable (Function.uncurry K)
      ((MeasureTheory.volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 (2 * Real.pi)))) := by
  dsimp only
  let K : ℝ → ℝ → ℂ := fun θ₁ θ₂ ↦
    deriv (circleMap (0 : ℂ) r₁) θ₁ *
      deriv (circleMap (0 : ℂ) r₂) θ₂ *
        (f (circleMap (0 : ℂ) r₁ θ₁, circleMap (0 : ℂ) r₂ θ₂) /
          ((circleMap (0 : ℂ) r₁ θ₁ - w₁) * (circleMap (0 : ℂ) r₂ θ₂ - z₂)))
  have hr₁pos : 0 < r₁ := lt_of_le_of_lt (norm_nonneg w₁) hw₁
  have hr₂pos : 0 < r₂ := lt_of_le_of_lt (norm_nonneg z₂) hz₂
  have hw₁_ball : w₁ ∈ Metric.ball (0 : ℂ) r₁ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw₁
  have hz₂_ball : z₂ ∈ Metric.ball (0 : ℂ) r₂ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz₂
  let B : ℝ × ℝ → ℂ × ℂ := fun p ↦
    (circleMap (0 : ℂ) r₁ p.1, circleMap (0 : ℂ) r₂ p.2)
  have hmap : MapsTo B Set.univ (hartogs_cross ρ₁ ρ₂ ε) := by
    intro p hp
    have hζ₁_mem : circleMap (0 : ℂ) r₁ p.1 ∈ Metric.sphere (0 : ℂ) r₁ := by
      exact circleMap_mem_sphere (0 : ℂ) hr₁pos.le p.1
    have hζ₁_norm : ‖circleMap (0 : ℂ) r₁ p.1‖ = r₁ := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hζ₁_mem
    have hζ₂_mem : circleMap (0 : ℂ) r₂ p.2 ∈ Metric.sphere (0 : ℂ) r₂ := by
      exact circleMap_mem_sphere (0 : ℂ) hr₂pos.le p.2
    have hζ₂_norm : ‖circleMap (0 : ℂ) r₂ p.2‖ = r₂ := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hζ₂_mem
    -- Every point of the distinguished torus lies in the Hartogs outer shell.
    exact mem_hartogs_cross.mpr <| Or.inr <| by
      constructor
      · simpa [B, hζ₁_norm] using hr₁low
      constructor
      · simpa [B, hζ₁_norm] using hr₁high
      · simpa [B, hζ₂_norm] using hr₂high
  have hbase_cont : Continuous B := by
    fun_prop
  have hnum_cont : Continuous fun p : ℝ × ℝ ↦ f (B p) := by
    simpa [B] using hcont.comp hbase_cont.continuousOn hmap
  have hden₁_inv_cont :
      Continuous fun p : ℝ × ℝ ↦ (circleMap (0 : ℂ) r₁ p.1 - w₁)⁻¹ := by
    simpa using (continuous_circleMap_inv hw₁_ball).comp continuous_fst
  have hden₂_inv_cont :
      Continuous fun p : ℝ × ℝ ↦ (circleMap (0 : ℂ) r₂ p.2 - z₂)⁻¹ := by
    simpa using (continuous_circleMap_inv hz₂_ball).comp continuous_snd
  have hquot_cont :
      Continuous fun p : ℝ × ℝ ↦
        f (B p) /
          ((circleMap (0 : ℂ) r₁ p.1 - w₁) * (circleMap (0 : ℂ) r₂ p.2 - z₂)) := by
    -- The two poles stay strictly inside their respective circles, so the quotient is continuous.
    simpa [B, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using
      hden₁_inv_cont.mul (hden₂_inv_cont.mul hnum_cont)
  have hkernel_cont : Continuous (Function.uncurry K) := by
    have hderiv₁_cont :
        Continuous fun p : ℝ × ℝ ↦ circleMap (0 : ℂ) r₁ p.1 * Complex.I := by
      simpa using
        (((continuous_circleMap (0 : ℂ) r₁).comp continuous_fst).mul continuous_const)
    have hderiv₂_cont :
        Continuous fun p : ℝ × ℝ ↦ circleMap (0 : ℂ) r₂ p.2 * Complex.I := by
      simpa using
        (((continuous_circleMap (0 : ℂ) r₂).comp continuous_snd).mul continuous_const)
    -- The full kernel is a product of three continuous factors.
    have hkernel_cont' :
        Continuous fun p : ℝ × ℝ ↦
          (circleMap (0 : ℂ) r₁ p.1 * Complex.I) *
            ((circleMap (0 : ℂ) r₂ p.2 * Complex.I) *
              (f (B p) /
                ((circleMap (0 : ℂ) r₁ p.1 - w₁) * (circleMap (0 : ℂ) r₂ p.2 - z₂)))) :=
      hderiv₁_cont.mul (hderiv₂_cont.mul hquot_cont)
    simpa [Function.uncurry, K, B, deriv_circleMap, mul_assoc, mul_left_comm, mul_comm] using
      hkernel_cont'
  have hkernel_int :
      MeasureTheory.IntegrableOn (Function.uncurry K)
        (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi))
        (MeasureTheory.volume.prod MeasureTheory.volume) := by
    -- Continuity on the compact angular square gives the required integrability there.
    exact hkernel_cont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hkernel_int_uIoc :
      MeasureTheory.IntegrableOn (Function.uncurry K)
        (Set.uIoc (0 : ℝ) (2 * Real.pi) ×ˢ Set.uIoc (0 : ℝ) (2 * Real.pi))
        (MeasureTheory.volume.prod MeasureTheory.volume) := by
    -- The Fubini theorem only uses the half-open interval measure, which is a subset of the
    -- compact square just treated.
    refine hkernel_int.mono_set ?_
    intro p hp
    rcases hp with ⟨hp₁, hp₂⟩
    simp only [Set.uIoc_of_le Real.two_pi_pos.le, Set.mem_Ioc] at hp₁ hp₂ ⊢
    exact ⟨⟨le_of_lt hp₁.1, hp₁.2⟩, ⟨le_of_lt hp₂.1, hp₂.2⟩⟩
  -- Rewrite the compact-square statement in the exact measure form needed by
  -- `MeasureTheory.intervalIntegral_integral_swap`.
  rw [MeasureTheory.Measure.prod_restrict]
  simpa [MeasureTheory.IntegrableOn, K, deriv_circleMap, mul_assoc, mul_left_comm, mul_comm] using
    hkernel_int_uIoc

/-- Helper for Remark IV.5-extra-3: for a fixed second coordinate in the smaller second disc, the
local double Cauchy transform is analytic as a function of `z₁` on the first disc. -/
lemma hartogs_cauchy_extension_left_slice_analyticOnNhd_ball
    {f : (ℂ × ℂ) → ℂ} {ρ₁ ρ₂ ε r₁ r₂ : ℝ}
    (hcont : ContinuousOn f (hartogs_cross ρ₁ ρ₂ ε))
    (hhol₂ :
      ∀ w : ℂ, ρ₁ - ε < ‖w‖ → ‖w‖ < ρ₁ →
        DifferentiableOn ℂ (fun z ↦ f (w, z)) (Metric.ball (0 : ℂ) ρ₂))
    (hr₁low : ρ₁ - ε < r₁) (hr₁high : r₁ < ρ₁) (hr₂high : r₂ < ρ₂)
    {w₂ : ℂ} (hw₂ : ‖w₂‖ < r₂) :
    AnalyticOnNhd ℂ (fun z₁ ↦ hartogs_cauchy_extension f r₁ r₂ (z₁, w₂))
      (Metric.ball (0 : ℂ) r₁) := by
  by_cases hr₁pos : 0 < r₁
  · let ψ : ℂ → ℂ := fun ζ₁ ↦ f (ζ₁, w₂)
    let G : ℂ → ℂ := fun z₁ ↦
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ ζ₁ in C(0, r₁), (ζ₁ - z₁)⁻¹ • ψ ζ₁)
    have hψ_cont : ContinuousOn ψ (Metric.sphere (0 : ℂ) r₁) :=
      hartogs_outer_boundary_left_section_continuousOn hcont hr₁low hr₁high hr₂high hw₂
    have hψ_int : CircleIntegrable ψ (0 : ℂ) r₁ :=
      hψ_cont.circleIntegrable hr₁pos.le
    let r₁NN : NNReal := ⟨r₁, hr₁pos.le⟩
    have hG_analytic : AnalyticOnNhd ℂ G (Metric.ball (0 : ℂ) r₁) := by
      -- The fixed-`w₂` boundary slice is a standard one-variable Cauchy transform in `z₁`.
      simpa [G, ψ, r₁NN] using
        (hasFPowerSeriesOn_cauchy_integral (f := ψ) (c := (0 : ℂ)) (R := r₁NN)
          (by simpa [r₁NN] using hψ_int) (by simpa [r₁NN] using hr₁pos)).analyticOnNhd
    have hEq :
        Set.EqOn (fun z₁ ↦ hartogs_cauchy_extension f r₁ r₂ (z₁, w₂)) G
          (Metric.ball (0 : ℂ) r₁) := by
      intro z₁ hz₁
      have hz₁_norm : ‖z₁‖ < r₁ := by
        simpa [Metric.mem_ball, dist_eq_norm] using hz₁
      -- Insert the already computed inner `ζ₂`-integral, then rewrite the remaining expression as
      -- the standard one-variable Cauchy transform.
      calc
        hartogs_cauchy_extension f r₁ r₂ (z₁, w₂) =
            ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
              ∮ ζ₁ in C(0, r₁), f (ζ₁, w₂) / (ζ₁ - z₁)) :=
          hartogs_cauchy_extension_left_slice_formula hhol₂ hr₁low hr₁high hr₂high hz₁_norm hw₂
        _ = G z₁ := by
          simp [G, ψ, smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    have hEq_symm :
        Set.EqOn G (fun z₁ ↦ hartogs_cauchy_extension f r₁ r₂ (z₁, w₂))
          (Metric.ball (0 : ℂ) r₁) := by
      intro z₁ hz₁
      exact (hEq hz₁).symm
    intro z₁ hz₁
    -- Analyticity transfers from the standard Cauchy transform to the local Hartogs extension
    -- because the two functions agree throughout the whole first disc.
    exact (hG_analytic z₁ hz₁).congr <|
      hEq_symm.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hz₁)
  · intro z₁ hz₁
    have hfalse : False := by
      have hr₁nonpos : r₁ ≤ 0 := le_of_not_gt hr₁pos
      have hz₁_norm : ‖z₁‖ < r₁ := by
        simpa [Metric.mem_ball, dist_eq_norm] using hz₁
      have hnot : ¬ ‖z₁‖ < r₁ := by
        exact not_lt.mpr (le_trans hr₁nonpos (norm_nonneg z₁))
      exact hnot hz₁_norm
    exact hfalse.elim

/-- Helper for Remark IV.5-extra-3: after swapping the two angular integrals, the local double
Cauchy transform with fixed first coordinate becomes the standard one-variable Cauchy transform in
`z₂`. -/
lemma hartogs_cauchy_extension_right_slice_formula
    {f : (ℂ × ℂ) → ℂ} {ρ₁ ρ₂ ε r₁ r₂ : ℝ}
    (hcont : ContinuousOn f (hartogs_cross ρ₁ ρ₂ ε))
    (hr₁low : ρ₁ - ε < r₁) (hr₁high : r₁ < ρ₁) (hr₂high : r₂ < ρ₂)
    {w₁ z₂ : ℂ} (hw₁ : ‖w₁‖ < r₁) (hz₂ : ‖z₂‖ < r₂) :
    hartogs_cauchy_extension f r₁ r₂ (w₁, z₂) =
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ∮ ζ₂ in C(0, r₂),
          (((2 * Real.pi * Complex.I : ℂ)⁻¹ *
            ∮ ζ₁ in C(0, r₁), f (ζ₁, ζ₂) / (ζ₁ - w₁)) / (ζ₂ - z₂))) := by
  let K : ℝ → ℝ → ℂ := fun θ₁ θ₂ ↦
    deriv (circleMap (0 : ℂ) r₁) θ₁ *
      deriv (circleMap (0 : ℂ) r₂) θ₂ *
        (f (circleMap (0 : ℂ) r₁ θ₁, circleMap (0 : ℂ) r₂ θ₂) /
          ((circleMap (0 : ℂ) r₁ θ₁ - w₁) * (circleMap (0 : ℂ) r₂ θ₂ - z₂)))
  have hswap :
      ∫ θ₁ in (0 : ℝ)..2 * Real.pi, ∫ θ₂ in (0 : ℝ)..2 * Real.pi, K θ₁ θ₂ =
        ∫ θ₂ in (0 : ℝ)..2 * Real.pi, ∫ θ₁ in (0 : ℝ)..2 * Real.pi, K θ₁ θ₂ := by
    -- Fubini applies because the parametrized double kernel is integrable on the angular square.
    simpa [intervalIntegral.integral_of_le Real.two_pi_pos.le,
      Set.uIoc_of_le Real.two_pi_pos.le] using
      MeasureTheory.intervalIntegral_integral_swap
        (μ := MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi)))
        (a := (0 : ℝ)) (b := 2 * Real.pi) (f := K)
        (hartogs_right_slice_kernel_integrable hcont hr₁low hr₁high hr₂high hw₁ hz₂)
  -- Unfold both circle integrals, swap the interval order once, and repack the result as the
  -- one-variable Cauchy transform in the second variable.
  calc
    hartogs_cauchy_extension f r₁ r₂ (w₁, z₂) =
        (((2 * Real.pi * Complex.I : ℂ) ^ (2 : ℕ))⁻¹ *
          ∫ θ₁ in (0 : ℝ)..2 * Real.pi, ∫ θ₂ in (0 : ℝ)..2 * Real.pi, K θ₁ θ₂) := by
            simp [hartogs_cauchy_extension, circleIntegral, K, smul_eq_mul, div_eq_mul_inv,
              mul_assoc, mul_left_comm, mul_comm]
    _ = (((2 * Real.pi * Complex.I : ℂ) ^ (2 : ℕ))⁻¹ *
          ∫ θ₂ in (0 : ℝ)..2 * Real.pi, ∫ θ₁ in (0 : ℝ)..2 * Real.pi, K θ₁ θ₂) := by
            rw [hswap]
    _ = ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
          ∮ ζ₂ in C(0, r₂),
            (((2 * Real.pi * Complex.I : ℂ)⁻¹ *
              ∮ ζ₁ in C(0, r₁), f (ζ₁, ζ₂) / (ζ₁ - w₁)) / (ζ₂ - z₂))) := by
            have hinner :
                ∀ θ₂ : ℝ,
                  ∫ θ₁ in (0 : ℝ)..2 * Real.pi, K θ₁ θ₂ =
                    (deriv (circleMap (0 : ℂ) r₂) θ₂ * (circleMap (0 : ℂ) r₂ θ₂ - z₂)⁻¹) *
                      ∮ ζ₁ in C(0, r₁), f (ζ₁, circleMap (0 : ℂ) r₂ θ₂) / (ζ₁ - w₁) := by
              intro θ₂
              calc
                ∫ θ₁ in (0 : ℝ)..2 * Real.pi, K θ₁ θ₂ =
                    ∫ θ₁ in (0 : ℝ)..2 * Real.pi,
                      (deriv (circleMap (0 : ℂ) r₂) θ₂ * (circleMap (0 : ℂ) r₂ θ₂ - z₂)⁻¹) *
                        (deriv (circleMap (0 : ℂ) r₁) θ₁ *
                          (f (circleMap (0 : ℂ) r₁ θ₁, circleMap (0 : ℂ) r₂ θ₂) /
                            (circleMap (0 : ℂ) r₁ θ₁ - w₁))) := by
                      apply intervalIntegral.integral_congr
                      intro θ₁ hθ₁
                      simp [K, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
                _ =
                    (deriv (circleMap (0 : ℂ) r₂) θ₂ * (circleMap (0 : ℂ) r₂ θ₂ - z₂)⁻¹) *
                      ∫ θ₁ in (0 : ℝ)..2 * Real.pi,
                        deriv (circleMap (0 : ℂ) r₁) θ₁ *
                          (f (circleMap (0 : ℂ) r₁ θ₁, circleMap (0 : ℂ) r₂ θ₂) /
                            (circleMap (0 : ℂ) r₁ θ₁ - w₁)) := by
                      rw [intervalIntegral.integral_const_mul]
                _ =
                    (deriv (circleMap (0 : ℂ) r₂) θ₂ * (circleMap (0 : ℂ) r₂ θ₂ - z₂)⁻¹) *
                      ∮ ζ₁ in C(0, r₁), f (ζ₁, circleMap (0 : ℂ) r₂ θ₂) / (ζ₁ - w₁) := by
                      rfl
            calc
              (((2 * Real.pi * Complex.I : ℂ) ^ (2 : ℕ))⁻¹ *
                  ∫ θ₂ in (0 : ℝ)..2 * Real.pi, ∫ θ₁ in (0 : ℝ)..2 * Real.pi, K θ₁ θ₂) =
                  (((2 * Real.pi * Complex.I : ℂ) ^ (2 : ℕ))⁻¹ *
                    ∫ θ₂ in (0 : ℝ)..2 * Real.pi,
                      (deriv (circleMap (0 : ℂ) r₂) θ₂ * (circleMap (0 : ℂ) r₂ θ₂ - z₂)⁻¹) *
                        ∮ ζ₁ in C(0, r₁), f (ζ₁, circleMap (0 : ℂ) r₂ θ₂) / (ζ₁ - w₁)) := by
                    congr 1
                    apply intervalIntegral.integral_congr
                    intro θ₂ hθ₂
                    exact hinner θ₂
              _ = ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
                    ∮ ζ₂ in C(0, r₂),
                      (((2 * Real.pi * Complex.I : ℂ)⁻¹ *
                        ∮ ζ₁ in C(0, r₁), f (ζ₁, ζ₂) / (ζ₁ - w₁)) / (ζ₂ - z₂))) := by
                    rw [circleIntegral]
                    simp [pow_two, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]
                    rw [← intervalIntegral.integral_const_mul]
                    apply intervalIntegral.integral_congr
                    intro x hx
                    ac_rfl

/-- Helper for Remark IV.5-extra-3: for a fixed first coordinate in the smaller first disc, the
local double Cauchy transform is analytic as a function of `z₂` on the second disc. -/
lemma hartogs_cauchy_extension_right_slice_analyticOnNhd_ball
    {f : (ℂ × ℂ) → ℂ} {ρ₁ ρ₂ ε r₁ r₂ : ℝ}
    (hcont : ContinuousOn f (hartogs_cross ρ₁ ρ₂ ε))
    (hr₁low : ρ₁ - ε < r₁) (hr₁high : r₁ < ρ₁) (hr₂high : r₂ < ρ₂)
    {w₁ : ℂ} (hw₁ : ‖w₁‖ < r₁) :
    AnalyticOnNhd ℂ (fun z₂ ↦ hartogs_cauchy_extension f r₁ r₂ (w₁, z₂))
      (Metric.ball (0 : ℂ) r₂) := by
  by_cases hr₂pos : 0 < r₂
  · let ψ : ℂ → ℂ := fun ζ₂ ↦
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ∮ ζ₁ in C(0, r₁), f (ζ₁, ζ₂) / (ζ₁ - w₁))
    let G : ℂ → ℂ := fun z₂ ↦
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ ζ₂ in C(0, r₂), (ζ₂ - z₂)⁻¹ • ψ ζ₂)
    have hψ_cont : ContinuousOn ψ (Metric.sphere (0 : ℂ) r₂) :=
      hartogs_outer_boundary_transform_continuousOn hcont hr₁low hr₁high hr₂high hw₁
    have hψ_int : CircleIntegrable ψ (0 : ℂ) r₂ :=
      hψ_cont.circleIntegrable hr₂pos.le
    let r₂NN : NNReal := ⟨r₂, hr₂pos.le⟩
    have hG_analytic : AnalyticOnNhd ℂ G (Metric.ball (0 : ℂ) r₂) := by
      -- The fixed-`w₁` boundary transform in `ζ₂` is a standard Cauchy transform.
      simpa [G, ψ, r₂NN] using
        (hasFPowerSeriesOn_cauchy_integral (f := ψ) (c := (0 : ℂ)) (R := r₂NN)
          (by simpa [r₂NN] using hψ_int) (by simpa [r₂NN] using hr₂pos)).analyticOnNhd
    have hEq :
        Set.EqOn (fun z₂ ↦ hartogs_cauchy_extension f r₁ r₂ (w₁, z₂)) G
          (Metric.ball (0 : ℂ) r₂) := by
      intro z₂ hz₂
      have hz₂_norm : ‖z₂‖ < r₂ := by
        simpa [Metric.mem_ball, dist_eq_norm] using hz₂
      -- Rewrite the local extension as the one-variable `z₂` Cauchy transform built from `ψ`.
      calc
        hartogs_cauchy_extension f r₁ r₂ (w₁, z₂) =
            ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
              ∮ ζ₂ in C(0, r₂),
                (((2 * Real.pi * Complex.I : ℂ)⁻¹ *
                  ∮ ζ₁ in C(0, r₁), f (ζ₁, ζ₂) / (ζ₁ - w₁)) / (ζ₂ - z₂))) :=
          hartogs_cauchy_extension_right_slice_formula hcont hr₁low hr₁high hr₂high hw₁ hz₂_norm
        _ = G z₂ := by
          simp [G, ψ, smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    have hEq_symm :
        Set.EqOn G (fun z₂ ↦ hartogs_cauchy_extension f r₁ r₂ (w₁, z₂))
          (Metric.ball (0 : ℂ) r₂) := by
      intro z₂ hz₂
      exact (hEq hz₂).symm
    intro z₂ hz₂
    -- Analyticity transfers from the standard `z₂` Cauchy transform to the Hartogs extension
    -- because the two functions agree throughout the whole second disc.
    exact (hG_analytic z₂ hz₂).congr <|
      hEq_symm.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hz₂)
  · intro z₂ hz₂
    have hfalse : False := by
      have hr₂nonpos : r₂ ≤ 0 := le_of_not_gt hr₂pos
      have hz₂_norm : ‖z₂‖ < r₂ := by
        simpa [Metric.mem_ball, dist_eq_norm] using hz₂
      have hnot : ¬ ‖z₂‖ < r₂ := by
        exact not_lt.mpr (le_trans hr₂nonpos (norm_nonneg z₂))
      exact hnot hz₂_norm
    exact hfalse.elim

/-- Helper for Remark IV.5-extra-3: on the inner tube, the local double Cauchy transform recovers
the original function by a second one-variable Cauchy evaluation in `ζ₁`. -/
lemma hartogs_cauchy_extension_eqOn_inner_tube
    {f : (ℂ × ℂ) → ℂ} {ρ₁ ρ₂ ε r₁ r₂ : ℝ}
    (hhol₁ :
      ∀ w : ℂ, ‖w‖ < ε →
        DifferentiableOn ℂ (fun z ↦ f (z, w)) (Metric.ball (0 : ℂ) ρ₁))
    (hhol₂ :
      ∀ w : ℂ, ρ₁ - ε < ‖w‖ → ‖w‖ < ρ₁ →
        DifferentiableOn ℂ (fun z ↦ f (w, z)) (Metric.ball (0 : ℂ) ρ₂))
    (hr₁low : ρ₁ - ε < r₁) (hr₁high : r₁ < ρ₁) (hr₂low : ε < r₂) (hr₂high : r₂ < ρ₂) :
    Set.EqOn (hartogs_cauchy_extension f r₁ r₂) f (hartogs_inner_tube r₁ ε) := by
  intro z hz
  rcases mem_hartogs_inner_tube.mp hz with ⟨hz₁, hz₂⟩
  have hz₂r₂ : ‖z.2‖ < r₂ := lt_trans hz₂ hr₂low
  have hr₁pos : 0 < r₁ := lt_of_le_of_lt (norm_nonneg z.1) hz₁
  have hz₁_ball : z.1 ∈ Metric.ball (0 : ℂ) r₁ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz₁
  have hleft_slice :
      DifferentiableOn ℂ (fun ζ₁ ↦ f (ζ₁, z.2)) (Metric.closedBall (0 : ℂ) r₁) :=
    (hhol₁ z.2 hz₂).mono fun ζ₁ hζ₁ ↦ by
      have hζ₁_le : ‖ζ₁‖ ≤ r₁ := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hζ₁
      simpa [Metric.mem_ball, dist_eq_norm] using lt_of_le_of_lt hζ₁_le hr₁high
  have houter_cauchy :
      (∮ ζ₁ in C(0, r₁), f (ζ₁, z.2) / (ζ₁ - z.1)) =
        (2 * Real.pi * Complex.I : ℂ) * f z := by
    have houter_cauchy' :
        (∮ ζ₁ in C(0, r₁), (ζ₁ - z.1)⁻¹ * f (ζ₁, z.2)) =
          (2 * Real.pi * Complex.I : ℂ) * f z := by
      -- The inner-tube hypothesis gives the textbook one-variable Cauchy formula in `z₁`.
      simpa [smul_eq_mul] using
        (hleft_slice.circleIntegral_sub_inv_smul (c := 0) (R := r₁) (w := z.1) hz₁_ball)
    calc
      (∮ ζ₁ in C(0, r₁), f (ζ₁, z.2) / (ζ₁ - z.1)) =
          ∮ ζ₁ in C(0, r₁), (ζ₁ - z.1)⁻¹ * f (ζ₁, z.2) := by
            apply circleIntegral.integral_congr hr₁pos.le
            intro ζ₁ hζ₁
            simp [div_eq_mul_inv, mul_comm]
      _ = (2 * Real.pi * Complex.I : ℂ) * f z := houter_cauchy'
  have htwo_pi_i_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    have htwo_pi_ne : (2 * Real.pi : ℂ) ≠ 0 := by
      refine mul_ne_zero ?_ ?_
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero htwo_pi_ne Complex.I_ne_zero
  -- This is the source proof on `|z₂| < ε`: first rewrite the double integral, then apply the
  -- one-variable Cauchy formula in `ζ₁`.
  calc
    hartogs_cauchy_extension f r₁ r₂ z =
        ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
          ∮ ζ₁ in C(0, r₁), f (ζ₁, z.2) / (ζ₁ - z.1)) :=
      hartogs_cauchy_extension_left_slice_formula hhol₂ hr₁low hr₁high hr₂high hz₁ hz₂r₂
    _ = ((2 * Real.pi * Complex.I : ℂ)⁻¹ * ((2 * Real.pi * Complex.I : ℂ) * f z)) := by
          rw [houter_cauchy]
    _ = f z := by
          rw [← mul_assoc, inv_mul_cancel₀ htwo_pi_i_ne, one_mul]

/-- Helper for Remark IV.5-extra-3: each admissible local double Cauchy transform is analytic on
its bidisc. -/
lemma hartogs_cauchy_extension_analyticOnNhd_bidisc
    {f : (ℂ × ℂ) → ℂ} {ρ₁ ρ₂ ε r₁ r₂ : ℝ}
    (hcont : ContinuousOn f (hartogs_cross ρ₁ ρ₂ ε))
    (_hhol₁ :
      ∀ w : ℂ, ‖w‖ < ε →
        DifferentiableOn ℂ (fun z ↦ f (z, w)) (Metric.ball (0 : ℂ) ρ₁))
    (hhol₂ :
      ∀ w : ℂ, ρ₁ - ε < ‖w‖ → ‖w‖ < ρ₁ →
        DifferentiableOn ℂ (fun z ↦ f (w, z)) (Metric.ball (0 : ℂ) ρ₂))
    (hr₁low : ρ₁ - ε < r₁) (hr₁high : r₁ < ρ₁) (_hr₂low : ε < r₂) (hr₂high : r₂ < ρ₂) :
    AnalyticOnNhd ℂ (hartogs_cauchy_extension f r₁ r₂) (bidisc r₁ r₂) := by
  -- Route correction: instead of unfolding the double integral globally, prove analyticity by
  -- treating the extension as separately analytic on the two coordinate discs and then applying
  -- the Hartogs/Osgood upgrade on `Fin 2`.
  have hleft :
      ∀ w₂ : ℂ, ‖w₂‖ < r₂ →
        AnalyticOnNhd ℂ (fun z₁ ↦ hartogs_cauchy_extension f r₁ r₂ (z₁, w₂))
          (Metric.ball (0 : ℂ) r₁) := by
    intro w₂ hw₂
    -- The `z₁`-slice is already the one-variable Cauchy transform from the previous lemma.
    exact hartogs_cauchy_extension_left_slice_analyticOnNhd_ball hcont hhol₂
      hr₁low hr₁high hr₂high hw₂
  have hright :
      ∀ w₁ : ℂ, ‖w₁‖ < r₁ →
        AnalyticOnNhd ℂ (fun z₂ ↦ hartogs_cauchy_extension f r₁ r₂ (w₁, z₂))
          (Metric.ball (0 : ℂ) r₂) := by
    intro w₁ hw₁
    -- The fixed-`z₁` slice is the symmetric one-variable Cauchy transform in `z₂`.
    exact hartogs_cauchy_extension_right_slice_analyticOnNhd_ball hcont
      hr₁low hr₁high hr₂high hw₁
  let D : Set (Fin 2 → ℂ) := {x | ‖x 0‖ < r₁ ∧ ‖x 1‖ < r₂}
  let G : (Fin 2 → ℂ) → ℂ := fun x ↦ hartogs_cauchy_extension f r₁ r₂ (x 0, x 1)
  have hD : IsOpen D := by
    have h0 : IsOpen {x : Fin 2 → ℂ | ‖x 0‖ < r₁} := by
      simpa using isOpen_lt ((continuous_apply 0).norm) continuous_const
    have h1 : IsOpen {x : Fin 2 → ℂ | ‖x 1‖ < r₂} := by
      simpa using isOpen_lt ((continuous_apply 1).norm) continuous_const
    simpa [D, Set.setOf_and] using h0.inter h1
  have hsep : ∀ x ∈ D, ∀ i : Fin 2, AnalyticAt ℂ (fun w ↦ G (Function.update x i w)) (x i) := by
    intro x hx i
    rcases hx with ⟨hx₀, hx₁⟩
    fin_cases i
    · have hslice : AnalyticOnNhd ℂ (fun z₁ ↦ hartogs_cauchy_extension f r₁ r₂ (z₁, x 1))
          (Metric.ball (0 : ℂ) r₁) := hleft (x 1) hx₁
      have hx₀_ball : x 0 ∈ Metric.ball (0 : ℂ) r₁ := by
        simpa [Metric.mem_ball, dist_eq_norm] using hx₀
      -- Updating the first coordinate reproduces the `z₁`-slice from `hleft`.
      simpa [G] using hslice (x 0) hx₀_ball
    · have hslice : AnalyticOnNhd ℂ (fun z₂ ↦ hartogs_cauchy_extension f r₁ r₂ (x 0, z₂))
          (Metric.ball (0 : ℂ) r₂) := hright (x 0) hx₀
      have hx₁_ball : x 1 ∈ Metric.ball (0 : ℂ) r₂ := by
        simpa [Metric.mem_ball, dist_eq_norm] using hx₁
      -- Updating the second coordinate reproduces the `z₂`-slice from `hright`.
      simpa [G] using hslice (x 1) hx₁_ball
  have hG : AnalyticOnNhd ℂ G D := separately_holomorphic_analyticOnNhd hD hsep
  let φ : ℂ × ℂ → Fin 2 → ℂ := fun p ↦ ![p.1, p.2]
  have hφ : AnalyticOnNhd ℂ φ (bidisc r₁ r₂) := by
    refine (analyticOnNhd_pi_iff :
      AnalyticOnNhd ℂ (fun p : ℂ × ℂ ↦ fun i : Fin 2 ↦ φ p i) (bidisc r₁ r₂) ↔
        ∀ i : Fin 2, AnalyticOnNhd ℂ (fun p : ℂ × ℂ ↦ φ p i) (bidisc r₁ r₂)).2 ?_
    intro i
    fin_cases i
    · simpa [φ] using
        (analyticOnNhd_fst (𝕜 := ℂ) (E := ℂ) (F := ℂ) (t := bidisc r₁ r₂))
    · simpa [φ] using
        (analyticOnNhd_snd (𝕜 := ℂ) (E := ℂ) (F := ℂ) (t := bidisc r₁ r₂))
  have hφmap : MapsTo φ (bidisc r₁ r₂) D := by
    intro p hp
    simpa [φ, D, mem_bidisc] using hp
  -- Compose the `Fin 2` Hartogs conclusion with the product-coordinate map `(z₁,z₂) ↦ ![z₁,z₂]`.
  simpa [G, φ, Function.comp] using hG.comp hφ hφmap

/-- Helper for Remark IV.5-extra-3: each admissible local double Cauchy transform agrees with the
original function on the corresponding local Hartogs cross. -/
lemma hartogs_cauchy_extension_eqOn_local_cross
    {f : (ℂ × ℂ) → ℂ} {ρ₁ ρ₂ ε r₁ r₂ : ℝ}
    (hcont : ContinuousOn f (hartogs_cross ρ₁ ρ₂ ε))
    (hhol₁ :
      ∀ w : ℂ, ‖w‖ < ε →
        DifferentiableOn ℂ (fun z ↦ f (z, w)) (Metric.ball (0 : ℂ) ρ₁))
    (hhol₂ :
      ∀ w : ℂ, ρ₁ - ε < ‖w‖ → ‖w‖ < ρ₁ →
        DifferentiableOn ℂ (fun z ↦ f (w, z)) (Metric.ball (0 : ℂ) ρ₂))
    (hr₁low : ρ₁ - ε < r₁) (hr₁high : r₁ < ρ₁) (hr₂low : ε < r₂) (hr₂high : r₂ < ρ₂) :
    Set.EqOn (hartogs_cauchy_extension f r₁ r₂) f
      ((hartogs_cross ρ₁ ρ₂ ε) ∩ bidisc r₁ r₂) := by
  intro z hz
  rcases hz with ⟨hz_cross, hz_local⟩
  rcases mem_bidisc.mp hz_local with ⟨hz₁_local, hz₂_local⟩
  rcases mem_hartogs_cross.mp hz_cross with hz_inner | hz_outer
  · -- The inner tube is the direct two-step Cauchy computation from the source text.
    exact hartogs_cauchy_extension_eqOn_inner_tube hhol₁ hhol₂
      hr₁low hr₁high hr₂low hr₂high (mem_hartogs_inner_tube.mpr ⟨hz₁_local, hz_inner.2⟩)
  · -- Route correction: the remaining shell case must use analytic continuation in `z₂` from the
    -- already proved inner-tube equality, not a fresh local recursion on the double integral.
    let g : ℂ → ℂ := fun w ↦ hartogs_cauchy_extension f r₁ r₂ (z.1, w)
    let h : ℂ → ℂ := fun w ↦ f (z.1, w)
    have hε : 0 < ε := by
      linarith [hr₁low, hr₁high]
    have hr₂pos : 0 < r₂ := lt_trans hε hr₂low
    have hg : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) r₂) :=
      hartogs_cauchy_extension_right_slice_analyticOnNhd_ball hcont
        hr₁low hr₁high hr₂high hz₁_local
    have hh : AnalyticOnNhd ℂ h (Metric.ball (0 : ℂ) r₂) :=
      ((hhol₂ z.1 hz_outer.1 hz_outer.2.1).analyticOnNhd Metric.isOpen_ball).mono <| by
        intro w hw
        have hw_norm : ‖w‖ < r₂ := by
          simpa [Metric.mem_ball, dist_eq_norm] using hw
        simpa [Metric.mem_ball, dist_eq_norm] using lt_trans hw_norm hr₂high
    have hEq_inner : Set.EqOn g h (Metric.ball (0 : ℂ) ε) := by
      intro w hw
      have hwε : ‖w‖ < ε := by
        simpa [Metric.mem_ball, dist_eq_norm] using hw
      -- On the smaller `|z₂| < ε` tube, the previous inner-tube computation already identifies
      -- the local extension with the original function.
      have hinner :
          hartogs_cauchy_extension f r₁ r₂ (z.1, w) = f (z.1, w) :=
        hartogs_cauchy_extension_eqOn_inner_tube hhol₁ hhol₂
          hr₁low hr₁high hr₂low hr₂high
          (mem_hartogs_inner_tube.mpr ⟨hz₁_local, hwε⟩)
      simpa [g, h] using hinner
    have hz₀D : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r₂ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hr₂pos
    have hz₀U : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ε := by
      simpa [Metric.mem_ball, dist_eq_norm] using hε
    have hEq_nhds : g =ᶠ[𝓝 (0 : ℂ)] h :=
      hEq_inner.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hz₀U)
    have hEq_all : Set.EqOn g h (Metric.ball (0 : ℂ) r₂) :=
      hg.eqOn_of_preconnected_of_eventuallyEq hh Metric.isPreconnected_ball
        hz₀D hEq_nhds
    -- The shell point lies in the larger `|z₂| < r₂` disc, so the analytic continuation equality
    -- applies at its second coordinate.
    exact hEq_all (by simpa [Metric.mem_ball, dist_eq_norm] using hz₂_local)

/-- Helper for Remark IV.5-extra-3: two admissible local double Cauchy transforms agree on their
common overlap. -/
lemma hartogs_cauchy_extensions_agree_on_overlap
    {f : (ℂ × ℂ) → ℂ} {ρ₁ ρ₂ ε r₁ r₂ r₁' r₂' : ℝ} {z : ℂ × ℂ}
    (hcont : ContinuousOn f (hartogs_cross ρ₁ ρ₂ ε))
    (hhol₁ :
      ∀ w : ℂ, ‖w‖ < ε →
        DifferentiableOn ℂ (fun z ↦ f (z, w)) (Metric.ball (0 : ℂ) ρ₁))
    (hhol₂ :
      ∀ w : ℂ, ρ₁ - ε < ‖w‖ → ‖w‖ < ρ₁ →
        DifferentiableOn ℂ (fun z ↦ f (w, z)) (Metric.ball (0 : ℂ) ρ₂))
    (hr₁low : ρ₁ - ε < r₁) (hr₁high : r₁ < ρ₁) (hr₂low : ε < r₂) (hr₂high : r₂ < ρ₂)
    (hr₁low' : ρ₁ - ε < r₁') (hr₁high' : r₁' < ρ₁) (hr₂low' : ε < r₂') (hr₂high' : r₂' < ρ₂)
    (hz₁ : ‖z.1‖ < min r₁ r₁') (hz₂ : ‖z.2‖ < min r₂ r₂') :
    hartogs_cauchy_extension f r₁ r₂ z = hartogs_cauchy_extension f r₁' r₂' z := by
  let u₁ : ℝ := min r₁ r₁'
  let u₂ : ℝ := min r₂ r₂'
  let a : ℝ := max ‖z.1‖ (ρ₁ - ε)
  let b : ℝ := max ‖z.2‖ ε
  have hu₁_gt : ρ₁ - ε < u₁ := lt_min hr₁low hr₁low'
  have hu₂_gt : ε < u₂ := lt_min hr₂low hr₂low'
  have ha_lt : a < u₁ := by
    refine max_lt hz₁ hu₁_gt
  have hb_lt : b < u₂ := by
    refine max_lt hz₂ hu₂_gt
  let s₁ : ℝ := (a + u₁) / 2
  let s₂ : ℝ := (b + u₂) / 2
  have hs₁_gt : ρ₁ - ε < s₁ := by
    have hρ₁a : ρ₁ - ε ≤ a := le_max_right ‖z.1‖ (ρ₁ - ε)
    dsimp [s₁]
    linarith
  have hs₂_gt : ε < s₂ := by
    have hεb : ε ≤ b := le_max_right ‖z.2‖ ε
    dsimp [s₂]
    linarith
  have hs₁_lt_u₁ : s₁ < u₁ := by
    dsimp [s₁]
    linarith
  have hs₂_lt_u₂ : s₂ < u₂ := by
    dsimp [s₂]
    linarith
  have hs₁_lt_r₁ : s₁ < r₁ := lt_of_lt_of_le hs₁_lt_u₁ (min_le_left _ _)
  have hs₁_lt_r₁' : s₁ < r₁' := lt_of_lt_of_le hs₁_lt_u₁ (min_le_right _ _)
  have hs₂_lt_r₂ : s₂ < r₂ := lt_of_lt_of_le hs₂_lt_u₂ (min_le_left _ _)
  have hs₂_lt_r₂' : s₂ < r₂' := lt_of_lt_of_le hs₂_lt_u₂ (min_le_right _ _)
  have hs₁_lt_ρ₁ : s₁ < ρ₁ := lt_of_lt_of_le hs₁_lt_r₁ hr₁high.le
  have hs₂_lt_ρ₂ : s₂ < ρ₂ := lt_of_lt_of_le hs₂_lt_r₂ hr₂high.le
  have hz₁s : ‖z.1‖ < s₁ := by
    have hz₁a : ‖z.1‖ ≤ a := le_max_left ‖z.1‖ (ρ₁ - ε)
    dsimp [s₁]
    linarith
  have hz₂s : ‖z.2‖ < s₂ := by
    have hz₂b : ‖z.2‖ ≤ b := le_max_left ‖z.2‖ ε
    dsimp [s₂]
    linarith
  have hs₁pos : 0 < s₁ := lt_of_le_of_lt (norm_nonneg z.1) hz₁s
  have hs₂pos : 0 < s₂ := lt_of_le_of_lt (norm_nonneg z.2) hz₂s
  have hanalytic₁ :
      AnalyticOnNhd ℂ (hartogs_cauchy_extension f r₁ r₂) (bidisc r₁ r₂) :=
    hartogs_cauchy_extension_analyticOnNhd_bidisc hcont hhol₁ hhol₂
      hr₁low hr₁high hr₂low hr₂high
  have hanalytic₂ :
      AnalyticOnNhd ℂ (hartogs_cauchy_extension f r₁' r₂') (bidisc r₁' r₂') :=
    hartogs_cauchy_extension_analyticOnNhd_bidisc hcont hhol₁ hhol₂
      hr₁low' hr₁high' hr₂low' hr₂high'
  have hformula₁ :
      hartogs_cauchy_extension f r₁ r₂ z =
        (((2 * Real.pi * Complex.I : ℂ) ^ (2 : ℕ))⁻¹ *
          ∮ ζ₁ in C(0, s₁), ∮ ζ₂ in C(0, s₂),
            hartogs_cauchy_extension f r₁ r₂ (ζ₁, ζ₂) /
              ((ζ₁ - z.1) * (ζ₂ - z.2))) :=
    cauchy_integral_formula_two_variables_on_bidisc
      (f := hartogs_cauchy_extension f r₁ r₂) (ρ₁ := r₁) (ρ₂ := r₂)
      (r₁ := s₁) (r₂ := s₂) (z := z)
      hs₁_lt_r₁ hs₂_lt_r₂ hz₁s hz₂s hanalytic₁.differentiableOn
  have hformula₂ :
      hartogs_cauchy_extension f r₁' r₂' z =
        (((2 * Real.pi * Complex.I : ℂ) ^ (2 : ℕ))⁻¹ *
          ∮ ζ₁ in C(0, s₁), ∮ ζ₂ in C(0, s₂),
            hartogs_cauchy_extension f r₁' r₂' (ζ₁, ζ₂) /
              ((ζ₁ - z.1) * (ζ₂ - z.2))) :=
    cauchy_integral_formula_two_variables_on_bidisc
      (f := hartogs_cauchy_extension f r₁' r₂') (ρ₁ := r₁') (ρ₂ := r₂')
      (r₁ := s₁) (r₂ := s₂) (z := z)
      hs₁_lt_r₁' hs₂_lt_r₂' hz₁s hz₂s hanalytic₂.differentiableOn
  have hboundary₁ :
      (((2 * Real.pi * Complex.I : ℂ) ^ (2 : ℕ))⁻¹ *
        ∮ ζ₁ in C(0, s₁), ∮ ζ₂ in C(0, s₂),
          hartogs_cauchy_extension f r₁ r₂ (ζ₁, ζ₂) /
            ((ζ₁ - z.1) * (ζ₂ - z.2))) =
        (((2 * Real.pi * Complex.I : ℂ) ^ (2 : ℕ))⁻¹ *
          ∮ ζ₁ in C(0, s₁), ∮ ζ₂ in C(0, s₂),
            f (ζ₁, ζ₂) / ((ζ₁ - z.1) * (ζ₂ - z.2))) := by
    congr 1
    apply circleIntegral.integral_congr hs₁pos.le
    intro ζ₁ hζ₁
    apply circleIntegral.integral_congr hs₂pos.le
    intro ζ₂ hζ₂
    have hζ₁_norm : ‖ζ₁‖ = s₁ := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hζ₁
    have hζ₂_norm : ‖ζ₂‖ = s₂ := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hζ₂
    have hcross :
        (ζ₁, ζ₂) ∈ (hartogs_cross ρ₁ ρ₂ ε) ∩ bidisc r₁ r₂ := by
      constructor
      · exact mem_hartogs_cross.mpr <| Or.inr <| by
          constructor
          · simpa [hζ₁_norm] using hs₁_gt
          constructor
          · simpa [hζ₁_norm] using hs₁_lt_ρ₁
          · simpa [hζ₂_norm] using hs₂_lt_ρ₂
      · exact mem_bidisc.mpr <| by
          constructor
          · simpa [hζ₁_norm] using hs₁_lt_r₁
          · simpa [hζ₂_norm] using hs₂_lt_r₂
    -- On the common distinguished torus, the first local extension matches the original boundary
    -- data `f`.
    simp [hartogs_cauchy_extension_eqOn_local_cross hcont hhol₁ hhol₂
      hr₁low hr₁high hr₂low hr₂high hcross]
  have hboundary₂ :
      (((2 * Real.pi * Complex.I : ℂ) ^ (2 : ℕ))⁻¹ *
        ∮ ζ₁ in C(0, s₁), ∮ ζ₂ in C(0, s₂),
          hartogs_cauchy_extension f r₁' r₂' (ζ₁, ζ₂) /
            ((ζ₁ - z.1) * (ζ₂ - z.2))) =
        (((2 * Real.pi * Complex.I : ℂ) ^ (2 : ℕ))⁻¹ *
          ∮ ζ₁ in C(0, s₁), ∮ ζ₂ in C(0, s₂),
            f (ζ₁, ζ₂) / ((ζ₁ - z.1) * (ζ₂ - z.2))) := by
    congr 1
    apply circleIntegral.integral_congr hs₁pos.le
    intro ζ₁ hζ₁
    apply circleIntegral.integral_congr hs₂pos.le
    intro ζ₂ hζ₂
    have hζ₁_norm : ‖ζ₁‖ = s₁ := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hζ₁
    have hζ₂_norm : ‖ζ₂‖ = s₂ := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hζ₂
    have hcross :
        (ζ₁, ζ₂) ∈ (hartogs_cross ρ₁ ρ₂ ε) ∩ bidisc r₁' r₂' := by
      constructor
      · exact mem_hartogs_cross.mpr <| Or.inr <| by
          constructor
          · simpa [hζ₁_norm] using hs₁_gt
          constructor
          · simpa [hζ₁_norm] using hs₁_lt_ρ₁
          · simpa [hζ₂_norm] using hs₂_lt_ρ₂
      · exact mem_bidisc.mpr <| by
          constructor
          · simpa [hζ₁_norm] using hs₁_lt_r₁'
          · simpa [hζ₂_norm] using hs₂_lt_r₂'
    -- The second local extension matches the same original boundary data on the same torus.
    simp [hartogs_cauchy_extension_eqOn_local_cross hcont hhol₁ hhol₂
      hr₁low' hr₁high' hr₂low' hr₂high' hcross]
  -- Apply the common-smaller-bidisc Cauchy formula to both local extensions and identify the
  -- boundary values through the local-cross equality.
  calc
    hartogs_cauchy_extension f r₁ r₂ z =
        (((2 * Real.pi * Complex.I : ℂ) ^ (2 : ℕ))⁻¹ *
          ∮ ζ₁ in C(0, s₁), ∮ ζ₂ in C(0, s₂),
            hartogs_cauchy_extension f r₁ r₂ (ζ₁, ζ₂) /
              ((ζ₁ - z.1) * (ζ₂ - z.2))) := hformula₁
    _ = (((2 * Real.pi * Complex.I : ℂ) ^ (2 : ℕ))⁻¹ *
          ∮ ζ₁ in C(0, s₁), ∮ ζ₂ in C(0, s₂),
            f (ζ₁, ζ₂) / ((ζ₁ - z.1) * (ζ₂ - z.2))) := hboundary₁
    _ = (((2 * Real.pi * Complex.I : ℂ) ^ (2 : ℕ))⁻¹ *
          ∮ ζ₁ in C(0, s₁), ∮ ζ₂ in C(0, s₂),
            hartogs_cauchy_extension f r₁' r₂' (ζ₁, ζ₂) /
              ((ζ₁ - z.1) * (ζ₂ - z.2))) := hboundary₂.symm
    _ = hartogs_cauchy_extension f r₁' r₂' z := hformula₂.symm

/-- Helper for Remark IV.5-extra-3: at any interior point, the glued function agrees with every
admissible local Cauchy extension through that point. -/
lemma pointwise_hartogs_extension_eq_given
    {f : (ℂ × ℂ) → ℂ} {ρ₁ ρ₂ ε : ℝ}
    (hε : 0 < ε) (hερ₁ : ε < ρ₁) (hερ₂ : ε < ρ₂)
    (hcont : ContinuousOn f (hartogs_cross ρ₁ ρ₂ ε))
    (hhol₁ :
      ∀ w : ℂ, ‖w‖ < ε →
        DifferentiableOn ℂ (fun z ↦ f (z, w)) (Metric.ball (0 : ℂ) ρ₁))
    (hhol₂ :
      ∀ w : ℂ, ρ₁ - ε < ‖w‖ → ‖w‖ < ρ₁ →
        DifferentiableOn ℂ (fun z ↦ f (w, z)) (Metric.ball (0 : ℂ) ρ₂))
    {z : ℂ × ℂ} (hz : z ∈ bidisc ρ₁ ρ₂) {r₁ r₂ : ℝ}
    (hr₁low : ρ₁ - ε < r₁) (hr₁high : r₁ < ρ₁) (hr₂low : ε < r₂) (hr₂high : r₂ < ρ₂)
    (hz₁ : ‖z.1‖ < r₁) (hz₂ : ‖z.2‖ < r₂) :
    pointwise_hartogs_extension f ρ₁ ρ₂ ε hε hερ₁ hερ₂ z =
      hartogs_cauchy_extension f r₁ r₂ z := by
  rcases chosen_local_radii_spec hε hερ₁ hερ₂ hz with
    ⟨hc₁low, hc₁high, hc₂low, hc₂high, hzc₁, hzc₂⟩
  -- The chosen local Cauchy transform and the prescribed admissible one coincide at the base
  -- point because both are valid local extensions there.
  have hoverlap :
      hartogs_cauchy_extension f
          (chosen_local_r₁ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z)
          (chosen_local_r₂ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z) z =
        hartogs_cauchy_extension f r₁ r₂ z := by
    refine hartogs_cauchy_extensions_agree_on_overlap hcont hhol₁ hhol₂
      hc₁low hc₁high hc₂low hc₂high hr₁low hr₁high hr₂low hr₂high ?_ ?_
    · exact lt_min hzc₁ hz₁
    · exact lt_min hzc₂ hz₂
  -- By definition, the glued function is the chosen local extension at the point.
  simpa [pointwise_hartogs_extension] using hoverlap

/-- Helper for Remark IV.5-extra-3: around each interior point, the glued function agrees with the
single local Cauchy extension centered there. -/
lemma pointwise_hartogs_extension_eqOn_chosen_bidisc
    {f : (ℂ × ℂ) → ℂ} {ρ₁ ρ₂ ε : ℝ}
    (hε : 0 < ε) (hερ₁ : ε < ρ₁) (hερ₂ : ε < ρ₂)
    (hcont : ContinuousOn f (hartogs_cross ρ₁ ρ₂ ε))
    (hhol₁ :
      ∀ w : ℂ, ‖w‖ < ε →
        DifferentiableOn ℂ (fun z ↦ f (z, w)) (Metric.ball (0 : ℂ) ρ₁))
    (hhol₂ :
      ∀ w : ℂ, ρ₁ - ε < ‖w‖ → ‖w‖ < ρ₁ →
        DifferentiableOn ℂ (fun z ↦ f (w, z)) (Metric.ball (0 : ℂ) ρ₂))
    {z : ℂ × ℂ} (hz : z ∈ bidisc ρ₁ ρ₂) :
    Set.EqOn
      (pointwise_hartogs_extension f ρ₁ ρ₂ ε hε hερ₁ hερ₂)
      (hartogs_cauchy_extension f
        (chosen_local_r₁ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z)
        (chosen_local_r₂ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z))
      (bidisc
        (chosen_local_r₁ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z)
        (chosen_local_r₂ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z)) := by
  intro y hy
  rcases chosen_local_radii_spec hε hερ₁ hερ₂ hz with
    ⟨hc₁low, hc₁high, hc₂low, hc₂high, _, _⟩
  rcases mem_bidisc.mp hy with ⟨hy₁, hy₂⟩
  have hyAmbient : y ∈ bidisc ρ₁ ρ₂ := by
    -- The chosen neighborhood around `z` still lies inside the ambient bidisc.
    exact mem_bidisc.mpr ⟨lt_trans hy₁ hc₁high, lt_trans hy₂ hc₂high⟩
  exact pointwise_hartogs_extension_eq_given hε hερ₁ hερ₂ hcont hhol₁ hhol₂ hyAmbient
    hc₁low hc₁high hc₂low hc₂high hy₁ hy₂

/-- Remark IV.5-extra-3: a continuous function on the Hartogs cross
`hartogs_cross ρ₁ ρ₂ ε`, holomorphic in `z₁` on the inner tube and holomorphic in `z₂` on the
outer shell, extends to a holomorphic function on the full bidisc `bidisc ρ₁ ρ₂`; for any radii
with `ρ₁ - ε < r₁ < ρ₁` and `ε < r₂ < ρ₂`, the extension is given on `|z₁| < r₁`, `|z₂| < r₂` by
the two-variable Cauchy integral formula with the original boundary data on the distinguished
torus. -/
theorem exists_analytic_extension_of_hartogs_cross
    {f : (ℂ × ℂ) → ℂ} {ρ₁ ρ₂ ε : ℝ}
    (hε : 0 < ε) (hερ₁ : ε < ρ₁) (hερ₂ : ε < ρ₂)
    (hcont : ContinuousOn f (hartogs_cross ρ₁ ρ₂ ε))
    (hhol₁ :
      ∀ w : ℂ, ‖w‖ < ε →
        DifferentiableOn ℂ (fun z ↦ f (z, w)) (Metric.ball (0 : ℂ) ρ₁))
    (hhol₂ :
      ∀ w : ℂ, ρ₁ - ε < ‖w‖ → ‖w‖ < ρ₁ →
        DifferentiableOn ℂ (fun z ↦ f (w, z)) (Metric.ball (0 : ℂ) ρ₂)) :
    ∃ F : (ℂ × ℂ) → ℂ,
      AnalyticOnNhd ℂ F (bidisc ρ₁ ρ₂) ∧
      EqOn F f (hartogs_cross ρ₁ ρ₂ ε) ∧
      ∀ ⦃r₁ r₂ : ℝ⦄, ρ₁ - ε < r₁ → r₁ < ρ₁ → ε < r₂ → r₂ < ρ₂ →
        ∀ ⦃z : ℂ × ℂ⦄, ‖z.1‖ < r₁ → ‖z.2‖ < r₂ →
          F z =
            (((2 * Real.pi * Complex.I : ℂ) ^ (2 : ℕ))⁻¹ *
              ∮ ζ₁ in C(0, r₁), ∮ ζ₂ in C(0, r₂),
                f (ζ₁, ζ₂) / ((ζ₁ - z.1) * (ζ₂ - z.2))) := by
  refine ⟨pointwise_hartogs_extension f ρ₁ ρ₂ ε hε hερ₁ hερ₂, ?_, ?_, ?_⟩
  · intro z hz
    rcases chosen_local_radii_spec hε hερ₁ hερ₂ hz with
      ⟨hc₁low, hc₁high, hc₂low, hc₂high, hzc₁, hzc₂⟩
    let U :=
      bidisc
        (chosen_local_r₁ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z)
        (chosen_local_r₂ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z)
    have hzU : z ∈ U := by
      -- The chosen radii were constructed to contain the base point.
      exact mem_bidisc.mpr ⟨hzc₁, hzc₂⟩
    have hlocal :
        AnalyticOnNhd ℂ
          (hartogs_cauchy_extension f
            (chosen_local_r₁ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z)
            (chosen_local_r₂ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z))
          U :=
      hartogs_cauchy_extension_analyticOnNhd_bidisc hcont hhol₁ hhol₂
        hc₁low hc₁high hc₂low hc₂high
    have hEq :
        Set.EqOn
          (pointwise_hartogs_extension f ρ₁ ρ₂ ε hε hερ₁ hερ₂)
          (hartogs_cauchy_extension f
            (chosen_local_r₁ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z)
            (chosen_local_r₂ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z))
          U :=
      pointwise_hartogs_extension_eqOn_chosen_bidisc hε hερ₁ hερ₂ hcont hhol₁ hhol₂ hz
    have hEq_symm :
        Set.EqOn
          (hartogs_cauchy_extension f
            (chosen_local_r₁ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z)
            (chosen_local_r₂ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z))
          (pointwise_hartogs_extension f ρ₁ ρ₂ ε hε hερ₁ hερ₂) U := by
      intro y hy
      exact (hEq hy).symm
    -- Near `z`, the glued function literally equals one fixed local Cauchy extension.
    exact (hlocal z hzU).congr <|
      hEq_symm.eventuallyEq_of_mem (IsOpen.mem_nhds isOpen_bidisc hzU)
  · intro z hz
    have hzAmbient : z ∈ bidisc ρ₁ ρ₂ := hartogs_cross_subset_bidisc hερ₂ hz
    rcases chosen_local_radii_spec hε hερ₁ hερ₂ hzAmbient with
      ⟨hc₁low, hc₁high, hc₂low, hc₂high, hzc₁, hzc₂⟩
    have hzLocal :
        z ∈ (hartogs_cross ρ₁ ρ₂ ε) ∩
          bidisc
            (chosen_local_r₁ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z)
            (chosen_local_r₂ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z) := by
      exact ⟨hz, mem_bidisc.mpr ⟨hzc₁, hzc₂⟩⟩
    -- At points of the Hartogs cross, the glued value is the original function because the chosen
    -- local Cauchy extension already agrees with `f` there.
    calc
      pointwise_hartogs_extension f ρ₁ ρ₂ ε hε hερ₁ hερ₂ z =
          hartogs_cauchy_extension f
            (chosen_local_r₁ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z)
            (chosen_local_r₂ ρ₁ ρ₂ ε hε hερ₁ hερ₂ z) z := by
              exact pointwise_hartogs_extension_eq_given hε hερ₁ hερ₂ hcont hhol₁ hhol₂ hzAmbient
                hc₁low hc₁high hc₂low hc₂high hzc₁ hzc₂
      _ = f z := hartogs_cauchy_extension_eqOn_local_cross hcont hhol₁ hhol₂
        hc₁low hc₁high hc₂low hc₂high hzLocal
  · intro r₁ r₂ hr₁low hr₁high hr₂low hr₂high z hz₁ hz₂
    have hzAmbient : z ∈ bidisc ρ₁ ρ₂ := by
      -- Any point of the smaller admissible bidisc lies in the ambient one.
      exact mem_bidisc.mpr ⟨lt_trans hz₁ hr₁high, lt_trans hz₂ hr₂high⟩
    -- The glued extension agrees pointwise with the admissible local Cauchy transform through `z`.
    simpa [hartogs_cauchy_extension] using
      pointwise_hartogs_extension_eq_given hε hερ₁ hερ₂ hcont hhol₁ hhol₂ hzAmbient
        hr₁low hr₁high hr₂low hr₂high hz₁ hz₂
