import Mathlib
import DifferentialForms_Cartan_1970.IV.section17.«0002_Theorem_IV_5_extra_2»

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling: Proposition 2.1 is a bidisc holomorphicity statement in several complex
-- variables. In this chapter the owner for holomorphicity on an open set is
-- `DifferentiableOn ℂ`, while separate-slice hypotheses are only a bridge/view used to recover the
-- uncurried several-variable map on the open bidisc.

open scoped Topology

noncomputable section

/-- The bidisc `‖z₁‖ < ρ₁`, `‖z₂‖ < ρ₂` in `ℂ²`. -/
def bidisc (ρ₁ ρ₂ : ℝ) : Set (ℂ × ℂ) :=
  (Metric.ball (0 : ℂ) ρ₁) ×ˢ (Metric.ball (0 : ℂ) ρ₂)

@[simp] theorem mem_bidisc {ρ₁ ρ₂ : ℝ} {z : ℂ × ℂ} :
    z ∈ bidisc ρ₁ ρ₂ ↔ ‖z.1‖ < ρ₁ ∧ ‖z.2‖ < ρ₂ := by
  simp [bidisc, Metric.mem_ball, dist_eq_norm]

/-- The bidisc is open in `ℂ²`. -/
theorem isOpen_bidisc {ρ₁ ρ₂ : ℝ} : IsOpen (bidisc ρ₁ ρ₂) :=
  Metric.isOpen_ball.prod Metric.isOpen_ball

/-- Helper for Proposition 2.1: restricting a bidisc-holomorphic function to a horizontal closed
slice remains holomorphic on that closed disc. -/
lemma differentiableOn_closedBall_left_slice
    {f : ℂ × ℂ → ℂ} {ρ₁ ρ₂ r₁ : ℝ} {w : ℂ}
    (hrρ₁ : r₁ < ρ₁) (hw : ‖w‖ < ρ₂)
    (hf : DifferentiableOn ℂ f (bidisc ρ₁ ρ₂)) :
    DifferentiableOn ℂ (fun z₁ ↦ f (z₁, w)) (Metric.closedBall (0 : ℂ) r₁) := by
  -- The slice map lands in the bidisc because the first coordinate stays inside the smaller disc
  -- and the second coordinate is fixed in the `ρ₂`-disc.
  have hmap :
      Set.MapsTo (fun z₁ : ℂ ↦ (z₁, w)) (Metric.closedBall (0 : ℂ) r₁) (bidisc ρ₁ ρ₂) := by
    intro z₁ hz₁
    rw [mem_bidisc]
    constructor
    · have hz₁_le : ‖z₁‖ ≤ r₁ := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hz₁
      exact lt_of_le_of_lt hz₁_le hrρ₁
    · exact hw
  -- The slice map itself is differentiable, so differentiability composes from the bidisc map.
  have hslice :
      DifferentiableOn ℂ (fun z₁ : ℂ ↦ (z₁, w)) (Metric.closedBall (0 : ℂ) r₁) := by
    simpa using (differentiableOn_id.prodMk (differentiableOn_const w))
  simpa using hf.comp hslice hmap

/-- Helper for Proposition 2.1: restricting a bidisc-holomorphic function to a vertical closed
slice remains holomorphic on that closed disc. -/
lemma differentiableOn_closedBall_right_slice
    {f : ℂ × ℂ → ℂ} {ρ₁ ρ₂ r₂ : ℝ} {w : ℂ}
    (hrρ₂ : r₂ < ρ₂) (hw : ‖w‖ < ρ₁)
    (hf : DifferentiableOn ℂ f (bidisc ρ₁ ρ₂)) :
    DifferentiableOn ℂ (fun z₂ ↦ f (w, z₂)) (Metric.closedBall (0 : ℂ) r₂) := by
  -- The vertical slice map also lands in the bidisc by the symmetric radius bounds.
  have hmap :
      Set.MapsTo (fun z₂ : ℂ ↦ (w, z₂)) (Metric.closedBall (0 : ℂ) r₂) (bidisc ρ₁ ρ₂) := by
    intro z₂ hz₂
    rw [mem_bidisc]
    constructor
    · exact hw
    · have hz₂_le : ‖z₂‖ ≤ r₂ := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hz₂
      exact lt_of_le_of_lt hz₂_le hrρ₂
  -- Compose differentiability with the vertical slice map.
  have hslice :
      DifferentiableOn ℂ (fun z₂ : ℂ ↦ (w, z₂)) (Metric.closedBall (0 : ℂ) r₂) := by
    simpa using ((differentiableOn_const w).prodMk differentiableOn_id)
  simpa using hf.comp hslice hmap

/-- Helper for Proposition 2.1: the two-variable Cauchy kernel factors into the product of the
two one-variable kernels. -/
lemma two_variable_cauchy_integrand_eq_inv_mul_inv
    {f : ℂ × ℂ → ℂ} {ζ₁ ζ₂ z₁ z₂ : ℂ} :
    f (ζ₁, ζ₂) / ((ζ₁ - z₁) * (ζ₂ - z₂)) =
      (ζ₁ - z₁)⁻¹ * ((ζ₂ - z₂)⁻¹ * f (ζ₁, ζ₂)) := by
  -- Normalize the denominator once so each Cauchy application sees the expected one-variable
  -- kernel `(ζ - z)⁻¹`.
  rw [div_eq_mul_inv, mul_inv_rev]
  ac_rfl

/-- Helper for Proposition 2.1: separate holomorphicity on the open bidisc upgrades to
holomorphicity of the uncurried map on the bidisc. -/
lemma separately_holomorphic_uncurry_differentiableOn_bidisc
    {f : ℂ → ℂ → ℂ} {ρ₁ ρ₂ : ℝ}
    (hhol₁ :
      ∀ w : ℂ, ‖w‖ < ρ₂ →
        DifferentiableOn ℂ (fun z ↦ f z w) (Metric.ball (0 : ℂ) ρ₁))
    (hhol₂ :
      ∀ w : ℂ, ‖w‖ < ρ₁ →
        DifferentiableOn ℂ (fun z ↦ f w z) (Metric.ball (0 : ℂ) ρ₂)) :
    DifferentiableOn ℂ (Function.uncurry f) (bidisc ρ₁ ρ₂) := by
  let D : Set (Fin 2 → ℂ) := {x | ‖x 0‖ < ρ₁ ∧ ‖x 1‖ < ρ₂}
  let g : (Fin 2 → ℂ) → ℂ := fun x ↦ f (x 0) (x 1)
  -- The coordinatewise radius conditions define an open set in `ℂ²`.
  have hD : IsOpen D := by
    have h0 : IsOpen {x : Fin 2 → ℂ | ‖x 0‖ < ρ₁} := by
      simpa using isOpen_lt ((continuous_apply 0).norm) continuous_const
    have h1 : IsOpen {x : Fin 2 → ℂ | ‖x 1‖ < ρ₂} := by
      simpa using isOpen_lt ((continuous_apply 1).norm) continuous_const
    simpa [D, Set.setOf_and] using h0.inter h1
  -- Each coordinate update is exactly one of the given one-variable slices.
  have hsep : ∀ x ∈ D, ∀ i : Fin 2, AnalyticAt ℂ (fun w ↦ g (Function.update x i w)) (x i) := by
    intro x hx i
    rcases hx with ⟨hx₀, hx₁⟩
    fin_cases i
    · have hslice : DifferentiableOn ℂ (fun z ↦ f z (x 1)) (Metric.ball (0 : ℂ) ρ₁) :=
        hhol₁ (x 1) hx₁
      have hx₀_ball : x 0 ∈ Metric.ball (0 : ℂ) ρ₁ := by
        simpa [Metric.mem_ball, dist_eq_norm] using hx₀
      -- The first-coordinate update literally recovers the `z₁`-slice from the hypothesis.
      simpa [g] using hslice.analyticAt (Metric.isOpen_ball.mem_nhds hx₀_ball)
    · have hslice : DifferentiableOn ℂ (fun z ↦ f (x 0) z) (Metric.ball (0 : ℂ) ρ₂) :=
        hhol₂ (x 0) hx₀
      have hx₁_ball : x 1 ∈ Metric.ball (0 : ℂ) ρ₂ := by
        simpa [Metric.mem_ball, dist_eq_norm] using hx₁
      -- The second-coordinate update recovers the `z₂`-slice from the hypothesis.
      simpa [g] using hslice.analyticAt (Metric.isOpen_ball.mem_nhds hx₁_ball)
  have hg : DifferentiableOn ℂ g D := separately_holomorphic_differentiableOn hD hsep
  let φ : ℂ × ℂ → Fin 2 → ℂ := fun p ↦ ![p.1, p.2]
  -- Transport the `Fin 2` result back to the product presentation of `ℂ²`.
  have hφdiff : DifferentiableOn ℂ φ (bidisc ρ₁ ρ₂) := by
    refine differentiableOn_pi'' ?_
    intro i
    fin_cases i
    · simpa [φ] using
        (differentiableOn_fst : DifferentiableOn ℂ (fun p : ℂ × ℂ ↦ p.1) (bidisc ρ₁ ρ₂))
    · simpa [φ] using
        (differentiableOn_snd : DifferentiableOn ℂ (fun p : ℂ × ℂ ↦ p.2) (bidisc ρ₁ ρ₂))
  have hφmap : Set.MapsTo φ (bidisc ρ₁ ρ₂) D := by
    intro p hp
    simpa [φ, D, mem_bidisc] using hp
  simpa [g, φ, Function.comp, Function.uncurry] using hg.comp hφdiff hφmap

/-- Proposition 2.1 in canonical several-variable form: a holomorphic function on the bidisc
satisfies the two-variable Cauchy integral formula on every smaller bidisc. -/
theorem cauchy_integral_formula_two_variables_on_bidisc
    {f : ℂ × ℂ → ℂ} {ρ₁ ρ₂ r₁ r₂ : ℝ} {z : ℂ × ℂ}
    (hrρ₁ : r₁ < ρ₁) (hrρ₂ : r₂ < ρ₂)
    (hz₁ : ‖z.1‖ < r₁) (hz₂ : ‖z.2‖ < r₂)
    (hf : DifferentiableOn ℂ f (bidisc ρ₁ ρ₂)) :
    f z =
      (((2 * Real.pi * Complex.I : ℂ) ^ (2 : ℕ))⁻¹ *
        ∮ ζ₁ in C(0, r₁), ∮ ζ₂ in C(0, r₂),
          f (ζ₁, ζ₂) / ((ζ₁ - z.1) * (ζ₂ - z.2))) := by
  have hr₁_pos : 0 < r₁ := lt_of_le_of_lt (norm_nonneg z.1) hz₁
  have hr₂_pos : 0 < r₂ := lt_of_le_of_lt (norm_nonneg z.2) hz₂
  have hz₁_ball : z.1 ∈ Metric.ball (0 : ℂ) r₁ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz₁
  have hz₂_ball : z.2 ∈ Metric.ball (0 : ℂ) r₂ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz₂
  have hleft_slice :
      DifferentiableOn ℂ (fun ζ₁ ↦ f (ζ₁, z.2)) (Metric.closedBall (0 : ℂ) r₁) :=
    differentiableOn_closedBall_left_slice hrρ₁ (lt_trans hz₂ hrρ₂) hf
  -- Apply one-variable Cauchy in the inner `ζ₂`-variable on each boundary point `ζ₁`.
  have hinner_boundary :
      Set.EqOn
        (fun ζ₁ ↦
          ∮ ζ₂ in C(0, r₂), f (ζ₁, ζ₂) / ((ζ₁ - z.1) * (ζ₂ - z.2)))
        (fun ζ₁ ↦ (ζ₁ - z.1)⁻¹ * ((2 * Real.pi * Complex.I : ℂ) * f (ζ₁, z.2)))
        (Metric.sphere (0 : ℂ) r₁) := by
    intro ζ₁ hζ₁
    have hζ₁_norm : ‖ζ₁‖ = r₁ := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hζ₁
    have hζ₁_lt : ‖ζ₁‖ < ρ₁ := by
      rw [hζ₁_norm]
      exact hrρ₁
    have hright_slice :
        DifferentiableOn ℂ (fun ζ₂ ↦ f (ζ₁, ζ₂)) (Metric.closedBall (0 : ℂ) r₂) :=
      differentiableOn_closedBall_right_slice hrρ₂ hζ₁_lt hf
    have hinner_cauchy :
        (∮ ζ₂ in C(0, r₂), (ζ₂ - z.2)⁻¹ * f (ζ₁, ζ₂)) =
          (2 * Real.pi * Complex.I : ℂ) * f (ζ₁, z.2) := by
      -- The inner slice is holomorphic on the closed `r₂`-disc, so one-variable Cauchy applies.
      simpa [smul_eq_mul] using
        (hright_slice.circleIntegral_sub_inv_smul (c := 0) (R := r₂) (w := z.2) hz₂_ball)
    calc
      ∮ ζ₂ in C(0, r₂), f (ζ₁, ζ₂) / ((ζ₁ - z.1) * (ζ₂ - z.2))
          = ∮ ζ₂ in C(0, r₂), (ζ₁ - z.1)⁻¹ * ((ζ₂ - z.2)⁻¹ * f (ζ₁, ζ₂)) := by
              apply circleIntegral.integral_congr hr₂_pos.le
              intro ζ₂ hζ₂
              simpa using
                (two_variable_cauchy_integrand_eq_inv_mul_inv
                  (f := f) (ζ₁ := ζ₁) (ζ₂ := ζ₂) (z₁ := z.1) (z₂ := z.2))
      _ = (ζ₁ - z.1)⁻¹ * ∮ ζ₂ in C(0, r₂), (ζ₂ - z.2)⁻¹ * f (ζ₁, ζ₂) := by
            rw [circleIntegral.integral_const_mul]
      _ = (ζ₁ - z.1)⁻¹ * ((2 * Real.pi * Complex.I : ℂ) * f (ζ₁, z.2)) := by
            rw [hinner_cauchy]
  have houter_cauchy :
      (∮ ζ₁ in C(0, r₁), (ζ₁ - z.1)⁻¹ * f (ζ₁, z.2)) =
        (2 * Real.pi * Complex.I : ℂ) * f z := by
    -- After the inner step, the outer slice is a one-variable holomorphic function of `ζ₁`.
    simpa [smul_eq_mul] using
      (hleft_slice.circleIntegral_sub_inv_smul (c := 0) (R := r₁) (w := z.1) hz₁_ball)
  have hdouble :
      (∮ ζ₁ in C(0, r₁), ∮ ζ₂ in C(0, r₂),
        f (ζ₁, ζ₂) / ((ζ₁ - z.1) * (ζ₂ - z.2))) =
        (((2 * Real.pi * Complex.I : ℂ) ^ (2 : ℕ)) * f z) := by
    -- The textbook proof is exactly two successive one-variable Cauchy formulas.
    calc
      (∮ ζ₁ in C(0, r₁), ∮ ζ₂ in C(0, r₂),
        f (ζ₁, ζ₂) / ((ζ₁ - z.1) * (ζ₂ - z.2))) =
          ∮ ζ₁ in C(0, r₁), (ζ₁ - z.1)⁻¹ * ((2 * Real.pi * Complex.I : ℂ) * f (ζ₁, z.2)) := by
            apply circleIntegral.integral_congr hr₁_pos.le
            intro ζ₁ hζ₁
            exact hinner_boundary hζ₁
      _ = ∮ ζ₁ in C(0, r₁), (2 * Real.pi * Complex.I : ℂ) *
            ((ζ₁ - z.1)⁻¹ * f (ζ₁, z.2)) := by
            apply circleIntegral.integral_congr hr₁_pos.le
            intro ζ₁ hζ₁
            ac_rfl
      _ = (2 * Real.pi * Complex.I : ℂ) *
            (∮ ζ₁ in C(0, r₁), (ζ₁ - z.1)⁻¹ * f (ζ₁, z.2)) := by
            rw [circleIntegral.integral_const_mul]
      _ = (2 * Real.pi * Complex.I : ℂ) * ((2 * Real.pi * Complex.I : ℂ) * f z) := by
            rw [houter_cauchy]
      _ = (((2 * Real.pi * Complex.I : ℂ) ^ (2 : ℕ)) * f z) := by
            simp [pow_two, mul_assoc]
  have hkernel_ne : (((2 * Real.pi * Complex.I : ℂ) ^ (2 : ℕ))) ≠ 0 := by
    have htwo_pi_ne : (2 * Real.pi : ℂ) ≠ 0 := by
      refine mul_ne_zero ?_ ?_
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    have htwo_pi_i_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      exact mul_ne_zero htwo_pi_ne Complex.I_ne_zero
    exact pow_ne_zero 2 htwo_pi_i_ne
  -- Multiply by the inverse scalar to isolate `f z`.
  calc
    f z = 1 * f z := by simp
    _ = (((2 * Real.pi * Complex.I : ℂ) ^ (2 : ℕ))⁻¹ *
        ((((2 * Real.pi * Complex.I : ℂ) ^ (2 : ℕ))) * f z)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hkernel_ne]
    _ = (((2 * Real.pi * Complex.I : ℂ) ^ (2 : ℕ))⁻¹ *
        ∮ ζ₁ in C(0, r₁), ∮ ζ₂ in C(0, r₂),
          f (ζ₁, ζ₂) / ((ζ₁ - z.1) * (ζ₂ - z.2))) := by
            rw [hdouble]

/-- Source-facing bridge/view of Proposition 2.1: separate holomorphicity on the open bidisc
already determines the canonical owner `DifferentiableOn ℂ (Function.uncurry f) (bidisc ρ₁ ρ₂)`,
so no extra continuity hypothesis belongs in the public statement. -/
theorem cauchy_integral_formula_two_variables_of_separately_holomorphic
    {f : ℂ → ℂ → ℂ} {ρ₁ ρ₂ r₁ r₂ : ℝ} {z₁ z₂ : ℂ}
    (hrρ₁ : r₁ < ρ₁) (hrρ₂ : r₂ < ρ₂)
    (hz₁ : ‖z₁‖ < r₁) (hz₂ : ‖z₂‖ < r₂)
    (hhol₁ :
      ∀ w : ℂ, ‖w‖ < ρ₂ →
        DifferentiableOn ℂ (fun z ↦ f z w) (Metric.ball (0 : ℂ) ρ₁))
    (hhol₂ :
      ∀ w : ℂ, ‖w‖ < ρ₁ →
        DifferentiableOn ℂ (fun z ↦ f w z) (Metric.ball (0 : ℂ) ρ₂)) :
    f z₁ z₂ =
      (((2 * Real.pi * Complex.I : ℂ) ^ (2 : ℕ))⁻¹ *
        ∮ ζ₁ in C(0, r₁), ∮ ζ₂ in C(0, r₂),
          f ζ₁ ζ₂ / ((ζ₁ - z₁) * (ζ₂ - z₂))) := by
  -- First upgrade separate holomorphicity to holomorphicity of the uncurried bidisc map.
  have huncurry : DifferentiableOn ℂ (Function.uncurry f) (bidisc ρ₁ ρ₂) :=
    separately_holomorphic_uncurry_differentiableOn_bidisc hhol₁ hhol₂
  -- Then apply the canonical bidisc Cauchy formula to the point `(z₁, z₂)`.
  simpa [Function.uncurry] using
    (cauchy_integral_formula_two_variables_on_bidisc
      (f := Function.uncurry f) (z := (z₁, z₂))
      hrρ₁ hrρ₂ hz₁ hz₂ huncurry)
