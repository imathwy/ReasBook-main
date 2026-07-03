import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

open MeasureTheory ProbabilityTheory Filter

universe u

namespace MeasureTheory.Measure

section AlongZero

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]
variable {t : ℕ → ℝ}

-- Proof sketch: use the doubling estimate for `1 - Re φ(2 t)` together with the hypothesis
-- `‖φ (t n)‖ = 1` to show that the law `μ` has the characteristic function of a Dirac measure.
/-- Law-level owner form of Exercise 15.2.4 (1): if a real probability law has characteristic
function of modulus `1` along a nonzero sequence of frequencies with `|t_n| ↓ 0`, then the law is
a Dirac mass. -/
theorem eq_dirac_of_charFun_norm_eq_one_along_zero
    (ht_antitone : Antitone fun n ↦ |t n|)
    (ht_zero : Tendsto (fun n ↦ |t n|) atTop (𝓝 0))
    (ht_nonzero : ∀ n, t n ≠ 0)
    (hφ_unit : ∀ n, ‖charFun μ (t n)‖ = 1) :
    ∃ b : ℝ, μ = Measure.dirac b := sorry

-- Proof sketch: apply the first law-level statement, then the additional hypothesis
-- `φ (t n) = 1` forces the Dirac characteristic function to be identically `1`, hence its atom is
-- located at `0`.
/-- Law-level owner form of Exercise 15.2.4 (2): if in addition the characteristic function is
equal to `1` along that same nonzero sequence, then the law is `δ₀`. -/
theorem eq_dirac_zero_of_charFun_eq_one_along_zero
    (ht_antitone : Antitone fun n ↦ |t n|)
    (ht_zero : Tendsto (fun n ↦ |t n|) atTop (𝓝 0))
    (ht_nonzero : ∀ n, t n ≠ 0)
    (hφ_one : ∀ n, charFun μ (t n) = 1) :
    μ = Measure.dirac 0 := sorry

end AlongZero

end MeasureTheory.Measure

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}

section AlongZero

variable (t : ℕ → ℝ)

-- Proof sketch: use the doubling estimate for `1 - Re φ(2 t)` together with the hypothesis
-- `‖φ (t n)‖ = 1` to show that the pushforward law `P.map X` is a Dirac measure, then conclude
-- that `X` is almost surely constant from `HasLaw.ae_iff`.
/-- Exercise 15.2.4 (1): if the characteristic function of a real random variable has modulus
`1` along a nonzero sequence of frequencies with `|t_n| ↓ 0`, then the random variable is almost
surely constant. -/
theorem ae_eq_const_of_charFun_norm_eq_one_along_zero
    (hX : Measurable X)
    (ht_antitone : Antitone fun n ↦ |t n|)
    (ht_zero : Tendsto (fun n ↦ |t n|) atTop (𝓝 0))
    (ht_nonzero : ∀ n, t n ≠ 0)
    (hφ_unit : ∀ n, ‖charFun (P.map X) (t n)‖ = 1) :
    ∃ b : ℝ, X =ᵐ[P] fun _ ↦ b := by
  letI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  obtain ⟨b, hb⟩ :=
    Measure.eq_dirac_of_charFun_norm_eq_one_along_zero ht_antitone ht_zero ht_nonzero hφ_unit
  refine ⟨b, ?_⟩
  let hX_law : HasLaw X (Measure.dirac b) P := ⟨hX.aemeasurable, hb⟩
  exact (hX_law.ae_iff (measurable_id.eq measurable_const)).2 (by simp)

-- Proof sketch: apply the law-level `δ₀` statement to the pushforward law `P.map X`, then use
-- `HasLaw.ae_iff` to transport the almost-everywhere identity under the Dirac law back to `P`.
/-- Exercise 15.2.4 (2): if in addition the characteristic function is equal to `1` along that
same nonzero sequence with `|t_n| ↓ 0`, then the random variable vanishes almost surely. -/
theorem ae_eq_zero_of_charFun_eq_one_along_zero
    (hX : Measurable X)
    (ht_antitone : Antitone fun n ↦ |t n|)
    (ht_zero : Tendsto (fun n ↦ |t n|) atTop (𝓝 0))
    (ht_nonzero : ∀ n, t n ≠ 0)
    (hφ_one : ∀ n, charFun (P.map X) (t n) = 1) :
    X =ᵐ[P] fun _ ↦ 0 := by
  letI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  let hX_law : HasLaw X (Measure.dirac 0) P :=
    ⟨hX.aemeasurable,
      Measure.eq_dirac_zero_of_charFun_eq_one_along_zero
        ht_antitone ht_zero ht_nonzero hφ_one⟩
  exact (hX_law.ae_iff (measurable_id.eq measurable_const)).2 (by simp)

end AlongZero
