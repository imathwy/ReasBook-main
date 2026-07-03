import Mathlib
import Mathlib.Dynamics.Ergodic.Ergodic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_20_6_1 (from Items/Chap20) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := by
  refine ⟨by
    rw [show (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) by norm_num]
    exact AddCircle.measure_univ (1 : ℝ)
  ⟩

/-- The mod-one doubling map on the additive-circle model of `[0,1)`. -/
def modOneDoubling : UnitAddCircle → UnitAddCircle :=
  fun x ↦ (2 : ℤ) • x

-- Proof sketch: multiplication by `2` on `AddCircle 1` is a continuous surjective group
-- endomorphism preserving Haar measure; identify Haar measure on `AddCircle 1` with Lebesgue
-- measure on `[0,1)`.
/-- The mod-one doubling map preserves Lebesgue/Haar measure on the circle. -/
theorem modOneDoubling_measurePreserving :
    MeasurePreserving modOneDoubling volume volume := by
  simpa [modOneDoubling] using
    (Measure.measurePreserving_zsmul volume (by norm_num : (2 : ℤ) ≠ 0))

-- Proof sketch: code the doubling map by binary expansions to obtain a measurable conjugacy with
-- the fair Bernoulli shift on two symbols, then apply the entropy computation for the fair binary
-- shift and evaluate the entropy of the uniform law on `Fin 2`.
/-- The dyadic coding identifies the entropy of the doubling map with the entropy of the fair
binary Bernoulli shift. -/
theorem kolmogorov_sinai_entropy_modOneDoubling_eq_entropy_uniformFinTwo :
    h(volume, modOneDoubling, modOneDoubling_measurePreserving.measurable) =
      entropy (PMF.uniformOfFintype (Fin 2)) := sorry

/-- Exercise 20.6.1: the Lebesgue-measure entropy of the doubling map `x ↦ 2x (mod 1)` on
`[0,1)` is `log 2`; equivalently, the corresponding system on `AddCircle 1` has entropy `log 2`. -/
theorem kolmogorov_sinai_entropy_modOneDoubling_eq_log_two :
    h(volume, modOneDoubling, modOneDoubling_measurePreserving.measurable) =
      ((Real.log 2 : ℝ) : EReal) := by
  rw [kolmogorov_sinai_entropy_modOneDoubling_eq_entropy_uniformFinTwo]
  rw [entropy_eq_sum]
  simp [PMF.uniformOfFintype_apply]

/-! ### Exercise_20_6_2 (from Items/Chap20) -/
open Filter

-- Proof sketch: use nonnegativity to get the uniform lower bound `0 ≤ a n / n`,
-- apply mathlib's owner theorem `Subadditive.tendsto_lim`, and unfold `Subadditive.lim`.
/-- Exercise 20.6.2: if a real sequence is nonnegative and subadditive, then the normalized
sequence `a n / n` converges to the infimum of its values over the positive indices. -/
theorem subadditive_nonnegative_tendsto_div_eq_sInf
    {a : ℕ → ℝ} (ha_nonneg : ∀ n : ℕ, 0 ≤ a n) (hsub : Subadditive a) :
    Tendsto (fun n : ℕ ↦ a n / n) atTop
      (nhds (sInf ((fun n : ℕ ↦ a n / n) '' Set.Ici 1))) := by
  have hbdd : BddBelow (Set.range fun n : ℕ ↦ a n / n) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact div_nonneg (ha_nonneg n) (Nat.cast_nonneg n)
  simpa [Subadditive.lim] using hsub.tendsto_lim hbdd

/-! ### Definition_20_6 (from Items/Chap20) -/
open MeasureTheory

/- Definition 20.6 (1): for a probability space `(Ω, 𝓐, P)` and measurable transformation `τ`,
the textbook condition `P[τ⁻¹(A)] = P[A]` for all `A ∈ 𝓐` is the canonical notion
`MeasurePreserving τ P P`; thus a measure-preserving dynamical system
`(Ω, 𝓐, P, τ)` is encoded by this predicate. -/
recall MeasurePreserving

/- Definition 20.6 (2): on a probability space, an ergodic measure-preserving dynamical system is
the canonical notion `Ergodic τ P`; equivalently, every measurable invariant set is `P`-trivial,
i.e. has probability `0` or `1`. -/
recall Ergodic
