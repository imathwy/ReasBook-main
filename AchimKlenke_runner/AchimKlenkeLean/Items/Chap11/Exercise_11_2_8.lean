import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Filtration
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/- Exercise 11.2.8 is `source-facing`: it describes a `{0,1}`-valued real process together with
its one-step conditional law. The public owner abstraction is therefore the transition-law
predicate `exercise1128Transition`, which packages both the binary state-space restriction and the
displayed conditional law along the natural filtration. The ambient-`ℝ` two-point row kernel below
is auxiliary support code for that statement, so it stays private. -/

private theorem exercise1128RowKernel_measurable (p : ℝ) :
    Measurable
      (fun x : ℝ ↦
        (ENNReal.ofReal x • Measure.dirac (1 - p + p * x) +
          ENNReal.ofReal (1 - x) • Measure.dirac (p * x) : Measure ℝ)) := by
  have h_left : Measurable (fun x : ℝ ↦ 1 - p + p * x) := by
    fun_prop
  have h_right : Measurable (fun x : ℝ ↦ p * x) := by
    fun_prop
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  simp only [Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ hs]
  refine Measurable.add ?_ ?_
  · refine measurable_id.ennreal_ofReal.mul ?_
    exact (measurable_const.indicator hs).comp h_left
  · refine (measurable_const.sub measurable_id).ennreal_ofReal.mul ?_
    exact (measurable_const.indicator hs).comp h_right

private def exercise1128RowKernel (p : ℝ) : Kernel ℝ ℝ where
  toFun x :=
    ENNReal.ofReal x • Measure.dirac (1 - p + p * x) +
      ENNReal.ofReal (1 - x) • Measure.dirac (p * x)
  measurable' := exercise1128RowKernel_measurable p

/-- The source-facing transition law from Exercise 11.2.8: with respect to the natural filtration
of `X`, the process is `{0,1}`-valued and the conditional law of `X_{n+1}` is the canonical
two-point law determined by `X_n` and `p`. -/
def exercise1128Transition (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ) (X : ℕ → Ω → ℝ) (hX_meas : ∀ n, Measurable (X n)) : Prop :=
  let ℱ := Filtration.natural X fun n ↦ (hX_meas n).stronglyMeasurable
  (∀ n ω, X n ω ∈ ({0, 1} : Set ℝ)) ∧
    ∀ n ⦃s : Set ℝ⦄, MeasurableSet s →
      μ⟦X (n + 1) ⁻¹' s | ℱ n⟧ =ᵐ[μ] fun ω ↦ (exercise1128RowKernel p (X n ω)).real s

/-- A process satisfying `exercise1128Transition` is `{0,1}`-valued at every time. -/
theorem exercise1128Transition_binary {p : ℝ} {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ n, Measurable (X n))
    (hX_transition : exercise1128Transition μ p X hX_meas) :
    ∀ n ω, X n ω ∈ ({0, 1} : Set ℝ) :=
  hX_transition.1

private theorem exercise1128Transition_conditionalLaw {p : ℝ} {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ n, Measurable (X n))
    (hX_transition : exercise1128Transition μ p X hX_meas) :
    let ℱ := Filtration.natural X fun n ↦ (hX_meas n).stronglyMeasurable
    ∀ n ⦃s : Set ℝ⦄, MeasurableSet s →
      μ⟦X (n + 1) ⁻¹' s | ℱ n⟧ =ᵐ[μ] fun ω ↦ (exercise1128RowKernel p (X n ω)).real s :=
  hX_transition.2

-- Proof sketch: if `x ∈ {0, 1}`, exactly one of the two weights in `exercise1128RowKernel p x`
-- is `1` and the other is `0`, so the two-point law reduces to the Dirac mass at `x`.
private theorem exercise1128RowKernel_eq_dirac_of_mem_zero_one {p x : ℝ}
    (hx : x ∈ ({0, 1} : Set ℝ)) :
    exercise1128RowKernel p x = Measure.dirac x := sorry

-- Proof sketch: under the conditional-law hypothesis, the one-step conditional law of
-- `X_{n + 1}` is `exercise1128RowKernel p (X n ω)` along the natural filtration. The binary part
-- of `exercise1128Transition` identifies this with `Measure.dirac (X n ω)` via
-- `exercise1128RowKernel_eq_dirac_of_mem_zero_one`,
-- `Measure.dirac (X n ω)`, so `X_{n + 1}` and `X_n` agree almost surely.
/-- For a process satisfying the source-facing Exercise 11.2.8 transition law,
consecutive time slices coincide almost everywhere. -/
theorem exercise1128_succ_ae_eq_self {p : ℝ} {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ n, Measurable (X n))
    (hX_transition : exercise1128Transition μ p X hX_meas) (n : ℕ) :
    X (n + 1) =ᵐ[μ] X n := sorry

-- Proof sketch: iterate the one-step almost-everywhere identity from the previous lemma and use
-- transitivity of `=ᵐ[μ]` to show inductively that every time slice agrees almost everywhere with
-- the initial value.
/-- A process satisfying the Exercise 11.2.8 transition law is constant in time up to
almost-everywhere equality, with time slices equal almost everywhere to the initial state. -/
theorem exercise1128_ae_eq_initial {p : ℝ} {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ n, Measurable (X n))
    (hX_transition : exercise1128Transition μ p X hX_meas) (n : ℕ) :
    X n =ᵐ[μ] X 0 := sorry

-- Proof sketch: `exercise1128_succ_ae_eq_self` gives the one-step almost-everywhere identity
-- needed by `MeasureTheory.martingale_nat` for the natural filtration; strong measurability comes
-- from `hX_meas`, and integrability follows from boundedness of the binary-valued process supplied
-- by `exercise1128Transition`.
/-- Exercise 11.2.8 (1): a real-valued process satisfying the displayed binary transition law from
the exercise is a martingale with respect to its natural filtration. -/
theorem binary_transition_process_martingale {p : ℝ}
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ n, Measurable (X n))
    (hX_transition : exercise1128Transition μ p X hX_meas) :
    Martingale X (Filtration.natural X fun n ↦ (hX_meas n).stronglyMeasurable) μ := sorry

-- Proof sketch: `exercise1128_ae_eq_initial` yields a countable family of almost-everywhere
-- equalities. Intersecting the corresponding full-measure sets gives a full-measure set on which
-- every time slice equals `X 0`, so the sample paths converge there to `X 0`.
/-- Exercise 11.2.8 (2): under the same binary transition hypotheses, the process converges almost
surely, and its almost sure limit is the initial random variable `X 0`. -/
theorem binary_transition_process_ae_tendsto_initial {p : ℝ} {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ n, Measurable (X n))
    (hX_transition : exercise1128Transition μ p X hX_meas) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (X 0 ω)) := sorry

-- Proof sketch: combine `binary_transition_process_martingale` with the previous almost-sure
-- convergence statement to identify the natural-filtration limit process with `X 0` almost
-- everywhere, then use `HasLaw.congr`.
/-- Exercise 11.2.8 (3): the canonical almost sure limit of the process has the same distribution
as the initial state `X 0`. -/
theorem binary_transition_process_limitProcess_hasLaw_initial {p : ℝ}
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ n, Measurable (X n))
    (hX_transition : exercise1128Transition μ p X hX_meas) :
    HasLaw
      ((Filtration.natural X fun n ↦ (hX_meas n).stronglyMeasurable).limitProcess X μ)
      (μ.map (X 0)) μ := sorry

end ProbabilityTheory
