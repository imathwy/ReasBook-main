import ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter MeasureTheory
open scoped BoundedContinuousFunction CompactlySupported Topology unitInterval

universe u

namespace MeasureTheory.SignedMeasure

section General

variable {E : Type u} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]

/-- Integration of a bounded continuous real-valued test function against a signed measure, via
its Jordan decomposition. This is the signed-measure extension of the weak test-function pairing
from Definition 13.12 (1). -/
def weakIntegral (f : E →ᵇ ℝ) : SignedMeasure E → ℝ :=
  fun φ ↦
    ∫ x, f x ∂φ.toJordanDecomposition.posPart - ∫ x, f x ∂φ.toJordanDecomposition.negPart

omit [BorelSpace E] in
@[simp] theorem weakIntegral_apply (f : E →ᵇ ℝ) (φ : SignedMeasure E) :
    weakIntegral f φ =
      ∫ x, f x ∂φ.toJordanDecomposition.posPart -
        ∫ x, f x ∂φ.toJordanDecomposition.negPart :=
  rfl

/-- Integration of a compactly supported continuous real-valued test function against a signed
measure. This is the signed-measure extension of the vague test-function pairing from
Definition 13.12 (2). -/
def vagueIntegral (f : C_c(E, ℝ)) : SignedMeasure E → ℝ :=
  weakIntegral f.toBoundedContinuousFunction

omit [BorelSpace E] in
@[simp] theorem vagueIntegral_apply (f : C_c(E, ℝ)) (φ : SignedMeasure E) :
    vagueIntegral f φ =
      ∫ x, f x ∂φ.toJordanDecomposition.posPart -
        ∫ x, f x ∂φ.toJordanDecomposition.negPart :=
  rfl

/-- The zero signed measure has zero weak integral against every bounded continuous real-valued
test function. -/
theorem weakIntegral_zero (f : E →ᵇ ℝ) : weakIntegral f 0 = 0 := sorry

/-- A signed measure is Radon when both parts of its Jordan decomposition are Radon measures. This
is the source-facing domain condition for vague convergence of signed measures. -/
def IsRadon (φ : SignedMeasure E) : Prop :=
  IsRadonMeasure φ.toJordanDecomposition.posPart ∧
    IsRadonMeasure φ.toJordanDecomposition.negPart

/-- The weak topology on signed measures is the coarsest topology making integration against every
bounded continuous real-valued test function continuous. -/
@[reducible] def weakTopology (E : Type u) [MetricSpace E] [MeasurableSpace E] [BorelSpace E] :
    TopologicalSpace (SignedMeasure E) :=
  ⨅ f : E →ᵇ ℝ, TopologicalSpace.induced (weakIntegral f) inferInstance

instance instTopologicalSpaceSignedMeasure :
    TopologicalSpace (SignedMeasure E) :=
  weakTopology E

/-- A sequence of signed measures converges weakly when it converges in the owner topology
`SignedMeasure.weakTopology`. -/
def weaklyConvergesTo (φs : ℕ → SignedMeasure E) (φ : SignedMeasure E) : Prop :=
  Tendsto φs atTop (𝓝 φ)

/-- A sequence of signed measures converges weakly exactly when every bounded continuous
real-valued test integral converges. -/
theorem weaklyConvergesTo_iff {φs : ℕ → SignedMeasure E} {φ : SignedMeasure E} :
    weaklyConvergesTo φs φ ↔
      ∀ f : E →ᵇ ℝ,
        Tendsto (fun n ↦ weakIntegral f (φs n)) atTop (𝓝 (weakIntegral f φ)) := by
  simp [weaklyConvergesTo, nhds_iInf, nhds_induced, Filter.tendsto_iInf,
    Filter.tendsto_comap_iff, Function.comp_def]

/-- Weak convergence to the zero signed measure amounts to convergence of every bounded continuous
test integral to `0`. -/
theorem weaklyConvergesTo_zero_iff (φs : ℕ → SignedMeasure E) :
    weaklyConvergesTo φs 0 ↔
      ∀ f : E →ᵇ ℝ, Tendsto (fun n ↦ weakIntegral f (φs n)) atTop (𝓝 0) := by
  constructor
  · intro h f
    simpa [weakIntegral, SignedMeasure.toJordanDecomposition_zero] using
      (weaklyConvergesTo_iff.mp h) f
  · intro h
    exact weaklyConvergesTo_iff.mpr fun f ↦ by
      simpa [weakIntegral, SignedMeasure.toJordanDecomposition_zero] using h f

/-- A sequence of signed measures converges vaguely when both the limit and the whole sequence are
Radon signed measures and all compactly supported continuous real-valued test integrals converge.
This is the signed-measure extension of Definition 13.12 (2). -/
def vaguelyConvergesTo (φs : ℕ → SignedMeasure E) (φ : SignedMeasure E) : Prop :=
  IsRadon φ ∧
    (∀ n, IsRadon (φs n)) ∧
    ∀ f : C_c(E, ℝ), Tendsto (fun n ↦ vagueIntegral f (φs n)) atTop (𝓝 (vagueIntegral f φ))

/- Vague convergence of signed measures means exactly convergence of integrals against all
compactly supported continuous real-valued test functions, together with the ambient Radon signed
measure assumptions on the sequence and its limit. -/
omit [BorelSpace E] in
theorem vaguelyConvergesTo_iff (φs : ℕ → SignedMeasure E) (φ : SignedMeasure E) :
    vaguelyConvergesTo φs φ ↔
      IsRadon φ ∧
        (∀ n, IsRadon (φs n)) ∧
        ∀ f : C_c(E, ℝ),
          Tendsto (fun n ↦ vagueIntegral f (φs n)) atTop (𝓝 (vagueIntegral f φ)) :=
  Iff.rfl

end General

end MeasureTheory.SignedMeasure

section UnitIntervalCounterexample

open MeasureTheory.SignedMeasure

/-- The reciprocal point `1 / (n + 2)` belongs to the closed unit interval. -/
lemma reciprocal_nat_add_two_mem_unit_interval (n : ℕ) :
    (((n : ℝ) + 2)⁻¹) ∈ Set.Icc (0 : ℝ) 1 := sorry

/-- The point `1 / (n + 2)` in the closed unit interval. -/
def reciprocal_unit_interval_point (n : ℕ) : I :=
  ⟨((n : ℝ) + 2)⁻¹, reciprocal_nat_add_two_mem_unit_interval n⟩

/-- The value of `reciprocal_unit_interval_point`. -/
theorem reciprocal_unit_interval_point_val (n : ℕ) :
    ((reciprocal_unit_interval_point n : I) : ℝ) = ((n : ℝ) + 2)⁻¹ :=
  rfl

/-- The point `2 / (n + 2)` belongs to the closed unit interval. -/
lemma double_reciprocal_nat_add_two_mem_unit_interval (n : ℕ) :
    ((2 : ℝ) / ((n : ℝ) + 2)) ∈ Set.Icc (0 : ℝ) 1 := sorry

/-- The point `2 / (n + 2)` in the closed unit interval. -/
def double_reciprocal_unit_interval_point (n : ℕ) : I :=
  ⟨(2 : ℝ) / ((n : ℝ) + 2), double_reciprocal_nat_add_two_mem_unit_interval n⟩

/-- The value of `double_reciprocal_unit_interval_point`. -/
theorem double_reciprocal_unit_interval_point_val (n : ℕ) :
    ((double_reciprocal_unit_interval_point n : I) : ℝ) =
      (2 : ℝ) / ((n : ℝ) + 2) :=
  rfl

/-- The dyadic point `2^{-n}` belongs to the closed unit interval. -/
lemma dyadic_inverse_mem_unit_interval (n : ℕ) :
    (((2 : ℝ) ^ n)⁻¹) ∈ Set.Icc (0 : ℝ) 1 := sorry

/-- The dyadic point `2^{-n}` in the closed unit interval. -/
def dyadic_unit_interval_point (n : ℕ) : I :=
  ⟨((2 : ℝ) ^ n)⁻¹, dyadic_inverse_mem_unit_interval n⟩

/-- The value of `dyadic_unit_interval_point`. -/
theorem dyadic_unit_interval_point_val (n : ℕ) :
    ((dyadic_unit_interval_point n : I) : ℝ) = ((2 : ℝ) ^ n)⁻¹ :=
  rfl

/-- The shifted Dirac-difference sequence used in the signed weak-convergence counterexample on
`[0,1]`. -/
def shifted_point_mass_difference (n : ℕ) : SignedMeasure I :=
  (Measure.dirac (reciprocal_unit_interval_point n)).toSignedMeasure -
    (Measure.dirac (double_reciprocal_unit_interval_point n)).toSignedMeasure

/-- The shifted Dirac-difference sequence is the difference of the two indicated Dirac masses. -/
theorem shifted_point_mass_difference_def (n : ℕ) :
    shifted_point_mass_difference n =
      (Measure.dirac (reciprocal_unit_interval_point n)).toSignedMeasure -
        (Measure.dirac (double_reciprocal_unit_interval_point n)).toSignedMeasure :=
  rfl

/-- Part (i): every fixed rescaling of the shifted Dirac-difference sequence converges weakly to
zero for the signed weak-convergence notion from this exercise. -/
theorem weakly_convergent_rescalings_of_shifted_point_mass_difference {C : ℝ} :
    weaklyConvergesTo (fun n ↦ C • shifted_point_mass_difference n) 0 := sorry

/-- Part (ii): if the weak topology on signed measures over `[0,1]` were metrizable, one could
choose rescaling factors tending to infinity while retaining weak convergence to zero. -/
theorem metrizable_weak_convergence_yields_unbounded_rescalings
    [TopologicalSpace.MetrizableSpace (SignedMeasure I)] :
    ∃ C : ℕ → ℝ,
      Monotone C ∧ Tendsto C atTop atTop ∧ (∀ n, 0 < C n) ∧
        weaklyConvergesTo (fun n ↦ C n • shifted_point_mass_difference n) 0 := sorry

/-- Part (iii): an unbounded positive rescaling sequence admits a bounded continuous real-valued
weak test function on `[0,1]` whose integrals against the rescaled signed measures fail to
converge to `0`. On the compact interval `[0,1]`, this is equivalent to using an ordinary
continuous test function. -/
theorem unbounded_rescalings_admit_obstructing_bounded_continuous_function
    {C : ℕ → ℝ} (hC_pos : ∀ n, 0 < C n) (hC_top : Tendsto C atTop atTop) :
    ∃ f : I →ᵇ ℝ,
      (∀ n, f (dyadic_unit_interval_point n) = (-1 : ℝ) ^ n / Real.sqrt (C n)) ∧
        ¬ Tendsto
          (fun n ↦ weakIntegral f (C n • shifted_point_mass_difference n))
          atTop (𝓝 0) := sorry

/-- Exercise 13.2.7: weak convergence on signed measures over `[0,1]` is not induced by any
metric. -/
theorem weak_convergence_on_signed_measures_over_unit_interval_not_metrizable :
    ¬ TopologicalSpace.MetrizableSpace (SignedMeasure I) := sorry

end UnitIntervalCounterexample
