import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_7_5_1 (from Items/Chap07) -/
open MeasureTheory
open scoped MeasureTheory

universe u

namespace MeasureTheory
namespace SignedMeasure

variable {Ω : Type u} [MeasurableSpace Ω]

open VectorMeasure

-- Proof sketch: this is exactly `VectorMeasure.AbsolutelyContinuous.ennrealToMeasure` specialized
-- to `μ.toENNRealVectorMeasure`, together with `ennrealToMeasure_toENNRealVectorMeasure`.
private theorem absolutelyContinuous_iff_forall_apply_eq_zero (φ : SignedMeasure Ω)
    (μ : Measure Ω) :
    φ ≪ᵥ μ.toENNRealVectorMeasure ↔
      ∀ A : Set Ω, μ A = 0 → φ A = 0 := by
  simpa [ennrealToMeasure_toENNRealVectorMeasure] using
    (AbsolutelyContinuous.ennrealToMeasure :
      (∀ ⦃s : Set Ω⦄, (μ.toENNRealVectorMeasure).ennrealToMeasure s = 0 → φ s = 0) ↔
        φ ≪ᵥ μ.toENNRealVectorMeasure).symm

-- Proof sketch: for the forward direction use the canonical Radon--Nikodym witness `φ.rnDeriv μ`
-- and `SignedMeasure.absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq`; for the reverse
-- direction, `Measure.withDensityᵥ_absolutelyContinuous` gives the absolute continuity.
/-- Exercise 7.5.1: For a `σ`-finite measure `μ`, a signed measure `φ` is absolutely continuous
with respect to `μ` if and only if there is an integrable real-valued density `f` with
`φ = μ.withDensityᵥ f`. -/
theorem absolutelyContinuous_iff_exists_integrable_density (μ : Measure Ω) [SigmaFinite μ]
    (φ : SignedMeasure Ω) :
    φ ≪ᵥ μ.toENNRealVectorMeasure ↔
      ∃ f : Ω → ℝ, Integrable f μ ∧ μ.withDensityᵥ f = φ := by
  constructor
  · intro hφ
    refine ⟨φ.rnDeriv μ, integrable_rnDeriv φ μ, ?_⟩
    exact (absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq φ μ).mp hφ
  · rintro ⟨f, hf, rfl⟩
    exact Measure.withDensityᵥ_absolutelyContinuous μ f

-- Proof sketch: rewrite the right-hand side using
-- `absolutelyContinuous_iff_exists_integrable_density`; the remaining equivalence is exactly
-- `absolutelyContinuous_iff_forall_apply_eq_zero`.
/-- Exercise 7.5.1 in textbook wording: for a `σ`-finite measure `μ`, a signed measure `φ`
vanishes on every `μ`-null set if and only if there is an integrable real-valued density `f`
with `φ = μ.withDensityᵥ f`. -/
theorem vanishes_on_null_iff_exists_integrable_density (μ : Measure Ω) [SigmaFinite μ]
    (φ : SignedMeasure Ω) :
    (∀ A : Set Ω, μ A = 0 → φ A = 0) ↔
      ∃ f : Ω → ℝ, Integrable f μ ∧ μ.withDensityᵥ f = φ := by
  rw [← absolutelyContinuous_iff_exists_integrable_density μ φ]
  exact (absolutelyContinuous_iff_forall_apply_eq_zero φ μ).symm

/- The canonical density witness for an absolutely continuous signed measure is `φ.rnDeriv μ`. -/
recall absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq (φ : SignedMeasure Ω) (μ : Measure Ω)
    [SigmaFinite μ] :
  φ ≪ᵥ μ.toENNRealVectorMeasure ↔ μ.withDensityᵥ (φ.rnDeriv μ) = φ

end SignedMeasure
end MeasureTheory

/-! ### Exercise_7_5_2 (from Items/Chap07) -/
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/- Exercise 7.5.2 (1): for finite measures, the chain rule for Radon--Nikodym derivatives is the
canonical theorem `Measure.rnDeriv_mul_rnDeriv`; the textbook assumption `μ ≪ ξ` is redundant for
the statement itself. -/
recall MeasureTheory.Measure.rnDeriv_mul_rnDeriv

private theorem rnDeriv_add_compl (μ ν : Measure Ω) [SigmaFinite μ] [SigmaFinite ν] :
    μ.rnDeriv (μ + ν) =ᵐ[μ] fun x ↦ 1 - ν.rnDeriv (μ + ν) x := by
  have h_add : (μ + ν).rnDeriv (μ + ν) =ᵐ[μ] μ.rnDeriv (μ + ν) + ν.rnDeriv (μ + ν) :=
    (ae_add_measure_iff.mp (rnDeriv_add' μ ν (μ + ν))).1
  have h_one : (μ + ν).rnDeriv (μ + ν) =ᵐ[μ] 1 :=
    (ae_add_measure_iff.mp (μ + ν).rnDeriv_self).1
  have h_le : ν ≤ μ + ν := by
    intro s
    rw [Measure.add_apply]
    exact le_add_of_nonneg_left (zero_le (μ s))
  have hμ_add : μ ≪ μ + ν := rfl.absolutelyContinuous.add_right _
  have h_rn_le : ν.rnDeriv (μ + ν) ≤ᵐ[μ] 1 :=
    hμ_add <| rnDeriv_le_one_of_le h_le
  filter_upwards [h_add, h_one, h_rn_le] with x hx_add hx_one hx_le
  rw [hx_one, Pi.add_apply] at hx_add
  exact ENNReal.eq_sub_of_add_eq' (by simp) hx_add.symm

-- Proof sketch: start from `Measure.rnDeriv_eq_div_rnDeriv_add` for the pair `(ν, μ)`, then
-- rewrite the denominator `μ.rnDeriv (μ + ν)` as `1 - ν.rnDeriv (μ + ν)` using the identities
-- relating the Radon--Nikodym derivatives of `μ` and `ν` with respect to `μ + ν`.
/-- Exercise 7.5.2 (2): For σ-finite measures and the canonical density `f = dν/d(μ + ν)`, one has
`dν/dμ = f / (1 - f)` `μ`-almost everywhere. -/
theorem rnDeriv_eq_div_one_sub_rnDeriv_add {μ ν : Measure Ω} [SigmaFinite μ] [SigmaFinite ν] :
    ν.rnDeriv μ =ᵐ[μ] fun ω ↦ ν.rnDeriv (μ + ν) ω / (1 - ν.rnDeriv (μ + ν) ω) := by
  have h_ratio : ν.rnDeriv μ =ᵐ[μ] fun x ↦ ν.rnDeriv (μ + ν) x / μ.rnDeriv (μ + ν) x := by
    simpa [add_comm] using ν.rnDeriv_eq_div_rnDeriv_add μ
  refine h_ratio.trans ?_
  filter_upwards [rnDeriv_add_compl μ ν] with x hx
  rw [hx]

/-! ### Example_7_5 (from Items/Chap07) -/
universe u v

open MeasureTheory Set
open unitInterval
open scoped NNReal unitInterval

/- Example 7.5 (1): A subset of `ℝ` is convex exactly when it is an interval, expressed in Lean
as order-connectedness. This is the canonical mathlib theorem
`convex_iff_ordConnected`; specializing it to `ℝ` gives the textbook statement. -/
recall convex_iff_ordConnected

/- Example 7.5 (2): Every linear subspace of a vector space is a convex subset of the ambient
space. This is exactly the canonical mathlib theorem `Submodule.convex`. -/
recall Submodule.convex

-- Proof sketch: if `μ` and `ν` both have total mass `1`, then any convex combination
-- `a • μ + b • ν` with `a + b = 1` again has total mass `1`.
/-- Example 7.5 (3): On a measurable space, the set of all probability measures is convex inside
the space of measures. -/
theorem probability_measures_convex {Ω : Type u} [MeasurableSpace Ω] :
    Convex ℝ≥0 {μ : Measure Ω | IsProbabilityMeasure μ} := by
  rw [convex_iff_add_mem]
  intro μ hμ ν hν a b ha hb hab
  letI : IsProbabilityMeasure μ := hμ
  letI : IsProbabilityMeasure ν := hν
  let p : I := ⟨a, ⟨ha, by
    have h : a ≤ a + b := le_add_of_nonneg_right hb
    simpa [hab] using h⟩⟩
  have hp : toNNReal p = a := rfl
  have hσp : toNNReal (σ p) = b := by
    apply NNReal.eq
    have hs : (a : ℝ) + (toNNReal (σ p) : ℝ) = 1 := by
      simpa [hp] using congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) (toNNReal_add_toNNReal_symm p)
    have hab' : (a : ℝ) + (b : ℝ) = 1 := by
      exact_mod_cast hab
    linarith
  simpa [hp, hσp] using
    (inferInstance : IsProbabilityMeasure (toNNReal p • μ + toNNReal (σ p) • ν))
