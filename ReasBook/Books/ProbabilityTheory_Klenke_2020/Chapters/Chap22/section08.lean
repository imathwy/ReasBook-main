import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_22_8 (from Items/Chap22) -/
open MeasureTheory
open scoped ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

/-- The explicit measure underlying the centered two-point law at support pair `(u,v)` with
`u < 0 ≤ v`. -/
private def negativeNonnegativeTwoPointMeasure
    (z : Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ)) : Measure ℝ :=
  let u : ℝ := z.1
  let v : ℝ := z.2
  ENNReal.ofReal (v / (v - u)) • Measure.dirac u +
    ENNReal.ofReal (-u / (v - u)) • Measure.dirac v

/-- The kernel sending `(u,v)` to the centered two-point law supported on `{u,v}`. -/
def negativeNonnegativeTwoPointKernel :
    Kernel (Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ)) ℝ where
  toFun := negativeNonnegativeTwoPointMeasure
  measurable' := by
    sorry

/-- At `z = (u,v)`, the kernel fiber is the explicit convex combination of the two Dirac masses
at `u` and `v` with zero-mean weights. -/
@[simp] theorem negativeNonnegativeTwoPointKernel_apply
    (u : Set.Iio (0 : ℝ)) (v : Set.Ici (0 : ℝ)) :
    negativeNonnegativeTwoPointKernel (u, v) =
      ENNReal.ofReal ((v : ℝ) / ((v : ℝ) - (u : ℝ))) • Measure.dirac (u : ℝ) +
        ENNReal.ofReal (-(u : ℝ) / ((v : ℝ) - (u : ℝ))) • Measure.dirac (v : ℝ) :=
  rfl

/-- The centered two-point family is a Markov kernel. -/
theorem negativeNonnegativeTwoPointKernel_isMarkovKernel :
    IsMarkovKernel negativeNonnegativeTwoPointKernel := by
  refine ⟨fun z ↦ ?_⟩
  change IsProbabilityMeasure (negativeNonnegativeTwoPointMeasure z)
  sorry

instance : IsMarkovKernel negativeNonnegativeTwoPointKernel :=
  negativeNonnegativeTwoPointKernel_isMarkovKernel

-- Proof sketch: split `μ` into its negative and nonnegative parts, use the textbook construction
-- of the mixing law `θ` on `(-∞,0) × [0,∞)`, identify `μ` with the resulting kernel mixture
-- mixture of the centered two-point laws, and then compute the second moment by integrating the
-- explicit second moment of each two-point law.
/-- Lemma 22.8: every centered probability measure on `ℝ` with finite second moment is a mixture
of centered two-point laws supported on one negative and one nonnegative point, and its second
moment is the negative `uv`-moment of the mixing measure. -/
theorem exists_centered_two_point_mixture
    (μ : ProbabilityMeasure ℝ)
    (h_mean : ∫ x, x ∂(μ : Measure ℝ) = 0)
    (h_sq : Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ)) :
    ∃ θ : ProbabilityMeasure (Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ)),
      (μ : Measure ℝ) =
        negativeNonnegativeTwoPointKernel ∘ₘ
          (θ : Measure (Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ))) ∧
      ∫ x, x ^ 2 ∂(μ : Measure ℝ) =
        ∫ z, -((z.1 : ℝ) * z.2) ∂(θ : Measure (Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ))) :=
  sorry

end ProbabilityTheory
