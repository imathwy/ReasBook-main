import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

namespace MeasureTheory.Measure

/-- A law on `ℝ` has the textbook finite absolute-moment root-growth limit property if all of its
absolute moments are finite and the normalized nth roots of those absolute moments converge to a
finite real limit. -/
def HasFiniteAbsoluteMomentRootLimit (μ : Measure ℝ) : Prop :=
  (∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) μ) ∧
    ∃ α : ℝ,
      Tendsto
        (fun n : ℕ ↦ ((n : ℝ)⁻¹) * Real.rpow (moment (fun x : ℝ ↦ |x|) n μ) (1 / (n : ℝ)))
        atTop (𝓝 α)

/-- Finite absolute-moment root-growth limit is exactly finiteness of all absolute moments together
with convergence of the normalized absolute-moment roots. -/
@[simp]
theorem hasFiniteAbsoluteMomentRootLimit_iff (μ : Measure ℝ) :
    Measure.HasFiniteAbsoluteMomentRootLimit μ ↔
      (∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) μ) ∧
        ∃ α : ℝ,
          Tendsto
            (fun n : ℕ ↦
              ((n : ℝ)⁻¹) * Real.rpow (moment (fun x : ℝ ↦ |x|) n μ) (1 / (n : ℝ)))
            atTop (𝓝 α) := by
  rfl

/-- A law on `ℝ` is moment determinate if it is a probability measure, has genuine finite absolute
moments of every order, and every comparison probability law with the same finite moments is equal
to it. -/
def IsMomentDeterminate (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧
    (∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) μ) ∧
    ∀ ⦃ν : Measure ℝ⦄, IsProbabilityMeasure ν →
      (∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) ν) →
      (∀ n : ℕ, moment id n μ = moment id n ν) →
      μ = ν

/-- Moment determinacy is exactly the conjunction of being a probability law, having all absolute
moments finite, and uniqueness among probability laws on `ℝ` with the same genuinely finite
moments. -/
@[simp]
theorem isMomentDeterminate_iff (μ : Measure ℝ) :
    Measure.IsMomentDeterminate μ ↔
      IsProbabilityMeasure μ ∧
        (∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) μ) ∧
        ∀ ⦃ν : Measure ℝ⦄, IsProbabilityMeasure ν →
          (∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) ν) →
          (∀ n : ℕ, moment id n μ = moment id n ν) →
          μ = ν := by
  rfl

/-- A moment-determinate law has finite absolute moments of every order. -/
theorem IsMomentDeterminate.integrable_abs_pow {μ : Measure ℝ}
    (hμ : Measure.IsMomentDeterminate μ) (n : ℕ) :
    Integrable (fun x : ℝ ↦ |x| ^ n) μ :=
  hμ.2.1 n

/-- A moment-determinate law is equal to every probability law on `ℝ` with the same genuinely
finite moments. -/
theorem IsMomentDeterminate.eq_of_forall_moment_eq {μ ν : Measure ℝ}
    (hμ : Measure.IsMomentDeterminate μ) [IsProbabilityMeasure ν]
    (hν_moments : ∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) ν)
    (h_moments : ∀ n : ℕ, moment id n μ = moment id n ν) :
    μ = ν :=
  hμ.2.2 inferInstance hν_moments h_moments

end MeasureTheory.Measure

/-- A real random variable has the textbook finite absolute-moment root-growth limit property if
it is measurable and its law has the corresponding owner-level property. -/
def HasFiniteAbsoluteMomentRootLimit (P : Measure Ω) (X : Ω → ℝ) : Prop :=
  Measurable X ∧ Measure.HasFiniteAbsoluteMomentRootLimit (P.map X)

/-- The source-facing finite absolute-moment root-growth property is exactly measurability together
with the owner-level property of the pushforward law. -/
@[simp]
theorem hasFiniteAbsoluteMomentRootLimit_iff (P : Measure Ω) (X : Ω → ℝ) :
    HasFiniteAbsoluteMomentRootLimit P X ↔
      Measurable X ∧ Measure.HasFiniteAbsoluteMomentRootLimit (P.map X) := by
  rfl

/-- A real random variable is moment determinate if it is measurable and its law is moment
determinate. -/
def IsMomentDeterminate (P : Measure Ω) (X : Ω → ℝ) : Prop :=
  Measurable X ∧ Measure.IsMomentDeterminate (P.map X)

/-- The source-facing moment-determinacy predicate is exactly measurability together with the
owner-level predicate on the pushforward law. -/
@[simp]
theorem isMomentDeterminate_iff (P : Measure Ω) (X : Ω → ℝ) :
    IsMomentDeterminate P X ↔ Measurable X ∧ Measure.IsMomentDeterminate (P.map X) := by
  rfl

private theorem integrable_abs_pow_map_iff (P : Measure Ω) {X : Ω → ℝ} (hX : Measurable X)
    (n : ℕ) :
    Integrable (fun x : ℝ ↦ |x| ^ n) (P.map X) ↔ Integrable (fun ω ↦ |X ω| ^ n) P := by
  simpa [Function.comp] using
    (integrable_map_measure
      (by
        fun_prop : AEStronglyMeasurable (fun x : ℝ ↦ |x| ^ n) (P.map X))
      hX.aemeasurable)

private theorem moment_id_map_eq (P : Measure Ω) {X : Ω → ℝ} (hX : Measurable X) (n : ℕ) :
    moment id n (P.map X) = moment X n P := by
  rw [moment, moment]
  simpa using
    (integral_map hX.aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ ↦ x ^ n) (P.map X)))

/-- If `X` is moment determinate, then any other measurable real random variable with genuinely
finite absolute moments of every order and the same moments has the same law. -/
theorem IsMomentDeterminate.map_eq {P : Measure Ω} {X : Ω → ℝ} (hX_det : IsMomentDeterminate P X)
    {Ω' : Type*} [MeasurableSpace Ω'] (Q : Measure Ω') [IsProbabilityMeasure Q] (Y : Ω' → ℝ)
    (hY : Measurable Y) (hY_moments : ∀ n : ℕ, Integrable (fun ω ↦ |Y ω| ^ n) Q)
    (h_moments : ∀ n : ℕ, moment X n P = moment Y n Q) :
    P.map X = Q.map Y := by
  rcases hX_det with ⟨hX, hPX_det⟩
  haveI : IsProbabilityMeasure (Q.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  exact hPX_det.eq_of_forall_moment_eq
    (fun n ↦ (integrable_abs_pow_map_iff Q hY n).2 (hY_moments n))
    (fun n ↦ by
      simpa [moment_id_map_eq P hX n, moment_id_map_eq Q hY n] using h_moments n)

/-- Corollary 15.32: if a probability law on `ℝ` has finite absolute moments of every order and
the normalized nth roots of those absolute moments converge to a finite limit, then its
characteristic function is analytic on `ℝ` and the law is determined by its moments among
probability laws with genuinely finite absolute moments of every order. -/
-- Proof sketch: use the moment-growth hypothesis to obtain a nontrivial analytic neighborhood for
-- the complex moment-generating function, identify the characteristic function on the imaginary
-- axis, and then apply analytic continuation together with `Measure.ext_of_charFun` to recover the
-- law from its moments.
theorem method_of_moments (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Measure.HasFiniteAbsoluteMomentRootLimit μ) :
    AnalyticOn ℝ (charFun μ) Set.univ ∧ Measure.IsMomentDeterminate μ := sorry

/-- Exponential integrability of `|x|` under a probability law implies the method-of-moments
conclusion for that law. -/
-- Proof sketch: exponential integrability of `|x|` gives an open neighborhood of `0` inside the
-- owner interval `integrableExpSet id μ`, hence finite absolute moments of every order and the
-- required absolute-moment root-growth control. The main method-of-moments theorem then applies.
theorem method_of_moments_of_integrable_exp_abs (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {t : ℝ} (ht : 0 < t) (h_exp : Integrable (fun x : ℝ ↦ Real.exp (t * |x|)) μ) :
    AnalyticOn ℝ (charFun μ) Set.univ ∧ Measure.IsMomentDeterminate μ := sorry

/-- Source-facing bridge for Corollary 15.32: if a real random variable has the root-growth
property, then its characteristic function is analytic on `ℝ` and its law is moment determinate. -/
theorem method_of_moments_map (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : HasFiniteAbsoluteMomentRootLimit P X) :
    AnalyticOn ℝ (charFun (P.map X)) Set.univ ∧ IsMomentDeterminate P X := by
  rcases hX with ⟨hX, hPX⟩
  haveI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  exact ⟨(method_of_moments (P.map X) hPX).1, hX, (method_of_moments (P.map X) hPX).2⟩

/-- Source-facing bridge: exponential integrability of `|X|` implies the method-of-moments
conclusion for the law of `X`. -/
theorem method_of_moments_of_integrable_exp_abs_map (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) {t : ℝ} (ht : 0 < t)
    (h_exp : Integrable (fun ω ↦ Real.exp (t * |X ω|)) P) :
    AnalyticOn ℝ (charFun (P.map X)) Set.univ ∧ IsMomentDeterminate P X := by
  haveI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have h_exp_map : Integrable (fun x : ℝ ↦ Real.exp (t * |x|)) (P.map X) := by
    simpa [Function.comp] using
      (integrable_map_measure
        (by
          fun_prop : AEStronglyMeasurable (fun x : ℝ ↦ Real.exp (t * |x|)) (P.map X))
        hX.aemeasurable).2 h_exp
  exact
    ⟨(method_of_moments_of_integrable_exp_abs (P.map X) ht h_exp_map).1,
      hX,
      (method_of_moments_of_integrable_exp_abs (P.map X) ht h_exp_map).2⟩
