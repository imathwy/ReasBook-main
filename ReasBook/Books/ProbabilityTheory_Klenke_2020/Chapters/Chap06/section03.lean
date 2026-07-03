import Mathlib.Probability.Moments.MGFAnalytic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_6_3_1 (from Items/Chap06) -/
open MeasureTheory ProbabilityTheory Set
open scoped Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
-- Proof sketch: `0` belongs to `integrableExpSet X P` because `exp (0 * X) = 1` is integrable on
-- a probability space, and the interval property is the canonical convexity result
-- `convex_integrableExpSet`, transported to `OrdConnected` on `ℝ`.
/-- Exercise 6.3.1 (1): for a finite measure, hence in particular for a probability measure, the
effective domain `D = {t : ℝ | log (𝔼[exp (tX)]) < ∞}`, formalized as `integrableExpSet X P`, is
nonempty and is an interval. -/
theorem integrableExpSet_nonempty_ordConnected (P : Measure Ω) [IsFiniteMeasure P]
    (X : Ω → ℝ) :
    (integrableExpSet X P).Nonempty ∧ OrdConnected (integrableExpSet X P) := by
  exact ⟨⟨0, by simp [integrableExpSet]⟩, convex_integrableExpSet.ordConnected⟩

-- Proof sketch: mathlib proves that the cumulant-generating function `cgf X P` is analytic on
-- `interior (integrableExpSet X P)` via `analyticOn_cgf`; analyticity over `ℝ` implies `C^∞`
-- regularity there by `AnalyticOn.contDiffOn_of_completeSpace`.
/-- Exercise 6.3.1 (2): for any measure, hence in particular for a probability measure, the
cumulant-generating function `Λ(t) = log (𝔼[exp (tX)])`, formalized as `cgf X P`, is infinitely
often differentiable on the interior of its effective domain. -/
theorem cgf_contDiffOn_interior_integrableExpSet (P : Measure Ω)
    (X : Ω → ℝ) :
    ContDiffOn ℝ ⊤ (cgf X P) (interior (integrableExpSet X P)) :=
  analyticOn_cgf.contDiffOn_of_completeSpace

/-! ### Remark_6_3 (from Items/Chap06) -/
open Filter MeasureTheory Set
open scoped Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [TopologicalSpace E]

-- Proof sketch: the textbook monotone finite-measure exhaustion is stronger than needed here; the
-- actual almost-everywhere equivalence is exactly the canonical restricted-measure `iUnion`
-- statement.
/-- Remark 6.3: if a countable family of sets `A n` covers `univ`, then `f n` converges to `g`
almost everywhere with respect to `μ` if and only if this convergence holds almost everywhere with
respect to each restricted measure `μ.restrict (A n)`. -/
theorem ae_tendsto_iff_forall_ae_restrict_of_iUnion_eq_univ
    (μ : Measure Ω) (A : ℕ → Set Ω) {f : ℕ → Ω → E} {g : Ω → E}
    (hA_union : (⋃ n, A n) = univ) :
    (∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) ↔
      ∀ n, ∀ᵐ x ∂μ.restrict (A n), Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)) := by
  let P : Ω → Prop := fun x ↦ Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))
  simpa [P, hA_union] using ae_restrict_iUnion_iff A P
