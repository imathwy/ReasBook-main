

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_19_16 (from Items/Chap19) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [Fintype E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]

variable {p C : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable [IsRandomWalkWithWeights p C]
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]

/- Layering for Corollary 19.16:
- `source-facing`: the first-entrance representation formula for an electrical potential on a
  finite conductance network.
- `core/canonical`: `IsElectricalPotential` as the owner abstraction, together with
  `IsRandomWalkWithWeights`, `hittingAfter X A 1`, and
  `stoppedValue X (hittingAfter X A 1)`.
- `bridge/view`: the realization hypothesis identifies the textbook random walk with the kernel
  owner `discreteMatrixKernel p`, while the stopping-time hypothesis keeps the source's
  probability-one finiteness event. -/

-- Proof sketch: `hu` gives harmonicity on `E \ A` by
-- `electricalPotential_isHarmonicOn_compl`. Since `E` is finite, the electrical potential is
-- bounded, so optional stopping applies to `u (X_n)` stopped at the first entrance time
-- `hittingAfter X A 1`. The assumption `hτ` then identifies the stopped value with the boundary
-- value `u (X_{τ_A})`.
/-- Corollary 19.16: on a finite conductance network, the value of an electrical potential at a
starting point `x ∉ A` equals the expected value at the first entrance point into `A`, provided
that this first entrance time is almost surely finite. In Lean, `X_{τ_A}` is represented by
`stoppedValue X (hittingAfter X A 1)`. -/
theorem electricalPotential_eq_expectation_at_firstEntrance
    {A : Set E} {u : E → ℝ} {x : E}
    (hu : IsElectricalPotential C A u) (hx : x ∉ A)
    (hτ : (P x : Measure Ω) {ω | hittingAfter X A 1 ω < ⊤} = 1) :
    u x = ∫ ω, u (stoppedValue X (hittingAfter X A 1) ω) ∂(P x : Measure Ω) := sorry

end ProbabilityTheory
