import ProbabilityTheory_Klenke_2020.Items.Chap07.Corollary_7_45
import ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_53
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BoundedContinuousFunction

noncomputable section

universe u

namespace ProbabilityTheory

section Wasserstein

variable {E : Type u} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]

/-- Example 17.55: the Wasserstein distance between two probability measures is the infimum, over
all couplings `π` of `P` and `Q`, of the transport cost `∫ dist(x, y) dπ(x, y)`. -/
def wassersteinDistance (P Q : ProbabilityMeasure E) : ℝ≥0∞ :=
  sInf {c : ℝ≥0∞ | ∃ π : ProbabilityMeasure (E × E),
    IsCoupling π P Q ∧
      c = ∫⁻ z : E × E, ENNReal.ofReal (dist z.1 z.2) ∂(π : Measure (E × E))}

variable [CompleteSpace E] [SecondCountableTopology E]
variable [BoundedSpace E]

-- Proof sketch: this is the Kantorovich--Rubinstein duality theorem; identify the primal
-- coupling infimum with the supremum of the signed integral difference over bounded continuous
-- real-valued `1`-Lipschitz test functions, then coerce the resulting real supremum into
-- `ℝ≥0∞`.
/-- The Kantorovich--Rubinstein formula expresses `wassersteinDistance P Q` as the dual supremum
over bounded continuous `1`-Lipschitz real-valued test functions on a bounded Polish metric
space. -/
theorem wassersteinDistance_eq_sSup_lipschitz
    (P Q : ProbabilityMeasure E) :
    wassersteinDistance P Q =
      ENNReal.ofReal
        (sSup {r : ℝ | ∃ f : E →ᵇ ℝ,
          LipschitzWith 1 f ∧
            r = ∫ x, f x ∂(P : Measure E) - ∫ x, f x ∂(Q : Measure E)}) := sorry

end Wasserstein

section TotalVariation

variable {E : Type u} [MeasurableSpace E]

/-- The total variation distance between two probability measures is half of the canonical
signed-measure total-variation norm of their difference. -/
def totalVariationDistance (P Q : ProbabilityMeasure E) : ℝ :=
  SignedMeasure.totalVariationNorm E
      ((P : Measure E).toSignedMeasure - (Q : Measure E).toSignedMeasure) / 2

/-- The probability total variation distance is the normalized signed-measure total-variation
norm of `P - Q`. -/
theorem totalVariationDistance_eq_half_totalVariationNorm
    (P Q : ProbabilityMeasure E) :
    totalVariationDistance P Q =
      SignedMeasure.totalVariationNorm E
        ((P : Measure E).toSignedMeasure - (Q : Measure E).toSignedMeasure) / 2 := rfl

-- Proof sketch: rewrite the total variation norm of the signed difference `P - Q` by the dual
-- characterization of total variation on bounded measurable test functions and use that
-- probability measures are finite.
/-- The probability total variation distance is half of the supremum of the signed integral
difference over measurable real-valued test functions bounded in absolute value by `1`. -/
theorem totalVariationDistance_eq_sSup_bounded_measurable
    (P Q : ProbabilityMeasure E) :
    totalVariationDistance P Q =
      sSup {r : ℝ | ∃ f : E → ℝ,
        Measurable f ∧
          (∀ x, ‖f x‖ ≤ 1) ∧
          r = ∫ x, f x ∂(P : Measure E) - ∫ x, f x ∂(Q : Measure E)} / 2 := sorry

-- Proof sketch: among all couplings of `P` and `Q`, minimize the mass away from the diagonal.
-- This off-diagonal mass equals the probability that the coupled coordinates disagree and yields
-- the classical coupling representation of total variation.
/-- The total variation distance is the infimum, over all couplings of `P` and `Q`, of the mass
that the coupling assigns to the complement of the diagonal in `E × E`. -/
theorem totalVariationDistance_eq_sInf_couplings_offDiagonal
    (P Q : ProbabilityMeasure E) :
    totalVariationDistance P Q =
      sInf {r : ℝ | ∃ π : ProbabilityMeasure (E × E),
        IsCoupling π P Q ∧
          r = ((π : Measure (E × E))
            ((Set.univ : Set (E × E)) \ Set.diagonal E)).toReal} := sorry

end TotalVariation

end ProbabilityTheory
