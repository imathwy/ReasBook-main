import ProbabilityTheory_Klenke_2020.Chap13.Definition_13_4
import ProbabilityTheory_Klenke_2020.Chap13.Definition_13_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open MeasureTheory Set
open scoped CompactlySupported unitInterval

variable {E : Type u}

/-- The family `Lip₁(E; [0,1])` of `[0,1]`-valued real functions on `E` with Lipschitz constant
at most `1`. -/
def unitIntervalLipschitzRealFunctionSpace (E : Type u) [MetricSpace E] : Set (E → ℝ) :=
  {f | LipschitzWith 1 f ∧ MapsTo f univ I}

/-- The family `C_c(E) ∩ Lip₁(E; [0,1])` inside the canonical owner type `C_c(E, ℝ)`. -/
def compactlySupportedUnitIntervalLipschitzRealMapSpace (E : Type u) [MetricSpace E] :
    Set (C_c(E, ℝ)) :=
  {f | LipschitzWith 1 f ∧ MapsTo f univ I}

-- Proof sketch: apply Definition 13.9 to reduce separation to equality of two Radon measures from
-- agreement of all common integrable tests in `Lip₁(E; [0,1])`; then approximate compact-set
-- indicators by the distance cutoffs from Lemma 13.10 and conclude by inner regularity.
/-- Theorem 13.11 (1): The family `Lip₁(E; [0,1])` is separating for the Radon measures
`𝓜(E)`. -/
theorem unitIntervalLipschitzRealFunctionSpace_isSeparatingFamilyFor_radonMeasureSpace
    [MeasurableSpace E] [MetricSpace E] [BorelSpace E] :
    IsSeparatingFamilyFor {μ : Measure E | IsRadonMeasure μ}
      (unitIntervalLipschitzRealFunctionSpace E) := sorry

-- Proof sketch: as in part (1), use the distance cutoffs around compact sets; local compactness
-- lets one choose relatively compact neighborhoods so that the same cutoffs have compact support
-- and therefore lie in `C_c(E) ∩ Lip₁(E; [0,1])`.
/-- Theorem 13.11 (2): If `E` is locally compact, then `C_c(E) ∩ Lip₁(E; [0,1])` is separating
for the Radon measures `𝓜(E)`. -/
theorem
    compactlySupportedUnitIntervalLipschitzRealFunctionSpace_isSeparatingFamilyFor_radonMeasureSpace
    [MeasurableSpace E] [MetricSpace E] [BorelSpace E] [LocallyCompactSpace E] :
    IsSeparatingFamilyFor {μ : Measure E | IsRadonMeasure μ}
      (((↑) : C_c(E, ℝ) → E → ℝ) '' compactlySupportedUnitIntervalLipschitzRealMapSpace E) := sorry
