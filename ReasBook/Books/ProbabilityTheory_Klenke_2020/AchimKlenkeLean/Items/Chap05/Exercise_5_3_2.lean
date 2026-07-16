import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap02.Definition_2_14
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap05.Definition_5_12

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: rewrite the event “`|X n| > n + 1` infinitely often” as membership in the limsup
-- of the tail events. For the forward implication, use the second Borel--Cantelli lemma together
-- with the i.i.d. hypothesis to force a divergent tail-probability series to give limsup measure
-- `1`; for the reverse implication, apply the first Borel--Cantelli lemma using the classical
-- tail characterization of integrability. This is internal bridge material for
-- `integrable_and_ae_eq_expectation_of_iid_ae_tendsto_average`, not a separate source-facing
-- chapter theorem.
private theorem measure_limsup_abs_gt_linear_eq_zero_iff_integrable_of_iid
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hX_iid : IsIID X P) :
    P (limsup (fun n : ℕ ↦ {ω | (n + 1 : ℝ) < |X n ω|}) atTop) = 0 ↔ Integrable (X 0) P :=
  sorry

-- Proof sketch: apply the hint theorem to the shifted i.i.d. sequence `n ↦ X (n + 1)` to obtain
-- `Integrable (X 1) P` from the assumed almost sure convergence of the empirical averages. Then
-- apply the strong law of large numbers to the same shifted i.i.d. sequence and compare its almost
-- sure limit `P[X 1]` with the given almost sure limit `Y`, yielding `Y = P[X 1]` almost surely.
/-- Exercise 5.3.2: if the empirical averages of an independent identically distributed real
sequence `X₁, X₂, …` converge almost surely to a random variable `Y`, then `X₁` is integrable and
the limit `Y` is almost surely equal to the common expectation `𝔼[X₁]`. -/
theorem integrable_and_ae_eq_expectation_of_iid_ae_tendsto_average
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (h_tendsto :
      ∀ᵐ ω ∂P, Tendsto (fun n ↦ (∑ i ∈ Finset.range n, X (i + 1) ω) / n) atTop (𝓝 (Y ω))) :
    Integrable (X 1) P ∧ Y =ᵐ[P] fun _ ↦ P[X 1] := sorry
