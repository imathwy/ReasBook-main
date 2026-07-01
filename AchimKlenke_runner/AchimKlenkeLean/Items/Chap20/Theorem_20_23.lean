import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped BigOperators ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {τ : Ω → Ω}

-- Proof sketch: for the forward implication, apply Birkhoff's ergodic theorem to the indicator
-- of `B` and integrate against the indicator of `A`, using dominated convergence to identify the
-- Cesàro averages of the correlation terms. For the converse, test the limit formula on an
-- invariant event `A` with `B = A`; then every summand is `P A`, so the limit forces
-- `P A = (P A)^2`, hence invariant events have probability `0` or `1`.
/-- Theorem 20.23: for a probability-preserving transformation `τ`, ergodicity is equivalent to
the convergence of the Cesàro averages of the correlation probabilities
`P (A ∩ (τ^[k])⁻¹(B))` to `P A * P B` for all measurable events `A` and `B`. -/
theorem ergodic_iff_tendsto_cesaro_preimage_intersection
    (hτ : MeasurePreserving τ P P) :
    Ergodic τ P ↔
      ∀ ⦃A B : Set Ω⦄, MeasurableSet A → MeasurableSet B →
        Tendsto
          (fun n : ℕ ↦
            (∑ k ∈ Finset.range (n + 1), P (A ∩ (τ^[k]) ⁻¹' B)) / (n + 1 : ℝ≥0∞))
          atTop
          (𝓝 (P A * P B)) := sorry
