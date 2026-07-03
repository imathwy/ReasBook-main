import AchimKlenkeLean.Items.Chap02.Definition_2_14

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

-- Proof sketch: by exchangeability of an i.i.d. finite family, the pairs
-- `(X i, fun ω ↦ ∑ j : Fin n, X j ω)` and `(X j, fun ω ↦ ∑ j : Fin n, X j ω)` have the same law,
-- so the conditional expectations of the coordinates given the total sum agree almost surely.
-- Use identical distribution to propagate integrability from the chosen coordinate `X i` to every
-- other coordinate. Summing the equal conditional expectations over all coordinates and using
-- `condExp_finset_sum` together with `condExp_of_measurable_ae_eq` for the total sum yields
-- `n * P[X i | σ(S_n)] = S_n`, hence `P[X i | σ(S_n)] = S_n / n`.
/-- Exercise 8.2.7: for a measurable i.i.d. family `X : Fin n → Ω → ℝ`, the conditional
expectation of any integrable coordinate given the total sum is almost surely the sample mean. -/
theorem condExp_coordinate_given_sum_ae_eq_average {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX_meas : ∀ i, Measurable (X i)) (hX_iid : IsIID X P) (i : Fin n)
    (hXi_int : Integrable (X i) P) :
    P[X i | MeasurableSpace.comap (fun ω ↦ ∑ j : Fin n, X j ω) inferInstance] =ᵐ[P]
      fun ω ↦ (∑ j : Fin n, X j ω) / n := sorry
