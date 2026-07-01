import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Function MeasureTheory Set

open scoped BigOperators Topology

noncomputable section

-- Proof sketch: apply Stieltjes integration by parts on `(a, b]` for the two Stieltjes measures
-- associated to `Fμ` and `Fν`, and use the boundary terms together with the left-limit version of
-- the Stieltjes integral.
/-- Exercise 14.2.3: for two distribution functions `F_μ` and `F_ν` of locally finite measures on
`ℝ`, partial integration on `(a, b]` identifies the integral of `F_μ` against `dν` with the
boundary term `F_μ(b) F_ν(b) - F_μ(a) F_ν(a)` minus the integral of the left limit `F_ν(x-)`
against `dμ`. -/
theorem partialIntegration_stieltjes_eq_boundary_sub_leftLimIntegral
    (Fμ Fν : StieltjesFunction ℝ) {a b : ℝ} (hab : a < b) :
    ∫ x in Ioc a b, Fμ x ∂Fν.measure =
      Fμ b * Fν b - Fμ a * Fν a -
        ∫ x in Ioc a b, leftLim Fν x ∂Fμ.measure := sorry

-- Proof sketch: start from the partial-integration identity with the left-limit integral, then
-- decompose `∫ Fν(x-) dμ` into `∫ Fν dμ` minus the sum of the products of the jumps, using the
-- singleton-mass formula for Stieltjes measures.
/-- A companion reformulation of partial integration replaces the left-limit integral by the
ordinary integral of `F_ν` against `dμ` plus the sum of the products of the jump heights on
`(a, b]`. -/
theorem partialIntegration_stieltjes_eq_boundary_sub_integral_add_jumpSum
    (Fμ Fν : StieltjesFunction ℝ) {a b : ℝ} (hab : a < b) :
    ∫ x in Ioc a b, Fμ x ∂Fν.measure =
      Fμ b * Fν b - Fμ a * Fν a -
        ∫ x in Ioc a b, Fν x ∂Fμ.measure +
          ∑' x : Ioc a b, (Fμ x - leftLim Fμ x) * (Fν x - leftLim Fν x) := sorry

end
