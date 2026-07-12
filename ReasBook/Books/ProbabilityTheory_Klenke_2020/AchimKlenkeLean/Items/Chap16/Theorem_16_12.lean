import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory MeasureTheory.ProbabilityMeasure
open scoped BigOperators

section

variable {k : ℕ → ℕ} {φs : ∀ n, Fin (k n) → ℝ → ℂ}

/- Theorem 16.12 is `source-facing`: its main mathematical content is the triangular-array
criterion producing an infinitely divisible limiting characteristic function from rowwise
characteristic-function data. Its `core/canonical` owner layers are the ambient
`ProbabilityMeasure` and `ProbabilityMeasure.IsInfinitelyDivisible`. The first theorem below keeps
the source-facing transform statement public, while the second theorem is the thin `bridge/view`
that specializes the limit function to `charFun (↑μ)` and reads the conclusion back at
the owner level for the law `μ`. -/

-- Proof sketch: fix a positive integer `m` and group each row into `m` asymptotically negligible
-- subproducts. The compact-uniform smallness hypothesis forces each subproduct to remain a CFP
-- close to `1`, while the pointwise product limit and continuity at `0` let one apply the
-- triangular-array version of Lévy's continuity theorem to obtain an `m`th characteristic-function
-- root of `φ`. Doing this for every `m` gives infinite divisibility.
/-- Theorem 16.12: if a triangular array of CFPs is uniformly close to `1` on every compact
interval in the sense of `(16.4)`, and the rowwise finite products converge pointwise to a limit
`φ` that is continuous at `0`, then `φ` is an infinitely divisible characteristic function. -/
theorem cfp_array_product_limit_isInfinitelyDivisibleCFP
    {φ : ℝ → ℂ}
    (hcfp : ∀ n : ℕ, ∀ l : Fin (k n), IsCFP (φs n l))
    (hsmall :
      ∀ L > 0, ∀ ε > 0, ∀ᶠ n in atTop,
        ∀ t ∈ Set.Icc (-L) L, ∀ l : Fin (k n), ‖φs n l t - 1‖ ≤ ε)
    (hprod : ∀ t : ℝ, Tendsto (fun n : ℕ ↦ ∏ l : Fin (k n), φs n l t) atTop (nhds (φ t)))
    (hφ0 : ContinuousAt φ 0) :
    IsInfinitelyDivisibleCFP φ := sorry

-- Proof sketch: apply the source-facing CFP theorem to the limiting characteristic function
-- `charFun (↑μ)`; its continuity at `0` is automatic, and the resulting infinite
-- divisibility of the characteristic function is read back at the owner level for `μ`.
/-- Bridge/view form of Theorem 16.12: if the rowwise product limit is the characteristic function
of a probability law `μ`, then `μ` is infinitely divisible in the measure-theoretic owner sense. -/
theorem cfp_array_product_limit_charFun_isInfinitelyDivisible
    {μ : ProbabilityMeasure ℝ}
    (hcfp : ∀ n : ℕ, ∀ l : Fin (k n), IsCFP (φs n l))
    (hsmall :
      ∀ L > 0, ∀ ε > 0, ∀ᶠ n in atTop,
        ∀ t ∈ Set.Icc (-L) L, ∀ l : Fin (k n), ‖φs n l t - 1‖ ≤ ε)
    (hprod :
      ∀ t : ℝ,
        Tendsto (fun n : ℕ ↦ ∏ l : Fin (k n), φs n l t) atTop
          (nhds (charFun (↑μ) t))) :
    IsInfinitelyDivisible μ := sorry

end
