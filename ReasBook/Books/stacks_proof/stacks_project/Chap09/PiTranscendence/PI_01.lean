import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for PI-01:
- primary domain: algebraicity across the fraction-ring bridge `ℤ → ℚ`;
- sampled owner declarations:
  `IsFractionRing.isAlgebraic_iff`,
  `IsLocalization.isAlgebraic`,
  `Algebra.isAlgebraic_iff_isIntegral`,
  `IsAlgebraic.exists_nonzero_coeff_and_aeval_eq_zero`;
- best owner abstraction: the owner predicate `IsAlgebraic` together with the canonical bridge
  `IsFractionRing.isAlgebraic_iff`;
- primitive data: algebraicity of `α` over `ℚ`;
- derived API: algebraicity over `ℤ`, then the integer-polynomial witness.

Source/core/bridge triage:
- `source-facing`: a complex number algebraic over `ℚ` satisfies a nonzero polynomial in `ℤ[X]`;
- `core/canonical`: `IsAlgebraic R α`;
- `bridge/view`: `IsFractionRing.isAlgebraic_iff` for the fraction field `ℚ` of `ℤ`;
- `layer`: `source-facing` for the theorem below, with the bridge recalled directly.
-/

/- Companion recall: for the fraction field `ℚ` of `ℤ`, algebraicity over `ℤ` and `ℚ` is the
canonical mathlib bridge `IsFractionRing.isAlgebraic_iff`. -/
recall IsFractionRing.isAlgebraic_iff

/-- Lemma PI-01: if `α : ℂ` is algebraic over `ℚ`, then there exists a nonzero polynomial
`P : Polynomial ℤ` such that `Polynomial.aeval α P = 0`. -/
theorem exists_nonzero_int_polynomial_aeval_eq_zero_of_isAlgebraic_rat {α : ℂ}
    (hα : IsAlgebraic ℚ α) : ∃ P : Polynomial ℤ, P ≠ 0 ∧ Polynomial.aeval α P = 0 := by
  exact (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr hα
