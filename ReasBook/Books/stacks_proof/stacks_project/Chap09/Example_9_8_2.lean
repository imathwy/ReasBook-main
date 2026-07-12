import Mathlib.Analysis.Complex.Polynomial.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial
open Complex
open scoped ComplexConjugate

/- Domain-style sampling for Example 9.8.2:
- primary domain: algebraic field extensions, with the concrete companion of writing an explicit
  annihilating polynomial for a complex number over `ℝ`;
- sampled owner declarations:
  `IsAlgebraic`,
  `Algebra.IsAlgebraic`,
  `Algebra.IsAlgebraic.isAlgebraic`;
- sampled supporting API for the explicit quadratic companion:
  `Polynomial.quadratic_dvd_of_aeval_eq_zero_im_ne_zero`,
  `Complex.mul_conj'`;
- best owner abstraction: the extension-level owner `Algebra.IsAlgebraic ℝ ℂ`, with pointwise
  algebraicity derived from that owner rather than introduced through a local wrapper;
- primitive data: none locally for the main example, since algebraicity of `ℂ/ℝ` is already the
  upstream canonical instance;
- derived API: the textbook quadratic polynomial attached to `z : ℂ`, exhibited here only as a
  thin source-facing companion.

Source/core/bridge triage:
- `source-facing`: the explicit quadratic over `ℝ` vanishing at `z`;
- `core/canonical`: `Algebra.IsAlgebraic ℝ ℂ`;
- `bridge/view`: the factorization of the mapped real quadratic as
  `(X - C (conj z)) * (X - C z)` in `ℂ[X]`.

This file should therefore keep the owner-level statement as a direct instance check and retain
only the explicit quadratic as companion API; introducing any separate local owner for the same
algebraicity notion would duplicate upstream chapter and mathlib declarations. -/

/- Example 9.8.2: the field `ℂ` is algebraic over `ℝ`; this is the canonical mathlib instance
`Algebra.IsAlgebraic ℝ ℂ`. -/
#check (inferInstance : Algebra.IsAlgebraic ℝ ℂ)

/-- Companion theorem: the textbook quadratic over `ℝ` attached to `z : ℂ` vanishes at `z`,
so every complex number is explicitly seen to be algebraic over `ℝ`. -/
theorem aeval_complex_quadratic_over_real (z : ℂ) :
    aeval z (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) : Polynomial ℝ) = 0 := by
  rw [aeval_def, eval₂_eq_eval_map]
  calc
    eval z (map (algebraMap ℝ ℂ) (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) : Polynomial ℝ)) =
        eval z ((X - C (conj z)) * (X - C z)) := by
          congr 1
          calc
            map (algebraMap ℝ ℂ) (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) : Polynomial ℝ) =
                X ^ 2 - C (↑(2 * z.re) : ℂ) * X + C (‖z‖ ^ 2 : ℂ) := by
                  simp
            _ = (X - C (conj z)) * (X - C z) := by
                rw [← add_conj, map_add, ← mul_conj', map_mul]
                ring
    _ = 0 := by
      simp
