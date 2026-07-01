import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Polynomial

/- Canonical recall: polynomial functions are analytic on the whole real line or complex plane;
this is the standard polynomial analyticity theorem. -/
recall AnalyticOnNhd.eval_polynomial

-- Proof sketch: `x ↦ P.eval x` and `x ↦ Q.eval x` are analytic everywhere by polynomial
-- analyticity; on the complement of the zero set of `Q`, apply the analytic quotient theorem.
/-- Example I.4-extra-1 (1): a rational function `P(x) / Q(x)` is analytic away from the zeros of
`Q`. -/
theorem analyticOnNhd_polynomial_div_polynomial {𝕜 : Type u} [NontriviallyNormedField 𝕜]
    (P Q : 𝕜[X]) :
    AnalyticOnNhd 𝕜 (fun x ↦ P.eval x / Q.eval x) {x | Q.eval x ≠ 0} := by
  have hP : AnalyticOnNhd 𝕜 (fun x ↦ P.eval x) {x | Q.eval x ≠ 0} :=
    (AnalyticOnNhd.eval_polynomial P).mono fun _ _ ↦ by simp
  have hQ : AnalyticOnNhd 𝕜 (fun x ↦ Q.eval x) {x | Q.eval x ≠ 0} :=
    (AnalyticOnNhd.eval_polynomial Q).mono fun _ _ ↦ by simp
  simpa using
    hP.div hQ fun x hx ↦ hx

/- Example I.4-extra-1 (2): the real arctangent function is analytic on all of `ℝ`; this is the
canonical consequence of the standard smoothness theorem `Real.contDiff_arctan`. -/
#check (Real.contDiff_arctan.analyticOnNhd : AnalyticOnNhd ℝ Real.arctan Set.univ)
