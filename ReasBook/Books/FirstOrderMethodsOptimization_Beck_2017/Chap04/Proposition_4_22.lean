import FirstOrderMethodsOptimization_Beck_2017.Chap01.Lemma_1_1
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 4.22 is `source-facing`: it identifies the Fenchel conjugate of the quadratic norm
function. The `core/canonical` owners are already present upstream: `conjugate_function` from
Definition 4.1 for Fenchel conjugacy and `dualNorm` from Chapter 1 for the dual norm. The only
primitive data here are therefore the quadratic norm objective and its dual quadratic value; the
proposition is the source-facing bridge between those owner declarations. -/
recall conjugate_function
recall dualNorm

-- Proof sketch: rewrite the conjugate as the supremum of
-- `x ↦ (y x : ℝ) - (1 / 2) * ‖x‖ ^ 2`. The dual-pairing inequality gives the upper bound
-- `y x ≤ dualNorm y * ‖x‖`, reducing the problem to maximizing
-- `r ↦ dualNorm y * r - (1 / 2) * r ^ 2` over `r ≥ 0`. Equality is attained by a unit vector that
-- realizes the dual norm, scaled by `dualNorm y`.
/-- Proposition 4.22: the Fenchel conjugate of the quadratic norm function
`x ↦ (1 / 2) ‖x‖²` on a finite-dimensional real normed space is the quadratic dual norm function
`y ↦ (1 / 2) ‖y‖_*²` on the dual space. -/
theorem half_squared_norm_conjugate_eq_half_dualNorm_sq
    (y : Module.Dual ℝ E) :
    conjugate_function (fun x : E ↦ ((((1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ)) : ℝ) : EReal)) y =
      ((((1 / 2 : ℝ) * dualNorm y ^ (2 : ℕ)) : ℝ) : EReal) := sorry

end
