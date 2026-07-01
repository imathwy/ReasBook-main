import FirstOrderMethodsinOptimization.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace (toDualMap)

noncomputable section

section

/- Proposition 4.10 is `source-facing`: its main content is that the scalar Fenchel objective
`x ↦ x * y - |x|^p / p` attains its maximum. The `core/canonical` owner abstraction for Chapter 4
conjugacy statements is `conjugate_function`, specialized on `ℝ` via `toDualMap ℝ ℝ`. There is no
additional primitive data here beyond that source integrand; the owner-level conjugacy formula
below is derived `bridge/view` API for downstream reuse. -/
recall conjugate_function
recall conjugate_function_apply

-- Proof sketch: rewrite the objective as the equality case of Young's inequality for the
-- Hölder-conjugate exponents `p` and `q`. The upper bound comes from `Real.young_inequality`,
-- and equality is attained at `x = sign y * |y| ^ (q - 1)`.
/-- Proposition 4.10: for the function `f(x) = |x|^p / p` with Hölder-conjugate exponent `q`,
the maximum of `x ↦ x * y - |x|^p / p` is `|y|^q / q`. Equivalently, the conjugate of
`x ↦ |x|^p / p` is `y ↦ |y|^q / q`. -/
theorem power_absolute_function_conjugate_isGreatest {p q : ℝ} (hpq : p.HolderConjugate q)
    (y : ℝ) :
    IsGreatest (Set.range fun x : ℝ ↦ x * y - (|x| ^ p) / p) ((|y| ^ q) / q) := sorry

-- Proof sketch: express the scalar Fenchel conjugate through the owner declaration
-- `conjugate_function` on `ℝ`, then identify its defining `sSup` with the greatest value from
-- `power_absolute_function_conjugate_isGreatest`.
/-- Proposition 4.10 in the Chapter 4 owner formulation: for `f(x) = |x|^p / p`, the Fenchel
conjugate `f*`, evaluated on `ℝ` via `toDualMap ℝ ℝ`, is `y ↦ |y|^q / q`. -/
theorem power_absolute_function_conjugate_eq {p q : ℝ} (hpq : p.HolderConjugate q) (y : ℝ) :
    conjugate_function (fun x : ℝ ↦ (((|x| ^ p) / p : ℝ) : EReal)) (toDualMap ℝ ℝ y) =
      (((|y| ^ q) / q : ℝ) : EReal) := sorry

end
