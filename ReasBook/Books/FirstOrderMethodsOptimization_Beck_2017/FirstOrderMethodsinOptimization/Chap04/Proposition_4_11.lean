import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace

noncomputable section

/- Proposition 4.11 is `source-facing`: its primitive data is the scalar integrand
`negative_rpow_extension`, while the `core/canonical` owner abstraction for Fenchel conjugates is
already `conjugate_function` from Definition 4.1. The conjugacy formulas below are therefore
derived API specialized to `ℝ` via `toDualMap ℝ ℝ`, rather than a parallel local owner
definition. -/

/-- The extended-real function equal to `-x^p / p` on the nonnegative ray and `∞` on the negative
half-line. -/
def negative_rpow_extension (p : ℝ) : ℝ → EReal :=
  fun x ↦ if 0 ≤ x then ((-(x ^ p) / p : ℝ) : EReal) else ⊤

-- Proof sketch: unfold `negative_rpow_extension` inside the canonical Chapter 4 definition
-- `conjugate_function`. On `x < 0`, the value of `negative_rpow_extension p x` is `⊤`, so the term
-- `(x * y : EReal) - ⊤` is `⊥` and does not change the supremum. On `x ≥ 0`, the affine term is
-- `x * y + x ^ p / p`, so the supremum is taken over `Set.Ici 0`.
/-- Evaluating the conjugate of `negative_rpow_extension p` at `y` reduces to the supremum of
`x * y + x ^ p / p` over the nonnegative ray. -/
theorem negative_rpow_extension_conjugate_eq_sSup_Ici
    (p y : ℝ) :
    conjugate_function (negative_rpow_extension p) (toDualMap ℝ ℝ y) =
      sSup ((fun x : ℝ ↦ ((x * y + x ^ p / p : ℝ) : EReal)) '' Set.Ici (0 : ℝ)) := sorry

-- Proof sketch: start from `negative_rpow_extension_conjugate_eq_sSup_Ici`. For `0 < p < 1`, the
-- objective `x ↦ x * y + x ^ p / p` is concave on `[0, ∞)`. If `y < 0`, its derivative vanishes at
-- the unique maximizer `x = (-y) ^ (1 / (1 - p))`, and evaluating there gives
-- `-((-y) ^ (p / (p - 1))) / (p / (p - 1))`. If `y ≥ 0`, the objective tends to `∞` along
-- `x → ∞`, so the conjugate value is `⊤`.
/-- Proposition 4.11: for `0 < p < 1`, let `f(x) = -x^p / p` on `[0, ∞)` and `f(x) = ∞` on
`(-∞, 0)`. Then the Fenchel conjugate of `f`, evaluated on `ℝ` via `toDualMap ℝ ℝ`, is
`-(-y)^q / q` for `y < 0` and `∞` otherwise, where `q = p / (p - 1) < 0`. -/
theorem negative_rpow_extension_conjugate_eq
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (y : ℝ) :
    conjugate_function (negative_rpow_extension p) (toDualMap ℝ ℝ y) =
      if y < 0 then ((-((-y) ^ (p / (p - 1))) / (p / (p - 1)) : ℝ) : EReal) else ⊤ := sorry
