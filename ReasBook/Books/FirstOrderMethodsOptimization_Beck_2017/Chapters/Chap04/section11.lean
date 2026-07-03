

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_4_11 (from Chap04) -/
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

/-! ### Theorem_4_11 (from Chap04) -/
noncomputable section

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Theorem 4.11 is `source-facing`: it rewrites Fenchel--Young equality in the textbook's
`argmax` language. The owner abstractions are already upstream: `conjugate_function` from
Definition 4.1 and Mathlib's `IsMaxOn`. This file is therefore only a `bridge/view` layer and
reuses those owners directly instead of repeating local copies of the same convex-analysis data. -/

recall conjugate_function

-- Proof sketch: unfold `conjugate_function`; by `isMaxOn_univ_iff`, saying that `x` maximizes the
-- affine-minus-`f` objective over `E` is exactly the statement that the value at `x` attains the
-- supremum defining `conjugate_function f y`.
/-- Theorem 4.11: the equality `f*(y) = ⟨y, x⟩ - f(x)` can be rewritten as the statement that `x`
is an argmax of the affine-minus-`f` objective, rendered in Lean as `IsMaxOn ... Set.univ x`. -/
theorem conjugate_function_eq_iff_isMaxOn_pairing_sub_function
    (f : E → EReal) (x : E) (y : Module.Dual ℝ E) :
    conjugate_function f y = (y x : EReal) - f x ↔
      IsMaxOn (fun x' : E ↦ (y x' : EReal) - f x') Set.univ x := sorry

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

recall is_convex_function
recall conjugate_function

-- Proof sketch: rewrite the right-hand side as the statement that `y` attains the supremum in
-- the definition of `f**(x)`, then use `biconjugate_function_eq_self_of_closed_convex` to
-- identify `f**` with `f`. The properness hypothesis from the textbook statement is redundant for
-- this equivalence, so the canonical owner-based formulation omits it.
/-- Under the chapter closedness and convexity hypotheses, the equality
`f(x) = ⟨x, y⟩ - f*(y)` is equivalent to saying that `y` is an argmax of the affine-minus-`f*`
objective on the dual space. -/
theorem self_eq_pairing_sub_conjugate_iff_isMaxOn_dual_of_closed_convex
    (f : E → EReal) (hclosed : LowerSemicontinuous f) (hconvex : is_convex_function f)
    (x : E) (y : Module.Dual ℝ E) :
    f x = (y x : EReal) - conjugate_function f y ↔
      IsMaxOn
        (fun y' : Module.Dual ℝ E ↦ (y' x : EReal) - conjugate_function f y')
        Set.univ y := sorry

end
