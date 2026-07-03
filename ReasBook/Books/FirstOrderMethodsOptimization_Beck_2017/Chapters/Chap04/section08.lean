

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_8 (from Chap04) -/
noncomputable section

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Definition 4.8 is `source-facing`: the split equality-constrained Lagrangian and the dual
value of that split problem are the chapter's source-level objects. The `core/canonical` owner
for Fenchel conjugates remains `conjugate_function` from Definition 4.1, so the only primitive
data introduced here is the split Lagrangian together with the resulting dual objective
`fenchel_dual_objective`; the infimum presentation and the dual-problem value are derived
`bridge/view` API. -/

/-- The Lagrangian of the split equality-constrained formulation
`min_{x,z} {f x + g z : x = z}` with dual variable `y ∈ E*`. -/
def fenchel_split_lagrangian
    (f g : E → EReal) (x z : E) (y : Module.Dual ℝ E) : EReal :=
  f x + g z + (y (z - x) : EReal)

-- Proof sketch: expand `y (z - x)` by linearity as `y z - y x`, then regroup the resulting
-- extended-real terms into the two bracketed affine pieces from equation (4.4.3).
/-- The split Lagrangian rewrites as the negative of the two affine-conjugate integrands appearing
in equation (4.4.3). -/
theorem fenchel_split_lagrangian_eq_neg_conjugate_integrands
    (f g : E → EReal) (x z : E) (y : Module.Dual ℝ E) :
    fenchel_split_lagrangian f g x z y =
      -((y x : EReal) - f x) - (((-y) z : EReal) - g z) := sorry

/-- Definition 4.8: the dual objective function of the primal problem
`min_x (f x + g x)`, equivalently of the split problem `min_{x,z} {f x + g z : x = z}`, is
Fenchel's dual objective `q(y) = -f*(y) - g*(-y)`, written using the Chapter 4 owner
`conjugate_function` for the conjugates of `f` and `g`. -/
def fenchel_dual_objective (f g : E → EReal) : Module.Dual ℝ E → EReal :=
  fun y ↦ -conjugate_function f y - conjugate_function g (-y)

-- Proof sketch: unfold `fenchel_dual_objective`; the statement is exactly the defining formula of
-- Fenchel's dual objective at the dual vector `y`.
/-- Evaluating Fenchel's dual objective at `y` gives `-f*(y) - g*(-y)`. -/
theorem fenchel_dual_objective_apply (f g : E → EReal) (y : Module.Dual ℝ E) :
    fenchel_dual_objective f g y = -conjugate_function f y - conjugate_function g (-y) :=
  rfl

-- Proof sketch: rewrite `fenchel_split_lagrangian` with
-- `fenchel_split_lagrangian_eq_neg_conjugate_integrands`, separate the infimum over the product
-- variables into the `x`- and `z`-parts, and identify those two order-theoretic infima with the
-- negatives of `conjugate_function f y` and `conjugate_function g (-y)`.
/-- The dual objective is the infimum form `q(y) = inf_{x,z} L(x, z; y)` of the split
Lagrangian. -/
theorem fenchel_dual_objective_eq_sInf_split_lagrangian
    (f g : E → EReal) (y : Module.Dual ℝ E) :
    fenchel_dual_objective f g y =
      sInf (Set.range fun xz : E × E ↦ fenchel_split_lagrangian f g xz.1 xz.2 y) := sorry

/-- The value of Fenchel's dual problem `(D)` is the supremum of the dual objective over the dual
space `E*`. -/
def fenchel_dual_problem_value (f g : E → EReal) : EReal :=
  sSup (Set.range (fenchel_dual_objective f g))

-- Proof sketch: unfold `fenchel_dual_problem_value`; the displayed supremum over the range of the
-- dual objective is exactly the defining formula for the dual maximization problem.
/-- The dual problem value is the `EReal` supremum of the range of `fenchel_dual_objective`. -/
theorem fenchel_dual_problem_value_eq_sSup (f g : E → EReal) :
    fenchel_dual_problem_value f g = sSup (Set.range (fenchel_dual_objective f g)) := rfl

end

/-! ### Proposition_4_8 (from Chap04) -/
noncomputable section

/- Proposition 4.8 is `source-facing` in the Chapter 4 conjugacy API. The chapter owner
abstraction for Fenchel conjugates is already `conjugate_function` from Definition 4.1, so this
file keeps only the negative-log barrier and its conjugacy formulas rather than a parallel local
copy of the owner definition. -/

/-- The negative-log barrier, equal to `-log x` on the positive ray and `∞` on the nonpositive
half-line. -/
def negative_log_barrier : ℝ → EReal :=
  fun x ↦ if 0 < x then ((-Real.log x : ℝ) : EReal) else ⊤

-- Proof sketch: unfold `negative_log_barrier` inside the canonical Fenchel-conjugate definition
-- `conjugate_function`. On the positive ray the barrier contributes `-(-log x) = log x`, while on
-- the nonpositive half-line the term `(x * y : EReal) - ⊤` is `⊥`, so those points do not affect
-- the supremum. Re-express the remaining supremum as the image of `Set.Ioi 0`.
/-- The conjugate of the negative-log barrier is the supremum of `x * y + log x` over the positive
ray. -/
theorem negative_log_barrier_conjugate_eq_sSup_Ioi (y : ℝ) :
    conjugate_function negative_log_barrier (InnerProductSpace.toDualMap ℝ ℝ y) =
      sSup ((fun x : ℝ ↦ ((x * y + Real.log x : ℝ) : EReal)) '' Set.Ioi (0 : ℝ)) := sorry

-- Proof sketch: use `negative_log_barrier_conjugate_eq_sSup_Ioi`. If `y < 0`, differentiate the
-- smooth objective `x ↦ x * y + log x` on `(0, ∞)` to find the unique maximizer `x = -1 / y`, and
-- evaluate the objective there to obtain `-1 - log (-y)`. If `y ≥ 0`, the objective tends to `∞`
-- along `x → ∞`, so the conjugate value is `⊤`.
/-- Proposition 4.8: the conjugate of the negative-log barrier equals `-1 - log (-y)` for `y < 0`
and equals `∞` for `y ≥ 0`. -/
theorem negative_log_barrier_conjugate_eq (y : ℝ) :
    conjugate_function negative_log_barrier (InnerProductSpace.toDualMap ℝ ℝ y) =
      if y < 0 then ((-1 - Real.log (-y) : ℝ) : EReal) else ⊤ := sorry

end

/-! ### Theorem_4_8 (from Chap04) -/
universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 4.8 is `source-facing` in the chapter conjugacy calculus. Its ambient notions are the
project owner declarations `IsProperExtendedRealFunction`, `is_convex_function`,
`infimal_convolution`, and `conjugate_function`, so this file reuses those owners directly rather
than restating parallel local copies. -/

-- Proof sketch: fix `y : Module.Dual ℝ E` and apply Fenchel--Rockafellar duality to the pair
-- `h₁` and `g x = h₂ x - y x`. Because `h₂` is finite everywhere, the qualification condition is
-- automatic from properness of `h₁`. Rewriting `g* z` as
-- `conjugate_function (fun x ↦ (h₂ x : EReal)) (y - z)` yields the infimal-convolution formula.
/-- Theorem 4.8: if `h₁` is a proper convex extended-real-valued function and `h₂` is a real-valued
convex function, then the Fenchel conjugate of the pointwise sum `h₁ + h₂` is the infimal
convolution of the conjugates `h₁*` and `h₂*`. The real-valued convexity of `h₂` is encoded by
`ConvexOn ℝ Set.univ h₂`. -/
theorem conjugate_function_add_eq_infimal_convolution
    (h₁ : E → EReal) (h₂ : E → ℝ) (hh₁_proper : IsProperExtendedRealFunction h₁)
    (hh₁_convex : is_convex_function h₁) (hh₂_convex : ConvexOn ℝ Set.univ h₂) :
    conjugate_function (fun x ↦ h₁ x + (h₂ x : EReal)) =
      conjugate_function h₁ □ conjugate_function (fun x ↦ (h₂ x : EReal)) := sorry

end
