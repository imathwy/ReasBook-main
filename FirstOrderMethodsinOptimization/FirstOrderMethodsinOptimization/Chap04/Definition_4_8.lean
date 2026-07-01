import FirstOrderMethodsinOptimization.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

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
