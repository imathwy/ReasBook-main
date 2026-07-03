import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_40 (from Chap03) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open NormedSpace

/- Definition 3.40 lies in the projected first-order convex minimization domain on a real inner
product space, with the textbook `ℝⁿ` presentation as a specialization. Completeness enters only
for the nearest-point projection bridge on the feasible set.

Sampled owner-style declarations:
* `FirstOrderOracle` in `Theorem_3_2_1`, the chapter owner for valid first-order replies
  `x ↦ g(x)`;
* `SetConstrainedMinimizationProblem` in `Definition_1_3_3`, the upstream owner for the feasible
  set and objective data before convexity is added;
* `ConvexMinimizationProblem` in `Definition_3_36`, the canonical derived owner once convexity of
  the objective is available;
* `euclideanProjection` and `euclideanProjection_isProjectionPointOn` in `Theorem_2_33`, the
  canonical nearest-point owner API on nonempty closed convex sets;
* mathlib `NormedSpace.normalize`, the canonical normalized-direction owner.

Best owner abstraction:
* source-facing: `FirstOrderConvexMinimizationProblem E`;
* core/canonical: `FirstOrderOracle`, `SetConstrainedMinimizationProblem`,
  `ConvexMinimizationProblem`, `euclideanProjection`, and `NormedSpace.normalize`;
* bridge/view: `problem.toConvexMinimizationProblem`, the problem-specialized projection map
  `problem.projection`, and the owner step `problem.normalizedSubgradientStep`.

Primitive data:
* the feasible set / objective package from `SetConstrainedMinimizationProblem`;
* the nonemptiness, closedness, and convexity of the feasible set;
* the oracle field `oracle : FirstOrderOracle objective`.

Derived API:
* the correction scalar attached to an oracle reply;
* whole-space convexity of the objective induced by the oracle;
* the bridge to `ConvexMinimizationProblem`;
* on complete spaces, the problem-specialized Euclidean projection and its feasibility lemmas;
* on complete spaces, the projected normalized subgradient step.

Accordingly, this file keeps the source-facing problem owner but removes the duplicate primitive
convexity field inherited from `ConvexMinimizationProblem`: the oracle already supplies that
whole-space convexity canonically. The file also deletes the duplicate local normalized-direction
wrapper in favor of mathlib's canonical `normalize`. -/

namespace FirstOrderOracle

/-- The textbook correction scalar `f(x) / ‖g(x)‖²` attached to the oracle response at `x`. -/
def correctionStepsize {f : E → ℝ} (oracle : FirstOrderOracle f) (x : E) : ℝ :=
  f x / ‖oracle.subgradient x‖ ^ (2 : ℕ)

/-- A first-order oracle already certifies whole-space convexity of its objective, since the
returned vector gives a global affine lower support at every point. -/
theorem convexOn_univ {f : E → ℝ} (oracle : FirstOrderOracle f) :
    ConvexOn ℝ Set.univ f := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  set z : E := a • x + b • y
  let g := oracle.subgradient z
  have hsub := oracle.subgradient_spec z
  have hx :
      f z + inner ℝ g (x - z) ≤ f x := by
    have hxTop :
        (((f z + inner ℝ g (x - z) : ℝ) : WithTop ℝ) ≤ (f x : WithTop ℝ)) := by
      simpa using hsub.2 (by simp)
    exact_mod_cast hxTop
  have hy :
      f z + inner ℝ g (y - z) ≤ f y := by
    have hyTop :
        (((f z + inner ℝ g (y - z) : ℝ) : WithTop ℝ) ≤ (f y : WithTop ℝ)) := by
      simpa using hsub.2 (by simp)
    exact_mod_cast hyTop
  have hax : a * (f z + inner ℝ g (x - z)) ≤ a * f x :=
    mul_le_mul_of_nonneg_left hx ha
  have hby : b * (f z + inner ℝ g (y - z)) ≤ b * f y :=
    mul_le_mul_of_nonneg_left hy hb
  have hsum :
      a * (f z + inner ℝ g (x - z)) + b * (f z + inner ℝ g (y - z)) ≤
        a * f x + b * f y :=
    add_le_add hax hby
  have hinner :
      a * inner ℝ g (x - z) + b * inner ℝ g (y - z) = 0 := by
    calc
      a * inner ℝ g (x - z) + b * inner ℝ g (y - z)
          = inner ℝ g (a • (x - z) + b • (y - z)) := by
              rw [inner_add_right, inner_smul_right, inner_smul_right]
      _ = inner ℝ g 0 := by
            congr 1
            calc
              a • (x - z) + b • (y - z)
                  = (a • x - a • z) + (b • y - b • z) := by
                      rw [smul_sub, smul_sub]
              _ = (a • x + b • y) - (a • z + b • z) := by
                    abel_nf
              _ = z - (a + b) • z := by
                    change z - (a • z + b • z) = z - (a + b) • z
                    rw [← add_smul]
              _ = z - z := by simp [z, hab]
              _ = 0 := sub_self z
      _ = 0 := by simp
  have hz :
      a * (f z + inner ℝ g (x - z)) + b * (f z + inner ℝ g (y - z)) = f z := by
    calc
      a * (f z + inner ℝ g (x - z)) + b * (f z + inner ℝ g (y - z))
          = (a + b) * f z + (a * inner ℝ g (x - z) + b * inner ℝ g (y - z)) := by
              ring
      _ = f z := by simp [hab, hinner]
  have hz' : z = a • x + b • y := by
    rfl
  calc
    f (a • x + b • y) = f z := by rw [hz']
    _ = a * (f z + inner ℝ g (x - z)) + b * (f z + inner ℝ g (y - z)) := hz.symm
    _ ≤ a * f x + b * f y := hsum
    _ = a • f x + b • f y := by simp [smul_eq_mul]

end FirstOrderOracle

/-- Definition 3.40: a convex minimization problem over a simple closed convex feasible set, with
its first-order oracle for the objective. On complete spaces, the canonical Euclidean projection
onto the feasible set and projected normalized subgradient step are derived below. -/
structure FirstOrderConvexMinimizationProblem (E : Type u) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    extends SetConstrainedMinimizationProblem E where
  /-- The feasible set `Q` is nonempty. -/
  feasibleSet_nonempty : feasibleSet.Nonempty
  /-- The feasible set `Q` is closed. -/
  feasibleSet_closed : IsClosed feasibleSet
  /-- The feasible set `Q` is convex. -/
  feasibleSet_convex : Convex ℝ feasibleSet
  /-- A first-order oracle for the objective. -/
  oracle : FirstOrderOracle objective

namespace FirstOrderConvexMinimizationProblem

/-- A first-order convex minimization problem can be used as its objective function. -/
instance : CoeFun (FirstOrderConvexMinimizationProblem E) (fun _ ↦ E → ℝ) where
  coe problem := problem.toSetConstrainedMinimizationProblem

/-- A first-order oracle already certifies whole-space convexity of the objective. -/
theorem objective_convex (problem : FirstOrderConvexMinimizationProblem E) :
    ConvexOn ℝ Set.univ problem.objective :=
  problem.oracle.convexOn_univ

/-- The canonical bridge from a first-order convex minimization problem to the upstream convex
minimization owner. -/
def toConvexMinimizationProblem
    (problem : FirstOrderConvexMinimizationProblem E) : ConvexMinimizationProblem E :=
  { problem.toSetConstrainedMinimizationProblem with
    feasibleSet_nonempty := problem.feasibleSet_nonempty
    feasibleSet_closed := problem.feasibleSet_closed
    feasibleSet_convex := problem.feasibleSet_convex
    objective_convex := problem.objective_convex }

/-- Restricting the oracle-induced whole-space convexity to the feasible set yields the canonical
convexity owner on `Q`. -/
theorem objective_convexOn (problem : FirstOrderConvexMinimizationProblem E) :
    ConvexOn ℝ problem.feasibleSet problem :=
  problem.toConvexMinimizationProblem.objective_convexOn

section Projection

variable [CompleteSpace E]

/-- The canonical Euclidean projection onto the owner's feasible set `Q`. -/
noncomputable def projection (problem : FirstOrderConvexMinimizationProblem E) : E → E :=
  euclideanProjection
    problem.feasibleSet
    problem.feasibleSet_nonempty
    problem.feasibleSet_closed
    problem.feasibleSet_convex

/-- The canonical projection point of `x` onto `Q` satisfies the owner nearest-point predicate. -/
theorem projection_spec (problem : FirstOrderConvexMinimizationProblem E) (x : E) :
    IsProjectionPointOn problem.feasibleSet x (problem.projection x) := by
  simpa [projection] using
    euclideanProjection_isProjectionPointOn
      problem.feasibleSet
      problem.feasibleSet_nonempty
      problem.feasibleSet_closed
      problem.feasibleSet_convex
      x

/-- The canonical Euclidean projection lands in the feasible set. -/
@[simp] theorem projection_mem (problem : FirstOrderConvexMinimizationProblem E) (x : E) :
    problem.projection x ∈ problem.feasibleSet :=
  (problem.projection_spec x).1

/-- The owner normalized subgradient step of length `h` at `x`, projected back to the feasible
set `Q`. -/
def normalizedSubgradientStep
    (problem : FirstOrderConvexMinimizationProblem E) (h : ℝ) (x : E) : E :=
  problem.projection
    (x - h • normalize (problem.oracle.subgradient x))

/-- The owner normalized subgradient step lands in the feasible set `Q`. -/
@[simp] theorem normalizedSubgradientStep_mem
    (problem : FirstOrderConvexMinimizationProblem E) (h : ℝ) (x : E) :
    problem.normalizedSubgradientStep h x ∈ problem.feasibleSet := by
  unfold normalizedSubgradientStep
  exact problem.projection_mem _

end Projection

end FirstOrderConvexMinimizationProblem

/-! ### Proposition_3_40 (from Chap03) -/
universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 3.40 lies in the real inner-product-space strong-convexity / quadratic-correction
bridge domain.

Sampled owner-style declarations:
- mathlib `StrongConvexOn`
- mathlib `strongConvexOn_iff_convex`
- chapter `StrongConvexOnWith` in `Definition_2_14`
- chapter `strongConvexOn_iff_quadratic_jensen_bound` in `Theorem_2_10`

Best owner abstraction:
- source-facing: Proposition 3.40's quadratic-corrected convexity statement
- core/canonical: `strongConvexOn_iff_convex`
- bridge/view: this recall-only source-facing entry

Primitive data:
- the ambient real inner product space `E`
- the feasible set `Q`, modulus `μ`, and objective `f`

Derived API:
- convexity of `fun x ↦ f x - μ / (2 : ℝ) * ‖x‖ ^ 2`, directly from the owner theorem

The previous file duplicated the forward direction of the canonical mathlib equivalence
`strongConvexOn_iff_convex` under the local name `StrongConvexOn.convexOn_sub_sq_norm`. This
refinement removes that parallel wrapper and recalls the owner theorem directly. The textbook
positivity hypothesis `μ > 0` is redundant for this bridge and is therefore omitted from the
public API.
-/

/- Proposition 3.40: in a real inner product space, `μ`-strong convexity on `Q` is exactly
convexity of the quadratic-corrected objective. -/
recall strongConvexOn_iff_convex
    {Q : Set E} {μ : ℝ} {f : E → ℝ} :
    StrongConvexOn Q μ f ↔ ConvexOn ℝ Q (fun x ↦ f x - μ / (2 : ℝ) * ‖x‖ ^ 2)

/-! ### Theorem_3_40 (from Chap03) -/
noncomputable section

open scoped BigOperators DeltaN

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Theorem 3.40 lies in the chapter's projected normalized subgradient / finite-horizon stepsize
bound domain.

Sampled owner-style declarations:
- `FirstOrderConvexMinimizationProblem.normalizedSubgradientStep` in `Definition_3_40`, the owner
  projected normalized oracle step;
- `SimpleSetSubgradientMethod.iterates` in `Algorithm_3_2`, the recursive owner iterate sequence;
- `bestFunctionValueUpTo` in `Theorem_3_2_10`, the chapter owner of best sampled objective values;
- `deltaN` and `deltaN_apply` in `Definition_3_41`, the chapter owner and evaluation bridge for
  the finite stepsize scalar `Δ_N`.

Best owner abstraction:
- `source-facing`: the best sampled-value bound for a run
  `method : SimpleSetSubgradientMethod problem`;
- `core/canonical`: the scalar owner `deltaN`, surfaced as `Δ[k; R]`, for the finite
  stepsize prefix;
- `bridge/view`: the finite prefix `method.stepsizePrefix k`.

Primitive data:
- the owner first-order convex minimization problem `problem`;
- the owner simple-set subgradient run `method`;
- the reference minimizer `xStar`, radius `R`, Lipschitz constant `M`, and stage `k`.

Derived API:
- the owner projected normalized step and iterate recursion;
- the iterate sequence `method`;
- the sampled best value `bestFunctionValueUpTo (fun i ↦ problem (method i)) k`;
- the finite stepsize bound expressed canonically as `Δ[k; R]` of the method's prefix.

The previous version exposed a parallel selector-style API through raw parameters
`Q`, `projQ`, `f`, `xSeq`, `g`, and `h`. This refinement keeps the theorem source-facing, but
also removes the redundant nonzero-subgradient hypothesis and rewrites the stepsize ratio through
the chapter owner `deltaN`, leaving only the finite-prefix bridge `method.stepsizePrefix k`.
-/

namespace SimpleSetSubgradientMethod

variable {problem : FirstOrderConvexMinimizationProblem E}

/-- Theorem 3.40: for a simple-set subgradient method on an owner first-order convex minimization
problem, the best objective value among the first `k + 1` iterates satisfies the standard
`M * Δ_k` error bound, written with the chapter owners
`bestFunctionValueUpTo (fun i ↦ problem (method i)) k` for the sampled minimum `f_k^*` and
`Δ[k; R] (method.stepsizePrefix k)` for the finite stepsize prefix. -/
-- Proof sketch: first use nonexpansiveness of the Euclidean projection to derive the one-step
-- distance recursion
-- `‖x_{i+1} - xStar‖² ≤ ‖x_i - xStar‖² - 2 h_i ⟪g_i / ‖g_i‖, x_i - xStar⟫ + h_i²`.
-- Summing this recursion yields an upper bound on the minimum normalized subgradient pairing over
-- `i = 0, …, k`. Then combine the subgradient inequality at the minimizer `xStar` with the
-- Lipschitz bound on the ball `Metric.closedBall xStar R` to estimate each objective gap by
-- `M` times the corresponding normalized pairing, identify the resulting stepsize quotient with
-- `Δ[k; R]` of the finite prefix, and finally take the minimum over the sampled iterates.
theorem bestFunctionValueUpTo_sub_le_of_projected_normalized_subgradient_method
    (method : SimpleSetSubgradientMethod problem) (xStar : E) (R M : NNReal)
    (hxStar_min : IsMinOn problem problem.feasibleSet xStar)
    (hf_lipschitz : LipschitzOnWith M problem (Metric.closedBall xStar R))
    (hx0_ball : method.x0 ∈ Metric.closedBall xStar R)
    (k : ℕ) :
    bestFunctionValueUpTo (fun i ↦ problem (method i)) k - problem xStar ≤
      (M : ℝ) * Δ[k; R] (method.stepsizePrefix k) := sorry

end SimpleSetSubgradientMethod

end
