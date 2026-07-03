import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_16 (from Chap07) -/
noncomputable section

open Matrix

variable {m n : ℕ}

local notation "Eₘ" => EuclideanSpace ℝ (Fin m)

/- Definition 7.16 lies in the chapter's homogeneous linear-programming / dual-value domain.

Sampled owner-style declarations:
- mathlib `Matrix.fromCols`, the canonical matrix augmentation used in the source rank hypotheses
- Chapter 7 `homogeneousLinearProgrammingFeasibleSet` in `Proposition_7_3`
- Chapter 7 `mem_homogeneousLinearProgrammingFeasibleSet_iff` in `Proposition_7_3`
- Chapter 7 `homogeneousLinearProgrammingOptimalValue` and
  `homogeneousLinearProgrammingOptimalValue_eq_sSup` in `Proposition_7_3`

Best owner abstraction:
- source-facing: Definition 7.16's homogeneous linear-programming value `f*` for a pair
  `(hatA, c)` satisfying the source's standing rank assumptions
- core/canonical: the existing Chapter 7 owner `homogeneousLinearProgrammingOptimalValue hatA c`
- bridge/view: the coordinatewise feasible-set expansion below

Primitive data:
- `hatA : Matrix (Fin m) (Fin (n - 1)) ℝ`
- `c : Eₘ`

Derived API:
- `homogeneousLinearProgrammingFeasibleSet hatA`
- `homogeneousLinearProgrammingOptimalValue hatA c`

Source/core/bridge triage:
- source-facing: the textbook dual homogeneous linear-programming value `f*`
- core/canonical: the Chapter 7 feasible-set and optimal-value owners attached to `(hatA, c)`
- bridge/view: the coordinatewise membership reformulation below

The source also records rank assumptions on `hatA` and on the augmented matrix `(hatA, c)`, but
those assumptions do not enter the definitional bodies of the feasible set or optimal value. This
file therefore stays recall-first on the existing pair-based Chapter 7 owners and keeps the rank
conditions as surrounding mathematical context rather than packaging them into a new public owner.
-/

section

variable (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) (c : Eₘ)

/- Definition 7.16: the homogeneous linear-programming feasible set and optimal value are the
existing Chapter 7 owners attached to `(hatA, c)`. -/
recall homogeneousLinearProgrammingFeasibleSet
recall homogeneousLinearProgrammingOptimalValue
recall homogeneousLinearProgrammingOptimalValue_eq_sSup

end

/-- Membership in `homogeneousLinearProgrammingFeasibleSet hatA` means satisfying the linear
constraint `\hat Aᵀ u = 0` together with the coordinatewise bounds `|u⁽ⁱ⁾| ≤ 1`. -/
theorem mem_homogeneousLinearProgrammingFeasibleSet_iff_coordinatewise
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) (u : Eₘ) :
    u ∈ homogeneousLinearProgrammingFeasibleSet hatA ↔
      hatA.transpose.mulVec u = 0 ∧ ∀ i, |u i| ≤ 1 := by
  rw [mem_homogeneousLinearProgrammingFeasibleSet_iff, mem_coordinatewiseUnitBox_iff]

end

/-! ### Lemma_7_16 (from Chap07) -/
noncomputable section

open scoped WithTopConvexAnalysis

universe u v

/- Lemma 7.16 lies in the Chapter 7 whole-space subdifferential / affine-pullback domain.

Mandatory domain-style sampling before refinement:
- `StrictlyPositiveOn` and `StrictlyPositiveOn.inequality` in `Definition_7_81`, the source-facing
  owner and its atomic projection lemma;
- `subdifferential_comp_affineMap_image_adjoint_subset` in `Chap03/Lemma_3_11`, the Euclidean
  affine-pullback bridge on subgradients;
- `IsSubgradientAt.comp_affineMap` in `Chap03/Definition_3_1_5`, the owner-level affine pullback
  theorem on subgradients;
- `matrix_transpose_adjointness` in `Chap01/Proposition_1_4_5`, the Euclidean bridge rewriting
  `⟪g, A (y - x)⟫` as `⟪Aᵀ g, y - x⟫`;
- `mem_preimage_linearMap_add_iff` in `Definition_7_82`, the chapter's canonical bridge for the
  affine preimage set `Q_y = {y | A y + b ∈ Q_x}`.

Best owner abstraction:
- source-facing: the affine-pullback inequality for explicit pulled-back subgradients;
- core/canonical: `StrictlyPositiveOn` together with the Chapter 3 affine-pullback owner
  `IsSubgradientAt.comp_affineMap`;
- bridge/view: the matrix specialization `y ↦ A y + b` from `Definition_7_82`, together with the
  transpose/adjoint identification from `Chap01/Proposition_1_4_5`.

Primitive data:
- the source-facing set `Q`;
- the real-valued objective `f`;
- the affine map `g`, or in coordinates the matrix `A` and translation `b`.

Derived API:
- the affine-pullback inequality for explicit pulled-back subgradients;
- the source-facing matrix-and-translation specialization.

Source/core/bridge triage:
- source-facing: Lemma 7.16's inequality for the affine pullback against pulled-back
  subgradients;
- core/canonical: `StrictlyPositiveOn` and `IsSubgradientAt.comp_affineMap`;
- bridge/view: the matrix specialization of the affine map, the affine preimage `Q_y`, and the
  transpose-adjoint identity.
-/

section AffinePullback

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

namespace StrictlyPositiveOn

/-- Lemma 7.16, affine form: for an explicit whole-space subgradient
`h ∈ ∂[Set.univ] f(g x)`, the
strict-positivity inequality for the affine pullback holds with the pulled-back vector
`g.linear.adjoint h`. -/
theorem inequality_comp_affineMap_image_adjoint
    {Qx : Set F} {f : F → ℝ}
    (hf : StrictlyPositiveOn Qx f) (g : E →ᵃ[ℝ] F)
    {x y : E}
    (hx : x ∈ g ⁻¹' Qx) (hy : y ∈ g ⁻¹' Qx)
    {h : F} (hh : h ∈ ∂[Set.univ] f((g x))) :
    0 ≤ f (g y) + f (g x) + inner ℝ (g.linear.adjoint h) (y - x) := by
  have hineq := hf.inequality hx hy hh
  have hgsub : g y - g x = g.linear (y - x) := by
    simpa using (g.linearMap_vsub y x).symm
  have hinner : inner ℝ h (g y - g x) = inner ℝ (g.linear.adjoint h) (y - x) := by
    rw [hgsub, ← g.linear.adjoint_inner_left]
  simpa [Function.comp, hinner] using hineq

end StrictlyPositiveOn

end AffinePullback

section MatrixSpecialization

variable {n m : ℕ}

local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "Em" => EuclideanSpace ℝ (Fin m)

open Matrix

namespace StrictlyPositiveOn

/-- Lemma 7.16, matrix specialization: for an explicit whole-space subgradient
`g ∈ ∂[Set.univ] f(A x + b)`, the
strict-positivity inequality for the affine pullback holds with the pulled-back vector `Aᵀ g`. -/
theorem inequality_comp_linearMap_add_image_adjoint
    {Qx : Set En} {f : En → ℝ}
    (hf : StrictlyPositiveOn Qx f)
    (A : Matrix (Fin n) (Fin m) ℝ) (b : En)
    {x y : Em}
    (hx : A.toEuclideanLin x + b ∈ Qx)
    (hy : A.toEuclideanLin y + b ∈ Qx)
    {g : En} (hg : g ∈ ∂[Set.univ] f((A.toEuclideanLin x + b))) :
    0 ≤
      f (A.toEuclideanLin y + b) + f (A.toEuclideanLin x + b) +
        inner ℝ (Aᵀ.toEuclideanLin g) (y - x) := by
  have hx' : x ∈ ((A.toEuclideanLin.toAffineMap +ᵥ AffineMap.const ℝ Em b) ⁻¹' Qx) := by
    rwa [mem_preimage_linearMap_add_iff]
  have hy' : y ∈ ((A.toEuclideanLin.toAffineMap +ᵥ AffineMap.const ℝ Em b) ⁻¹' Qx) := by
    rwa [mem_preimage_linearMap_add_iff]
  have hadjoint : A.toEuclideanLin.adjoint = Aᵀ.toEuclideanLin := by
    simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm
  simpa [hadjoint] using
    hf.inequality_comp_affineMap_image_adjoint
      (A.toEuclideanLin.toAffineMap +ᵥ AffineMap.const ℝ Em b) hx' hy' hg

end StrictlyPositiveOn

end MatrixSpecialization

end

/-! ### Proposition_7_16 (from Chap07) -/
noncomputable section

open scoped ConstrainedArgmin PositiveDefMatrixNorm

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 7.16 lies in Chapter 7's weighted smooth convex minimization / accelerated
projected-gradient domain.

Sampled owner-style declarations:
- `AcceleratedConvexMinimizationScheme` in `Algorithm_7_8`, the chapter owner of an accelerated
  feasible-set run with chosen gradient field, weighted proximal matrix, and positive smoothness
  constant;
- `argmin[Q]` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the project owner of
  a constrained minimizer together with the canonical feasibility-plus-`IsMinOn` membership
  bridge;
- `acceleratedSchemeSearchPoint` and `acceleratedSchemeProximalMinimand` in `Algorithm_7_8`, the
  derived chapter API for the extrapolated point and proximal objective;
- `positiveDefMatrixNorm` and the notations `‖·‖[G]`, `‖·‖[G,*]` in `Definition_7_23`, the
  chapter owners of the weighted norm and its dual norm for a positive-definite matrix;
- `CompositeSmoothConvexMinimizationProblem` in `Definition_7_39`, the nearby problem owner that
  uses the same positive `NNRealˣ` smoothness parameter and positive-definite matrix owner.

Best owner abstraction:
- source-facing: Proposition 7.16's rate estimate for an accelerated run on a closed convex set;
- core/canonical: `AcceleratedConvexMinimizationScheme n N`;
- bridge/view: the weighted dual-gradient Lipschitz hypothesis, stated pointwise on the feasible
  set and consumed by the accelerated-scheme owner, together with the constrained-minimizer
  membership `xStar ∈ argmin[Q] φ` unpacked via `mem_constrainedArgmin_iff` when needed.

Primitive data:
- the constrained problem, chosen gradient field, positive smoothness constant, positive-definite
  matrix owner, initial point, and iterate/prox-center sequences, all owned by
  `AcceleratedConvexMinimizationScheme`;
- the minimizing point `xStar`, packaged canonically as a member of
  `argmin[scheme.problem.feasibleSet] scheme.problem`.

Derived API:
- the extrapolated point `yₖ`, through `acceleratedSchemeSearchPoint`;
- the proximal argmin step, through `scheme.v_succ_mem_argmin`;
- feasibility and `IsMinOn` for `xStar`, through `mem_constrainedArgmin_iff`;
- the weighted and dual weighted norms, through `positiveDefMatrixNorm`.

The previous version duplicated the chapter owner by introducing a second public scheme structure
with the same mathematical content and a weaker raw-`L` parameter surface. This refinement
deletes that duplicate layer and states the proposition directly over the existing Chapter 7 owner.
-/

-- Proof sketch: derive the weighted smoothness inequality from the assumed dual-gradient Lipschitz
-- bound, then run the standard estimate-sequence argument for the chapter owner
-- `scheme : AcceleratedConvexMinimizationScheme n N`. Evaluating the resulting potential estimate
-- at the minimizer `xStar` gives the final bound for the output iterate `x_N`.
namespace AcceleratedConvexMinimizationScheme

/-- Proposition 7.16: if `scheme` is the accelerated projected-gradient run
`S(φ, L, Q, G, x₀, N)` with positive horizon `N ≥ 1`, and the chosen gradient field is
`L`-Lipschitz with respect to the weighted norm `‖·‖[G]` and dual norm `‖·‖[G,*]` on the
feasible set, then the output point `scheme.outputPoint = x_N` satisfies
`φ(x_N) - φ(xStar) ≤ 2 L ‖x₀ - xStar‖[G]^2 / (N (N + 1))` for every minimizer `xStar` of `φ` on
`Q`. -/
theorem outputPoint_suboptimality_le
    {N : ℕ} (scheme : AcceleratedConvexMinimizationScheme n N)
    (hN : 1 ≤ N)
    (hgradient_lipschitz :
      ∀ ⦃x y : E⦄,
        x ∈ scheme.problem.feasibleSet →
        y ∈ scheme.problem.feasibleSet →
          ‖scheme.gradient x - scheme.gradient y‖[scheme.metricMatrix,*] ≤
            (scheme.smoothness : ℝ) * ‖x - y‖[scheme.metricMatrix])
    {xStar : E} (hxStar : xStar ∈ argmin[scheme.problem.feasibleSet] scheme.problem) :
    scheme.problem scheme.outputPoint - scheme.problem xStar ≤
      (2 * (scheme.smoothness : ℝ) * ‖scheme.initialPoint - xStar‖[scheme.metricMatrix] ^ (2 : ℕ)) /
        ((N : ℝ) * ((N : ℝ) + 1)) := sorry

end AcceleratedConvexMinimizationScheme

end

/-! ### Theorem_7_16 (from Chap07) -/
open scoped BigOperators Gradient HessianDualLocalNorm

noncomputable section

universe u

section

variable {X : Type u}

/-- The explicit rate term
`δ_k = 2 (√(ν / (k + 1)) + ν / (k + 1))
  (1 + log (2 + (3 / 2) √(ν (k + 1))))`
from the relative-accuracy estimate for the barrier subgradient method. -/
def barrierSubgradientRelativeAccuracyDelta (ν : ℝ) (k : ℕ) : ℝ :=
  2 * (Real.sqrt (ν / ((k : ℝ) + 1)) + ν / ((k : ℝ) + 1)) *
    (1 + Real.log (2 + (3 / 2 : ℝ) * Real.sqrt (ν * ((k : ℝ) + 1))))

/-- The explicit relative-accuracy rate is positive whenever the barrier parameter `ν` is
positive. -/
theorem barrierSubgradientRelativeAccuracyDelta_pos {ν : ℝ} (hν : 0 < ν) (k : ℕ) :
    0 < barrierSubgradientRelativeAccuracyDelta ν k := sorry

/-- The geometric mean of the positive values `ψ(x₀), …, ψ(x_k)`. -/
def positiveIterateGeometricMean
    (ψ : X → {r : ℝ // 0 < r}) (x : ℕ → X) (k : ℕ) : ℝ :=
  Real.rpow
    (Finset.prod (Finset.range (k + 1)) fun i ↦ (ψ (x i) : ℝ))
    (1 / ((k : ℝ) + 1))

/-- Expanding `positiveIterateGeometricMean ψ x k` gives the geometric mean of the first `k + 1`
positive values along the iterate sequence. -/
@[simp] theorem positiveIterateGeometricMean_def
    (ψ : X → {r : ℝ // 0 < r}) (x : ℕ → X) (k : ℕ) :
    positiveIterateGeometricMean ψ x k =
      Real.rpow
        (Finset.prod (Finset.range (k + 1)) fun i ↦ (ψ (x i) : ℝ))
        (1 / ((k : ℝ) + 1)) :=
  rfl

section RelativeAccuracyBridge

variable (ψ : X → {r : ℝ // 0 < r}) (x : ℕ → X)
variable (ψStar : {r : ℝ // 0 < r}) {ν : ℝ} (k : ℕ)

-- Proof sketch: rewrite the arithmetic mean of the logarithms as the logarithm of the geometric
-- mean, then exponentiate the bound
-- `log ψ⋆ - (1 / (k + 1)) ∑_{i=0}^k log ψ(x_i) ≤ δ_k`.
/-- Exponentiating the logarithmic average estimate yields the geometric-mean lower bound
`[∏_{i=0}^k ψ(x_i)]^(1 / (k + 1)) ≥ ψ⋆ exp(-δ_k)`. This is the generic bridge/view step used in
Theorem 7.16 once the owner-level logarithmic estimate has been established. -/
theorem positiveIterateGeometricMean_ge_optimal_mul_exp_neg_rate_of_log_rate
    (hlog_rate :
      Real.log (ψStar : ℝ) -
          (Finset.sum (Finset.range (k + 1)) fun i ↦ Real.log (ψ (x i) : ℝ)) /
            ((k : ℝ) + 1) ≤
        barrierSubgradientRelativeAccuracyDelta ν k)
    :
    positiveIterateGeometricMean ψ x k ≥
      (ψStar : ℝ) * Real.exp (-barrierSubgradientRelativeAccuracyDelta ν k) := sorry

/-- Once the geometric mean is known to lie between `ψ⋆ exp (-δ_k)` and `ψ⋆`, it is a
relative-scale `δ_k` approximation of `ψ⋆` in the sense of Definition 7.65. -/
theorem positiveIterateGeometricMean_isRelativeScaleDeltaApproximation_of_bounds
    (hexp_bound :
      positiveIterateGeometricMean ψ x k ≥
        (ψStar : ℝ) * Real.exp (-barrierSubgradientRelativeAccuracyDelta ν k))
    (hmean_le : positiveIterateGeometricMean ψ x k ≤ (ψStar : ℝ))
    (hδ_pos : 0 < barrierSubgradientRelativeAccuracyDelta ν k) :
    IsRelativeScaleDeltaApproximation
      (ψStar : ℝ)
      (barrierSubgradientRelativeAccuracyDelta ν k)
      (positiveIterateGeometricMean ψ x k) := sorry

-- Proof sketch: combine the exponential estimate with the elementary inequality
-- `exp (-t) ≥ 1 - t`.
/-- The exponential lower bound implies the weaker linear lower bound obtained from
`exp (-δ_k) ≥ 1 - δ_k`. -/
theorem positiveIterateGeometricMean_ge_optimal_mul_one_sub_rate_of_exp_bound
    (hexp_bound :
      positiveIterateGeometricMean ψ x k ≥
        (ψStar : ℝ) * Real.exp (-barrierSubgradientRelativeAccuracyDelta ν k)) :
    positiveIterateGeometricMean ψ x k ≥
      (ψStar : ℝ) * (1 - barrierSubgradientRelativeAccuracyDelta ν k) := sorry

end RelativeAccuracyBridge

section BarrierSubgradient

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/- Theorem 7.16 lies in Chapter 7's primal barrier-subgradient / relative-scale maximization
domain.

Mandatory domain-style sampling:
- `BarrierSubgradientMethod` in `Chap07/Algorithm_7_14`, the source-facing owner of the primal
  barrier-subgradient run `(7.3.33)`;
- `IsMaxOn`, the canonical maximizer predicate for the positive optimum `x⋆`;
- `logarithmicTransform_has_constrained_subgradient_norm_le_one_and_concaveOn` in
  `Chap07/Lemma_7_14`, the chapter bridge that turns positivity and concavity of `ψ` into the
  logarithmic barrier-subgradient hypotheses needed for the dual explicit-rate owner;
- `DualBarrierSubgradientMethod.maximalGap_le_explicit_rate` in `Chap07/Theorem_7_15`, the
  upstream explicit-rate owner whose scalar error term is recorded below as `δ_k`.

Best owner abstraction:
- source-facing: Theorem 7.16 for an actual `BarrierSubgradientMethod` and an actual maximizing
  point `x⋆`;
- core/canonical: `BarrierSubgradientMethod`, `IsMaxOn`, and the generic owner
  `positiveIterateGeometricMean`;
- bridge/view: the logarithmic average estimate and the generic exponentiation lemmas from the
  previous section.

Primitive data:
- the method owner `method : BarrierSubgradientMethod P₀ F ψ v x₀`;
- the maximizing feasible point `x⋆`;
- the maximizing property of `x⋆`;
- concavity of `ψ` on `P₀`;
- the Chapter 7 barrier assumptions on `F`;
- the canonical Hessian-dual local norm bound `‖∇ ψ(x)‖*ₓ ≤ ψ(x)` on `P₀`.

Derived API:
- the positive iterate geometric mean `method.iterateGeometricMean k`;
- the logarithmic average estimate for `log ψ`;
- the exponential and linear relative-scale lower bounds.
-/

namespace BarrierSubgradientMethod

variable {P0 : Set E} {F ψ : E → ℝ} {v : NNRealˣ} {x0 : P0}

/-- The geometric mean of the positive values `ψ(x₀), …, ψ(x_k)` along a barrier subgradient
method. -/
def iterateGeometricMean
    (method : BarrierSubgradientMethod P0 F ψ v x0) (k : ℕ) : ℝ :=
  positiveIterateGeometricMean
    (fun x : P0 ↦ ⟨ψ x, method.ψ_pos x.property⟩)
    method.iterate k

/-- If `x⋆` maximizes `ψ` on `P₀`, then the geometric mean of the positive iterate values of `ψ`
along `method` is bounded above by `ψ(x⋆)`. -/
theorem iterateGeometricMean_le_optimal
    (method : BarrierSubgradientMethod P0 F ψ v x0)
    (xStar : P0) (hoptimal : IsMaxOn ψ P0 xStar) (k : ℕ) :
    method.iterateGeometricMean k ≤ ψ xStar := sorry

section ExplicitRate

variable (method : BarrierSubgradientMethod P0 F ψ v x0)
variable (xStar : P0) (hoptimal : IsMaxOn ψ P0 xStar)
variable (ν : NNReal) (hν : 0 < (ν : ℝ))
variable [IsSelfConcordantBarrierOnWith P0 ν F]
variable [HasPositiveDefiniteHessianOn P0 F]
variable (hψ_concave : ConcaveOn ℝ P0 ψ)
variable
  (hψ_dual_bound :
    ∀ x : P0,
      HessianDualLocalNorm.ofPosDefMem F x.2
          (InnerProductSpace.toDualMap ℝ E (∇ ψ x)) ≤
        ψ x)

-- Proof sketch: apply Lemma 7.14 to `logarithmicTransform ψ`, using concavity of `ψ`, positivity
-- and differentiability from `method`, and the local Hessian-dual norm bound `‖∇ ψ(x)‖*ₓ ≤ ψ(x)`
-- to place `-log ψ` in the Chapter 7 barrier-subgradient class with bound `1`; then invoke the
-- explicit-rate owner from Theorem 7.15 for the resulting logarithmic barrier-subgradient run and
-- rewrite its normalized maximal-gap bound as the logarithmic average estimate below.
/-- Theorem 7.16 first yields the logarithmic average estimate for `log ψ` along the actual
barrier-subgradient run from Algorithm 7.14, under the source-facing Chapter 7 assumptions:
`x⋆` maximizes `ψ` on `P₀`, `ψ` is concave on `P₀`, `F` is a `ν`-self-concordant barrier on
`P₀`, and the gradient of `ψ` has Hessian-dual local norm at most `ψ(x)` at every feasible point.
-/
theorem logarithmicAverageGap_le_relativeAccuracyDelta
    (k : ℕ) :
    Real.log (ψ xStar) -
        (Finset.sum (Finset.range (k + 1)) fun i ↦ Real.log (ψ (method i))) /
          ((k : ℝ) + 1) ≤
      barrierSubgradientRelativeAccuracyDelta (ν : ℝ) k := sorry

/-- Theorem 7.16 on the primal owner surface: under the same Chapter 7 source assumptions as the
preceding logarithmic-gap theorem, the geometric mean of the first `k + 1` iterate values of `ψ`
along the actual barrier-subgradient run is bounded below by `ψ(x⋆) exp (-δ_k)`. -/
theorem positiveIterateGeometricMean_ge_optimal_mul_exp_neg_rate
    (k : ℕ) :
    method.iterateGeometricMean k ≥
      ψ xStar * Real.exp (-barrierSubgradientRelativeAccuracyDelta (ν : ℝ) k) := sorry

/-- Theorem 7.16 expressed through the chapter owner
`IsRelativeScaleDeltaApproximation`: the upper bound by `ψ(x⋆)` and positivity of `δ_k` are
derived from the maximizing property of `x⋆`, the positivity of the barrier parameter `ν`, and
the logarithmic estimate above, so the public theorem stays on the primal source-facing owner
surface. -/
theorem positiveIterateGeometricMean_isRelativeScaleDeltaApproximation
    (k : ℕ) :
    IsRelativeScaleDeltaApproximation
      (ψ xStar)
      (barrierSubgradientRelativeAccuracyDelta (ν : ℝ) k)
      (method.iterateGeometricMean k) := sorry

-- Proof sketch: combine the exponential estimate from Theorem 7.16 with the elementary
-- inequality `exp (-t) ≥ 1 - t`.
/-- The weaker linear lower bound obtained from Theorem 7.16 via `exp (-δ_k) ≥ 1 - δ_k`, again
derived from the same Chapter 7 bridge assumptions rather than from a separately supplied
logarithmic-rate hypothesis. -/
theorem positiveIterateGeometricMean_ge_optimal_mul_one_sub_rate
    (k : ℕ) :
    method.iterateGeometricMean k ≥
      ψ xStar * (1 - barrierSubgradientRelativeAccuracyDelta (ν : ℝ) k) := sorry

end ExplicitRate

end BarrierSubgradientMethod

end BarrierSubgradient

end
