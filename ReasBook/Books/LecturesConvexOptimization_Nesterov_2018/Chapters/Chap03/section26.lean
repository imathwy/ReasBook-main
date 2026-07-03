import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_26 (from Chap03) -/
universe u

namespace LagrangianProblem

variable {Q : Type u} {m : ℕ}

local notation "Λ" => EuclideanSpace ℝ (Fin m)

open scoped EuclideanOrthant

/- Definition 3.26 lies in the chapter's Lagrangian-duality API.

Primary domain:
- Lagrangian duality for finitely many inequality constraints.

Sampled owner-style declarations:
- `LagrangianProblem.dualFunction`
- `EuclideanSpace.nonnegativeOrthant`
- `IsMaxOn`
- `isMaxOn_iff`
- `EuclideanSpace.mem_nonnegativeOrthant_iff`

Best owner abstraction:
- `problem : LagrangianProblem Q m`, with a source-facing predicate on a multiplier vector
  `lamStar : Λ`.

Primitive data:
- the owner problem `problem`
- the candidate multiplier `lamStar`

Derived API:
- the dual function `problem.dualFunction`
- nonnegativity via `ℝ₊^m`
- dual optimality on `ℝ₊^m` via `IsMaxOn`
- the coordinatewise textbook spelling via `isOptimalDualMultiplier_iff`

Source/core/bridge triage:
- source-facing: the notion that `lamStar` is a vector of optimal dual multipliers
- core/canonical: membership in the nonnegative orthant together with `IsMaxOn` of the dual
  function on that orthant
- bridge/view: `EuclideanSpace.mem_nonnegativeOrthant_iff` and `isMaxOn_iff`

The source definition is genuinely about a named property of a multiplier vector, so this file
keeps a source-facing predicate instead of only recalling a raw type expression. The earlier
`dualFeasibleSet = dualDomain ∩ ℝ₊ᵐ` packaging is not used in the main owner here because the
textbook definition quantifies over all nonnegative multipliers, not only over those with
`q(λ) > -∞`. -/

/-- Definition 3.26: a vector `λ*` is a vector of optimal dual (Lagrange) multipliers if it is
nonnegative and maximizes the dual function on `ℝ₊^m`. -/
def IsOptimalDualMultiplier (problem : LagrangianProblem Q m) (lamStar : Λ) : Prop :=
  lamStar ∈ ℝ₊^m ∧
    IsMaxOn problem.dualFunction (ℝ₊^m) lamStar

section

variable {problem : LagrangianProblem Q m} {lamStar : Λ}

/-- The source-facing predicate `problem.IsOptimalDualMultiplier lamStar` is equivalent to the
textbook coordinatewise formulation `λ* ≥ 0` and `q(λ*) ≥ q(λ)` for every nonnegative
multiplier `λ`. -/
-- Proof sketch: unfold `LagrangianProblem.IsOptimalDualMultiplier`, rewrite orthant membership
-- by `EuclideanSpace.mem_nonnegativeOrthant_iff` and optimality by `isMaxOn_iff`, then regroup
-- the resulting conjunction and quantifiers.
theorem isOptimalDualMultiplier_iff :
    problem.IsOptimalDualMultiplier lamStar ↔
      (∀ j : Fin m, 0 ≤ lamStar j) ∧
        ∀ lam : Λ, (∀ j : Fin m, 0 ≤ lam j) →
          problem.dualFunction lam ≤ problem.dualFunction lamStar := by
  rw [IsOptimalDualMultiplier, EuclideanSpace.mem_nonnegativeOrthant_iff]
  constructor
  · rintro ⟨hlamStar, hmax⟩
    refine ⟨hlamStar, ?_⟩
    intro lam hlam
    exact (isMaxOn_iff.mp hmax) lam <| by
      simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using hlam
  · rintro ⟨hlamStar, hmax⟩
    refine ⟨hlamStar, isMaxOn_iff.mpr ?_⟩
    intro lam hlam
    exact hmax lam <| by
      simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using hlam

end

end LagrangianProblem

/-! ### Lemma_3_26 (from Chap03) -/
noncomputable section

open scoped PointwiseGrowthFunction

universe u

section

variable {X : Type u} [MetricSpace X] {Q : Set X}

/- Lemma 3.26 lies in the chapter's pointwise-growth / best-value-gap domain.

Sampled owner-style declarations:
- `pointwiseGrowthFunction` in `Lemma_3_2_1`, the owner growth profile on a metric space
- `pointwiseGrowthFunction_monotone` in `Proposition_3_34`, the radius-monotonicity theorem for
  the owner growth profile
- `sub_le_pointwiseGrowthFunction_dist` in `Proposition_3_34`, the owner pointwise comparison at
  the metric distance
- `bestRadiusUpTo` in `Theorem_3_2_10`, the chapter source-facing owner for the best sampled
  radius
- `bestFunctionValueGapUpTo_le_modulusAtBestRadius` in `Lemma_3_2_2`, the owner best-value
  comparison for a monotone modulus

Best owner abstraction:
- `pointwiseGrowthFunction`

Primitive data:
- a restricted objective `f : ↥Q → ℝ`
- a subtype-valued sample history `xSeq : ℕ → ↥Q`
- a reference point `xStar : ↥Q`

Derived API:
- the best-value bound obtained by applying the owner theorem directly to the subtype `↥Q`
- the pointwise comparison `sub_le_pointwiseGrowthFunction_dist` specialized to `↥Q`

Source/core/bridge triage:
- source-facing: Lemma 3.26's best sampled-value gap bound on the feasible set `Q`, stated for an
  arbitrary reference point and hence specializing to the textbook minimizer case
- core/canonical: `pointwiseGrowthFunction` and
  `bestFunctionValueGapUpTo_le_modulusAtBestRadius`
- bridge/view: the specialization of the owner growth profile to the subtype `↥Q`

This file specializes the owner theorem
`bestFunctionValueGapUpTo_le_modulusAtBestRadius` directly to the subtype metric space `↥Q`. Its
public surface is just that source-facing specialization, stated with the canonical owner
expression `pointwiseGrowthFunction f xStar` and no redundant local wrapper or extra optimality
binder.
-/

/-- Lemma 3.26: for any reference point `xStar ∈ Q`, the best objective-value gap above `f xStar`
among the sample points `x₀, …, x_k` is bounded by the pointwise growth function of the
restricted objective, evaluated at the best sampled distance to `xStar`. The growth function is
`WithTop ℝ`-valued so that unbounded ball-growth is represented by `⊤`. In particular, this
recovers the textbook minimizer formulation when `xStar` is optimal on `Q`. -/
-- Proof sketch: apply `bestFunctionValueGapUpTo_le_modulusAtBestRadius` directly on the subtype
-- `↥Q`, with modulus `pointwiseGrowthFunction f xStar` and radius sequence
-- `i ↦ dist (xSeq i) xStar`. The required pointwise bound is exactly
-- `sub_le_pointwiseGrowthFunction_dist` on the subtype metric space.
theorem bestFunctionValueUpTo_sub_le_pointwiseGrowthFunction_at_bestRadius
    (f : ↥Q → ℝ) (xSeq : ℕ → ↥Q) (xStar : ↥Q) (k : ℕ) :
    bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k - f xStar ≤
      ω[f; xStar] (bestRadiusUpTo (fun i ↦ dist (xSeq i) xStar) k) := by
  simpa using
    bestFunctionValueGapUpTo_le_modulusAtBestRadius
      f
      (ω[f; xStar])
      (pointwiseGrowthFunction_monotone f xStar)
      xSeq xStar (fun i ↦ dist (xSeq i) xStar) k
      (fun i ↦ sub_le_pointwiseGrowthFunction_dist f xStar (xSeq i))

end

end

/-! ### Proposition_3_26 (from Chap03) -/
noncomputable section

universe uE uU uι uR

open scoped BigOperators
open scoped WithTopConvexAnalysis

/- Proposition 3.26 (1) lies in the chapter's sampled affine-minorant aggregation domain.

Relevant owner-style declarations sampled before refinement:
- `subdifferential` and the notation `∂ f(x)` in `Definition_3_1_5`, the chapter owner for
  extended-valued subgradients;
- `mem_subdifferential_iff` in `Definition_3_1_5`, the atomic bridge from the owner notation to
  the supporting-inequality predicate;
- the mathlib affine-map owner `E →ᵃ[ℝ] ℝ`, whose additive and `ℝ`-module structure canonically
  organizes weighted sums of sampled affine minorants;
- `Convex.centerMass_mem`, the owner theorem used for Proposition 3.26 (2).

Best owner abstractions:
- source-facing: the weighted sampled affine lower model from Proposition 3.26 (1);
- core/canonical: the affine-map sum
  `∑ i, α i • sampledAffineMinorant (y i) (g i) (f (y i)) : E →ᵃ[ℝ] ℝ`;
- bridge/view: the pointwise evaluation formula for that affine-map sum, together with
  `mem_subdifferential_iff` for the subgradient hypotheses.

Primitive data:
- weights `α : ι → ℝ`;
- sampled points `y : ι → E`;
- sampled subgradients `g : ι → E`;
- sampled values `f (y i)`.

Derived API:
- the sampled affine minorants and their affine-map sum
  `∑ i, α i • sampledAffineMinorant (y i) (g i) (f (y i))`;
- the pointwise expansion `sum_smul_sampledAffineMinorant_apply`;
- the lower-bound theorem `sum_smul_sampledAffineMinorant_le`.

The earlier version exposed the sampled model through a proposition-local wrapper around the
canonical affine-map sum and stated the subgradient data through the lower-level predicate
`IsSubgradientAt`. This refinement keeps the same mathematical semantics, but removes that
duplicate owner in favor of the affine-map sum itself and states the hypotheses through the
existing subdifferential notation `∂ f(x)`.
-/

section

variable {ι : Type uι}
variable {E : Type uE} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The affine minorant determined by one sampled value `f y`, one sample point `y`, and one
chosen subgradient `g`. -/
def sampledAffineMinorant (y g : E) (fy : ℝ) : E →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ E (fy - inner ℝ g y) +
    LinearMap.toAffineMap (((innerSL ℝ) g).toLinearMap)

/-- Evaluating the sampled affine minorant recovers the textbook pointwise affine lower model
`f(y) + ⟪g, x - y⟫`. -/
@[simp] theorem sampledAffineMinorant_apply (y g x : E) (fy : ℝ) :
    sampledAffineMinorant y g fy x = fy + inner ℝ g (x - y) := by
  simp [sampledAffineMinorant, sub_eq_add_neg, inner_add_right, inner_neg_right]
  ring

/-- Evaluating the canonical affine-map sum of the sampled affine minorants gives the weighted
pointwise sum of the textbook lower models. -/
@[simp] theorem sum_smul_sampledAffineMinorant_apply [Fintype ι]
    (α : ι → ℝ) (y g : ι → E) (f : E → ℝ) (x : E) :
    (∑ i, α i • sampledAffineMinorant (y i) (g i) (f (y i)) : E →ᵃ[ℝ] ℝ) x =
      ∑ i, α i * (f (y i) + inner ℝ (g i) (x - y i)) := by
  classical
  let s : Finset ι := Finset.univ
  change (s.sum fun i ↦ α i • sampledAffineMinorant (y i) (g i) (f (y i))) x =
    s.sum fun i ↦ α i * (f (y i) + inner ℝ (g i) (x - y i))
  clear_value s
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert i s his ih =>
      simp [his, ih, sampledAffineMinorant_apply]

/-- Proposition 3.26 (1): the aggregated affine lower model is dominated by the original convex
function. -/
-- Proof sketch: rewrite `g i ∈ ∂ (fun z ↦ (f z : WithTop ℝ))((y i))` via
-- `mem_subdifferential_iff`, apply the resulting affine lower-support inequality at the
-- comparison point `x`, multiply by the nonnegative weight `α i`, sum over the finite index type,
-- and use `∑ i, α i = 1`.
theorem sum_smul_sampledAffineMinorant_le
    [Fintype ι] {f : E → ℝ} (y g : ι → E)
    (hsubgrad : ∀ i, g i ∈ ∂ (fun z ↦ (f z : WithTop ℝ))((y i)))
    (α : ι → ℝ) (hα_nonneg : ∀ i, 0 ≤ α i)
    (hα_sum : ∑ i, α i = 1) (x : E) :
    (∑ i, α i • sampledAffineMinorant (y i) (g i) (f (y i)) : E →ᵃ[ℝ] ℝ) x ≤ f x := by
  have hsupport : ∀ i, f (y i) + inner ℝ (g i) (x - y i) ≤ f x := by
    intro i
    have hx_dom : x ∈ dom (fun z ↦ (f z : WithTop ℝ)) := by
      simp [withTopEffectiveDomain]
    have hineq :
        ((f x : WithTop ℝ) ≥
          (f (y i) : WithTop ℝ) + inner ℝ (g i) (x - y i)) :=
      (mem_subdifferential_iff.mp (hsubgrad i)).2 hx_dom
    exact_mod_cast hineq
  calc
    (∑ i, α i • sampledAffineMinorant (y i) (g i) (f (y i)) : E →ᵃ[ℝ] ℝ) x
        = ∑ i, α i * (f (y i) + inner ℝ (g i) (x - y i)) := by
          rw [sum_smul_sampledAffineMinorant_apply]
    _ ≤ ∑ i, α i * f x := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      exact mul_le_mul_of_nonneg_left (hsupport i) (hα_nonneg i)
    _ = (∑ i, α i) * f x := by
      rw [Finset.sum_mul]
    _ = f x := by
      rw [hα_sum, one_mul]

end

section

variable {ι : Type uι}
variable {R : Type uR} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/- Proposition 3.26 (2) lies in the finite convex-combination / center-of-mass domain.

Sampled owner-style declarations:
- `Finset.centerMass`
- `Convex.centerMass_mem`
- `ConvexOn.exists_ge_of_centerMass` in `Chap03/Theorem_3_1`

Best owner abstraction:
- `Convex.centerMass_mem`

Primitive data:
- a convex feasible set `S`
- a finite family `u : ι → U` with `u i ∈ S`
- normalized nonnegative weights `α`

Derived API:
- the weighted average `(Finset.univ).centerMass α u`

Source/core/bridge triage:
- source-facing: the normalized weighted-average feasibility statement in Proposition 3.26 (2)
- core/canonical: `Convex.centerMass_mem`
- bridge/view: the source normalization `∑ i, α i = 1`, used only to discharge the owner's
  positivity hypothesis

The previous file exposed an extra proposition-local argmax wrapper and then projected away all of
its maximizer data in the proof. This refinement keeps only the primitive feasibility data that
affect the conclusion and reuses the canonical owner directly.
-/

/-- Proposition 3.26 (2): a convex feasible set contains the normalized weighted average of
finitely many feasible points. The textbook real statement is the specialization `R = ℝ`. -/
-- Proof sketch: apply the canonical owner theorem `Convex.centerMass_mem`; the source
-- normalization `∑ i, α i = 1` supplies the required positivity hypothesis.
theorem centerMass_mem_of_sum_eq_one
    {U : Type uU} [Fintype ι] [AddCommGroup U] [Module R U]
    {S : Set U} (hS : Convex R S) (u : ι → U) (hu : ∀ i, u i ∈ S)
    (α : ι → R) (hα_nonneg : ∀ i, 0 ≤ α i) (hα_sum : ∑ i, α i = 1) :
    (Finset.univ).centerMass α u ∈ S := by
  classical
  exact hS.centerMass_mem
    (fun i _ ↦ hα_nonneg i)
    (by simp [hα_sum])
    (fun i _ ↦ hu i)

end

end

/-! ### Theorem_3_26 (from Chap03) -/
open scoped WithTopConvexAnalysis

/- Theorem 3.26 is a `bridge/view` recall in the chapter's extended-valued
homogeneous-subdifferential domain.

Primary domain:
- convex analysis of `ℝ ∪ {+∞}`-valued functions on real inner-product spaces, with effective
  domains, subgradients, and positive homogeneity on cones.

Relevant owner-style declarations sampled before refinement:
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter bridge from extended values to the
  effective-domain real part;
- `subdifferential` and the notation `∂ f(x)` in `Definition_3_1_5`, the chapter owner API for
  subgradients;
- `IsPositivelyHomogeneousOn` in `Definition_3_1_7`, the chapter owner for positive homogeneity;
- `euler_homogeneous_function_theorem` in `Theorem_3_1_21`, the exact upstream chapter theorem
  with the target interface;
- the inner-product evaluation `inner ℝ g x`, the canonical pairing available in the current
  ambient real inner-product-space owner.

Best owner abstraction:
- `euler_homogeneous_function_theorem` on the owner data
  `IsPositivelyHomogeneousOn p (dom f) (withTopRealPart f)` and `g ∈ ∂ f(x)`.

Primitive data:
- an extended-valued function `f : E → WithTop ℝ`;
- a degree `p : ℝ`;
- the owner homogeneity hypothesis `IsPositivelyHomogeneousOn p (dom f) (withTopRealPart f)`;
- a subgradient witness `hg : g ∈ ∂ f(x)`.

Derived API:
- the Euler identity `inner ℝ g x = p * withTopRealPart f x`, already provided upstream by
  `euler_homogeneous_function_theorem`.

Source/core/bridge triage:
- source-facing: the numbered Euler identity for homogeneous extended-valued functions;
- core/canonical: `euler_homogeneous_function_theorem`;
- bridge/view: this numbered restatement, expressed on the chapter owners `dom f`,
  `withTopRealPart f`, `∂ f(x)`, and `IsPositivelyHomogeneousOn`.

The textbook states the result for convex functions on `ℝ^n` and assumes subdifferentiability at
every point of `dom f`, but the actual identity only uses the chosen subgradient witness
`g ∈ ∂ f(x)` together with homogeneity on the effective domain. The public statement therefore
keeps the source meaning while removing those redundant global assumptions and the unnecessary
coordinate specialization. Since the exact theorem already exists upstream in
`Theorem_3_1_21`, this file recalls that canonical declaration directly instead of keeping a
parallel local theorem name.
-/

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
Theorem 3.26: if an `ℝ ∪ {+∞}`-valued function is homogeneous of degree `p` on its effective
domain, then every subgradient at `x` pairs with `x` to give `p` times the finite real part of the
function value at `x`.
-/
recall euler_homogeneous_function_theorem
    {f : E → WithTop ℝ} {p : ℝ}
    (hhom : IsPositivelyHomogeneousOn p (dom f) (withTopRealPart f))
    {x g : E} (hg : g ∈ ∂ f(x)) :
    inner ℝ g x = p * withTopRealPart f x
