import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_25 (from Chap03) -/
namespace GeneralMinimizationProblem

variable {n m : ℕ}

/- Definition 3.25 is a source-facing recall in the constrained-optimization domain of owner
predicates on `GeneralMinimizationProblem n m`.

Primary mathematical domain:
* smooth inequality-constrained minimization on a closed convex feasible set

Sampled owner-style declarations:
* `problem.IsSmooth` in `Definition_1_1_4_3`
* `problem.IsFunctionalConstraintProblem` in `Definition_1_10_21`
* `problem.HasLeConstraints` in `Definition_1_1_1`
* `problem.constraintVector_continuous_iff` in `Definition_1_10_21`

Best owner abstraction:
* `GeneralMinimizationProblem n m`, with the owner smoothness predicate `problem.IsSmooth` and
  the source-facing feasible-set hypotheses expressed directly on `problem.basicFeasibleSet`

Primitive data:
* the owner problem `problem`
* the smoothness hypothesis `problem.IsSmooth`
* the inequality-sense hypothesis `problem.HasLeConstraints`
* closedness and convexity of `problem.basicFeasibleSet`

Derived API:
* objective continuity from `problem.IsSmooth`
* scalar-constraint continuity from `problem.constraintVector_continuous_iff` together with
  `problem.IsSmooth`
* the bundled Chapter 1 bridge `problem.IsFunctionalConstraintProblem`, recovered by
  `smoothFunctionalConstraintProblem_iff`

Source/core/bridge triage:
* source-facing: Definition 3.25 as `problem.IsSmooth`, `problem.HasLeConstraints`, and
  closed-convex geometry of `problem.basicFeasibleSet`
* core/canonical: the owner problem together with its Chapter 1 smoothness predicate
  `problem.IsSmooth`
* bridge/view: the companion equivalence that repackages the source-facing hypothesis list as the
  bundled Chapter 1 predicate `problem.IsFunctionalConstraintProblem`

This file therefore keeps no parallel `IsSmoothFunctionalConstraintProblem` wrapper. Downstream
usage should use the source-facing owner expression directly, and only use the package bridge when
that bundled Chapter 1 API is specifically needed. -/

variable (problem : GeneralMinimizationProblem n m)

/- Definition 3.25: a smooth minimization problem with functional constraints is a smooth
minimization problem whose constraints are all of the form `fⱼ(x) ≤ 0` and whose basic feasible
set `Q` is closed and convex. -/
#check (
  problem.IsSmooth ∧
    problem.HasLeConstraints ∧
    IsClosed problem.basicFeasibleSet ∧
    Convex ℝ problem.basicFeasibleSet
)

section

variable {problem : GeneralMinimizationProblem n m}

/-- The source-facing hypothesis list for Definition 3.25 is equivalent to the bundled Chapter 1
functional-constraint package together with convexity of the basic feasible set. -/
theorem smoothFunctionalConstraintProblem_iff :
    (problem.IsSmooth ∧
      problem.HasLeConstraints ∧
      IsClosed problem.basicFeasibleSet ∧
      Convex ℝ problem.basicFeasibleSet) ↔
      (problem.IsSmooth ∧
        problem.IsFunctionalConstraintProblem ∧
        Convex ℝ problem.basicFeasibleSet) := by
  constructor
  · rintro ⟨hsmooth, hle, hclosed, hconvex⟩
    exact
      ⟨hsmooth,
        { basicFeasibleSet_isClosed := hclosed
          objective_continuous := hsmooth.objective_continuous
          constraint_continuous := fun j ↦
            (problem.constraintVector_continuous_iff.mp hsmooth.constraintVector_continuous) j
          hasLeConstraints := hle },
        hconvex⟩
  · rintro ⟨hsmooth, hfunctional, hconvex⟩
    exact ⟨hsmooth, hfunctional.hasLeConstraints, hfunctional.basicFeasibleSet_isClosed, hconvex⟩

end

end GeneralMinimizationProblem

/-! ### Lemma_3_25 (from Chap03) -/
/- Lemma 3.25 lies in the chapter's subgradient-localization / pointwise-growth domain.

Primary mathematical domain:
- real-valued convex analysis on `ℝⁿ`, organized around subgradient-based localization radii and
  growth functions.

Sampled owner-style declarations:
- `IsSubgradientAt` in `Definition_3_1_5`, the chapter owner predicate for subgradients via the
  canonical `WithTop`-valued formulation;
- `subgradientLocalizationMeasure` in `Lemma_3_2_1`, with source-facing surface `v[g; xBar] x`
  for the localization radius attached to a chosen subgradient selection;
- `pointwiseGrowthFunction` in `Lemma_3_2_1`, with source-facing surface `ω[f; xBar] t` for the
  supremal ball-growth profile;
- `sub_le_lipschitz_mul_max_localizationMeasure` in `Lemma_3_2_1`, the owner theorem for the
  Lipschitz growth bound.

Best owner abstraction:
- `subgradientLocalizationMeasure`
- `pointwiseGrowthFunction`
- the owner comparison theorems built from them in `Lemma_3_2_1`

Primitive data:
- a real-valued function `f : V → ℝ` on a real inner product space;
- a chosen subgradient selection `g : V → V`;
- the base point `xBar` and evaluation point `x`.

Derived API:
- the growth comparison
  `sub_le_pointwiseGrowthFunction_of_localizationMeasure`;
- the Lipschitz refinement
  `sub_le_lipschitz_mul_max_localizationMeasure`.

Source/core/bridge triage:
- source-facing: Lemma 3.25's comparison of `f x - f xBar` with the canonical growth function and
  its Lipschitz specialization;
- core/canonical: `IsSubgradientAt`, `subgradientLocalizationMeasure`, and
  `pointwiseGrowthFunction`;
- bridge/view: none beyond the coercion `fun y ↦ (f y : WithTop ℝ)` already absorbed by the owner
  theorems.

The previous version duplicated a real-valued subgradient predicate, its subdifferential, the
localization measure, the growth function, and two theorem wrappers carrying an unused convexity
hypothesis. The chapter already centers this domain on `Lemma_3_2_1`, so this file now recalls the
owner theorems directly instead of keeping a second local API surface.
-/

recall sub_le_pointwiseGrowthFunction_of_localizationMeasure

recall sub_le_lipschitz_mul_max_localizationMeasure

/-! ### Proposition_3_25 (from Chap03) -/
open Set
open scoped Gradient WithTopConvexAnalysis EuclideanOrthant

noncomputable section

/- Proposition 3.25 is a `bridge/view` theorem in the chapter's support-envelope / convex-hull
subdifferential domain.

Mandatory domain-style sampling before refinement:
- `pointwiseSupremumOn` and `activePointwiseSupremumOnIndices`, the chapter owners for a support
  envelope and its active-index set;
- `activeSupportFunctionMultipliers` and `weightedGradientCombination` in `Lemma_3_1_16`, the
  canonical source-facing active-face / gradient bridge for the support-function composition;
- `subdifferential_supportFunction_comp_vectorMap_eq_convexHull_image_activeMultipliers_of_bounded`
  in `Lemma_3_16`, the chapter owner bridge from bounded weight sets to the convex-hull surface.

Best owner abstraction:
- `subdifferential_supportFunction_comp_vectorMap_eq_convexHull_image_activeMultipliers_of_bounded`.

Primitive data:
- a nonempty compact convex nonnegative weight set `Λ`;
- a convex coordinate family `fs`;
- the evaluation point `x`.

Derived API:
- the support-function composition `x ↦ ξ[Λ] (vectorMap fs x)`;
- the active-multiplier owner `activeSupportFunctionMultipliers Λ fs x`;
- the weighted-gradient map `weightedGradientCombination fs x`;
- the bounded owner bridge over `closure Λ`, specialized below using compactness.

Source/core/bridge triage:
- source-facing: Proposition 3.25's compact-set convex-hull formula for the support-function
  subdifferential;
- core/canonical: `supportFunction`, `pointwiseSupremumOn`, `weightedGradientCombination`, and
  `subdifferential`;
- bridge/view: the passage from the bounded owner bridge over `closure Λ` back to the compact
  source set `Λ`.

The previous file introduced unsupported proposition-local names `partialProtoDerivativeOfF`,
`indexSet`, and `partialProtoDerivativeOfPsi`, then proved the target equality by assuming it.
This refinement instead states Proposition 3.25 directly on the support-function composition from
`Lemma_3_16`: compactness supplies the boundedness needed by the owner bridge, and `closure Λ = Λ`
for compact `Λ` removes the closure from the public statement. The proposition keeps the
source-facing convexity data needed by the bounded owner bridge instead of relying on an
under-specified compact specialization.
-/

section

universe u

variable {m : ℕ} {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Proposition 3.25: for a nonempty compact convex nonnegative weight set, the subdifferential
of the thin `WithTop` bridge of the support-function composition `x ↦ ξ[Λ] (vectorMap fs x)` at
`x` is the convex hull of the image of the active-multiplier face under
`weightedGradientCombination fs x`. This is the representation (3.1.80) at `x`. -/
-- Proof sketch: apply the bounded owner bridge from `Lemma_3_16` using
-- `hΛ_compact.isBounded`, then simplify the resulting closure active face with
-- `hΛ_compact.isClosed.closure_eq`.
theorem subdifferential_supportFunction_comp_vectorMap_eq_convexHull_image_activeMultipliers
    {Λ : Set (EuclideanSpace ℝ (Fin m))} {fs : Fin m → E → ℝ}
    (hΛ_nonempty : Λ.Nonempty) (hΛ_compact : IsCompact Λ)
    (hΛ_convex : Convex ℝ Λ) (hΛ_nonneg : Λ ⊆ ℝ₊^m)
    (hfs_convex : ∀ i, ConvexOn ℝ Set.univ (fs i))
    (x : E) (hfs_grad : ∀ i, HasGradientAt (fs i) (∇ (fs i) x) x) :
    ∂ (supportFunctionCompWithTop Λ fs)(x) =
      convexHull ℝ
        ((weightedGradientCombination fs x) '' activeSupportFunctionMultipliers Λ fs x) :=
  by
    have hsub :=
      subdifferential_supportFunction_comp_vectorMap_eq_convexHull_image_activeMultipliers_of_bounded
        hΛ_compact.isBounded hΛ_nonempty hΛ_nonneg hΛ_convex hfs_convex x hfs_grad
    simpa [hΛ_compact.isClosed.closure_eq] using hsub

end

/-! ### Theorem_3_25 (from Chap03) -/
open scoped ConstrainedArgmin WithTopConvexAnalysis

universe u

/- Theorem 3.25 is a `bridge/view` recall in the chapter's extended-valued convex-analysis
minimizer/common-subdifferential domain.

Primary mathematical domain:
- effective-domain minimizers of `WithTop ℝ`-valued convex functions and their
  common-subdifferential optimality criterion.

Relevant owner-style declarations sampled before refinement:
- `IsMinOn` and `isMinOn_iff` in mathlib, the canonical minimizer predicate on a set;
- `constrainedArgmin` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the canonical
  minimizer-set owner on a feasible set;
- `commonRegularSubdifferential` and `mem_commonRegularSubdifferential_iff` in
  `Definition_3_1_5_4`, the chapter owner API for common subdifferentials;
- `subset_constrainedArgmin_effectiveDomain_iff_zero_mem_commonRegularSubdifferential` in
  `Theorem_3_1_20`, the upstream chapter theorem for this exact optimality statement.

Best owner abstraction:
- `argmin[dom f] f` together with
  `subset_constrainedArgmin_effectiveDomain_iff_zero_mem_commonRegularSubdifferential`.

Primitive data:
- an extended-valued function `f`;
- a set `XStar`.

Derived API:
- the minimizer-set owner `argmin[dom f] f`;
- its atomic membership theorem `mem_constrainedArgmin_iff`;
- the zero-common-subgradient optimality criterion.

Source/core/bridge triage:
- source-facing: the textbook criterion identifying sets of global minimizers by the common
  regular subdifferential;
- core/canonical: `argmin[dom f] f` together with the theorem in `Theorem_3_1_20`;
- bridge/view: this numbered recall surface.

The previous file duplicated a local owner `globalMinimizers` for the canonical minimizer set
`argmin[dom f] f`, together with a parallel membership theorem. The chapter theorem in
`Theorem_3_1_20` now lives directly on the canonical owner surface, so this file reuses that
surface instead of preserving the redundant wrapper vocabulary. -/

section MinimizersRecall

variable {X : Type u} (f : X → WithTop ℝ) (x : X)

/- The set `arg min_{x ∈ dom f} f(x)` is the canonical owner `argmin[dom f] f`. -/
set_option linter.hashCommand false in
#check (argmin[dom f] f : Set X)

/- Membership in `argmin[dom f] f` is exactly effective-domain membership together
with minimizing on that domain. -/
set_option linter.hashCommand false in
#check (show x ∈ argmin[dom f] f ↔ x ∈ dom f ∧ IsMinOn f (dom f) x from
  mem_constrainedArgmin_iff)

end MinimizersRecall

section CommonSubdifferentialRecall

variable {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/- Theorem 3.25: a set is contained in `arg min_{x ∈ dom f} f(x)` if and only if the zero vector
lies in the common regular subdifferential on that set. -/
recall subset_constrainedArgmin_effectiveDomain_iff_zero_mem_commonRegularSubdifferential
    {f : V → WithTop ℝ} {XStar : Set V} :
    XStar ⊆ argmin[dom f] f ↔ (0 : V) ∈ ∂̂ f(XStar)

end CommonSubdifferentialRecall
