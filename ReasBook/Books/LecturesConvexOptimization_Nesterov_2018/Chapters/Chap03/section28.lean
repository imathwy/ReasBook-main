import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_28 (from Chap03) -/
noncomputable section

universe u v

open scoped WithTopConvexAnalysis

/- Definition 3.28 lies in the chapter's convex-concave max-representation domain.

Sampled owner-style declarations:
- `SetConstrainedMinimizationProblem`
- `SetConstrainedMinimizationProblem.optimalValue`
- `pointwiseSupremumOn`
- the lower-value function `u ↦ sInf ((fun x ↦ problem.kernel x u) '' problem.feasibleSet)`

Best owner abstraction:
- source-facing/core: `MaxRepresentationPrimalDualProblem E U`, extending the ambient owner
  `SetConstrainedMinimizationProblem E`
- bridge/view: the inherited owner projection together with
  `objective_eq_pointwiseSupremumOn`, `objective_closedConvex`,
  `objective_eq_kernel_of_isMaxOn`

Primitive data:
- the primal feasible set `P` and objective `f`, owned by
  `SetConstrainedMinimizationProblem E`
- the parameter set `S`
- convexity of the parameter set `S`
- the kernel `Ψ`
- closed-convexity of the primal slices `x ↦ Ψ(x, u)` on `P`
- closed-concavity of the dual slices `u ↦ Ψ(x, u)` on `S`, encoded as closed convexity of
  `u ↦ -Ψ(x, u)`
- the max-attainment representation `f(x) = max_{u ∈ S} Ψ(x, u)` recorded canonically by
  `IsGreatest ((fun u ↦ Ψ x u) '' S) (f x)`

Derived API:
- the inherited owner projection `toSetConstrainedMinimizationProblem`
- the induced convexity of `P`
- the induced nonemptiness of `S` from any feasible point, via `objective_isGreatest`
- the pointwise-supremum bridge for `f`
- the induced closed-convexity of `f`
- the Chapter 1 owner optimal value
  `problem.toSetConstrainedMinimizationProblem.optimalValue`
- the lower-value function
  `u ↦ sInf ((fun x ↦ problem.kernel x u) '' problem.feasibleSet)`

Source/core/bridge triage:
- source-facing: Definition 3.28's primal problem together with its max-representation by a
  convex-concave kernel
- core/canonical: the ambient primal owner plus the kernel-slice hypotheses
- bridge/view: the owner projection and the supremum bridge derived from that owner

This file therefore keeps the source `f` and `Ψ` primitive, but moves the public API away from a
supremum-only wrapper and routes optimal-value and lower-value access through the existing owner
declarations instead of adding parallel aliases. The dual-set convexity remains primitive, while
the primal-set convexity, owner bridges, and max-attainment consequences are kept derived. -/

/-- Definition 3.28, generalized from the textbook `ℝⁿ × ℝᵐ` setting: a convex optimization
problem with a max-representation consists of a convex primal owner on `E`, a convex parameter
set `S ⊆ U`, and a real-valued kernel `Ψ : E → U → ℝ` such that each primal slice
`x ↦ Ψ(x, u)` is closed and convex on `P`, each dual slice `u ↦ Ψ(x, u)` is closed and concave on
`S`, and for every `x ∈ P` the objective value `f(x)` is the maximum of `u ↦ Ψ(x, u)` over
`S`. The textbook `P ⊆ ℝⁿ`, `S ⊆ ℝᵐ` form is recovered by specializing `E` and `U` to Euclidean
spaces. -/
structure MaxRepresentationPrimalDualProblem
    (E : Type u) (U : Type v)
    [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    [TopologicalSpace U] [AddCommMonoid U] [Module ℝ U]
    extends SetConstrainedMinimizationProblem E where
  /-- The parameter set `S ⊆ U` indexing the max-representation. -/
  dualSet : Set U
  /-- The parameter set `S` is convex. -/
  dualSet_convex : Convex ℝ dualSet
  /-- The real-valued kernel `Ψ(x, u)`. -/
  kernel : E → U → ℝ
  /-- Each primal slice `x ↦ Ψ(x, u)` is closed and convex on `P`. -/
  kernel_primal_closedConvex {u : U} (_ : u ∈ dualSet) :
    ClosedConvexOn feasibleSet (fun x ↦ (kernel x u : WithTop ℝ))
  /-- Each dual slice `u ↦ Ψ(x, u)` is closed and concave on `S`, encoded by closed convexity of
  `u ↦ -Ψ(x, u)`. -/
  kernel_dual_closedConcave {x : E} (_ : x ∈ feasibleSet) :
    ClosedConvexOn dualSet (fun u ↦ (-kernel x u : WithTop ℝ))
  /-- On `P`, the objective value is the maximum of `u ↦ Ψ(x, u)` over `S`. -/
  objective_isGreatest {x : E} (_ : x ∈ feasibleSet) :
    IsGreatest (kernel x '' dualSet) (objective x)

namespace MaxRepresentationPrimalDualProblem

variable {E : Type u} {U : Type v}
variable [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
variable [TopologicalSpace U] [AddCommMonoid U] [Module ℝ U]

/-- A max-representation primal-dual problem can be used as its primal objective function. -/
instance : CoeFun (MaxRepresentationPrimalDualProblem E U) (fun _ ↦ E → ℝ) where
  coe problem := problem.toSetConstrainedMinimizationProblem

/-- Evaluating a max-representation primal-dual problem returns its primal objective value. -/
@[simp] theorem coe_apply (problem : MaxRepresentationPrimalDualProblem E U) (x : E) :
    problem x = problem.objective x :=
  rfl

/-- The primal feasible set is convex, derived from any primal slice when the feasible set is
nonempty and otherwise from `Convex ℝ ∅`. -/
theorem feasibleSet_convex
    (problem : MaxRepresentationPrimalDualProblem E U) :
    Convex ℝ problem.feasibleSet := by
  by_cases hfeasible : problem.feasibleSet.Nonempty
  · rcases hfeasible with ⟨x, hx⟩
    rcases (problem.objective_isGreatest hx).1 with ⟨u, hu, _⟩
    exact (problem.kernel_primal_closedConvex hu).convex
  · rw [Set.not_nonempty_iff_eq_empty] at hfeasible
    simpa [hfeasible] using (convex_empty : Convex ℝ (∅ : Set E))

/-- The parameter set `S` is nonempty because every feasible `x` realizes `f(x)` as
`Ψ(x, u)` for some `u ∈ S`. -/
theorem dualSet_nonempty
    (problem : MaxRepresentationPrimalDualProblem E U)
    {x : E} (hx : x ∈ problem.feasibleSet) :
    problem.dualSet.Nonempty := by
  rcases (problem.objective_isGreatest hx).1 with ⟨u, hu, _⟩
  exact ⟨u, hu⟩

/-- On the primal feasible set, the objective agrees with the corresponding pointwise supremum of
the kernel over `S`. This is the bridge from the source-facing max-attainment hypothesis to the
chapter owner `pointwiseSupremumOn`. -/
theorem objective_eq_pointwiseSupremumOn
    (problem : MaxRepresentationPrimalDualProblem E U)
    {x : E} (hx : x ∈ problem.feasibleSet) :
    (problem x : WithTop ℝ) =
      pointwiseSupremumOn problem.dualSet
        (fun x' u ↦ (problem.kernel x' u : WithTop ℝ)) x := by
  rw [pointwiseSupremumOn_apply]
  have hobjective :
      IsGreatest
        ((fun u ↦ (problem.kernel x u : WithTop ℝ)) '' problem.dualSet)
        (problem x : WithTop ℝ) := by
    refine ⟨?_, ?_⟩
    · rcases (problem.objective_isGreatest hx).1 with ⟨u, hu, hux⟩
      refine ⟨u, hu, ?_⟩
      exact congrArg (fun t : ℝ ↦ (t : WithTop ℝ)) hux
    · intro y hy
      rcases hy with ⟨u, hu, rfl⟩
      change ((problem.kernel x u : ℝ) : WithTop ℝ) ≤
        ((problem x : ℝ) : WithTop ℝ)
      exact_mod_cast (problem.objective_isGreatest hx).2 ⟨u, hu, rfl⟩
  exact hobjective.csSup_eq.symm

/-- The primal objective is closed and convex on `P`, derived from the primal-slice hypotheses via
the pointwise-supremum owner theorem. -/
theorem objective_closedConvex
    (problem : MaxRepresentationPrimalDualProblem E U) :
    ClosedConvexOn problem.feasibleSet (fun x ↦ (problem x : WithTop ℝ)) := by
  let Φ : E → U → WithTop ℝ := fun x u ↦ (problem.kernel x u : WithTop ℝ)
  by_cases hfeasible : problem.feasibleSet.Nonempty
  · rcases hfeasible with ⟨x₀, hx₀⟩
    have hsup :
        ClosedConvexOn
          (pointwiseSupremumOnEffectiveDomain problem.feasibleSet problem.dualSet Φ)
          (pointwiseSupremumOn problem.dualSet Φ) :=
      ClosedConvexOn.pointwise_sSup (problem.dualSet_nonempty hx₀) fun u hu ↦
        problem.kernel_primal_closedConvex hu
    have heffective :
        pointwiseSupremumOnEffectiveDomain problem.feasibleSet problem.dualSet Φ =
          problem.feasibleSet := by
      ext x
      rw [mem_pointwiseSupremumOnEffectiveDomain_iff]
      constructor
      · exact fun hx ↦ hx.1
      · intro hx
        refine ⟨hx, ?_⟩
        rw [mem_withTopEffectiveDomain_iff, ← problem.objective_eq_pointwiseSupremumOn hx]
        exact WithTop.coe_lt_top (problem x)
    have hepigraph :
        constrainedEpigraph problem.feasibleSet (fun x ↦ (problem x : WithTop ℝ)) =
          constrainedEpigraph
            (pointwiseSupremumOnEffectiveDomain problem.feasibleSet problem.dualSet Φ)
            (pointwiseSupremumOn problem.dualSet Φ) := by
      ext p
      rw [mem_constrainedEpigraph_iff, mem_constrainedEpigraph_iff]
      constructor
      · rintro ⟨hp, hp₂⟩
        refine ⟨by simpa [heffective] using hp, ?_⟩
        simpa [Φ, problem.objective_eq_pointwiseSupremumOn hp] using hp₂
      · rintro ⟨hp, hp₂⟩
        have hp' : p.1 ∈ problem.feasibleSet := by
          simpa [heffective] using hp
        refine ⟨hp', ?_⟩
        simpa [Φ, problem.objective_eq_pointwiseSupremumOn hp'] using hp₂
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact
        (show (((problem x : ℝ) : WithTop ℝ) < (⊤ : WithTop ℝ)) from
          WithTop.coe_lt_top (problem x))
    · simpa [hepigraph] using hsup.2.1
    · simpa [hepigraph] using hsup.2.2
  · have hfeasible_eq : problem.feasibleSet = ∅ :=
        by
          ext x
          constructor
          · intro hx
            exact False.elim <| hfeasible ⟨x, hx⟩
          · intro hx
            exact False.elim hx
    refine ⟨?_, ?_, ?_⟩
    · exact by
        simp [hfeasible_eq]
    · exact by
        simp [constrainedEpigraph, hfeasible_eq]
    · simpa [constrainedEpigraph, hfeasible_eq] using
        (convex_empty : Convex ℝ (∅ : Set (E × ℝ)))

/-- If a feasible parameter `u ∈ S` maximizes the slice `Ψ(x, ·)` over `S` at a feasible point
`x ∈ P`, then it realizes the represented objective value `f(x)`. -/
theorem objective_eq_kernel_of_isMaxOn
    (problem : MaxRepresentationPrimalDualProblem E U)
    {x : E} (hx : x ∈ problem.feasibleSet) (u : problem.dualSet)
    (hu : IsMaxOn (problem.kernel x) problem.dualSet u) :
    problem x = problem.kernel x u := by
  rw [isMaxOn_iff] at hu
  have hkernel : IsGreatest (problem.kernel x '' problem.dualSet) (problem.kernel x u) := by
    refine ⟨⟨u, u.2, rfl⟩, ?_⟩
    intro y hy
    rcases hy with ⟨v, hv, rfl⟩
    exact hu v hv
  exact (problem.objective_isGreatest hx).unique hkernel

/-
The relative-subgradient bridge needs the stronger inner-product-space owner used by
`subdifferentialWithin`, but the max-representation owner itself remains at the weaker
topological-module layer above.
-/
section SubgradientBridge

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- At a feasible point of a max-representation problem, any relative subgradient of an active
slice is also a relative subgradient of the represented objective over the primal feasible set,
written on the chapter's canonical relative-subdifferential surface `∂[Q] f(x)`. -/
theorem subgradient_mem_subdifferentialWithin_of_isMaxOn
    (problem : MaxRepresentationPrimalDualProblem E U) (x : problem.feasibleSet)
    (u : problem.dualSet)
    (hu : IsMaxOn (problem.kernel x) problem.dualSet u)
    {g : E}
    (hg :
      g ∈ ∂[problem.feasibleSet]
        (((fun y ↦ problem.kernel y (u : U)) : E → ℝ))
        ((x : E))) :
    g ∈ ∂[problem.feasibleSet] problem ((x : E)) := by
  rw [mem_subdifferentialWithin_iff] at hg ⊢
  refine ⟨x.2, ?_⟩
  intro y hy
  have hy_kernel :
      problem.kernel y u ≤ problem y :=
    (problem.objective_isGreatest hy).2 ⟨u, u.2, rfl⟩
  calc
    problem y
      ≥ problem.kernel y u := hy_kernel
    _ ≥ problem.kernel x u + inner ℝ g (y - x) := hg.2 hy
    _ = problem x + inner ℝ g (y - x) := by
      rw [problem.objective_eq_kernel_of_isMaxOn x.2 u hu]

/- The primal optimal value is the Chapter 1 owner
`problem.toSetConstrainedMinimizationProblem.optimalValue`, and the lower-value function
`u ↦ inf_{x ∈ P} Ψ(x, u)` is expressed directly as
`u ↦ sInf ((fun x ↦ problem.kernel x u) '' problem.feasibleSet)`.
No parallel aliases are kept here. -/

end SubgradientBridge

end MaxRepresentationPrimalDualProblem

end

/-! ### Lemma_3_28 (from Chap03) -/
/-
Lemma 3.28 lies in the Euclidean closed-ball / midpoint-bisection-box domain.

Sampled owner-style declarations:
- mathlib `Metric.closedBall`
- project `FeasibilityResistingOracleState.currentCenter`
- project `FeasibilityResistingOracleState.currentBox`
- project `FeasibilityResistingOracleState.closedBall_subset_currentBox`

Best owner abstraction:
- the earlier chapter owner theorem
  `FeasibilityResistingOracleState.closedBall_subset_currentBox`.

Primitive data:
- a radius parameter `R`
- the positive dimension witness `hn`
- the resisting-oracle transcript `state`

Derived API:
- the textbook-radius closed-ball inclusion in the current realized midpoint-bisection box.

Source/core/bridge triage:
- source-facing: the textbook-radius ball inclusion in the current realized box
- core/canonical: the midpoint-bisection box owner in `Algorithm_3_5`
- bridge/view: the earlier chapter theorem
  `FeasibilityResistingOracleState.closedBall_subset_currentBox`, which already expresses exactly
  this source-level consequence

This item is recall-only: `Lemma_3_28` duplicated the earlier chapter theorem exactly, so the file
keeps the canonical recall instead of a second parallel public theorem.
-/

recall FeasibilityResistingOracleState.closedBall_subset_currentBox

/-! ### Proposition_3_28 (from Chap03) -/
noncomputable section

open Set
open EuclideanSpace
open scoped Pointwise WithTopConvexAnalysis

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "e[" i "]" => EuclideanSpace.single i (1 : ℝ)

/- Proposition 3.28 lies in the chapter's Nemirovski hard-instance / finite active-subdifferential
domain.

Mandatory domain-style sampling before refinement:
- `f_k`, `FirstKIndex`, `firstKCoordinateFamily`, and `first_k_coordinate_max` in
  `Definition_3_35`, the source-facing hard-instance owner and its restricted-coordinate bridge;
- `activePointwiseSupremumOnIndices` in `Lemma_3_1_14`, the chapter owner for active indices of a
  pointwise supremum;
- `subdifferential_coordinatewiseMaximum_eq_convexHull_activeBasis` in `Proposition_3_15`, the
  coordinate-maximum specialization showing the active-basis convex-hull pattern already lives on
  the chapter owner surface;
- `subdifferential_nonneg_weighted_add_eq_of_pos` in `Lemma_3_1_12`, the generic weighted-sum
  owner theorem behind the quadratic-plus-max decomposition.

Best owner abstraction:
- source-facing: Proposition 3.28 as the subdifferential formula for the hard-instance owner
  `f_k`;
- core/canonical: `subdifferential`, `activePointwiseSupremumOnIndices`, and the restricted
  coordinate family `firstKCoordinateFamily`;
- bridge/view: the active-basis embedding `i ↦ e[i.1]` and the affine image
  `v ↦ μ • x + γ • v`.

Primitive data:
- the prefix length `k` together with the source-facing assumptions `0 < k ≤ n`;
- the hard-instance parameters `μ`, `γ`;
- the query point `x : E`.

Derived API:
- the active-index set
  `activePointwiseSupremumOnIndices (Set.univ : Set (FirstKIndex n k))
    (firstKCoordinateFamily n k) x`;
- the affine-image description of `∂ f_k(x)` by the convex hull of the active standard basis
  vectors.

Source/core/bridge triage:
- source-facing: `subdifferential_f_k_eq_affineImage_convexHull_activeBasis`;
- core/canonical: `f_k`, `subdifferential`, `activePointwiseSupremumOnIndices`;
- bridge/view: the standard-basis map `i ↦ e[i.1]`.

This refinement keeps the source-facing theorem centered on the hard-instance owner `f_k`, reuses
the canonical active-supremum and weighted-sum subdifferential owners, and makes the scalar
parameters `μ` and `γ` explicit in the exported theorem header. The source-text regime
`0 < k ≤ n` remains part of the public statement, because the theorem is about the first `k`
coordinates of `ℝ^n`, not the generalized `min(k, n)` variant.
-/

section

variable (k : ℕ)

/-- Helper for Proposition 3.28: after coercing to `WithTop ℝ`, the hard-instance objective is the
canonical weighted sum of the quadratic term and the restricted-coordinate supremum. -/
lemma withTop_f_k_eq_weighted_sum
    [Nonempty (FirstKIndex n k)] (μ γ : ℝ) :
    (fun y : E ↦ (f_k n k μ γ y : WithTop ℝ)) =
      ((μ : WithTop ℝ) •
          (fun z : E ↦ (((1 / 2 : ℝ) * ‖z‖ ^ (2 : ℕ) : ℝ) : WithTop ℝ)) +
        (γ : WithTop ℝ) •
          pointwiseSupremumOn
            (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k)) := by
  -- Rewrite the source-facing definition `f_k` into the chapter owners used by the sum rule.
  funext y
  rw [f_k_def, div_eq_mul_inv, WithTop.coe_add]
  rw [show (((γ * first_k_coordinate_max n k y : ℝ) : WithTop ℝ)) =
      (γ : WithTop ℝ) * (((first_k_coordinate_max n k y : ℝ) : WithTop ℝ)) by simp]
  rw [coe_first_k_coordinate_max_eq_pointwiseSupremumOn_univ (n := n) (k := k) (x := y)]
  simp [Pi.smul_apply, mul_assoc]

/-- Helper for Proposition 3.28: the half squared norm is finite everywhere, so its effective
domain is all of `E`. -/
lemma half_norm_sq_dom_eq_univ :
    dom (fun y : E ↦ (((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : WithTop ℝ)) = Set.univ := by
  -- A coerced real number never equals `⊤`.
  ext y
  constructor
  · intro _
    simp
  · intro _
    change (((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : WithTop ℝ) < ⊤
    exact WithTop.coe_lt_top _

/-- Helper for Proposition 3.28: the half squared norm defines a closed convex function. -/
lemma half_norm_sq_closedConvexFunction :
    ClosedConvexFunction
      (fun y : E ↦ (((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : WithTop ℝ)) := by
  -- Package the standard convexity and continuity of `(1 / 2) ‖·‖²`.
  apply closedConvexFunction_coe_of_convexOn_continuous
  · simpa using
      ((convexOn_univ_norm : ConvexOn ℝ (Set.univ : Set E) norm).pow
        (fun _ _ ↦ norm_nonneg _) 2).smul (show 0 ≤ (1 / 2 : ℝ) by norm_num)
  · simpa using
      (continuous_const.mul
        (continuous_norm.pow 2 :
          Continuous fun y : E ↦ ‖y‖ ^ (2 : ℕ)))

/-- Helper for Proposition 3.28: the quadratic term `(1 / 2) ‖·‖²` has singleton
subdifferential `{x}`. -/
lemma subdifferential_half_norm_sq_eq_singleton
    (x : E) :
    ∂ (fun y : E ↦ (((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : WithTop ℝ))(x) = {x} := by
  let q : E → WithTop ℝ :=
    fun y ↦ (((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : WithTop ℝ)
  have hconv' :
      ConvexOn ℝ (Set.univ : Set E) (fun y : E ↦ (1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ)) := by
    -- The real-valued owner is convex on all of `E`.
    simpa using
      ((convexOn_univ_norm : ConvexOn ℝ (Set.univ : Set E) norm).pow
        (fun _ _ ↦ norm_nonneg _) 2).smul (show 0 ≤ (1 / 2 : ℝ) by norm_num)
  have hconv : ConvexOn ℝ (dom q) (withTopRealPart q) := by
    -- Convert the real-valued convexity statement to the chapter `WithTop` owner.
    rw [half_norm_sq_dom_eq_univ (n := n)]
    simpa [q, withTopRealPart] using hconv'
  have hx : x ∈ interior (dom q) := by
    -- The quadratic term is finite everywhere.
    rw [half_norm_sq_dom_eq_univ (n := n)]
    simp
  have hgrad : HasGradientAt (withTopRealPart q) x x := by
    -- Differentiate `‖·‖²` and scale by `1 / 2` to recover gradient `x`.
    simpa [q, withTopRealPart] using
      (show HasGradientAt (fun y : E ↦ (1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ)) x x by
        rw [hasGradientAt_iff_hasFDerivAt]
        convert (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_smul (1 / 2 : ℝ) using 1
        ext y
        simp [ContinuousLinearMap.smul_apply])
  exact subdifferential_eq_singleton_of_hasGradientAt hconv hx hgrad

/-- Helper for Proposition 3.28: every restricted coordinate slice is a closed convex function. -/
lemma firstKCoordinate_slice_closedConvexFunction
    (i : FirstKIndex n k) :
    ClosedConvexFunction (fun y : E ↦ firstKCoordinateFamily n k y i) := by
  -- The restricted coordinate slice is a continuous linear functional.
  apply closedConvexFunction_coe_of_convexOn_continuous
  · simpa [firstKCoordinateFamily] using (EuclideanSpace.projₗ i.1).convexOn convex_univ
  · simpa [firstKCoordinateFamily] using
      (EuclideanSpace.proj i.1 : E →L[ℝ] ℝ).continuous

/-- Helper for Proposition 3.28: each restricted coordinate slice has singleton subdifferential
equal to its standard basis vector. -/
lemma firstKCoordinate_slice_subdifferential_eq_singleton_basis
    (i : FirstKIndex n k) (x : E) :
    ∂ (fun y : E ↦ firstKCoordinateFamily n k y i)(x) = {e[i.1]} := by
  have hconv :
      ConvexOn ℝ (dom (fun y : E ↦ firstKCoordinateFamily n k y i))
        (withTopRealPart (fun y : E ↦ firstKCoordinateFamily n k y i)) := by
    -- Return to the real-valued coordinate projection to prove convexity.
    simpa [withTopEffectiveDomain, withTopRealPart, firstKCoordinateFamily] using
      (EuclideanSpace.projₗ i.1).convexOn convex_univ
  have hgrad :
      HasGradientAt
        (withTopRealPart (fun y : E ↦ firstKCoordinateFamily n k y i))
        (e[i.1]) x := by
    -- The derivative of the `i.1`-th coordinate is the dual of the corresponding basis vector.
    rw [hasGradientAt_iff_hasFDerivAt]
    have hderiv :
        HasFDerivAt (fun y : E ↦ y i.1) (EuclideanSpace.proj i.1 : E →L[ℝ] ℝ) x := by
      simpa using (EuclideanSpace.proj i.1 : E →L[ℝ] ℝ).hasFDerivAt
    have hdual :
        (EuclideanSpace.proj i.1 : E →L[ℝ] ℝ) =
          InnerProductSpace.toDual ℝ E (e[i.1]) := by
      ext y
      simpa using (EuclideanSpace.inner_single_left i.1 (1 : ℝ) y).symm
    simpa [withTopRealPart, firstKCoordinateFamily] using hderiv.congr_fderiv hdual
  have hx : x ∈ interior (dom (fun y : E ↦ firstKCoordinateFamily n k y i)) := by
    -- Every coordinate slice is finite everywhere.
    simp [withTopEffectiveDomain, firstKCoordinateFamily]
  exact subdifferential_eq_singleton_of_hasGradientAt hconv hx hgrad

/-- Helper for Proposition 3.28: the restricted `Set.univ` supremum is a closed convex function. -/
lemma firstKCoordinateSup_closedConvexFunction :
    ClosedConvexFunction
      (pointwiseSupremumOn
        (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k)) := by
  -- Apply the finite-family closed-convex supremum theorem to the restricted coordinate family.
  exact closedConvexFunction_pointwiseSupremumOn_univ
    (ι := FirstKIndex n k) (φ := firstKCoordinateFamily n k)
    (fun i ↦ firstKCoordinate_slice_closedConvexFunction (n := n) (k := k) i)

/-- Helper for Proposition 3.28: when `0 < k ≤ n`, the restricted-coordinate supremum is finite
everywhere, so its effective domain is all of `E`. -/
lemma firstKCoordinateSup_dom_eq_univ
    (hk : 0 < k) (hkn : k ≤ n) :
    dom
        (pointwiseSupremumOn
          (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k)) =
      Set.univ := by
  let _ : Nonempty (FirstKIndex n k) := firstKIndex_nonempty hk hkn
  -- Finite attainment for the restricted family shows the supremum is a coerced real number.
  ext y
  constructor
  · intro _
    simp
  · intro _
    change
      pointwiseSupremumOn
          (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k) y <
        ⊤
    simpa using pointwiseSupremumOn_univ_firstKCoordinateFamily_lt_top (n := n) (k := k) y

/-- Helper for Proposition 3.28: rewriting the active slice-subgradient union for the restricted
coordinate family replaces each slice by the corresponding basis vector. -/
lemma active_firstK_slice_subgradient_set_eq_activeBasisImage
    (x : E) :
    {g | ∃ i : FirstKIndex n k,
        i ∈ activePointwiseSupremumOnIndices
          (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k) x ∧
          g ∈ ∂ (fun y : E ↦ firstKCoordinateFamily n k y i)(x)} =
      ((fun i : FirstKIndex n k ↦ e[i.1]) ''
        activePointwiseSupremumOnIndices
          (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k) x) := by
  ext g
  constructor
  · rintro ⟨i, hi, hg⟩
    -- Each active slice contributes exactly the singleton `{e[i.1]}`.
    rw [firstKCoordinate_slice_subdifferential_eq_singleton_basis] at hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    -- Conversely, every active basis vector comes from its active coordinate slice.
    refine ⟨i, hi, ?_⟩
    rw [firstKCoordinate_slice_subdifferential_eq_singleton_basis]
    simp

/-- Helper for Proposition 3.28: when `0 < k ≤ n`, some prefix coordinate attains the restricted
supremum, so the active prefix index set is nonempty. -/
lemma active_prefix_indices_nonempty
    (hk : 0 < k) (hkn : k ≤ n) (x : E) :
    (activePointwiseSupremumOnIndices
      (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k) x).Nonempty := by
  let _ : Nonempty (FirstKIndex n k) := firstKIndex_nonempty hk hkn
  -- Pick an index attaining the finite supremum over the restricted coordinate family.
  obtain ⟨i, -, hsup⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (firstKCoordinateFamily n k x)
  refine ⟨i, ?_⟩
  rw [mem_activePointwiseSupremumOnIndices_univ_iff, pointwiseSupremumOn_univ_eq_sup']
  simpa using hsup.symm

/-- Helper for Proposition 3.28: the convex hull of the active restricted basis vectors is
nonempty whenever `0 < k ≤ n`. -/
lemma convexHull_activeBasis_nonempty
    (hk : 0 < k) (hkn : k ≤ n) (x : E) :
    (convexHull ℝ
      ((fun i : FirstKIndex n k ↦ e[i.1]) ''
        activePointwiseSupremumOnIndices
          (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k) x)).Nonempty := by
  -- Lift an active basis vector into the convex hull.
  rcases active_prefix_indices_nonempty (n := n) (k := k) hk hkn x with ⟨i, hi⟩
  refine ⟨e[i.1], subset_convexHull ℝ _ ?_⟩
  exact Set.mem_image_of_mem (fun j : FirstKIndex n k ↦ e[j.1]) hi

/-- Helper for Proposition 3.28: the subdifferential of the restricted-coordinate supremum is the
convex hull of its active basis vectors. -/
lemma subdifferential_firstKCoordinateSup_eq_convexHull_activeBasis
    (hk : 0 < k) (hkn : k ≤ n) (x : E) :
    ∂ (pointwiseSupremumOn
        (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k))(x) =
      convexHull ℝ
        ((fun i : FirstKIndex n k ↦ e[i.1]) ''
          activePointwiseSupremumOnIndices
            (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k) x) := by
  let _ : Nonempty (FirstKIndex n k) := firstKIndex_nonempty hk hkn
  have hx :
      x ∈ interior
        (dom (pointwiseSupremumOn
          (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k))) := by
    -- The restricted coordinate supremum is finite on every slice, hence on all of `E`.
    rw [interior_dom_pointwiseSupremumOn_univ
      (ι := FirstKIndex n k) (φ := firstKCoordinateFamily n k)]
    simp [withTopEffectiveDomain, firstKCoordinateFamily]
  have hmain :=
    subdifferential_pointwiseSupremumOn_univ_eq_convexHull_activeSubdifferentials
      (ι := FirstKIndex n k) (φ := firstKCoordinateFamily n k)
      (fun i ↦ firstKCoordinate_slice_closedConvexFunction (n := n) (k := k) i) hx
  -- Replace the abstract active slice-subgradient hull by the active basis-vector hull.
  rw [hmain, active_firstK_slice_subgradient_set_eq_activeBasisImage (n := n) (k := k) (x := x)]

/-- Helper for Proposition 3.28: adding a scaled singleton to a scaled set is the affine image of
that set. -/
lemma singleton_add_smul_eq_affineImage
    (μ γ : ℝ) (x : E) (A : Set E) :
    μ • ({x} : Set E) + γ • A =
      (fun v : E ↦ μ • x + γ • v) '' A := by
  -- Expand the Minkowski-sum membership condition and eliminate the singleton witness.
  ext z
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    rcases hv with ⟨w, hw, rfl⟩
    have hu' : u = μ • x := by
      simpa using hu
    subst hu'
    exact ⟨w, hw, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    refine ⟨μ • x, ?_, γ • v, ?_, by simp⟩
    · simp
    · show γ • v ∈ γ • A
      exact ⟨v, hv, rfl⟩

/-- Helper for Proposition 3.28: the zero `WithTop`-valued function is closed convex. -/
lemma zero_withTop_closedConvexFunction :
    ClosedConvexFunction (fun _ : E ↦ (0 : WithTop ℝ)) := by
  -- The zero function is the coercion of a continuous convex real-valued constant.
  simpa using
    (closedConvexFunction_coe_of_convexOn_continuous
      (f := fun _ : E ↦ (0 : ℝ))
      (convexOn_const (0 : ℝ) convex_univ) continuous_const)

/-- Helper for Proposition 3.28: the zero function has singleton subdifferential `{0}` at every
point. -/
lemma subdifferential_zero_eq_singleton_zero
    (x : E) :
    ∂ (fun _ : E ↦ (0 : WithTop ℝ))(x) = {(0 : E)} := by
  have hconv :
      ConvexOn ℝ (dom (fun _ : E ↦ (0 : WithTop ℝ)))
        (withTopRealPart (fun _ : E ↦ (0 : WithTop ℝ))) := by
    -- The zero function is convex on all of `E`.
    simpa [withTopEffectiveDomain, withTopRealPart] using
      (convexOn_const (0 : ℝ) convex_univ)
  have hx : x ∈ interior (dom (fun _ : E ↦ (0 : WithTop ℝ))) := by
    -- The zero function is finite everywhere.
    simp [withTopEffectiveDomain]
  have hgrad :
      HasGradientAt (withTopRealPart (fun _ : E ↦ (0 : WithTop ℝ))) (0 : E) x := by
    -- Its gradient is identically zero.
    simpa [withTopRealPart] using (hasGradientAt_const (c := (0 : ℝ)) (x := x))
  exact subdifferential_eq_singleton_of_hasGradientAt hconv hx hgrad

/-- Helper for Proposition 3.28: the image of a nonempty set under a constant map is the matching
singleton. -/
lemma constant_image_eq_singleton
    {A : Set E} (hA : A.Nonempty) (c : E) :
    (fun _ : E ↦ c) '' A = {c} := by
  -- One inclusion is immediate, and the reverse inclusion uses any witness from the nonempty set.
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp
  · intro hz
    rcases hA with ⟨y, hy⟩
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact ⟨y, hy, rfl⟩

/-- Proposition 3.28: for nonnegative parameters `μ` and `γ`, the subdifferential of
`f_k n k μ γ`, i.e. the Nemirovski hard instance
`x ↦ (μ / 2) ‖x‖² + γ max_{1 ≤ i ≤ k} xᵢ`, is the affine image of
the convex hull of the active standard basis vectors among the first `k` coordinates. -/
-- Proof sketch: split `f_k n k μ γ` into the differentiable quadratic term and the
-- coordinate-maximum term. The quadratic part contributes the singleton subgradient `μ • x`, while
-- the maximum term contributes the convex hull of the active basis vectors. In the strictly
-- positive case, apply the weighted-sum rule; the edge cases `μ = 0` and/or `γ = 0` reduce to the
-- corresponding single-summand formulas, yielding the same affine-image description.
theorem subdifferential_f_k_eq_affineImage_convexHull_activeBasis
    (μ γ : ℝ) (hk : 0 < k) (hkn : k ≤ n) (hμ : 0 ≤ μ) (hγ : 0 ≤ γ) (x : E) :
    ∂ (fun y : E ↦ (f_k n k μ γ y : WithTop ℝ))(x) =
      (fun v : E ↦ μ • x + γ • v) ''
        convexHull ℝ
          ((fun i : FirstKIndex n k ↦ e[i.1]) ''
            activePointwiseSupremumOnIndices
              (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k) x) := by
  let _ : Nonempty (FirstKIndex n k) := firstKIndex_nonempty hk hkn
  let A : Set E :=
    convexHull ℝ
      ((fun i : FirstKIndex n k ↦ e[i.1]) ''
        activePointwiseSupremumOnIndices
          (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k) x)
  have hA_nonempty : A.Nonempty := by
    -- The active restricted basis hull is nonempty because an active prefix index always exists.
    simpa [A] using convexHull_activeBasis_nonempty (n := n) (k := k) hk hkn x
  rcases eq_or_lt_of_le hμ with rfl | hμpos
  · rcases eq_or_lt_of_le hγ with rfl | hγpos
    · -- When both weights vanish, `f_k` is the zero function and the affine image is constant.
      have hzero :
          (fun y : E ↦ (f_k n k (0 : ℝ) (0 : ℝ) y : WithTop ℝ)) =
            fun _ : E ↦ (0 : WithTop ℝ) := by
        -- Unfold `f_k` and simplify both zero coefficients.
        funext y
        simp [f_k_def]
      rw [hzero, subdifferential_zero_eq_singleton_zero]
      calc
        ({(0 : E)} : Set E) = (fun _ : E ↦ (0 : E)) '' A := by
          simpa using (constant_image_eq_singleton (A := A) hA_nonempty (0 : E)).symm
        _ = (fun v : E ↦ (0 : ℝ) • x + (0 : ℝ) • v) '' A := by
          ext v
          simp
        _ = (fun v : E ↦ (0 : ℝ) • x + (0 : ℝ) • v) ''
              convexHull ℝ
                ((fun i : FirstKIndex n k ↦ e[i.1]) ''
                  activePointwiseSupremumOnIndices
                    (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k) x) := by
          simp [A]
    · -- When `μ = 0`, add the zero function with weight `1` to keep the weighted-sum owner form.
      have hzero_term :
          ((0 : WithTop ℝ) •
              (fun y : E ↦ (((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : WithTop ℝ))) =
            fun _ : E ↦ (0 : WithTop ℝ) := by
        -- The vanished quadratic term is the zero function.
        funext y
        simp [Pi.smul_apply]
      have hdom :
          interior
              (dom
                ((fun _ : E ↦ (0 : WithTop ℝ)) +
                  (γ : WithTop ℝ) •
                    pointwiseSupremumOn
                      (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k))) =
            interior (dom (fun _ : E ↦ (0 : WithTop ℝ))) ∩
              interior
                (dom
                  (pointwiseSupremumOn
                    (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k))) := by
        simpa using interior_effectiveDomain_nonneg_weighted_add_eq_of_pos
          (f₁ := fun _ : E ↦ (0 : WithTop ℝ))
          (f₂ := pointwiseSupremumOn
            (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k))
          zero_lt_one hγpos
      have hx :
          x ∈ interior
            (dom
              ((fun _ : E ↦ (0 : WithTop ℝ)) +
                (γ : WithTop ℝ) •
                  pointwiseSupremumOn
                    (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k))) := by
        -- Both summands are finite everywhere, so the common interior domain is all of `E`.
        rw [hdom]
        rw [firstKCoordinateSup_dom_eq_univ (n := n) (k := k) hk hkn]
        simp [withTopEffectiveDomain]
      have hx' :
          x ∈ interior
            (dom
              (((1 : WithTop ℝ) • (fun _ : E ↦ (0 : WithTop ℝ)) +
                (γ : WithTop ℝ) •
                  pointwiseSupremumOn
                    (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k)))) := by
        simpa using hx
      calc
        ∂ (fun y : E ↦ (f_k n k (0 : ℝ) γ y : WithTop ℝ))(x) =
            ∂ ((((0 : ℝ) : WithTop ℝ) •
                (fun y : E ↦ (((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : WithTop ℝ)) +
                (γ : WithTop ℝ) •
                  pointwiseSupremumOn
                    (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k)))(x) := by
          -- Replace `f_k` by the weighted sum with a trivial zero summand.
          rw [withTop_f_k_eq_weighted_sum (n := n) (k := k) (μ := 0) (γ := γ)]
        _ = ∂ ((fun _ : E ↦ (0 : WithTop ℝ)) +
                (γ : WithTop ℝ) •
                  pointwiseSupremumOn
                    (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k))(x) := by
          -- Collapse the vanished quadratic term to the zero function.
          have hcollapse :
              ∂ ((((0 : ℝ) : WithTop ℝ) •
                  (fun y : E ↦ (((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : WithTop ℝ)) +
                  (γ : WithTop ℝ) •
                    pointwiseSupremumOn
                      (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k)))(x) =
                ∂ ((fun _ : E ↦ (0 : WithTop ℝ)) +
                  (γ : WithTop ℝ) •
                    pointwiseSupremumOn
                      (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k))(x) := by
            congr 1
            funext y
            simp [Pi.smul_apply]
          exact hcollapse
        _ = (1 : ℝ) • ∂ (fun _ : E ↦ (0 : WithTop ℝ))(x) +
              γ • ∂ (pointwiseSupremumOn
                (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k))(x) := by
          -- Apply the positive-weight subdifferential sum rule.
          simpa using
            (subdifferential_nonneg_weighted_add_eq_of_pos
            (f₁ := fun _ : E ↦ (0 : WithTop ℝ))
            (f₂ := pointwiseSupremumOn
              (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k))
            zero_withTop_closedConvexFunction
            (firstKCoordinateSup_closedConvexFunction (n := n) (k := k))
            zero_lt_one hγpos hx')
        _ = (1 : ℝ) • ({(0 : E)} : Set E) + γ • A := by
          -- Substitute the component subdifferentials.
          rw [subdifferential_zero_eq_singleton_zero]
          rw [subdifferential_firstKCoordinateSup_eq_convexHull_activeBasis
            (n := n) (k := k) hk hkn x]
        _ = (fun v : E ↦ (1 : ℝ) • (0 : E) + γ • v) '' A := by
          -- Convert the Minkowski sum description to the affine-image form.
          rw [singleton_add_smul_eq_affineImage
            (μ := (1 : ℝ)) (γ := γ) (x := (0 : E)) (A := A)]
        _ = (fun v : E ↦ (0 : ℝ) • x + γ • v) '' A := by
          ext v
          simp
        _ = (fun v : E ↦ (0 : ℝ) • x + γ • v) ''
              convexHull ℝ
                ((fun i : FirstKIndex n k ↦ e[i.1]) ''
                  activePointwiseSupremumOnIndices
                    (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k) x) := by
          simp [A]
  · rcases eq_or_lt_of_le hγ with rfl | hγpos
    · -- When `γ = 0`, adjoin the zero function with coefficient `1` and collapse the constant image.
      have hzero_term :
          ((0 : WithTop ℝ) •
              pointwiseSupremumOn
                (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k)) =
            fun _ : E ↦ (0 : WithTop ℝ) := by
        -- The vanished maximum term is the zero function.
        funext y
        simp [Pi.smul_apply]
      have hdom :
          interior
              (dom
                (((μ : WithTop ℝ) •
                    (fun y : E ↦ (((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : WithTop ℝ)) +
                  (fun _ : E ↦ (0 : WithTop ℝ))))) =
            interior
              (dom
                (fun y : E ↦ (((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : WithTop ℝ))) ∩
              interior (dom (fun _ : E ↦ (0 : WithTop ℝ))) := by
        simpa using interior_effectiveDomain_nonneg_weighted_add_eq_of_pos
          (f₁ := fun y : E ↦ (((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : WithTop ℝ))
          (f₂ := fun _ : E ↦ (0 : WithTop ℝ))
          hμpos zero_lt_one
      have hx :
          x ∈ interior
            (dom
              (((μ : WithTop ℝ) •
                  (fun y : E ↦ (((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : WithTop ℝ)) +
                (fun _ : E ↦ (0 : WithTop ℝ))))) := by
        -- The weighted quadratic-plus-zero sum is finite everywhere.
        rw [hdom]
        rw [half_norm_sq_dom_eq_univ (n := n)]
        simp [withTopEffectiveDomain]
      have hx' :
          x ∈ interior
            (dom
              (((μ : WithTop ℝ) •
                  (fun y : E ↦ (((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : WithTop ℝ)) +
                (1 : WithTop ℝ) • (fun _ : E ↦ (0 : WithTop ℝ))))) := by
        simpa using hx
      calc
        ∂ (fun y : E ↦ (f_k n k μ (0 : ℝ) y : WithTop ℝ))(x) =
            ∂ (((μ : WithTop ℝ) •
                (fun y : E ↦ (((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : WithTop ℝ)) +
                (((0 : ℝ) : WithTop ℝ)) •
                  pointwiseSupremumOn
                    (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k)))(x) := by
          -- Rewrite `f_k` so that the zero maximum term becomes an explicit zero summand.
          rw [withTop_f_k_eq_weighted_sum (n := n) (k := k) (μ := μ) (γ := 0)]
        _ = ∂ (((μ : WithTop ℝ) •
                (fun y : E ↦ (((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : WithTop ℝ)) +
                (fun _ : E ↦ (0 : WithTop ℝ))))(x) := by
          -- Collapse the vanished maximum term to the zero function.
          have hcollapse :
              ∂ (((μ : WithTop ℝ) •
                  (fun y : E ↦ (((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : WithTop ℝ)) +
                  (((0 : ℝ) : WithTop ℝ)) •
                    pointwiseSupremumOn
                      (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k)))(x) =
                ∂ (((μ : WithTop ℝ) •
                    (fun y : E ↦ (((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : WithTop ℝ)) +
                  (fun _ : E ↦ (0 : WithTop ℝ))))(x) := by
            congr 1
            funext y
            simp [Pi.smul_apply]
          exact hcollapse
        _ = μ • ∂ (fun y : E ↦ (((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : WithTop ℝ))(x) +
              (1 : ℝ) • ∂ (fun _ : E ↦ (0 : WithTop ℝ))(x) := by
          -- Use the positive-weight sum rule with the zero function as the second summand.
          simpa using
            (subdifferential_nonneg_weighted_add_eq_of_pos
            (f₁ := fun y : E ↦ (((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : WithTop ℝ))
            (f₂ := fun _ : E ↦ (0 : WithTop ℝ))
            (half_norm_sq_closedConvexFunction (n := n))
            zero_withTop_closedConvexFunction
            hμpos zero_lt_one hx')
        _ = μ • ({x} : Set E) + (1 : ℝ) • ({(0 : E)} : Set E) := by
          -- Substitute the quadratic and zero-function subdifferentials.
          rw [subdifferential_half_norm_sq_eq_singleton (n := n)]
          rw [subdifferential_zero_eq_singleton_zero]
        _ = ({μ • x} : Set E) := by
          -- The zero-summand branch collapses to a singleton.
          rw [singleton_add_smul_eq_affineImage
            (μ := μ) (γ := (1 : ℝ)) (x := x) ({(0 : E)} : Set E)]
          simp
        _ = (fun v : E ↦ μ • x + (0 : ℝ) • v) '' A := by
          calc
            ({μ • x} : Set E) = (fun _ : E ↦ μ • x) '' A := by
              simpa using (constant_image_eq_singleton (A := A) hA_nonempty (μ • x)).symm
            _ = (fun v : E ↦ μ • x + (0 : ℝ) • v) '' A := by
              ext v
              simp
        _ = (fun v : E ↦ μ • x + (0 : ℝ) • v) ''
              convexHull ℝ
                ((fun i : FirstKIndex n k ↦ e[i.1]) ''
                  activePointwiseSupremumOnIndices
                    (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k) x) := by
          simp [A]
    · -- In the strictly positive case, the textbook weighted-sum decomposition applies directly.
      have hx :
          x ∈ interior
            (dom
              (((μ : WithTop ℝ) •
                  (fun y : E ↦ (((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : WithTop ℝ)) +
                (γ : WithTop ℝ) •
                  pointwiseSupremumOn
                    (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k)))) := by
        -- Both component functions have full domain, so the common interior domain is all of `E`.
        rw [interior_effectiveDomain_nonneg_weighted_add_eq_of_pos
          (f₁ := fun y : E ↦ (((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : WithTop ℝ))
          (f₂ := pointwiseSupremumOn
            (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k))
          hμpos hγpos]
        rw [half_norm_sq_dom_eq_univ (n := n)]
        rw [firstKCoordinateSup_dom_eq_univ (n := n) (k := k) hk hkn]
        simp
      calc
        ∂ (fun y : E ↦ (f_k n k μ γ y : WithTop ℝ))(x) =
            ∂ (((μ : WithTop ℝ) •
                (fun y : E ↦ (((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : WithTop ℝ)) +
                (γ : WithTop ℝ) •
                  pointwiseSupremumOn
                    (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k)))(x) := by
          -- Rewrite the source-facing hard instance into the canonical weighted sum.
          rw [withTop_f_k_eq_weighted_sum (n := n) (k := k) (μ := μ) (γ := γ)]
        _ = μ • ∂ (fun y : E ↦ (((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : WithTop ℝ))(x) +
              γ • ∂ (pointwiseSupremumOn
                (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k))(x) := by
          -- Apply the positive-weight subdifferential sum rule to the two canonical owners.
          simpa using
            (subdifferential_nonneg_weighted_add_eq_of_pos
            (f₁ := fun y : E ↦ (((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : WithTop ℝ))
            (f₂ := pointwiseSupremumOn
              (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k))
            (half_norm_sq_closedConvexFunction (n := n))
            (firstKCoordinateSup_closedConvexFunction (n := n) (k := k))
            hμpos hγpos hx)
        _ = μ • ({x} : Set E) + γ • A := by
          -- Replace the component subdifferentials by their explicit formulas.
          rw [subdifferential_half_norm_sq_eq_singleton (n := n)]
          rw [subdifferential_firstKCoordinateSup_eq_convexHull_activeBasis
            (n := n) (k := k) hk hkn x]
        _ = (fun v : E ↦ μ • x + γ • v) '' A := by
          -- Normalize the Minkowski sum to the affine image appearing in the statement.
          exact singleton_add_smul_eq_affineImage μ γ x A
        _ = (fun v : E ↦ μ • x + γ • v) ''
              convexHull ℝ
                ((fun i : FirstKIndex n k ↦ e[i.1]) ''
                  activePointwiseSupremumOnIndices
                    (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k) x) := by
          simp [A]

end

end

/-! ### Theorem_3_28 (from Chap03) -/
/- Theorem 3.28 lies in the chapter's convex composite minimization / first-order optimality
domain.

Sampled owner-style declarations:
- `ConvexOn.isMinOn_iff_variational_inequality_of_hasGradientAt` in `Chap02/Theorem_2_29`
- `ConvexOn.isMinOn_add_iff_neg_hasGradient_mem_constrainedSubdifferential`
  in `Chap03/Theorem_3_1_23`
- `ConvexOn.isMinOn_add_iff_variational_inequality_of_hasGradientAt`
  in `Chap03/Theorem_3_1_23`
- `isMinOn_add_convex_iff_forall_inner_gradient_add_ge` in `Chap03/Theorem_3_1_23`

Best owner abstraction:
- `ConvexOn.isMinOn_add_iff_neg_hasGradient_mem_constrainedSubdifferential`, the primitive
  gradient-witness owner theorem for convex composite minimization on a real inner-product space,
  phrased through the chapter's constrained-subdifferential owner.

Primitive data:
- `ConvexOn ℝ Q f`
- `ConvexOn ℝ Q Ψ`
- `xStar ∈ Q`
- `HasGradientAt f g xStar`

Derived API:
- the raw variational-inequality bridge
  `ConvexOn.isMinOn_add_iff_variational_inequality_of_hasGradientAt`
- the source-facing gradient specialization
  `isMinOn_add_convex_iff_forall_inner_gradient_add_ge`

Source/core/bridge triage:
- source-facing: Theorem 3.28's variational inequality for minimizing `x ↦ f x + Ψ x` on `Q`
- core/canonical: `ConvexOn.isMinOn_add_iff_neg_hasGradient_mem_constrainedSubdifferential`
- bridge/view: `ConvexOn.isMinOn_add_iff_variational_inequality_of_hasGradientAt` and
  `isMinOn_add_convex_iff_forall_inner_gradient_add_ge`

This file is recall-only. The earlier duplicate local theorem has already been removed, and the
upstream owner file now carries the right abstraction layer: general real inner-product spaces, no
redundant `Convex ℝ Q` binder, and only pointwise differentiability at `xStar` for the
gradient-based view. Accordingly, Theorem 3.28 recalls that source-facing corollary directly
rather than rebuilding a parallel local bridge. -/

recall isMinOn_add_convex_iff_forall_inner_gradient_add_ge
