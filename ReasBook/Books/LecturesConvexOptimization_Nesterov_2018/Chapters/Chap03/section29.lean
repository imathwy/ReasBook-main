import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_29 (from Chap03) -/
section

universe u v

open scoped WithTopConvexAnalysis

variable {E : Type u} {U : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [TopologicalSpace U] [AddCommMonoid U] [Module ℝ U]

/- Definition 3.29 lies in the convex-analysis max-representation oracle domain.

Primary domain:
- pointwise-max representations of convex objectives and oracle access to active slices.

Sampled owner-style declarations:
- `MaxRepresentationPrimalDualProblem`
- `MaxRepresentationPrimalDualProblem.objective_eq_kernel_of_isMaxOn`
- `subdifferentialWithin`
- `IsMaxOn`

Best owner abstraction:
- `MaxRepresentationPrimalDualProblem E U`, which already owns the primal feasible set, parameter
  set, objective, and kernel;
- `IsMaxOn` for maximizer optimality on the parameter set;
- the generic `subdifferentialWithin` owner from `Theorem_3_44` for relative slice subgradients.

Source/core/bridge triage:
- `source-facing`: the combined oracle of Definition 3.29;
- `core/canonical`: the owner problem `MaxRepresentationPrimalDualProblem E U` together with the
  owner notions `IsMaxOn` and `subdifferentialWithin`;
- `bridge/view`: the owner theorems
  `MaxRepresentationPrimalDualProblem.objective_eq_kernel_of_isMaxOn` and
  `MaxRepresentationPrimalDualProblem.subgradient_mem_subdifferentialWithin_of_isMaxOn`, which
  turn maximizer optimality and active-slice relative subgradients into represented-objective
  statements.

Primitive data:
- `answer : problem.feasibleSet → problem.dualSet × E`

Derived API:
- the selected maximizer `u(x)` and slice subgradient `g(x)` obtained by projecting `answer x`
- value attainment in the owner objective `problem.objective`
- maximizer optimality via `IsMaxOn`
- the owner bridge
  `MaxRepresentationPrimalDualProblem.subgradient_mem_subdifferentialWithin_of_isMaxOn`
  from active-slice relative subgradients to represented-objective relative subgradients
- relative subgradient membership via `subdifferentialWithin`

This file therefore keeps the source-facing oracle notion, but attaches it directly to the chapter
owner problem instead of repeating `P`, `S`, `f`, and `Ψ` as parallel parameters. -/

/-- Definition 3.29: for a max-representation problem, an oracle chooses at each feasible query
point `x ∈ P` a feasible maximizer `u(x) ∈ S` and a relative subgradient of the active slice
`Ψ(·, u(x))` at `x`. The equality `f(x) = Ψ(x, u(x))` is derived from maximizer optimality via
the owner problem. -/
structure MaxRepresentationOracle
    (problem : MaxRepresentationPrimalDualProblem E U) where
  /-- The oracle reply at the feasible query point `x`, consisting of the selected maximizer
  `u(x)` together with the selected relative subgradient `g(x)`. -/
  answer : problem.feasibleSet → problem.dualSet × E
  /-- At feasible query points, the selected `u(x)` maximizes `Ψ(x, ·)` over the parameter set. -/
  maximizer_spec :
    ∀ x : problem.feasibleSet,
      IsMaxOn (problem.kernel x) problem.dualSet (answer x).1
  /-- At feasible query points, the selected `g(x)` lies in the relative subdifferential of the
  active slice `Ψ(·, u(x))` over the primal set. -/
  subgradient_spec :
    ∀ x : problem.feasibleSet,
      (answer x).2 ∈
        ∂[problem.feasibleSet]
          (((fun y ↦ problem.kernel y ((answer x).1 : U)) : E → ℝ))
          ((x : E))

namespace MaxRepresentationOracle

variable {problem : MaxRepresentationPrimalDualProblem E U}
variable (oracle : MaxRepresentationOracle problem)

/-- The selected maximizer `u(x)` at the feasible query point `x`. -/
def maximizer (x : problem.feasibleSet) : problem.dualSet :=
  (oracle.answer x).1

/-- The selected relative subgradient `g(x)` at the feasible query point `x`. -/
def subgradient (x : problem.feasibleSet) : E :=
  (oracle.answer x).2

/-- The first component of the oracle reply is the selected maximizer. -/
@[simp] theorem answer_fst (x : problem.feasibleSet) :
    (oracle.answer x).1 = oracle.maximizer x :=
  rfl

/-- The second component of the oracle reply is the selected slice subgradient. -/
@[simp] theorem answer_snd (x : problem.feasibleSet) :
    (oracle.answer x).2 = oracle.subgradient x :=
  rfl

/-- At a feasible query point, the oracle's selected maximizer realizes the represented objective
value. -/
theorem objective_eq_kernel (x : problem.feasibleSet) :
    problem x = problem.kernel x (oracle.maximizer x) :=
  problem.objective_eq_kernel_of_isMaxOn
    x.2 (oracle.maximizer x) (oracle.maximizer_spec x)

/-- At a feasible query point, the oracle's selected slice subgradient is also a relative
subgradient of the represented objective over the primal feasible set. -/
theorem subgradient_mem_subdifferentialWithin (x : problem.feasibleSet) :
    oracle.subgradient x ∈ ∂[problem.feasibleSet] problem ((x : E)) := by
  exact
    problem.subgradient_mem_subdifferentialWithin_of_isMaxOn
      x (oracle.maximizer x) (oracle.maximizer_spec x) (oracle.subgradient_spec x)

end MaxRepresentationOracle

end

/-! ### Lemma_3_29 (from Chap03) -/
open scoped ConstrainedArgmin
open scoped NormalCone
open scoped WithTopConvexAnalysis

/- Lemma 3.29 lies in the chapter's constrained convex minimization / common-certificate domain.

Mandatory domain-style sampling before refinement:
- `argmin[Q] f` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the canonical owner
  for constrained minimizers;
- `commonRegularSubdifferential` and `mem_commonRegularSubdifferential_iff` in
  `Definition_3_1_5_4`, the chapter owner for common subdifferentials;
- `normalCone` and `mem_normalCone_iff` in `Definition_3_22`, the pointwise normal-cone owner;
- `subgradient_mem_commonRegularSubdifferential_commonNormalCone_of_mem_constrainedArgmin` in
  `Theorem_3_29`, the owner theorem already proving the propagated certificate statement.

Best owner abstraction:
- the constrained minimizer set `argmin[Q] f`;
- the common regular subdifferential `∂̂ f(X)`;
- the common normal cone `NormalCone.common X`.

Primitive data:
- a feasible set `Q`;
- a real-valued objective `f`;
- an optimal point `xStar`;
- a subgradient certificate `gStar`.

Derived API:
- the source-facing propagated pairing certificate on `argmin[Q] f`;
- the owner-level common-normal-cone corollary.

Source/core/bridge triage:
- source-facing:
  `subgradient_mem_commonRegularSubdifferential_and_nonneg_pairing_of_mem_constrainedArgmin`;
- core/canonical:
  `subgradient_mem_commonRegularSubdifferential_commonNormalCone_of_mem_constrainedArgmin`;
- bridge/view:
  `NormalCone.mem_common_iff_nonneg_pairing` from `Theorem_3_29`.

The previous file imported the nonexistent module `Theorem_3_2_4` and wandered into the
approximate-Lagrange-multiplier domain. The actual Chapter 3 owner declarations already live in
`Theorem_3_29`, so this file is recall-only and reuses that canonical surface directly instead of
keeping a parallel local statement. -/

/- Lemma 3.29, pairing form: the propagated certificate belongs to the common regular
subdifferential and satisfies the normal-cone pairing inequalities on the whole constrained
minimizer set. -/
recall subgradient_mem_commonRegularSubdifferential_and_nonneg_pairing_of_mem_constrainedArgmin

/- Owner-level corollary: the same propagated certificate belongs to the common normal cone of the
constrained minimizer set. -/
recall subgradient_mem_commonRegularSubdifferential_commonNormalCone_of_mem_constrainedArgmin

/-! ### Proposition_3_29 (from Chap03) -/
noncomputable section

open scoped WithTopConvexAnalysis

universe u

/- Proposition 3.29 lies in the chapter's local subgradient-growth / Lipschitz-regularity domain.

Mandatory domain-style sampling before refinement:
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter owners for the effective domain and
  finite-value representative of an `ℝ ∪ {+∞}`-valued function;
- `IsSubgradientAt`, `subdifferential`, and `mem_subdifferential_iff` in `Definition_3_1_5`, the
  chapter owner surface for extended-valued subgradients and the textbook notation `∂ f(x)`;
- `LipschitzOnWith.of_le_add_mul`, the canonical mathlib bridge from one-sided difference bounds
  to a Lipschitz estimate on a set;
- nearby owner usage in `Theorem_3_1_11` and `Theorem_3_1_15`, which already organize local
  convex regularity around `dom f`, `withTopRealPart f`, and `∂ f(x)`.

Best owner abstraction:
- source-facing: the local ball estimate and Lipschitz consequence below;
- core/canonical: `dom f`, `∂ f(x)`, and `withTopRealPart f`;
- bridge/view: `LipschitzOnWith.of_le_add_mul`.

Primitive data:
- a ball `Metric.ball xStar ρ`;
- the domain-containment hypothesis on that ball;
- the subgradient-growth bound on that ball.

Derived API:
- the one-sided difference estimate for `withTopRealPart f`;
- the resulting Lipschitz estimate on the same ball.

The previous file rebuilt local copies of the effective domain, subgradient predicate, and
subdifferential, even though those notions are already owned upstream in `Definition_3_1_5`.
This refinement keeps Proposition 3.29 on the same mathematical content, but deletes that
duplicate wrapper layer and states the result directly on the chapter owner surface.
-/

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Proposition 3.29: if every point of the ball `Metric.ball xStar ρ` lies in the effective
domain of `f` and every subgradient on that ball satisfies `‖g‖ ≤ μ * ‖y‖ + γ`, then for
`x, y ∈ Metric.ball xStar ρ` and any `g ∈ ∂ f(y)` one has the local estimate
`withTopRealPart f y - withTopRealPart f x ≤ (μ * ‖xStar‖ + μ * ρ + γ) * ‖y - x‖`. -/
-- Proof sketch: apply the subgradient inequality at `y` with comparison point `x`. Then bound
-- `⟪g, y - x⟫` by Cauchy-Schwarz, use the assumed estimate on `‖g‖`, and control `‖y‖` by
-- `‖xStar‖ + ρ` via the triangle inequality because `y ∈ Metric.ball xStar ρ`.
theorem subgradient_upper_difference_bound_on_ball
    {f : E → WithTop ℝ} {xStar x y g : E} {ρ μ γ : ℝ}
    (hμ : 0 ≤ μ)
    (hball_dom : Metric.ball xStar ρ ⊆ dom f)
    (hsubgrad_bound :
      ∀ ⦃z s : E⦄, z ∈ Metric.ball xStar ρ → s ∈ ∂ f(z) → ‖s‖ ≤ μ * ‖z‖ + γ)
    (hx : x ∈ Metric.ball xStar ρ) (hy : y ∈ Metric.ball xStar ρ)
    (hg : g ∈ ∂ f(y)) :
    withTopRealPart f y - withTopRealPart f x ≤
      (μ * ‖xStar‖ + μ * ρ + γ) * ‖y - x‖ := by
  have hx_dom : x ∈ dom f := hball_dom hx
  have hy_dom : y ∈ dom f := hball_dom hy
  have hsupport : f y + (inner ℝ g (x - y) : WithTop ℝ) ≤ f x := by
    exact (mem_subdifferential_iff.mp hg).2 hx_dom
  have hsupport_real : withTopRealPart f y + inner ℝ g (x - y) ≤ withTopRealPart f x := by
    rw [← coe_withTopRealPart hy_dom, ← coe_withTopRealPart hx_dom] at hsupport
    exact_mod_cast hsupport
  have hsubgrad_norm : ‖g‖ ≤ μ * ‖y‖ + γ := hsubgrad_bound hy hg
  have hy_ball : ‖y - xStar‖ < ρ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hy
  have hy_norm : ‖y‖ ≤ ‖xStar‖ + ρ := by
    calc
      ‖y‖ = ‖(y - xStar) + xStar‖ := by abel_nf
      _ ≤ ‖y - xStar‖ + ‖xStar‖ := norm_add_le _ _
      _ = ‖xStar‖ + ‖y - xStar‖ := by ring
      _ ≤ ‖xStar‖ + ρ := by gcongr
  calc
    withTopRealPart f y - withTopRealPart f x ≤ inner ℝ g (y - x) := by
      have hinner : inner ℝ g (x - y) = -inner ℝ g (y - x) := by
        simp [inner_sub_right]
      linarith
    _ ≤ ‖g‖ * ‖y - x‖ := real_inner_le_norm _ _
    _ ≤ (μ * ‖y‖ + γ) * ‖y - x‖ := by
      gcongr
    _ ≤ (μ * ‖xStar‖ + μ * ρ + γ) * ‖y - x‖ := by
      have hbound : μ * ‖y‖ + γ ≤ μ * ‖xStar‖ + μ * ρ + γ := by
        have hmul : μ * ‖y‖ ≤ μ * (‖xStar‖ + ρ) := by gcongr
        linarith
      gcongr

/-- If every point of `Metric.ball xStar ρ` has a subgradient and all such subgradients satisfy
the same affine norm bound, then the finite-value representative `withTopRealPart f` is Lipschitz
on that ball. -/
-- Proof sketch: for each `y` in the ball choose some `g ∈ ∂ f(y)` using the nonemptiness
-- assumption, apply `subgradient_upper_difference_bound_on_ball` to get the one-sided estimate,
-- and conclude with `LipschitzOnWith.of_le_add_mul`.
theorem lipschitzOnWith_on_ball_of_subgradient_bound
    {f : E → WithTop ℝ} {xStar : E} {ρ μ γ : ℝ}
    (hμ : 0 ≤ μ)
    (hsubgrad_nonempty :
      ∀ y ∈ Metric.ball xStar ρ, (∂ f(y)).Nonempty)
    (hsubgrad_bound :
      ∀ ⦃y g : E⦄, y ∈ Metric.ball xStar ρ → g ∈ ∂ f(y) → ‖g‖ ≤ μ * ‖y‖ + γ) :
    LipschitzOnWith (Real.toNNReal (μ * ‖xStar‖ + μ * ρ + γ))
      (withTopRealPart f) (Metric.ball xStar ρ) := by
  have hball_dom : Metric.ball xStar ρ ⊆ dom f := by
    intro y hy
    rcases hsubgrad_nonempty y hy with ⟨g, hg⟩
    exact (mem_subdifferential_iff.mp hg).mem_dom
  refine LipschitzOnWith.of_le_add_mul' (μ * ‖xStar‖ + μ * ρ + γ) ?_
  intro x hx y hy
  rcases hsubgrad_nonempty x hx with ⟨g, hg⟩
  simpa [dist_eq_norm, add_comm, add_left_comm, add_assoc] using
    subgradient_upper_difference_bound_on_ball hμ hball_dom hsubgrad_bound hy hx hg

end

/-! ### Theorem_3_29 (from Chap03) -/
noncomputable section

open scoped ConstrainedArgmin
open scoped NormalCone
open scoped WithTopConvexAnalysis

universe u

/- Theorem 3.29 lies in the chapter's constrained convex minimization / common-certificate domain.

Mandatory domain-style sampling before drafting:
- `argmin[Q] f` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the canonical owner
  for constrained minimizers;
- `mem_constrainedArgmin_iff_exists_subgradient_nonneg_pairing` in `Theorem_3_1_24`, the exact
  earlier optimality criterion reused here;
- `normalCone` and `mem_normalCone_iff` in `Definition_3_22`, the pointwise normal-cone owner;
- `commonRegularSubdifferential` and `mem_commonRegularSubdifferential_iff` in
  `Definition_3_1_5_4`, the owner for common subdifferentials.

Best owner abstraction:
- the constrained minimizer set `argmin[Q] f`;
- the pointwise normal cone `N[Q] x`;
- the common regular subdifferential `∂̂ f(X)`.

Primitive data:
- a feasible set `Q`;
- a real-valued objective `f`;
- an optimal point `xStar`;
- a subgradient certificate `gStar`.

Derived API introduced here:
- the normal-cone owner bridge `NormalCone.common X` and its membership / pairing expansions;
- the propagated common-certificate theorem in source-facing pairing form;
- the owner-level common-normal-cone corollary.

Source/core/bridge triage:
- source-facing: Theorem 3.29's optimality criterion together with the propagated certificate on
  the whole optimal set;
- core/canonical: `argmin[Q] f`, `mem_constrainedArgmin_iff_exists_subgradient_nonneg_pairing`,
  `normalCone`, and `commonRegularSubdifferential`;
- bridge/view: the common-normal-cone owner `NormalCone.common`, defined as the intersection of
  the pointwise normal cones and paired with its inequality-form expansion.
-/

section OptimalityCriterionRecall

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/- Helper for Theorem 3.29 [Chapter3_2.json:34]: recall the earlier constrained-optimality
criterion stating that a feasible point `xStar ∈ Q` belongs to `argmin[Q] f` if and only if there
exists a subgradient `gStar ∈ ∂f(xStar)` with nonnegative pairing against every feasible
displacement. The propagated common-subdifferential / common-normal-cone consequence is stated in
the companion theorem below. -/
recall mem_constrainedArgmin_iff_exists_subgradient_nonneg_pairing
    [FiniteDimensional ℝ V]
    {Q : Set V} (hQ_convex : Convex ℝ Q)
    {f : V → ℝ} (hf_conv : ConvexOn ℝ Set.univ f)
    {xStar : V} (hxStar : xStar ∈ Q) :
    xStar ∈ argmin[Q] f ↔
      ∃ gStar : V,
        gStar ∈ ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar) ∧
          ∀ x ∈ Q, 0 ≤ inner ℝ gStar (x - xStar)

end OptimalityCriterionRecall

section CommonNormalConeOwner

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

namespace NormalCone

/-- Helper for Theorem 3.29 [Chapter3_2.json:34]: the common normal cone of `X` is the
intersection of the pointwise normal cones `N[X] x` over all `x ∈ X`. -/
def common (X : Set V) : Set V :=
  ⋂ x ∈ X, N[X] x

/-- Helper for Theorem 3.29 [Chapter3_2.json:34]: membership in the common normal cone means
belonging to the normal cone of `X` at every point of `X`. -/
-- Proof sketch: unfold `NormalCone.common`; membership in the iterated intersection is exactly the
-- universal pointwise normal-cone condition.
@[simp] theorem mem_common_iff
    {X : Set V} {g : V} :
    g ∈ common X ↔ ∀ x ∈ X, g ∈ N[X] x := by
  simp [common]

/-- Helper for Theorem 3.29 [Chapter3_2.json:34]: the common normal-cone owner can be read
entirely through the textbook pairing inequalities at every pair of points of `X`. -/
theorem mem_common_iff_nonneg_pairing
    {X : Set V} {g : V} :
    g ∈ common X ↔ ∀ x ∈ X, ∀ y ∈ X, 0 ≤ inner ℝ g (y - x) := by
  rw [mem_common_iff]
  constructor
  · intro hg x hx y hy
    exact (mem_normalCone_iff.mp (hg x hx)) y hy
  · intro hg x hx
    rw [mem_normalCone_iff]
    intro y hy
    exact hg x hx y hy

end NormalCone

end CommonNormalConeOwner

section CommonCertificatePairing

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

section

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] in
/-- Helper for Theorem 3.29 [Chapter3_2.json:34]: all constrained minimizers have the same
objective value. -/
theorem value_eq_of_mem_argmin
    {Q : Set V} {f : V → ℝ} {xStar x : V}
    (hxStar : xStar ∈ argmin[Q] f)
    (hx : x ∈ argmin[Q] f) :
    f x = f xStar := by
  -- Compare the two minimizers against each other using the owner expansion of `argmin`.
  rcases mem_constrainedArgmin_iff.mp hxStar with ⟨hxStar_mem_Q, hxStar_min⟩
  rcases mem_constrainedArgmin_iff.mp hx with ⟨hx_mem_Q, hx_min⟩
  exact le_antisymm (hx_min hxStar_mem_Q) (hxStar_min hx_mem_Q)

end

section DisplacementAlgebra

variable {V : Type u} [NormedAddCommGroup V]

/-- Helper for Theorem 3.29 [Chapter3_2.json:34]: split the displacement from `xStar` to `y`
through an intermediate point `x`. -/
private theorem displacement_split
    (y x xStar : V) :
    y - xStar = (y - x) + (x - xStar) := by
  abel

/-- Helper for Theorem 3.29 [Chapter3_2.json:34]: the displacement from `x` to `y` is the
difference of their displacements from `xStar`. -/
private theorem displacement_difference
    (y x xStar : V) :
    y - x = (y - xStar) - (x - xStar) := by
  abel

end DisplacementAlgebra

/-- Helper for Theorem 3.29 [Chapter3_2.json:34]: the certificate pairing is tight at every
constrained minimizer. -/
theorem pairing_eq_zero_of_mem_argmin
    {Q : Set V} {f : V → ℝ} {xStar gStar x : V}
    (hxStar : xStar ∈ argmin[Q] f)
    (hgStar_sub : gStar ∈ ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar))
    (hgStar_nonneg : ∀ y ∈ Q, 0 ≤ inner ℝ gStar (y - xStar))
    (hx : x ∈ argmin[Q] f) :
    inner ℝ gStar (x - xStar) = 0 := by
  rcases mem_constrainedArgmin_iff.mp hx with ⟨hx_mem_Q, hx_min⟩
  have hvalue : f x = f xStar := value_eq_of_mem_argmin hxStar hx
  have hsubgrad := mem_subdifferential_coe_real_iff.mp hgStar_sub
  have hnonneg : 0 ≤ inner ℝ gStar (x - xStar) := hgStar_nonneg x hx_mem_Q
  -- Sandwich the pairing between the subgradient lower bound and optimality equality.
  have hsupport : f x ≥ f xStar + inner ℝ gStar (x - xStar) := hsubgrad x
  have hx_le : f x ≤ f xStar := hx_min (mem_constrainedArgmin_iff.mp hxStar).1
  linarith

/-- Helper for Theorem 3.29 [Chapter3_2.json:34]: a subgradient certificate at one constrained
minimizer propagates to the whole minimizer set and satisfies the pairwise normal-cone inequalities
there. -/
-- Proof sketch: if `x ∈ argmin[Q] f`, then both `x` and `xStar` minimize `f` on `Q`, so the
-- subgradient inequality at `xStar` together with the nonnegative-pairing condition forces
-- `inner ℝ gStar (x - xStar) = 0`. This identity propagates the subgradient inequality from
-- `xStar` to every minimizer `x`, and the same vanishing pairing gives normal-cone membership at
-- every point of `argmin[Q] f`.
theorem
    subgradient_mem_commonRegularSubdifferential_and_nonneg_pairing_of_mem_constrainedArgmin
    {Q : Set V} {f : V → ℝ} {xStar gStar : V}
    (hxStar : xStar ∈ argmin[Q] f)
    (hgStar_sub : gStar ∈ ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar))
    (hgStar_nonneg : ∀ x ∈ Q, 0 ≤ inner ℝ gStar (x - xStar)) :
    gStar ∈
      ∂̂ (fun x : V ↦ (f x : WithTop ℝ))((argmin[Q] f)) ∧
        ∀ x ∈ argmin[Q] f, ∀ y ∈ argmin[Q] f, 0 ≤ inner ℝ gStar (y - x) := by
  have hgStar_sub' := mem_subdifferential_coe_real_iff.mp hgStar_sub
  refine ⟨?_, ?_⟩
  · rw [mem_commonRegularSubdifferential_iff]
    intro x hx
    rw [mem_subdifferential_coe_real_iff]
    have hx_value : f x = f xStar := value_eq_of_mem_argmin hxStar hx
    have hx_pairing : inner ℝ gStar (x - xStar) = 0 :=
      pairing_eq_zero_of_mem_argmin hxStar hgStar_sub hgStar_nonneg hx
    -- Transport the affine support inequality from `xStar` to the minimizer `x`.
    intro y
    calc
      f y ≥ f xStar + inner ℝ gStar (y - xStar) := hgStar_sub' y
      _ = f x + inner ℝ gStar (y - x) := by
        rw [displacement_split y x xStar, inner_add_right, hx_pairing, ← hx_value]
        simp
  · intro x hx y hy
    have hx_pairing : inner ℝ gStar (x - xStar) = 0 :=
      pairing_eq_zero_of_mem_argmin hxStar hgStar_sub hgStar_nonneg hx
    have hy_pairing : inner ℝ gStar (y - xStar) = 0 :=
      pairing_eq_zero_of_mem_argmin hxStar hgStar_sub hgStar_nonneg hy
    -- Re-express the pairwise displacement through `xStar`; both terms vanish separately.
    have hxy : inner ℝ gStar (y - x) = 0 := by
      rw [displacement_difference y x xStar, sub_eq_add_neg, inner_add_right, inner_neg_right,
        hy_pairing, hx_pairing]
      simp
    simp [hxy]

end CommonCertificatePairing

section CommonCertificateOwner

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Consequence for Theorem 3.29 [Chapter3_2.json:34]: a subgradient certificate at one
constrained minimizer propagates to the whole optimal set as a common regular subgradient and a
common normal vector. -/
theorem
    subgradient_mem_commonRegularSubdifferential_commonNormalCone_of_mem_constrainedArgmin
    {Q : Set V} {f : V → ℝ} {xStar gStar : V}
    (hxStar : xStar ∈ argmin[Q] f)
    (hgStar_sub : gStar ∈ ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar))
    (hgStar_nonneg : ∀ x ∈ Q, 0 ≤ inner ℝ gStar (x - xStar)) :
    gStar ∈
      ∂̂ (fun x : V ↦ (f x : WithTop ℝ))((argmin[Q] f)) ∩
        NormalCone.common (argmin[Q] f) := by
  -- Reuse the pairing-form propagation theorem and then rewrite the normal-cone owner.
  rcases
      subgradient_mem_commonRegularSubdifferential_and_nonneg_pairing_of_mem_constrainedArgmin
        hxStar hgStar_sub hgStar_nonneg with
    ⟨hgStar_commonSub, hgStar_pairing⟩
  refine ⟨hgStar_commonSub, ?_⟩
  rw [NormalCone.mem_common_iff_nonneg_pairing]
  intro x hx y hy
  exact hgStar_pairing x hx y hy

/-- Theorem 3.29 [Chapter3_2.json:34]: a feasible point `xStar ∈ Q` belongs to the constrained
optimal set `argmin[Q] f` if and only if there exists a subgradient certificate with nonnegative
pairing on `Q`; every such certificate then belongs to the common regular subdifferential and the
common normal cone of the whole minimizer set. -/
theorem mem_constrainedArgmin_iff_exists_subgradient_nonneg_pairing_with_common_certificate
    [FiniteDimensional ℝ V]
    {Q : Set V} (hQ_convex : Convex ℝ Q)
    {f : V → ℝ} (hf_conv : ConvexOn ℝ Set.univ f)
    {xStar : V} (hxStar : xStar ∈ Q) :
    (xStar ∈ argmin[Q] f ↔
      ∃ gStar : V,
        gStar ∈ ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar) ∧
          ∀ x ∈ Q, 0 ≤ inner ℝ gStar (x - xStar)) ∧
      ∀ {gStar : V},
        gStar ∈ ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar) →
          (∀ x ∈ Q, 0 ≤ inner ℝ gStar (x - xStar)) →
            gStar ∈
              ∂̂ (fun x : V ↦ (f x : WithTop ℝ))((argmin[Q] f)) ∩
                NormalCone.common (argmin[Q] f) := by
  refine ⟨?_, ?_⟩
  · exact mem_constrainedArgmin_iff_exists_subgradient_nonneg_pairing hQ_convex hf_conv hxStar
  · intro gStar hgStar_sub hgStar_nonneg
    -- Recover minimizer membership from the recalled optimality criterion, then propagate the
    -- certificate to the whole minimizer set.
    have hxStar_argmin : xStar ∈ argmin[Q] f :=
      (mem_constrainedArgmin_iff_exists_subgradient_nonneg_pairing hQ_convex hf_conv hxStar).2
        ⟨gStar, hgStar_sub, hgStar_nonneg⟩
    exact
      subgradient_mem_commonRegularSubdifferential_commonNormalCone_of_mem_constrainedArgmin
        hxStar_argmin hgStar_sub hgStar_nonneg

end CommonCertificateOwner
