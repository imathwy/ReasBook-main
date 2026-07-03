import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_21 (from Chap02) -/
open AffineMap

universe u

/- Primary domain: estimating sequences for real-valued objective functions.

Source/core/bridge triage for Definition 2.21:
* source-facing: `IsEstimatingSequence f φ lam`
* core/canonical: `Filter.Tendsto` for `λₖ → 0` and `AffineMap.lineMap` on the function space
  `X → ℝ` for the affine upper model between `f` and `φ₀`
* bridge/view: the pointwise textbook inequality `upper_bound_apply` and the gap consequences
  specialized from `Lemma_2_7`

Relevant declarations sampled before refining:
* `AffineMap.lineMap`
* `AffineMap.lineMap_apply_module`
* `estimatingSequence_gap_mem_Icc`
* `estimatingSequence_gap_tendsto_zero`

Owner abstraction:
* the chapter's source-facing owner is `IsEstimatingSequence`; its stagewise affine upper model is
  canonically expressed by `AffineMap.lineMap` rather than by repeating a raw function-space affine
  combination in every declaration. The source chapter applies it to functions on `ℝⁿ`, but the
  owner itself is purely pointwise and therefore lives on an arbitrary domain `X`.

Primitive data:
* the domain `X`
* the coefficient sequence `lam : ℕ → NNReal`
* the function sequence `φ`
* the asymptotic condition `lam ⟶ 0`
* the stagewise upper bound `φ k ≤ lineMap f (φ 0) (lam k : ℝ)`

Derived API:
* the projection lemmas `tendsto_zero` and `upper_bound`
* the source-facing pointwise bridge `upper_bound_apply`
* the gap corollaries `gap_mem_Icc` and `gap_tendsto_zero`
-/

/-- Definition 2.21: a pair of sequences `φₖ : X → ℝ` and `λₖ ∈ [0, ∞)` is an estimating
sequence for `f` when `λₖ → 0` and each model `φₖ` satisfies the upper estimate
`φₖ(x) ≤ (1 - λₖ) f(x) + λₖ φ₀(x)` for every `k` and every `x`. -/
def IsEstimatingSequence
    {X : Type u}
    (f : X → ℝ)
    (φ : ℕ → X → ℝ)
    (lam : ℕ → NNReal) : Prop :=
  Filter.Tendsto lam Filter.atTop (nhds 0) ∧
    ∀ k : ℕ,
      φ k ≤ lineMap f (φ 0) (lam k : ℝ)

namespace IsEstimatingSequence

variable {X : Type u} {f : X → ℝ} {φ : ℕ → X → ℝ} {lam : ℕ → NNReal}

section Core

/-- An estimating sequence has coefficient sequence converging to `0`. -/
theorem tendsto_zero (h : IsEstimatingSequence f φ lam) :
    Filter.Tendsto lam Filter.atTop (nhds 0) :=
  h.1

/-- An estimating sequence is bounded above by the canonical function-space line map from `f` to
`φ₀` at every index. -/
theorem upper_bound
    (h : IsEstimatingSequence f φ lam) (k : ℕ) :
    φ k ≤ lineMap f (φ 0) (lam k : ℝ) :=
  h.2 k

/-- Evaluating the function-space upper bound recovers the textbook pointwise inequality. -/
theorem upper_bound_apply
    (h : IsEstimatingSequence f φ lam) (k : ℕ) (x : X) :
    φ k x ≤ (1 - (lam k : ℝ)) * f x + (lam k : ℝ) * φ 0 x := by
  simpa [lineMap_apply_module] using h.upper_bound k x

end Core

section Gap

/-- An estimating sequence satisfying the Lemma 2.7 minimum-value hypotheses controls the
optimality gap by the canonical interval
`[0, lambda_k * (phi_0 x* - f x*)]`. -/
theorem gap_mem_Icc
    (h : IsEstimatingSequence f φ lam)
    (xStar : X)
    (hmin : IsMinOn f Set.univ xStar)
    (phiStar : ℕ → ℝ)
    (hphiStar : ∀ k, IsLeast (Set.range (φ k)) (phiStar k))
    (x : ℕ → X)
    (hx : ∀ k, f (x k) ≤ phiStar k)
    (k : ℕ) :
    f (x k) - f xStar ∈ Set.Icc 0 ((lam k : ℝ) * (φ 0 xStar - f xStar)) := by
  simpa using estimatingSequence_gap_mem_Icc xStar phiStar x hmin h.upper_bound hphiStar hx k

/-- Under the hypotheses of `gap_mem_Icc`, the optimality gap of an estimating sequence
converges to `0`. -/
theorem gap_tendsto_zero
    (h : IsEstimatingSequence f φ lam)
    (xStar : X)
    (hmin : IsMinOn f Set.univ xStar)
    (phiStar : ℕ → ℝ)
    (hphiStar : ∀ k, IsLeast (Set.range (φ k)) (phiStar k))
    (x : ℕ → X)
    (hx : ∀ k, f (x k) ≤ phiStar k) :
    Filter.Tendsto (fun k ↦ f (x k) - f xStar) Filter.atTop (nhds 0) := by
  simpa using estimatingSequence_gap_tendsto_zero xStar phiStar x hmin
    (NNReal.tendsto_coe.2 h.tendsto_zero) h.upper_bound hphiStar hx

end Gap

end IsEstimatingSequence

/-! ### Lemma_2_21 (from Chap02) -/
noncomputable section

universe u

namespace LagrangianProblem

variable {Q : Type u} {m : ℕ}

/- Primary domain: inequality-constrained Lagrangian problems and their auxiliary max-violation
value function.

Owner abstractions sampled before refining:
- `LagrangianProblem.feasibleSet`, `LagrangianProblem.primalOptimalValue`, and
  `LagrangianProblem.lagrangian` in Chapter 1's owner file
  `LecturesConvexOptimization_Nesterov_2018/Items/Chap01/Definition_1_10_2.lean`;
- `GeneralMinimizationProblem.componentOnAmbient` in
  `LecturesConvexOptimization_Nesterov_2018/Items/Chap01/Definition_1_1_4_3.lean`, which packages an objective together with its
  constraint family as a canonical `Fin (m + 1)`-indexed component map;
- the later Euclidean bridge
  `SmoothFunctionalConstraintsMinimizationProblem.toLagrangianProblem`, which reuses this same
  owner component family on `EuclideanSpace`;
- `maxTypeObjective` in `LecturesConvexOptimization_Nesterov_2018/Items/Chap02/Lemma_2_18.lean`, the Euclidean finite-maximum
  owner that matches the same construction once the ambient space has specialized to `ℝⁿ`.

The best owner abstraction here is still the generic `LagrangianProblem Q m` itself: the later
Euclidean chapter API is a specialization, while this file needs the intrinsic max-violation
objective on an arbitrary ambient type `Q`.

Primitive data here are only the underlying `LagrangianProblem` and the scalar parameter `t`.
The canonical derived component family is indexed by `Fin (m + 1)`: index `0` is
`x ↦ f₀(x) - t`, and successor indices are the constraints. The public derived API then consists
of that component family, the auxiliary objective, and the corresponding unconstrained optimal
value from Chapter 1's owner `SetConstrainedMinimizationProblem.unconstrained` /
`optimalValue`.

Source/core/bridge triage:
- source-facing: the threshold sign statements of Lemma 2.21 itself;
- core/canonical: `problem.constrainedAuxiliaryComponents`,
  `problem.constrainedAuxiliaryObjective`, and
  `SetConstrainedMinimizationProblem.optimalValue`;
- bridge/view: the unconditional lower bounds by `min (tStar - t) 0`, which package the
feasible/infeasible case split into one inequality but are not the source-facing main statement.
-/

/-- The canonical `Fin (m + 1)` component family whose maximum is the auxiliary objective:
index `0` is the shifted objective gap `x ↦ f₀(x) - t`, and successor indices are the inequality
constraints. -/
def constrainedAuxiliaryComponents
    (problem : LagrangianProblem Q m) (t : ℝ) : Fin (m + 1) → Q → ℝ :=
  Fin.cases (fun x ↦ problem x - t) problem.constraints

@[simp] theorem constrainedAuxiliaryComponents_zero
    (problem : LagrangianProblem Q m) (t : ℝ) :
    problem.constrainedAuxiliaryComponents t 0 = fun x ↦ problem x - t :=
  rfl

@[simp] theorem constrainedAuxiliaryComponents_succ
    (problem : LagrangianProblem Q m) (t : ℝ) (i : Fin m) :
    problem.constrainedAuxiliaryComponents t i.succ = problem.constraints i :=
  rfl

/-- The auxiliary objective `f(t; x)`, defined as the maximum of the objective gap `f₀(x) - t`
and all inequality-constraint values. -/
def constrainedAuxiliaryObjective (problem : LagrangianProblem Q m) (t : ℝ) : Q → ℝ :=
  maxTypeObjective (problem.constrainedAuxiliaryComponents t)

/-- The objective residual `f₀(x) - t` is one of the terms contributing to the owner auxiliary
objective `f(t; x)`. -/
-- Proof sketch: in the finite-maximum formula for `problem.constrainedAuxiliaryObjective t x`,
-- the zero index contributes
-- exactly `problem.objective x - t`; apply `Finset.le_sup'` to that term.
theorem objective_sub_le_constrainedAuxiliaryObjective
    (problem : LagrangianProblem Q m) (t : ℝ) (x : Q) :
    problem x - t ≤ problem.constrainedAuxiliaryObjective t x := by
  rw [constrainedAuxiliaryObjective, maxTypeObjective_apply]
  simpa using
    (Finset.le_sup'
      (fun j : Fin (m + 1) ↦ problem.constrainedAuxiliaryComponents t j x)
      (by simp : (0 : Fin (m + 1)) ∈ Finset.univ))

/-- Each individual constraint value `fᵢ(x)` is one of the terms contributing to the owner
auxiliary objective `f(t; x)`. -/
-- Proof sketch: in the finite-maximum formula for `problem.constrainedAuxiliaryObjective t x`,
-- the index `i.succ`
-- contributes exactly `problem.constraints i x`; apply `Finset.le_sup'` to that term.
theorem constraint_le_constrainedAuxiliaryObjective
    (problem : LagrangianProblem Q m) (t : ℝ) (x : Q) (i : Fin m) :
    problem.constraints i x ≤ problem.constrainedAuxiliaryObjective t x := by
  rw [constrainedAuxiliaryObjective, maxTypeObjective_apply]
  simpa using
    (Finset.le_sup'
      (fun j : Fin (m + 1) ↦ problem.constrainedAuxiliaryComponents t j x)
      (by simp : i.succ ∈ Finset.univ))

/-- Increasing the parameter by a nonnegative amount can only decrease the auxiliary objective at
each point. -/
-- Proof sketch: in the finite maximum defining `problem.constrainedAuxiliaryObjective (t + Δ) x`,
-- the zero component drops from `problem x - t` to `problem x - (t + Δ)`, while every successor
-- component is unchanged.
theorem constrainedAuxiliaryObjective_shift_le
    (problem : LagrangianProblem Q m) {t Δ : ℝ} (hΔ : 0 ≤ Δ) (x : Q) :
    problem.constrainedAuxiliaryObjective (t + Δ) x ≤
      problem.constrainedAuxiliaryObjective t x := by
  rw [constrainedAuxiliaryObjective, maxTypeObjective_apply,
    constrainedAuxiliaryObjective, maxTypeObjective_apply]
  refine Finset.sup'_le _ _ ?_
  intro j hj
  cases j using Fin.cases with
  | zero =>
      have hobj : problem x - (t + Δ) ≤ problem.constrainedAuxiliaryObjective t x := by
        linarith [problem.objective_sub_le_constrainedAuxiliaryObjective t x]
      rw [← maxTypeObjective_apply, ← constrainedAuxiliaryObjective]
      simpa using hobj
  | succ i =>
      rw [← maxTypeObjective_apply, ← constrainedAuxiliaryObjective]
      simpa using problem.constraint_le_constrainedAuxiliaryObjective t x i

/-- Increasing the parameter by `Δ ≥ 0` lowers the auxiliary objective by at most `Δ` at each
point. -/
-- Proof sketch: the zero component changes by exactly `Δ`, while every constraint component is
-- unchanged, so the finite maximum can drop by no more than `Δ`.
theorem constrainedAuxiliaryObjective_sub_le_shift
    (problem : LagrangianProblem Q m) {t Δ : ℝ} (hΔ : 0 ≤ Δ) (x : Q) :
    problem.constrainedAuxiliaryObjective t x - Δ ≤
      problem.constrainedAuxiliaryObjective (t + Δ) x := by
  rw [sub_le_iff_le_add, constrainedAuxiliaryObjective, maxTypeObjective_apply]
  refine Finset.sup'_le _ _ ?_
  intro j hj
  cases j using Fin.cases with
  | zero =>
      have hobj :
          problem x - t ≤ problem.constrainedAuxiliaryObjective (t + Δ) x + Δ := by
        linarith [problem.objective_sub_le_constrainedAuxiliaryObjective (t + Δ) x]
      simpa using hobj
  | succ i =>
      simpa using
        (problem.constraint_le_constrainedAuxiliaryObjective (t + Δ) x i).trans
          (le_add_of_nonneg_right hΔ)

/-- The auxiliary optimal value `f*(t)` is the extended-real infimum of the auxiliary objective
over the ambient domain `Q`, routed through the canonical unconstrained owner
`SetConstrainedMinimizationProblem.unconstrained`. -/
def constrainedAuxiliaryOptimalValue (problem : LagrangianProblem Q m) (t : ℝ) : EReal :=
  (SetConstrainedMinimizationProblem.unconstrained
    (problem.constrainedAuxiliaryObjective t)).optimalValue

/-- The auxiliary optimal value is the infimum of the range of the auxiliary objective. -/
-- Proof sketch: unfold `constrainedAuxiliaryOptimalValue`.
theorem constrainedAuxiliaryOptimalValue_eq_sInf (problem : LagrangianProblem Q m) (t : ℝ) :
    problem.constrainedAuxiliaryOptimalValue t =
      sInf (Set.range fun x : Q ↦ (problem.constrainedAuxiliaryObjective t x : EReal)) :=
  by
  simpa [constrainedAuxiliaryOptimalValue, Set.image_univ] using
    (SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image
      (SetConstrainedMinimizationProblem.unconstrained
        (problem.constrainedAuxiliaryObjective t)))

/-- An attained minimum of the auxiliary objective realizes the owner auxiliary optimal value. -/
-- Proof sketch: apply the Chapter 1 owner theorem `optimalValue_eq_of_isMinOn` to the canonical
-- unconstrained minimization problem with objective `problem.constrainedAuxiliaryObjective t`, and
-- simplify back to `problem.constrainedAuxiliaryOptimalValue t`.
theorem constrainedAuxiliaryOptimalValue_eq_of_isMinOn
    (problem : LagrangianProblem Q m) {t : ℝ} {x : Q}
    (hmin : IsMinOn (problem.constrainedAuxiliaryObjective t) Set.univ x) :
    problem.constrainedAuxiliaryOptimalValue t =
      (problem.constrainedAuxiliaryObjective t x : EReal) := by
  simpa [constrainedAuxiliaryOptimalValue] using
    (SetConstrainedMinimizationProblem.unconstrained
      (problem.constrainedAuxiliaryObjective t)).optimalValue_eq_of_isMinOn
      (by simp)
      hmin

section ThresholdBounds

variable (problem : LagrangianProblem Q m) {tStar : ℝ}

/-- Auxiliary bridge: every auxiliary objective value is bounded below by `min (tStar - t) 0`.
Feasible points contribute the primal-gap lower bound `tStar - t`, while infeasible points
contribute a positive constraint violation and hence at least `0`. The source-facing
below-threshold statement of Lemma 2.21 is recorded separately at the owner value-function layer
by `constrainedAuxiliaryOptimalValue_pos_of_lt`, while this pointwise bound remains companion
bridge API. -/
-- Proof sketch: if `x` is feasible, apply the lower-bound part of `htStar` to the feasible point
-- `x`; if `x` is infeasible, some constraint is positive, so the finite maximum defining the
-- auxiliary objective is at least `0`.
theorem min_sub_zero_le_constrainedAuxiliaryObjective
    (htStar : IsGLB (Set.range fun x : problem.feasibleSet ↦ problem x) tStar)
    (t : ℝ) (x : Q) :
    min (tStar - t) 0 ≤ problem.constrainedAuxiliaryObjective t x := by
  by_cases hx : x ∈ problem.feasibleSet
  · -- On the feasible branch, the primal lower bound controls the zero component.
    have hbound : tStar ≤ problem x := by
      exact htStar.1 ⟨⟨x, hx⟩, rfl⟩
    have hgap : tStar - t ≤ problem x - t := sub_le_sub_right hbound t
    exact
      (min_le_left (tStar - t) 0).trans <|
        hgap.trans (problem.objective_sub_le_constrainedAuxiliaryObjective t x)
  · -- On the infeasible branch, some constraint is positive, so the maximum is at least `0`.
    rw [problem.mem_feasibleSet_iff] at hx
    push Not at hx
    rcases hx with ⟨i, hi⟩
    have hnonneg : 0 ≤ problem.constrainedAuxiliaryObjective t x := by
      exact (le_of_lt hi).trans (problem.constraint_le_constrainedAuxiliaryObjective t x i)
    exact (min_le_right (tStar - t) 0).trans hnonneg

/-- Auxiliary bridge: if `t < tStar`, then every auxiliary objective value is strictly positive.
This pointwise statement is the bridge input for the source-facing positivity result on
`problem.constrainedAuxiliaryOptimalValue t`. -/
-- Proof sketch: if `x` is feasible, then `htStar` gives `tStar ≤ problem x`, so the zero
-- component `problem x - t` is strictly positive. If `x` is infeasible, some constraint is
-- strictly positive, so the corresponding successor component makes the same finite maximum
-- strictly positive.
theorem constrainedAuxiliaryObjective_pos_of_lt
    (htStar : IsGLB (Set.range fun x : problem.feasibleSet ↦ problem x) tStar)
    (t : ℝ) (ht : t < tStar) (x : Q) :
    0 < problem.constrainedAuxiliaryObjective t x := by
  by_cases hx : x ∈ problem.feasibleSet
  · -- Feasible points inherit `problem x ≥ tStar`, so the zero component is strictly positive.
    have hbound : tStar ≤ problem x := by
      exact htStar.1 ⟨⟨x, hx⟩, rfl⟩
    have hgap : 0 < problem x - t := by
      linarith
    exact hgap.trans_le (problem.objective_sub_le_constrainedAuxiliaryObjective t x)
  · -- Infeasible points have a strictly positive violated constraint component.
    rw [problem.mem_feasibleSet_iff] at hx
    push Not at hx
    rcases hx with ⟨i, hi⟩
    exact hi.trans_le (problem.constraint_le_constrainedAuxiliaryObjective t x i)

/-- Helper for Lemma 2.21: a feasible point whose objective value is below `t + ε` has auxiliary
value at most `ε`. -/
theorem constrainedAuxiliaryObjective_le_of_mem_feasibleSet_lt_add
    {t ε : ℝ} {x : Q} (hx : x ∈ problem.feasibleSet) (hε : 0 ≤ ε)
    (hobj : problem x < t + ε) :
    problem.constrainedAuxiliaryObjective t x ≤ ε := by
  -- Bound each component of the finite maximum by the same threshold `ε`.
  rw [constrainedAuxiliaryObjective]
  refine (maxTypeObjective_le_iff (problem.constrainedAuxiliaryComponents t) x ε).2 ?_
  intro j
  cases j using Fin.cases with
  | zero =>
      -- The objective-gap component is exactly the assumed bound `problem x - t < ε`.
      have hgap : problem x - t < ε := by
        linarith
      simpa using hgap.le
  | succ i =>
      -- Feasibility makes every constraint component nonpositive, hence at most `ε`.
      have hconstraint : problem.constraints i x ≤ 0 := (problem.mem_feasibleSet_iff.mp hx) i
      exact (hconstraint.trans hε)

/-- Lemma 2.21 (below-threshold side): if `t < tStar` and the auxiliary objective attains its
minimum, then the auxiliary optimal value is strictly positive. This is the source-facing
threshold-sign law for the owner value `problem.constrainedAuxiliaryOptimalValue t`; the explicit
attainment input keeps the infimum-to-minimum step faithful to the mathematics. -/
-- Proof sketch: choose a minimizer `x` from `hattained`. By
-- `constrainedAuxiliaryObjective_pos_of_lt`, the real value
-- `problem.constrainedAuxiliaryObjective t x` is strictly positive. The owner bridge theorem
-- `constrainedAuxiliaryOptimalValue_eq_of_isMinOn` then identifies the auxiliary optimal value
-- with that attained real minimum.
theorem constrainedAuxiliaryOptimalValue_pos_of_lt
    (htStar : IsGLB (Set.range fun x : problem.feasibleSet ↦ problem x) tStar)
    (t : ℝ) (ht : t < tStar)
    (hattained : ∃ x : Q, IsMinOn (problem.constrainedAuxiliaryObjective t) Set.univ x) :
    (0 : EReal) < problem.constrainedAuxiliaryOptimalValue t := by
  rcases hattained with ⟨x, hx⟩
  have hpos : (0 : EReal) < (problem.constrainedAuxiliaryObjective t x : EReal) := by
    exact_mod_cast problem.constrainedAuxiliaryObjective_pos_of_lt htStar t ht x
  rw [problem.constrainedAuxiliaryOptimalValue_eq_of_isMinOn hx]
  exact hpos

/-- The auxiliary optimal value inherits the unconditional lower bound `min (tStar - t) 0` as an
extended-real inequality. -/
-- Proof sketch: apply `min_sub_zero_le_constrainedAuxiliaryObjective` pointwise and pass to the
-- infimum of the range.
theorem min_sub_zero_le_constrainedAuxiliaryOptimalValue
    (htStar : IsGLB (Set.range fun x : problem.feasibleSet ↦ problem x) tStar)
    (t : ℝ) :
    ((min (tStar - t) 0 : ℝ) : EReal) ≤ problem.constrainedAuxiliaryOptimalValue t := by
  rw [problem.constrainedAuxiliaryOptimalValue_eq_sInf]
  refine le_sInf ?_
  rintro _ ⟨x, rfl⟩
  -- Lift the pointwise real lower bound to the extended-real infimum.
  change ((min (tStar - t) 0 : ℝ) : EReal) ≤
    (problem.constrainedAuxiliaryObjective t x : EReal)
  exact_mod_cast problem.min_sub_zero_le_constrainedAuxiliaryObjective htStar t x

/-- Lemma 2.21 (above-threshold side): if `tStar ≤ t`, then the auxiliary optimal value is at
most `0`. Together with `constrainedAuxiliaryOptimalValue_pos_of_lt`, this records the two
threshold sign regimes of the source statement in the canonical `EReal` owner API. -/
-- Proof sketch: use the `IsGLB` property of `tStar`, which already forces the feasible set to be
-- nonempty, to choose feasible points with objective values arbitrarily close to `tStar`. For
-- `tStar ≤ t`, the shifted objective values at those points are arbitrarily close to `0` from
-- above and the constraints are nonpositive, so the auxiliary infimum is at most `0`.
theorem constrainedAuxiliaryOptimalValue_nonpos_of_le
    (htStar : IsGLB (Set.range fun x : problem.feasibleSet ↦ problem x) tStar)
    (t : ℝ) (ht : tStar ≤ t) :
    problem.constrainedAuxiliaryOptimalValue t ≤ (0 : EReal) := by
  -- Route correction: make the primal `IsGLB` witness explicit in the theorem header, then use
  -- an `ε`-witness below the positive auxiliary infimum to contradict an arbitrarily good
  -- feasible point coming from `htStar.exists_between_self_add`.
  by_contra hnonpos
  have hpos : (0 : EReal) < problem.constrainedAuxiliaryOptimalValue t := lt_of_not_ge hnonpos
  rcases (EReal.lt_iff_exists_real_btwn).mp hpos with ⟨ε, hεposE, hεlt⟩
  have hεpos : 0 < ε := by
    exact_mod_cast hεposE
  rcases htStar.exists_between_self_add hεpos with ⟨_, ⟨x, rfl⟩, _, hxlt⟩
  have hxlt' : problem (x : Q) < t + ε := by
    exact lt_of_lt_of_le hxlt (by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right ht ε)
  have haux_le : problem.constrainedAuxiliaryObjective t (x : Q) ≤ ε := by
    exact problem.constrainedAuxiliaryObjective_le_of_mem_feasibleSet_lt_add
      x.property
      (le_of_lt hεpos)
      hxlt'
  have hopt_le_point :
      problem.constrainedAuxiliaryOptimalValue t ≤
        (problem.constrainedAuxiliaryObjective t (x : Q) : EReal) := by
    simpa [constrainedAuxiliaryOptimalValue] using
      (SetConstrainedMinimizationProblem.optimalValue_le_of_mem_feasibleSet
        (problem := SetConstrainedMinimizationProblem.unconstrained
          (problem.constrainedAuxiliaryObjective t))
        (x := (x : Q))
        (by simp))
  have hopt_le_eps : problem.constrainedAuxiliaryOptimalValue t ≤ (ε : EReal) :=
    hopt_le_point.trans (by exact_mod_cast haux_le)
  exact (not_le_of_gt hεlt) hopt_le_eps

end ThresholdBounds

end LagrangianProblem

/-! ### Proposition_2_21 (from Chap02) -/
open scoped Gradient SeminormDualNorm
open scoped PrimalEqualityConstrainedProblem.LagrangianMinimizerSelectionNotation

noncomputable section

universe u v

/- Primary domain: equality-constrained Lagrangian duality with a chosen minimizing primal
selection.

Owner declarations sampled before refining this file:
* `PrimalEqualityConstrainedProblem.constraintResidual` and
  `PrimalEqualityConstrainedProblem.dualFunction` in `Definition_2_30.lean`;
* `PrimalEqualityConstrainedProblem.LagrangianMinimizerSelection`,
  `LagrangianMinimizerSelection.selectedDualProfile`, `dualResidual`, and `isMinOn` in
  `Definition_2_31.lean`;
* `LagrangianMinimizerSelection.isMinOn_feasibleSet_of_dualOptimal` in `Proposition_2_20.lean`,
  the owner theorem turning dual optimality into primal optimality for the selected point;
* `Seminorm.inner_le_dualNorm_mul` in `Proposition_2_1.lean`, the dual Cauchy--Schwarz estimate
  used to bound the objective gap.

Best owner abstraction: the equality problem's own Lagrangian layer with
`selection : PrimalEqualityConstrainedProblem.LagrangianMinimizerSelection problem`.
The selected dual profile `selectedDualProfile selection` and residual `dualResidual selection`
are derived owner API, not primitive public data.

Primitive data:
* the equality-constrained problem `problem`;
* a minimizing selection `selection`;
* a seminorm `d` on the multiplier space.

Derived API:
* the selected dual profile;
* the selected dual residual;
* the primal optimality of `selection uStar` obtained from owner dual optimality;
* dual-norm bounds via `dualNorm d`.

Source/core/bridge triage:
* source-facing: Proposition 2.21's infeasibility and primal-gap estimate for a selected
  equality-constrained dual profile;
* core/canonical: the owner selected profile and residual on
  `PrimalEqualityConstrainedProblem.LagrangianMinimizerSelection`;
* bridge/view: the coordinate formula `b - A x(u)` for the same residual, which remains available
  through `problem.constraintResidual (selection u)`.
-/

namespace PrimalEqualityConstrainedProblem
namespace LagrangianMinimizerSelection

variable {E : Type u} {Λ : Type v} [AddCommMonoid E] [Module ℝ E]
variable [NormedAddCommGroup Λ] [InnerProductSpace ℝ Λ]
variable [FiniteDimensional ℝ Λ]
variable {problem : PrimalEqualityConstrainedProblem E Λ}

variable (selection : LagrangianMinimizerSelection problem)

local notation "Q₌" => problem.equalityFeasibleSet
local notation "φ" => φ[selection]
local notation "g" => g[selection]

/-- Proposition 2.21 in owner form: if the selected dual profile `φ(u) = 𝓛(x(u), u)` has
pointwise gradient `g(u) = b - A x(u)` at the optimal multiplier `uStar` and at the comparison
point `uBar`, and `uStar` is a global maximizer of `φ`, then the dual norm of the infeasibility
at `uBar` equals the dual norm of `∇ φ(uBar)`, and the primal suboptimality of `x(uBar)` relative
to the optimal selected point `x(uStar)` is bounded by `‖uBar‖_d ‖∇ φ(uBar)‖_{d,*}`. -/
-- Proof sketch: `hprofile_grad_bar.gradient` identifies the owner residual `g uBar` with the
-- actual gradient at `uBar`, giving the infeasibility norm identity. Proposition 2.20 upgrades
-- `huStar` and the pointwise gradient witness `hprofile_grad_star` at `uStar` to primal
-- optimality of `selection uStar`; this identifies `φ(uStar)` with `problem (selection uStar)`.
-- Maximality gives `φ(uBar) ≤ φ(uStar)`, expanding
-- `φ(uBar) = problem (selection uBar) + ⟪uBar, selection.dualResidual uBar⟫`; the remaining
-- pairing is bounded by `Seminorm.inner_le_dualNorm_mul`.
theorem dual_gradient_bounds_infeasibility_and_suboptimality
    (d : Seminorm ℝ Λ) [Seminorm.IsNorm d]
    {uStar uBar : Λ}
    (hprofile_grad_star : HasGradientAt φ (g uStar) uStar)
    (hprofile_grad_bar : HasGradientAt φ (g uBar) uBar)
    (huStar : IsMaxOn φ Set.univ uStar) :
    ‖g uBar‖[d,*] = ‖∇ φ uBar‖[d,*] ∧
      problem (selection uBar) - problem (selection uStar) ≤
        d uBar * ‖∇ φ uBar‖[d,*] := by
  have hoptimal :=
    selection.isMinOn_feasibleSet_of_dualOptimal huStar hprofile_grad_star
  have hselected_star : φ uStar = problem (selection uStar) :=
    selection.selectedDualProfile_eq_objective_of_mem_feasibleSet hoptimal.1
  have hprofile_le :
      problem (selection uBar) + inner ℝ uBar (g uBar) ≤ problem (selection uStar) := by
    calc
      problem (selection uBar) + inner ℝ uBar (g uBar) = φ uBar := by
        symm
        exact selection.selectedDualProfile_eq_objective_add_inner_dualResidual uBar
      _ ≤ φ uStar := by
        simpa using (isMaxOn_univ_iff.mp huStar) uBar
      _ = problem (selection uStar) := hselected_star
  have hgap :
      problem (selection uBar) - problem (selection uStar) ≤ -inner ℝ uBar (g uBar) := by
    linarith
  have hpair :
      -inner ℝ uBar (g uBar) ≤ d uBar * ‖g uBar‖[d,*] := by
    simpa [real_inner_comm, mul_comm] using
      (Seminorm.inner_le_dualNorm_mul d (-uBar) (g uBar))
  constructor
  · simp [hprofile_grad_bar.gradient]
  · calc
      problem (selection uBar) - problem (selection uStar) ≤ -inner ℝ uBar (g uBar) :=
        hgap
      _ ≤ d uBar * ‖g uBar‖[d,*] := hpair
      _ = d uBar * ‖∇ φ uBar‖[d,*] := by
        rw [hprofile_grad_bar.gradient]

end LagrangianMinimizerSelection
end PrimalEqualityConstrainedProblem

/-! ### Theorem_2_21 (from Chap02) -/
open scoped StrongConvexSmooth

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: strongly convex type-II accelerated optimal-method rates on a real Hilbert
space.

Owner declarations sampled before refining this file:
* `GeneralOptimalMethodScheme` in `Algorithm_2_2` owns the optimal-method trajectory and its
  canonical scalar sequences;
* `optimal_method_alpha0_initial_curvature`,
  `optimal_method_alpha0_initial_curvature_mem_Ioc` in `Algorithm_2_4` own the intrinsic map
  `α₀ ↦ γ₀` and the source-to-owner interval bridge;
* `optimal_method_hyperbolic_suboptimality_le_of_mem_Ioc` in `Theorem_2_20` owns the
  hyperbolic objective-gap estimate for the owner method once
  `γ₀ ∈ (μ, 3L + μ]`;
* `optimal_method_quadratic_suboptimality_le_of_mem_Ioc` in `Theorem_2_20` owns the quadratic
  objective-gap estimate for the same owner method under the same interval hypothesis on `γ₀`.

Best owner abstraction: the public object here is the owner method
`method : GeneralOptimalMethodScheme ... γ₀` with
`γ₀ = optimal_method_alpha0_initial_curvature μ L α₀`. The admissible interval for `α₀` is the
source-facing hypothesis, while the interval condition on `γ₀` and the resulting rate bounds are
derived owner API.

Primitive data:
* the source-facing objective hypothesis `f ∈ 𝓢[μ, L]¹¹`;
* the admissible parameter `α₀`;
* a minimizer `xStar`;
* the owner method started from the induced curvature `γ₀`.

Derived API:
* the internal bridge from the admissible `α₀` range to the owner interval
  `γ₀ ∈ (μ, 3L + μ]`;
* the owner hyperbolic objective-gap estimate;
* the owner quadratic objective-gap estimate. -/

variable {μ L : ℝ}

local notation "qf" => q[μ, L]
local notation "αRange" =>
  Set.Ioc (Real.sqrt qf) (constantStepSchemeIIAlphaUpper qf)

section OptimalMethodAlpha0Rates

variable {f : E → ℝ}
variable (α0 : ℝ)
local notation "γ0" => optimal_method_alpha0_initial_curvature μ L α0
variable (xStar : E)
variable {x0 : E}

/-- Helper for Theorem 2.21: the admissible `α₀` range induces the owner interval
condition `γ₀ ∈ (μ, 3L + μ]`. -/
private theorem gamma0_mem_Ioc
    (hf : f ∈ 𝓢[μ, L]¹¹)
    (hα0 : α0 ∈ αRange)
    (method : GeneralOptimalMethodScheme f L μ x0 γ0) :
    γ0 ∈ Set.Ioc μ (3 * L + μ) :=
  -- This is the source-to-owner bridge: convert the textbook `α₀` hypothesis into the exact
  -- curvature interval required by the owner theorems from Theorem 2.20.
  optimal_method_alpha0_initial_curvature_mem_Ioc
    (IsStrongConvexSmoothObjective.mu_pos (mem_S11_iff.mp hf))
    method.L_pos hα0

/-- Theorem 2.21: for a smooth `μ`-strongly convex objective on a real Hilbert space, the
optimal-method trajectory started from the parameter `α₀` in the stated admissible range
satisfies the displayed hyperbolic upper bound on the objective gap. -/
-- Proof sketch: use the owner bridge
-- `optimal_method_alpha0_initial_curvature_mem_Ioc
--   (IsStrongConvexSmoothObjective.mu_pos hf') method.L_pos hα0` to place
-- `γ₀` in `(μ, 3L + μ]`, then apply the owner rate theorem
-- `optimal_method_hyperbolic_suboptimality_le_of_mem_Ioc`.
theorem optimal_method_alpha0_hyperbolic_objective_gap_le
    (hf : f ∈ 𝓢[μ, L]¹¹)
    (hα0 : α0 ∈ αRange)
    (hxStar : IsMinOn f Set.univ xStar)
    (method : GeneralOptimalMethodScheme f L μ x0 γ0)
    (k : ℕ) :
    f (method k) - f xStar ≤
      (4 * μ *
        (f x0 - f xStar + (γ0 / 2) * ‖x0 - xStar‖ ^ (2 : ℕ))) /
        ((γ0 - μ) *
          (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt qf) -
            Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt qf))) ^
            (2 : ℕ)) := by
  -- First place the induced curvature `γ₀` in the owner interval from Theorem 2.20.
  have hγ0 : γ0 ∈ Set.Ioc μ (3 * L + μ) := gamma0_mem_Ioc α0 hf hα0 method
  -- Then the owner hyperbolic estimate applies directly; `method.x_zero` identifies the initial
  -- point with the source-facing `x0`.
  simpa [method.x_zero] using
    optimal_method_hyperbolic_suboptimality_le_of_mem_Ioc
      method hf hxStar hγ0 k

/-- Under the same admissible choice of `α₀`, the hyperbolic estimate yields the simpler
quadratic `O((k + 1)⁻²)` upper bound on the objective gap. -/
-- Proof sketch: use the same bridge `α₀ ↦ γ₀ ∈ (μ, 3L + μ]` and apply the owner quadratic rate
-- theorem `optimal_method_quadratic_suboptimality_le_of_mem_Ioc`.
theorem optimal_method_alpha0_quadratic_objective_gap_le
    (hf : f ∈ 𝓢[μ, L]¹¹)
    (hα0 : α0 ∈ αRange)
    (hxStar : IsMinOn f Set.univ xStar)
    (method : GeneralOptimalMethodScheme f L μ x0 γ0)
    (k : ℕ) :
    f (method k) - f xStar ≤
      (4 * L / ((γ0 - μ) * (k + 1 : ℝ) ^ (2 : ℕ))) *
        (f x0 - f xStar + (γ0 / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) := by
  -- Reuse the same bridge from the admissible `α₀` hypothesis to the owner curvature interval.
  have hγ0 : γ0 ∈ Set.Ioc μ (3 * L + μ) := gamma0_mem_Ioc α0 hf hα0 method
  -- The quadratic owner estimate is now immediate, with the same normalization at time zero.
  simpa [method.x_zero] using
    optimal_method_quadratic_suboptimality_le_of_mem_Ioc
      method hf hxStar hγ0 k

end OptimalMethodAlpha0Rates

end
