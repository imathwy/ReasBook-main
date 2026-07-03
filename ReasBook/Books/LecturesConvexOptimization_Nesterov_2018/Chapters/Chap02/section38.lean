

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_2_38_1 (from Chap02) -/
open scoped Gradient ProjectedGradient StrongConvexSmooth
open scoped ConstrainedArgmin

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- The primary domain here is the linear convergence of the simple-set gradient method on a closed
convex feasible set in a real Hilbert space.

Owner abstractions sampled for this refinement:
* `f ∈ 𝓢[μ, L]¹¹` and `mem_S11_iff` from `Definition_2_17`, reexported through
  `Theorem_2_38`, provide the source-facing objective hypothesis and its bridge to the canonical
  owner predicate `IsStrongConvexSmoothObjective μ L f`;
* `simpleSetGradientMethod` together with
  `simpleSetGradientMethod_zero` and `simpleSetGradientMethod_succ_eq_gradientMapping` from
  `Algorithm_2_6` owns the recursive trajectory of Algorithm 2.6;
* `projectedGradientSequence_dist_le_geometric` from `Theorem_2_38` owns the ambient projected-
  gradient contraction statement.

Best owner abstraction:
* source-facing: `simpleSetGradientMethod`;
* core/canonical: `projectedGradientSequence_dist_le_geometric`;
* bridge/view: the identification `(γ : ℝ) = (L + μ) / 2`, which turns the generic contraction
  factor `1 - μ / γ` into `((L - μ) / (L + μ))`.

Primitive data are only the feasible set `Q`, objective `f`, feasible initial point `x0 ∈ Q`,
the constrained minimizer certificate `xStar ∈ argmin[Q] f`, and the Algorithm 2.6 owner
trajectory
`simpleSetGradientMethod ... γ`. The explicit start and recurrence laws are derived API imported
from `Algorithm_2_6`, so this file does not store them again as primitive public data. -/

/-- Remark 2.38.1: when Algorithm 2.6 uses the optimal inverse-stepsize parameter
`γ = (L + μ) / 2`, its canonical trajectory `simpleSetGradientMethod` contracts the distance to
the constrained minimizer at the same sharp linear rate as the unconstrained gradient method:
`‖x_k - xStar‖ ≤ ((L - μ) / (L + μ))^k ‖x₀ - xStar‖`. The textbook `ℝⁿ` statement is the
specialization `E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: apply `projectedGradientSequence_dist_le_geometric` to the recursive owner
-- `simpleSetGradientMethod`. The only bridge work is rewriting the parameter assumption
-- `(γ : ℝ) = (L + μ) / 2` and simplifying the contraction factor `1 - μ / γ`.
theorem simpleSetGradientMethod_dist_le_optimal_geometric_rate
    {μ L : ℝ} {Q : Set E} {f : E → ℝ} {γ : NNRealˣ}
    (hf : f ∈ 𝓢[μ, L]¹¹)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    {x0 xStar : E}
    (hx0_mem : x0 ∈ Q)
    (hxStar : xStar ∈ argmin[Q] f)
    (hγ : (γ : ℝ) = (L + μ) / 2)
    (k : ℕ) :
    ‖simpleSetGradientMethod Q hQ_closed hQ_convex f x0 hx0_mem γ k - xStar‖ ≤
      ((L - μ) / (L + μ)) ^ k * ‖x0 - xStar‖ := by
  have hγ_pos : 0 < (γ : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))
  have hLμ_pos : 0 < L + μ := by
    linarith [hγ_pos, hγ]
  have hrate : 1 - μ / ((L + μ) / 2) = (L - μ) / (L + μ) := by
    field_simp [hLμ_pos.ne']
    ring
  have hγ_bound : (L + μ) / 2 ≤ (γ : ℝ) := by
    rw [hγ]
  simpa [hγ, hrate] using
    projectedGradientSequence_dist_le_geometric Q hQ_closed hQ_convex
      hf hx0_mem hxStar
      (simpleSetGradientMethod Q hQ_closed hQ_convex f x0 hx0_mem γ)
      (simpleSetGradientMethod_zero Q hQ_closed hQ_convex f x0 hx0_mem γ)
      (simpleSetGradientMethod_succ_eq_gradientMapping Q hQ_closed hQ_convex f x0 hx0_mem γ)
      hγ_bound
      k

end

/-! ### Definition_2_38 (from Chap02) -/
open scoped StrongConvexSmooth

noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type v} [Fintype ι] [Nonempty ι] {μ L : ℝ}

/- Definition 2.38 lies in the chapter's smooth minimax optimization domain.

Sampled owner-style declarations:
* `SetConstrainedMinimizationProblem E` in `Chap01/Definition_1_3_3`, the canonical owner of an
  ambient feasible set together with a real-valued objective;
* `maxTypeObjective` in `Lemma_2_18`, which canonically forms the finite maximum attached to a
  component family;
* `maxTypeAffineApproximation` in `Lemma_2_18`, which canonically forms the affine max-type model
  at a base point;
* `IsStrongConvexSmoothObjective μ L` in `Definition_2_17`, the owner predicate for each
  component function.

Best owner abstraction:
* `SetConstrainedMinimizationProblem E` for the ambient feasible-set/objective pair.

Primitive data:
* the nonempty finite component family `components : ι → E → ℝ` together with
  `components_mem : ∀ i, components i ∈ 𝓢[μ, L]¹¹`;
* the nonempty closed convex feasible set `feasibleSet`.

Derived API:
* the max-type objective `objective`;
* the affine max-type approximation `affineApproximation`;
* the owner bridge `toSetConstrainedMinimizationProblem`;
* the coercion to the ambient objective function.
* existence and uniqueness of a feasible minimizer.

Source/core/bridge triage:
* source-facing: `SmoothMinimaxProblem`;
* core/canonical: `SetConstrainedMinimizationProblem`, `maxTypeObjective`,
  `maxTypeAffineApproximation`;
* bridge/view: `toSetConstrainedMinimizationProblem`. -/

/-- Definition 2.38: a smooth minimax problem with parameters `μ` and `L` consists of a nonempty
closed convex feasible set `Q ⊆ E` on a real Hilbert space together with finitely many component
functions `fᵢ ∈ 𝓢^{1,1}_{μ,L}(E)` indexed by a nonempty finite type `ι`; its objective is the
max-type function `x ↦ max_i fᵢ(x)`, so the problem is `min_{x ∈ Q} max_i fᵢ(x)`. The textbook
`ℝⁿ`/`Fin m` presentation is the specialization `E = EuclideanSpace ℝ (Fin n)` and
`ι = Fin m`. -/
structure SmoothMinimaxProblem
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (ι : Type v) [Fintype ι] [Nonempty ι] (μ L : ℝ) where
  /-- The closed convex feasible set `Q ⊆ E`. -/
  feasibleSet : Set E
  /-- The feasible set is nonempty. -/
  feasible_nonempty : feasibleSet.Nonempty
  /-- The feasible set is closed. -/
  feasible_closed : IsClosed feasibleSet
  /-- The feasible set is convex. -/
  feasible_convex : Convex ℝ feasibleSet
  /-- The component functions whose pointwise maximum defines the minimax objective. -/
  components : ι → E → ℝ
  /-- Each component belongs to the smooth strongly convex class `𝓢^{1,1}_{μ,L}(E)`. -/
  components_mem : ∀ i : ι, components i ∈ 𝓢[μ, L]¹¹

namespace SmoothMinimaxProblem

/-- The objective of a smooth minimax problem is the canonical max-type objective of its
component family. -/
abbrev objective (problem : SmoothMinimaxProblem E ι μ L) : E → ℝ :=
  maxTypeObjective problem.components

/-- The affine max-type approximation of a smooth minimax problem at the base point `xBar`. -/
abbrev affineApproximation (problem : SmoothMinimaxProblem E ι μ L) (xBar : E) : E → ℝ :=
  maxTypeAffineApproximation problem.components xBar

/-- The Chapter 1 owner abstraction attached to a smooth minimax problem. -/
def toSetConstrainedMinimizationProblem
    (problem : SmoothMinimaxProblem E ι μ L) :
    SetConstrainedMinimizationProblem E where
  feasibleSet := problem.feasibleSet
  objective := problem.objective

/-- The owner bridge preserves the textbook feasible set `Q`. -/
@[simp] theorem toSetConstrainedMinimizationProblem_feasibleSet
    (problem : SmoothMinimaxProblem E ι μ L) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = problem.feasibleSet :=
  rfl

/-- The owner bridge evaluates to the max-type objective of the component family. -/
@[simp] theorem toSetConstrainedMinimizationProblem_apply
    (problem : SmoothMinimaxProblem E ι μ L) (x : E) :
    problem.toSetConstrainedMinimizationProblem x = problem.objective x :=
  rfl

/-- A smooth minimax problem can be used as its objective function. -/
instance : CoeFun (SmoothMinimaxProblem E ι μ L) (fun _ ↦ E → ℝ) where
  coe problem := problem.toSetConstrainedMinimizationProblem

/-- Evaluating a smooth minimax problem returns its max-type objective value. -/
@[simp] theorem coe_apply (problem : SmoothMinimaxProblem E ι μ L) (x : E) :
    problem x = problem.objective x :=
  rfl

/-- Helper for Definition 2.38: the max-type objective of the component family is strongly convex
on the whole ambient space with the common modulus `μ`. -/
lemma objective_strongConvexOn_univ (problem : SmoothMinimaxProblem E ι μ L) :
    StrongConvexOn Set.univ μ problem.objective := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  -- Each component is `μ`-strongly convex, and the finite maximum preserves the same estimate.
  rw [objective, maxTypeObjective_apply, Finset.sup'_le_iff]
  intro i hi
  have hcomponent : IsStrongConvexSmoothObjective μ L (problem.components i) :=
    mem_S11_iff.mp (problem.components_mem i)
  have hstrong :=
    hcomponent.strongConvexOn.2 (x := x) (y := y) (by simp) (by simp) ha hb hab
  have hstrong' :
      problem.components i (a • x + b • y) ≤
        a * problem.components i x + b * problem.components i y -
          a * b * ((μ / 2) * ‖x - y‖ ^ (2 : ℕ)) := by
    simpa [smul_eq_mul] using hstrong
  have hxmax : problem.components i x ≤ problem.objective x := by
    rw [objective, maxTypeObjective_apply]
    exact Finset.le_sup' (fun j : ι ↦ problem.components j x) (by simp)
  have hymax : problem.components i y ≤ problem.objective y := by
    rw [objective, maxTypeObjective_apply]
    exact Finset.le_sup' (fun j : ι ↦ problem.components j y) (by simp)
  calc
    problem.components i (a • x + b • y)
        ≤ a * problem.components i x + b * problem.components i y -
            a * b * ((μ / 2) * ‖x - y‖ ^ (2 : ℕ)) := hstrong'
    _ ≤ a * problem.objective x + b * problem.objective y -
          a * b * ((μ / 2) * ‖x - y‖ ^ (2 : ℕ)) := by
            gcongr
    _ = a • problem.objective x + b • problem.objective y -
          a * b * ((μ / 2) * ‖x - y‖ ^ (2 : ℕ)) := by
            simp [smul_eq_mul]

/-- Helper for Definition 2.38: the max-type objective is continuous because it is a finite
maximum of `C¹` component functions. -/
lemma objective_continuous (problem : SmoothMinimaxProblem E ι μ L) :
    Continuous problem.objective := by
  classical
  -- Continuity of the finite maximum follows from continuity of each smooth component.
  have hcont :
      Continuous
        (fun x : E ↦
          Finset.univ.sup' Finset.univ_nonempty (fun i : ι ↦ problem.components i x)) :=
    Continuous.finset_sup'_apply Finset.univ_nonempty fun i _ ↦
      (mem_S11_iff.mp (problem.components_mem i)).contDiff.continuous
  simpa [objective, maxTypeObjective_apply] using hcont

/-- Helper for Definition 2.38: a linear term plus the quadratic `μ/2 * ‖u‖²` is bounded below
by the completed-square constant `-‖g‖² / (2 μ)`. -/
lemma inner_add_quadratic_lower_bound
    (μ : ℝ) (hμ : 0 < μ) (g u : E) :
    -(‖g‖ ^ (2 : ℕ)) / (2 * μ) ≤
      inner ℝ g u + (μ / 2) * ‖u‖ ^ (2 : ℕ) := by
  have hnorm : -(‖g‖ * ‖u‖) ≤ inner ℝ g u := by
    -- Cauchy-Schwarz bounds the linear term from below by `-‖g‖ ‖u‖`.
    have hnorm' : -inner ℝ g u ≤ ‖g‖ * ‖u‖ := by
      simpa [inner_neg_left] using (real_inner_le_norm (-g) u)
    linarith
  calc
    -(‖g‖ ^ (2 : ℕ)) / (2 * μ) ≤ -(‖g‖ * ‖u‖) + (μ / 2) * ‖u‖ ^ (2 : ℕ) := by
      -- This is the scalar completed-square inequality `(μ‖u‖ - ‖g‖)^2 ≥ 0`.
      have hsq : 0 ≤ (μ * ‖u‖ - ‖g‖) ^ (2 : ℕ) := sq_nonneg (μ * ‖u‖ - ‖g‖)
      have hμ2 : 0 < 2 * μ := by positivity
      refine (div_le_iff₀ hμ2).2 ?_
      nlinarith
    _ ≤ inner ℝ g u + (μ / 2) * ‖u‖ ^ (2 : ℕ) := by
      gcongr

/-- Helper for Definition 2.38: the feasible objective values are bounded below by evaluating one
component at one feasible base point and completing the square in the tangent inequality. -/
lemma objective_image_bddBelow (problem : SmoothMinimaxProblem E ι μ L) :
    BddBelow (problem.objective '' problem.feasibleSet) := by
  classical
  rcases problem.feasible_nonempty with ⟨x0, hx0⟩
  let i0 : ι := Classical.choice inferInstance
  have hcomponent : IsStrongConvexSmoothObjective μ L (problem.components i0) :=
    mem_S11_iff.mp (problem.components_mem i0)
  have hμ : 0 < μ := hcomponent.mu_pos
  -- A single component lower-bounds the max objective, and its tangent model has a uniform lower
  -- bound after completing the square.
  set g0 : E := gradient (problem.components i0) x0
  let c : ℝ :=
    problem.components i0 x0 - ‖g0‖ ^ (2 : ℕ) / (2 * μ)
  refine ⟨c, ?_⟩
  rintro _ ⟨x, hxQ, rfl⟩
  have hobj_ge : problem.components i0 x ≤ problem.objective x := by
    rw [objective, maxTypeObjective_apply]
    exact Finset.le_sup' (fun j : ι ↦ problem.components j x) (by simp)
  have htan :
      problem.components i0 x ≥
        problem.components i0 x0 +
          inner ℝ g0 (x - x0) +
          (μ / 2) * ‖x - x0‖ ^ (2 : ℕ) :=
    by simpa [g0] using hcomponent.lower_tangent_quadratic x0 x
  have hquad :
      -(‖g0‖ ^ (2 : ℕ)) / (2 * μ) ≤
        inner ℝ g0 (x - x0) +
          (μ / 2) * ‖x - x0‖ ^ (2 : ℕ) :=
    inner_add_quadratic_lower_bound μ hμ _ _
  have hcomp_lower : c ≤ problem.components i0 x := by
    dsimp [c]
    have hraw' :
        problem.components i0 x0 - ‖g0‖ ^ (2 : ℕ) / (2 * μ) ≤
          problem.components i0 x0 +
            inner ℝ g0 (x - x0) +
            (μ / 2) * ‖x - x0‖ ^ (2 : ℕ) := by
      have hsum := add_le_add_left hquad (problem.components i0 x0)
      convert hsum using 1 <;> ring
    exact le_trans hraw' htan
  exact le_trans hcomp_lower hobj_ge

/-- Helper for Definition 2.38: midpoint strong convexity turns two approximate minimizers into a
quantitative distance estimate, which is the Cauchy-sequence core of the existence proof. -/
lemma strongConvexOn_distance_sq_le_of_upper_bounds
    {f : E → ℝ} {Q : Set E} {μ α ε₁ ε₂ : ℝ}
    (hstrong : StrongConvexOn Q μ f)
    {x₁ x₂ : E} (hx₁ : x₁ ∈ Q) (hx₂ : x₂ ∈ Q)
    (hα : α ≤ f ((1 / 2 : ℝ) • x₁ + (1 / 2 : ℝ) • x₂))
    (hx₁_le : f x₁ ≤ α + ε₁) (hx₂_le : f x₂ ≤ α + ε₂) :
    (μ / 8) * ‖x₁ - x₂‖ ^ (2 : ℕ) ≤ (ε₁ + ε₂) / 2 := by
  -- Apply strong convexity at the midpoint and compare both endpoint values with `α`.
  have hmid :
      f ((1 / 2 : ℝ) • x₁ + (1 / 2 : ℝ) • x₂) ≤
        (1 / 2 : ℝ) * f x₁ + (1 / 2 : ℝ) * f x₂ -
          (1 / 2 : ℝ) * (1 / 2 : ℝ) * ((μ / 2) * ‖x₁ - x₂‖ ^ (2 : ℕ)) := by
    simpa using hstrong.2 hx₁ hx₂ (by norm_num) (by norm_num) (by norm_num)
  nlinarith

/-- Helper for Definition 2.38: on a nonempty closed set in a complete real Hilbert space, a
continuous strongly convex function with bounded-below image attains its minimum. -/
lemma exists_isMinOn_of_isClosed_of_complete_of_bddBelow
    {Q : Set E} {f : E → ℝ} {μ : ℝ}
    (hQ_closed : IsClosed Q) (hQ_nonempty : Q.Nonempty)
    (hf_cont : ContinuousOn f Q)
    (hstrong : StrongConvexOn Q μ f) (hμ : 0 < μ)
    (hbdd : BddBelow (f '' Q)) :
    ∃ x : E, x ∈ Q ∧ IsMinOn f Q x := by
  let α : ℝ := sInf (f '' Q)
  have himage_nonempty : (f '' Q).Nonempty := by
    rcases hQ_nonempty with ⟨x, hxQ⟩
    exact ⟨f x, ⟨x, hxQ, rfl⟩⟩
  have hsInf_le : ∀ x ∈ Q, α ≤ f x := by
    intro x hxQ
    exact csInf_le hbdd ⟨x, hxQ, rfl⟩
  have happrox :
      ∀ n : ℕ, ∃ x : E, x ∈ Q ∧ f x < α + 1 / ((n : ℝ) + 1) := by
    intro n
    -- Choose a feasible point whose value is within `1 / (n + 1)` of the infimum `α`.
    have hlt : α < α + 1 / ((n : ℝ) + 1) := by
      have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    rcases exists_lt_of_csInf_lt himage_nonempty hlt with ⟨y, hy, hylt⟩
    rcases hy with ⟨x, hxQ, rfl⟩
    exact ⟨x, hxQ, hylt⟩
  choose xSeq hxSeq_mem hxSeq_lt using happrox
  have hxSeq_cauchy : CauchySeq xSeq := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have htarget : 0 < (μ / 8) * ε ^ (2 : ℕ) := by
      positivity
    rcases exists_nat_one_div_lt htarget with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hm_div :
        1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le
      positivity
      exact_mod_cast Nat.succ_le_succ hm
    have hn_div :
        1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le
      positivity
      exact_mod_cast Nat.succ_le_succ hn
    have hmid_mem :
        ((1 / 2 : ℝ) • xSeq m + (1 / 2 : ℝ) • xSeq n) ∈ Q :=
      hstrong.1 (hxSeq_mem m) (hxSeq_mem n) (by norm_num) (by norm_num) (by norm_num)
    have hdist_sq :
        (μ / 8) * ‖xSeq m - xSeq n‖ ^ (2 : ℕ) ≤
          (1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1)) / 2 :=
      strongConvexOn_distance_sq_le_of_upper_bounds hstrong (hxSeq_mem m) (hxSeq_mem n)
        (hsInf_le _ hmid_mem) (le_of_lt (hxSeq_lt m)) (le_of_lt (hxSeq_lt n))
    have hdist_sq' : ‖xSeq m - xSeq n‖ ^ (2 : ℕ) < ε ^ (2 : ℕ) := by
      have hsmall :
          (1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1)) / 2 <
            (μ / 8) * ε ^ (2 : ℕ) := by
        have hsum :
            (1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1)) / 2 ≤ 1 / ((N : ℝ) + 1) := by
          nlinarith
        exact lt_of_le_of_lt hsum hN
      have hμ8 : 0 < μ / 8 := by positivity
      nlinarith
    have hdist_lt : ‖xSeq m - xSeq n‖ < ε := by
      simpa [abs_of_nonneg (norm_nonneg _), abs_of_pos hε] using (sq_lt_sq).mp hdist_sq'
    simpa [dist_eq_norm] using hdist_lt
  obtain ⟨xStar, hxStarQ, hxSeq_tendsto⟩ :=
    cauchySeq_tendsto_of_isComplete hQ_closed.isComplete hxSeq_mem hxSeq_cauchy
  have hxSeq_tendsto_within :
      Filter.Tendsto xSeq Filter.atTop (nhdsWithin xStar Q) :=
    (tendsto_nhdsWithin_iff.2 ⟨hxSeq_tendsto, Filter.Eventually.of_forall hxSeq_mem⟩)
  have hvalues_tendsto :
      Filter.Tendsto (fun n ↦ f (xSeq n)) Filter.atTop (nhds (f xStar)) := by
    -- Continuity on `Q` transfers the convergence of the feasible minimizing sequence.
    have hf_within :
        Filter.Tendsto f (nhdsWithin xStar Q) (nhdsWithin (f xStar) Set.univ) := by
      exact (hf_cont xStar hxStarQ).tendsto_nhdsWithin (by
        intro x hx
        exact Set.mem_univ _)
    have hf_plain : Filter.Tendsto f (nhdsWithin xStar Q) (nhds (f xStar)) := by
      simpa [nhdsWithin_univ] using hf_within
    exact hf_plain.comp hxSeq_tendsto_within
  have hupper_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ α + 1 / ((n : ℝ) + 1)) Filter.atTop (nhds α) := by
    have hfrac_tendsto :
        Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) := by
      have hsucc :
          Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) Filter.atTop Filter.atTop := by
        exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      simpa [one_div] using tendsto_inv_atTop_zero.comp hsucc
    simpa using hfrac_tendsto.const_add α
  have hvalues_tendsto_alpha :
      Filter.Tendsto (fun n ↦ f (xSeq n)) Filter.atTop (nhds α) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hupper_tendsto
      (fun n ↦ hsInf_le (xSeq n) (hxSeq_mem n))
      (fun n ↦ le_of_lt (hxSeq_lt n))
  have hxStar_value : f xStar = α :=
    tendsto_nhds_unique hvalues_tendsto hvalues_tendsto_alpha
  refine ⟨xStar, hxStarQ, ?_⟩
  -- Once the objective value equals the infimum `α`, the feasible point is a minimizer.
  rw [isMinOn_iff]
  intro y hyQ
  rw [hxStar_value]
  exact hsInf_le y hyQ

-- Proof sketch: the component hypotheses make the max-type objective `problem.objective`
-- `μ`-strongly convex, so on the nonempty closed feasible set `problem.feasibleSet` the canonical
-- strong-convexity minimizer theorem yields existence and uniqueness.
/-- A smooth minimax problem has a unique feasible minimizer. -/
theorem existsUnique_isMinOn (problem : SmoothMinimaxProblem E ι μ L) :
    ∃! x : E, x ∈ problem.feasibleSet ∧ IsMinOn problem problem.feasibleSet x := by
  have hstrong_univ := objective_strongConvexOn_univ problem
  have hstrong :
      StrongConvexOn problem.feasibleSet μ problem.objective := by
    -- Restrict the whole-space strong convexity estimate to the closed convex feasible set.
    rw [strongConvexOn_iff_convex] at hstrong_univ ⊢
    exact hstrong_univ.subset (by simp) problem.feasible_convex
  have hμ :
      0 < μ := (mem_S11_iff.mp (problem.components_mem (Classical.choice inferInstance))).mu_pos
  obtain ⟨xStar, hxStarQ, hxStarMin⟩ :=
    exists_isMinOn_of_isClosed_of_complete_of_bddBelow
      problem.feasible_closed problem.feasible_nonempty
      (objective_continuous problem).continuousOn
      hstrong hμ (objective_image_bddBelow problem)
  refine ⟨xStar, ?_, ?_⟩
  · simpa [coe_apply] using ⟨hxStarQ, hxStarMin⟩
  · intro y hy
    exact
      (hstrong.strictConvexOn hμ).eq_of_isMinOn
        (by simpa [coe_apply] using hy.2)
        (by simpa [coe_apply] using hxStarMin)
        hy.1 hxStarQ

/- A global minimizer of a smooth minimax problem is expressed directly by the canonical predicate
`IsMinOn problem problem.feasibleSet x`. No additional wrapper declaration is needed. -/

end SmoothMinimaxProblem

/-! ### Theorem_2_38 (from Chap02) -/
open scoped Gradient ProjectedGradient StrongConvexSmooth
open scoped ConstrainedArgmin

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- The primary domain here is projected-gradient trajectories on a closed convex feasible set in a
real Hilbert space.

Owner abstractions sampled for this refinement:
* `gradientMapping` from `Definition_2_35_1`, the chapter's source-facing projected-gradient point;
* `euclideanProjection_isProjectionPointOn` from `Theorem_2_33`, the owner projection theorem
  reused after unfolding `gradientMapping`;
* `IsProjectionPointOn Q y p` from `Definition_2_33`, the core nearest-point predicate;
* `f ∈ 𝓢[μ, L]¹¹` and `mem_S11_iff` from `Definition_2_17`, the source-facing objective class
  and its bridge to the core owner predicate `IsStrongConvexSmoothObjective μ L f`.

Best owner abstraction:
* the one-step map `x ↦ gradientMapping Q ⟨x0, hx0_mem⟩ hQ_closed hQ_convex f x γ`.

Primitive data here are the closed/convex feasible-set geometry, the source-facing objective
hypothesis `f ∈ 𝓢[μ, L]¹¹`, the feasible initial point `x0 ∈ Q`, the constrained minimizer
certificate `xStar ∈ argmin[Q] f`, and the iterate sequence `x` satisfying the explicit
projected-gradient recursion. The core owner predicate `IsStrongConvexSmoothObjective μ L f`, the
projection-point view, and feasibility of later iterates are derived API. This keeps the public
theorem surface on the chapter notation and the source-facing recursion rather than packaging the
trajectory as a separate wrapper predicate. -/

namespace ProjectedGradientSequence

section

variable {Q : Set E} {hQ_closed : IsClosed Q} {hQ_convex : Convex ℝ Q}
variable {f : E → ℝ} {γ : NNRealˣ} {x0 : E} {x : ℕ → E}

/-- Each projected-gradient step is a Euclidean projection point of the explicit gradient step
onto `Q`. -/
theorem step_isProjectionPointOn
    (hx0_mem : x0 ∈ Q)
    (k : ℕ)
    (hx_step :
      x (k + 1) = x_Q[Q;⟨x0, hx0_mem⟩;hQ_closed;hQ_convex|f;γ](x k)) :
    IsProjectionPointOn Q (gradientStep f (x k) γ) (x (k + 1)) := by
  simpa [hx_step] using
    gradientMapping_isProjectionPointOn Q ⟨x0, hx0_mem⟩ hQ_closed hQ_convex f γ (x k)

/-- Every projected-gradient step lands back in the feasible set. -/
theorem mem_succ
    (hx0_mem : x0 ∈ Q)
    (k : ℕ)
    (hx_step :
      x (k + 1) = x_Q[Q;⟨x0, hx0_mem⟩;hQ_closed;hQ_convex|f;γ](x k)) :
    x (k + 1) ∈ Q :=
  (step_isProjectionPointOn hx0_mem k hx_step).1

/-- The projected-gradient recursion stays in the feasible set. -/
theorem mem
    (hx0_mem : x0 ∈ Q)
    (hx_zero : x 0 = x0)
    (hx_succ : ∀ k : ℕ,
      x (k + 1) = x_Q[Q;⟨x0, hx0_mem⟩;hQ_closed;hQ_convex|f;γ](x k))
    (k : ℕ) :
    x k ∈ Q := by
  induction k with
  | zero =>
      simpa [hx_zero] using hx0_mem
  | succ k hk =>
      exact mem_succ hx0_mem k (hx_succ k)

end

section

variable {Q : Set E} {hQ_closed : IsClosed Q} {hQ_convex : Convex ℝ Q}
variable {μ L : ℝ} {γ : NNRealˣ} {f : E → ℝ}
variable {x0 xStar : E} {x : ℕ → E}

/-- Helper for Theorem 2.38: a constrained minimizer is a projection point of its own explicit
gradient step on the feasible set. -/
theorem isProjectionPointOn_gradientStep_of_constrainedArgmin
    (hQ_convex : Convex ℝ Q)
    (hf : IsStrongConvexSmoothObjective μ L f)
    (hxStar : xStar ∈ argmin[Q] f) :
    IsProjectionPointOn Q (gradientStep f xStar γ) xStar := by
  rcases mem_constrainedArgmin_iff.mp hxStar with ⟨hxStar_mem, hxStar_min⟩
  have hgrad :
      HasGradientAt f (∇ f xStar) xStar :=
    (hf.contDiff.differentiable_one xStar).hasGradientAt
  -- Turn first-order optimality at the constrained minimizer into the projection inequality.
  have hvariational :
      ∀ x ∈ Q, inner ℝ (gradientStep f xStar γ - xStar) (x - xStar) ≤ 0 := by
    intro x hx
    have hγ_pos : 0 < (γ : ℝ) := by
      exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))
    have hdir : x - xStar ∈ posTangentConeAt Q xStar := by
      exact sub_mem_posTangentConeAt_of_segment_subset (hQ_convex.segment_subset hxStar_mem hx)
    have hfirstOrder :=
      hxStar_min.localize.hasFDerivWithinAt_nonneg
        hgrad.hasFDerivAt.hasFDerivWithinAt hdir
    have hinner_nonneg : 0 ≤ inner ℝ (∇ f xStar) (x - xStar) := by
      simpa [hgrad.hasFDerivAt.fderiv, innerSL_apply_apply] using hfirstOrder
    have hscaled : 0 ≤ (γ : ℝ)⁻¹ * inner ℝ (∇ f xStar) (x - xStar) :=
      mul_nonneg (inv_nonneg.mpr hγ_pos.le) hinner_nonneg
    simpa [gradientStep, sub_eq_add_neg, inner_smul_left, mul_comm, mul_left_comm, mul_assoc] using
      (neg_nonpos.mpr hscaled)
  -- Package that variational inequality into the owner projection-point predicate.
  have hmin :
      ‖gradientStep f xStar γ - xStar‖ =
        ⨅ w : Q, ‖gradientStep f xStar γ - w‖ :=
    (norm_eq_iInf_iff_real_inner_le_zero hQ_convex hxStar_mem).2 hvariational
  exact IsProjectionPointOn.of_norm_eq_iInf hxStar_mem hmin

/-- Helper for Theorem 2.38: two projection points onto the same convex feasible set are no
farther apart than their base points. -/
theorem projectionPoint_dist_le_dist
    (hQ_convex : Convex ℝ Q)
    {x₁ p₁ x₂ p₂ : E}
    (hp₁ : IsProjectionPointOn Q x₁ p₁)
    (hp₂ : IsProjectionPointOn Q x₂ p₂) :
    dist p₁ p₂ ≤ dist x₁ x₂ := by
  have h₁ : 0 ≤ inner ℝ (p₁ - x₁) (p₂ - p₁) :=
    hp₁.inner_sub_nonneg hQ_convex hp₂.1
  have h₂ : 0 ≤ inner ℝ (p₂ - x₂) (p₁ - p₂) :=
    hp₂.inner_sub_nonneg hQ_convex hp₁.1
  have hpair : p₂ - p₁ = -(p₁ - p₂) := by
    abel
  have h₁' : inner ℝ (p₁ - x₁) (p₁ - p₂) ≤ 0 := by
    rw [hpair, inner_neg_right] at h₁
    linarith
  -- Add the two projection inequalities and isolate the displacement `p₁ - p₂`.
  have haux : 0 ≤ inner ℝ ((x₁ - x₂) - (p₁ - p₂)) (p₁ - p₂) := by
    have hrewrite :
        inner ℝ ((x₁ - x₂) - (p₁ - p₂)) (p₁ - p₂) =
          inner ℝ (p₂ - x₂) (p₁ - p₂) - inner ℝ (p₁ - x₁) (p₁ - p₂) := by
      simp [sub_eq_add_neg, inner_add_left, add_comm, add_left_comm, add_assoc]
    rw [hrewrite]
    linarith
  have hmain : ‖p₁ - p₂‖ ^ (2 : ℕ) ≤ inner ℝ (p₁ - p₂) (x₁ - x₂) := by
    have hrewrite :
        inner ℝ ((x₁ - x₂) - (p₁ - p₂)) (p₁ - p₂) =
          inner ℝ (p₁ - p₂) (x₁ - x₂) - ‖p₁ - p₂‖ ^ (2 : ℕ) := by
      rw [inner_sub_left, real_inner_comm (x₁ - x₂), real_inner_self_eq_norm_sq]
    rw [hrewrite] at haux
    linarith
  have hcs : inner ℝ (p₁ - p₂) (x₁ - x₂) ≤ ‖p₁ - p₂‖ * ‖x₁ - x₂‖ := by
    simpa [Real.norm_eq_abs] using real_inner_le_norm (p₁ - p₂) (x₁ - x₂)
  have hnorm : ‖p₁ - p₂‖ ≤ ‖x₁ - x₂‖ := by
    nlinarith [hmain, hcs, norm_nonneg (p₁ - p₂), norm_nonneg (x₁ - x₂)]
  simpa [dist_eq_norm] using hnorm

/-- Helper for Theorem 2.38: the next projected-gradient iterate is no farther from the minimizer
than the corresponding pair of explicit gradient steps. -/
theorem step_dist_le_gradientStep_dist
    (hf : IsStrongConvexSmoothObjective μ L f)
    (hx0_mem : x0 ∈ Q)
    (hxStar : xStar ∈ argmin[Q] f)
    (k : ℕ)
    (hx_step :
      x (k + 1) = x_Q[Q;⟨x0, hx0_mem⟩;hQ_closed;hQ_convex|f;γ](x k)) :
    ‖x (k + 1) - xStar‖ ≤ ‖gradientStep f (x k) γ - gradientStep f xStar γ‖ := by
  -- Compare the two projection points attached to the iterate and to the minimizer.
  have hx_proj :
      IsProjectionPointOn Q (gradientStep f (x k) γ) (x (k + 1)) :=
    step_isProjectionPointOn hx0_mem k hx_step
  have hxStar_proj :
      IsProjectionPointOn Q (gradientStep f xStar γ) xStar :=
    isProjectionPointOn_gradientStep_of_constrainedArgmin
      hQ_convex hf hxStar
  -- Projection nonexpansiveness now gives the distance comparison.
  simpa [dist_eq_norm] using
    projectionPoint_dist_le_dist hQ_convex hx_proj hxStar_proj

/-- Helper for Theorem 2.38: strong convexity forces the gradient difference to dominate the point
difference in norm. -/
theorem mu_mul_norm_sub_le_norm_gradient_sub
    (hf : IsStrongConvexSmoothObjective μ L f)
    (x y : E) :
    μ * ‖x - y‖ ≤ ‖∇ f x - ∇ f y‖ := by
  -- Combine strong monotonicity with Cauchy--Schwarz and cancel one nonnegative norm factor.
  have hmono := hf.gradient_strong_mono x y
  have hcs :
      inner ℝ (∇ f x - ∇ f y) (x - y) ≤
        ‖∇ f x - ∇ f y‖ * ‖x - y‖ := by
    exact real_inner_le_norm _ _
  nlinarith [hmono, hcs, hf.mu_pos, norm_nonneg (x - y), norm_nonneg (∇ f x - ∇ f y)]

/-- Helper for Theorem 2.38: the squared distance to the constrained minimizer contracts in one
projected-gradient step by the factor `(1 - μ / γ)^2`. -/
theorem dist_succ_sq_le_contraction_sq
    (hf : IsStrongConvexSmoothObjective μ L f)
    (hx0_mem : x0 ∈ Q)
    (hxStar : xStar ∈ argmin[Q] f)
    (k : ℕ)
    (hx_step :
      x (k + 1) = x_Q[Q;⟨x0, hx0_mem⟩;hQ_closed;hQ_convex|f;γ](x k))
    (hγ : (L + μ) / 2 ≤ (γ : ℝ)) :
    ‖x (k + 1) - xStar‖ ^ (2 : ℕ) ≤
      (1 - μ / (γ : ℝ)) ^ (2 : ℕ) * ‖x k - xStar‖ ^ (2 : ℕ) := by
  by_cases hE : Subsingleton E
  · have hxsucc : x (k + 1) = xStar := hE.elim _ _
    have hxk : x k = xStar := hE.elim _ _
    simp [hxsucc, hxk]
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    have hμL : μ ≤ L := hf.mu_le_L
    have hγ_pos : 0 < (γ : ℝ) := by
      exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))
    have hγ_inv_nonneg : 0 ≤ (γ : ℝ)⁻¹ := inv_nonneg.mpr hγ_pos.le
    have hden : 0 < μ + L := by
      nlinarith [hf.mu_pos, hμL]
    have hstep :=
      step_dist_le_gradientStep_dist hf hx0_mem hxStar k hx_step
    have hstep_sq :
        ‖x (k + 1) - xStar‖ ^ (2 : ℕ) ≤
          ‖gradientStep f (x k) γ - gradientStep f xStar γ‖ ^ (2 : ℕ) := by
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hstep
    have hstep_diff :
        gradientStep f (x k) γ - gradientStep f xStar γ =
          (x k - xStar) - ((γ : ℝ)⁻¹) • (∇ f (x k) - ∇ f xStar) := by
      rw [gradientStep, gradientStep, smul_sub]
      abel_nf
    -- Expand the explicit gradient-step difference into a point part and a gradient part.
    have hexpand :
        ‖gradientStep f (x k) γ - gradientStep f xStar γ‖ ^ (2 : ℕ) =
          ‖x k - xStar‖ ^ (2 : ℕ) -
            2 * (γ : ℝ)⁻¹ *
              inner ℝ (∇ f (x k) - ∇ f xStar) (x k - xStar) +
            ((γ : ℝ)⁻¹) ^ (2 : ℕ) * ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) := by
      calc
        ‖gradientStep f (x k) γ - gradientStep f xStar γ‖ ^ (2 : ℕ)
            = ‖(x k - xStar) - ((γ : ℝ)⁻¹) • (∇ f (x k) - ∇ f xStar)‖ ^ (2 : ℕ) := by
                rw [hstep_diff]
        _ = ‖x k - xStar‖ ^ (2 : ℕ) -
              2 * inner ℝ (x k - xStar) (((γ : ℝ)⁻¹) • (∇ f (x k) - ∇ f xStar)) +
              ‖((γ : ℝ)⁻¹) • (∇ f (x k) - ∇ f xStar)‖ ^ (2 : ℕ) := by
              simpa using
                norm_sub_sq_real
                  (x k - xStar)
                  (((γ : ℝ)⁻¹) • (∇ f (x k) - ∇ f xStar))
        _ = ‖x k - xStar‖ ^ (2 : ℕ) -
              2 * (γ : ℝ)⁻¹ *
                inner ℝ (∇ f (x k) - ∇ f xStar) (x k - xStar) +
              ((γ : ℝ)⁻¹) ^ (2 : ℕ) * ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) := by
              rw [real_inner_smul_right, real_inner_comm]
              simp [norm_smul, Real.norm_of_nonneg hγ_inv_nonneg, sq]
              ring
    have hpair := hf.pairing_lower_bound (x k) xStar
    have hμ_grad :=
      mu_mul_norm_sub_le_norm_gradient_sub hf (x k) xStar
    have hμ_grad_sq :
        μ ^ (2 : ℕ) * ‖x k - xStar‖ ^ (2 : ℕ) ≤
          ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) := by
      have hsq :
          (μ * ‖x k - xStar‖) ^ (2 : ℕ) ≤
            ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) := by
        exact
          (sq_le_sq₀
            (mul_nonneg hf.mu_pos.le (norm_nonneg _))
            (norm_nonneg _)).2 hμ_grad
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq
    have hγ' : (μ + L) / 2 ≤ (γ : ℝ) := by
      simpa [add_comm] using hγ
    have hhalf_pos : 0 < (μ + L) / 2 := by
      positivity
    have hinv_le :
        (γ : ℝ)⁻¹ ≤ 2 / (μ + L) := by
      simpa [one_div, div_eq_mul_inv, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc] using
        (one_div_le_one_div_of_le hhalf_pos hγ')
    have hcoeff_nonpos :
        (γ : ℝ)⁻¹ * ((γ : ℝ)⁻¹ - 2 / (μ + L)) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos hγ_inv_nonneg (sub_nonpos.mpr hinv_le)
    -- The secant inequality controls the mixed term, and the remaining gradient term is
    -- nonpositive after substituting the lower bound `‖∇ f x - ∇ f y‖ ≥ μ ‖x - y‖`.
    have hpair' :
        2 * (γ : ℝ)⁻¹ *
            ((μ * L / (μ + L)) * ‖x k - xStar‖ ^ (2 : ℕ) +
              (1 / (μ + L)) * ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ)) ≤
          2 * (γ : ℝ)⁻¹ *
            inner ℝ (∇ f (x k) - ∇ f xStar) (x k - xStar) := by
      exact mul_le_mul_of_nonneg_left hpair (by positivity)
    have hstep₁ :
        ‖x (k + 1) - xStar‖ ^ (2 : ℕ) ≤
          ‖x k - xStar‖ ^ (2 : ℕ) -
            2 * (γ : ℝ)⁻¹ * (μ * L / (μ + L)) * ‖x k - xStar‖ ^ (2 : ℕ) -
            2 * (γ : ℝ)⁻¹ * (1 / (μ + L)) * ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) +
            ((γ : ℝ)⁻¹) ^ (2 : ℕ) * ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) := by
      calc
        ‖x (k + 1) - xStar‖ ^ (2 : ℕ) ≤
            ‖gradientStep f (x k) γ - gradientStep f xStar γ‖ ^ (2 : ℕ) :=
          hstep_sq
        _ = ‖x k - xStar‖ ^ (2 : ℕ) -
              2 * (γ : ℝ)⁻¹ *
                inner ℝ (∇ f (x k) - ∇ f xStar) (x k - xStar) +
              ((γ : ℝ)⁻¹) ^ (2 : ℕ) * ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) := hexpand
        _ ≤ ‖x k - xStar‖ ^ (2 : ℕ) -
              2 * (γ : ℝ)⁻¹ * (μ * L / (μ + L)) * ‖x k - xStar‖ ^ (2 : ℕ) -
              2 * (γ : ℝ)⁻¹ * (1 / (μ + L)) * ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) +
              ((γ : ℝ)⁻¹) ^ (2 : ℕ) * ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) := by
              nlinarith [hpair']
    have hstep₂ :
        ‖x (k + 1) - xStar‖ ^ (2 : ℕ) ≤
          (1 - 2 * (γ : ℝ)⁻¹ * (μ * L / (μ + L))) * ‖x k - xStar‖ ^ (2 : ℕ) +
            ((γ : ℝ)⁻¹ * ((γ : ℝ)⁻¹ - 2 / (μ + L))) *
              ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) := by
      calc
        ‖x (k + 1) - xStar‖ ^ (2 : ℕ) ≤
            ‖x k - xStar‖ ^ (2 : ℕ) -
              2 * (γ : ℝ)⁻¹ * (μ * L / (μ + L)) * ‖x k - xStar‖ ^ (2 : ℕ) -
              2 * (γ : ℝ)⁻¹ * (1 / (μ + L)) * ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) +
              ((γ : ℝ)⁻¹) ^ (2 : ℕ) * ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) :=
          hstep₁
        _ = (1 - 2 * (γ : ℝ)⁻¹ * (μ * L / (μ + L))) * ‖x k - xStar‖ ^ (2 : ℕ) +
              ((γ : ℝ)⁻¹ * ((γ : ℝ)⁻¹ - 2 / (μ + L))) *
                ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) := by
              ring
    have hgrad_term :
        ((γ : ℝ)⁻¹ * ((γ : ℝ)⁻¹ - 2 / (μ + L))) *
            ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) ≤
          ((γ : ℝ)⁻¹ * ((γ : ℝ)⁻¹ - 2 / (μ + L))) *
            (μ ^ (2 : ℕ) * ‖x k - xStar‖ ^ (2 : ℕ)) := by
      exact mul_le_mul_of_nonpos_left hμ_grad_sq hcoeff_nonpos
    have hcoeff_eq :
        (1 - 2 * (γ : ℝ)⁻¹ * (μ * L / (μ + L))) +
            ((γ : ℝ)⁻¹ * ((γ : ℝ)⁻¹ - 2 / (μ + L))) * μ ^ (2 : ℕ) =
          (1 - μ / (γ : ℝ)) ^ (2 : ℕ) := by
      have hγ_ne : (γ : ℝ) ≠ 0 := ne_of_gt hγ_pos
      have hden_ne : μ + L ≠ 0 := ne_of_gt hden
      field_simp [pow_two, hγ_ne, hden_ne]
      ring
    calc
      ‖x (k + 1) - xStar‖ ^ (2 : ℕ) ≤
          (1 - 2 * (γ : ℝ)⁻¹ * (μ * L / (μ + L))) * ‖x k - xStar‖ ^ (2 : ℕ) +
            ((γ : ℝ)⁻¹ * ((γ : ℝ)⁻¹ - 2 / (μ + L))) *
              ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) := hstep₂
      _ ≤ ((1 - 2 * (γ : ℝ)⁻¹ * (μ * L / (μ + L))) +
            ((γ : ℝ)⁻¹ * ((γ : ℝ)⁻¹ - 2 / (μ + L))) * μ ^ (2 : ℕ)) *
            ‖x k - xStar‖ ^ (2 : ℕ) := by
            nlinarith [hgrad_term]
      _ = (1 - μ / (γ : ℝ)) ^ (2 : ℕ) * ‖x k - xStar‖ ^ (2 : ℕ) := by
            rw [hcoeff_eq]

/-- Under the hypotheses of Theorem 2.38, each projected-gradient step contracts the distance to
the constrained minimizer by the factor `1 - μ / γ`. -/
-- Proof sketch: Theorem 2.35 identifies `xStar` with the projection of its explicit gradient
-- step, and `euclideanProjection_nonexpansive` compares that projection with the one defining
-- `x (k + 1)`. Expanding the resulting squared norm and applying
-- `IsStrongConvexSmoothObjective.pairing_lower_bound` yields the one-step contraction once
-- `γ ≥ (L + μ) / 2` makes the gradient term nonpositive.
theorem dist_succ_le_contraction
    (hf : IsStrongConvexSmoothObjective μ L f)
    (hx0_mem : x0 ∈ Q)
    (hxStar : xStar ∈ argmin[Q] f)
    (k : ℕ)
    (hx_step :
      x (k + 1) = x_Q[Q;⟨x0, hx0_mem⟩;hQ_closed;hQ_convex|f;γ](x k))
    (hγ : (L + μ) / 2 ≤ (γ : ℝ)) :
    ‖x (k + 1) - xStar‖ ≤ (1 - μ / (γ : ℝ)) * ‖x k - xStar‖ := by
  by_cases hE : Subsingleton E
  · have hxsucc : x (k + 1) = xStar := hE.elim _ _
    have hxk : x k = xStar := hE.elim _ _
    simp [hxsucc, hxk]
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    have hμL : μ ≤ L := hf.mu_le_L
    have hμγ : μ ≤ (γ : ℝ) := by
      nlinarith
    have hγ_pos : 0 < (γ : ℝ) := by
      exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))
    have hρ_nonneg : 0 ≤ 1 - μ / (γ : ℝ) := by
      have hdiv : μ / (γ : ℝ) ≤ 1 := by
        exact (div_le_one hγ_pos).2 hμγ
      nlinarith
    have hsq :=
      dist_succ_sq_le_contraction_sq hf hx0_mem hxStar k hx_step hγ
    have hsq' :
        ‖x (k + 1) - xStar‖ ^ (2 : ℕ) ≤
          ((1 - μ / (γ : ℝ)) * ‖x k - xStar‖) ^ (2 : ℕ) := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq
    -- Extract the distance estimate from the squared contraction.
    exact
      (sq_le_sq₀
        (norm_nonneg _)
        (mul_nonneg hρ_nonneg (norm_nonneg _))).1 hsq'

end

end ProjectedGradientSequence

/-- Theorem 2.38: if `Q` is closed and convex in a real Hilbert space `E`, `f` belongs to
`𝓢^{1,1}_{μ,L}(E)`, and `xStar ∈ Q` minimizes `f` on `Q`, then every projected-gradient
trajectory with inverse-stepsize parameter `γ ≥ (L + μ) / 2` contracts linearly toward `xStar`, with
`‖x_k - xStar‖ ≤ (1 - μ / γ)^k ‖x0 - xStar‖` for all `k ≥ 0`. Uniqueness of the constrained
minimizer is derived from strong convexity and is not stored as a separate hypothesis; likewise, in
the nontrivial real-Hilbert-space cases the owner hypothesis already forces `μ ≤ L`, while the
subsingleton case is tautological. The textbook `ℝⁿ` theorem is the specialization
`E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: because `xStar ∈ Q` minimizes `f` on `Q`, Theorem 2.35 makes `xStar` a fixed
-- point of the projection step. Then use nonexpansiveness of Euclidean projection to compare
-- `x (k + 1)` with `xStar`, expand the squared norm, and apply the standard interpolation
-- inequality for an objective in `𝓢^{1,1}_{μ,L}(E)`. The condition `γ ≥ (L + μ) / 2` makes the
-- gradient term contribute with the correct sign, yielding the one-step contraction
-- `‖x (k + 1) - xStar‖ ≤ (1 - μ / γ) ‖x k - xStar‖`; iterate this inequality over `k`.
theorem projectedGradientSequence_dist_le_geometric
    (Q : Set E) (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    {μ L : ℝ} {γ : NNRealˣ} {f : E → ℝ}
    (hf : f ∈ 𝓢[μ, L]¹¹)
    {x0 xStar : E}
    (hx0_mem : x0 ∈ Q)
    (hxStar : xStar ∈ argmin[Q] f)
    (x : ℕ → E)
    (hx_zero : x 0 = x0)
    (hx_succ : ∀ k : ℕ,
      x (k + 1) = x_Q[Q;⟨x0, hx0_mem⟩;hQ_closed;hQ_convex|f;γ](x k))
    (hγ : (L + μ) / 2 ≤ (γ : ℝ))
    (k : ℕ) :
    ‖x k - xStar‖ ≤ (1 - μ / (γ : ℝ)) ^ k * ‖x0 - xStar‖ := by
  have hf' : IsStrongConvexSmoothObjective μ L f := mem_S11_iff.mp hf
  by_cases hE : Subsingleton E
  · have hxk : x k = xStar := hE.elim _ _
    have hx0' : x0 = xStar := hE.elim _ _
    simp [hxk, hx0']
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    let ρ : ℝ := 1 - μ / (γ : ℝ)
    have hμL : μ ≤ L := hf'.mu_le_L
    have hμγ : μ ≤ (γ : ℝ) := by
      nlinarith
    have hρ_nonneg : 0 ≤ ρ := by
      have hγ : 0 < (γ : ℝ) := by
        exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))
      have hdiv : μ / (γ : ℝ) ≤ 1 := by
        exact (div_le_one hγ).2 hμγ
      nlinarith
    induction k with
    | zero =>
        simp [hx_zero]
    | succ k hk =>
        calc
          ‖x (k + 1) - xStar‖ ≤ ρ * ‖x k - xStar‖ := by
            simpa [ρ] using
              ProjectedGradientSequence.dist_succ_le_contraction
                hf' hx0_mem hxStar k (hx_succ k) hγ
          _ ≤ ρ * (ρ ^ k * ‖x0 - xStar‖) := by
            exact mul_le_mul_of_nonneg_left hk hρ_nonneg
          _ = ρ ^ (k + 1) * ‖x0 - xStar‖ := by
            simp [pow_succ, ρ, mul_left_comm, mul_comm]
