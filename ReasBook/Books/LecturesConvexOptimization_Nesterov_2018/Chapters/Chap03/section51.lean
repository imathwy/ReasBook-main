import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_51 (from Chap03) -/
noncomputable section

open Set

universe u

section Ambient

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A vector `g` strictly separates the query point `xBar` from the feasible set `Q` by an affine
inequality `⟪g, x⟫ ≤ β < ⟪g, xBar⟫`. -/
def SeparatesByCuttingVector (Q : Set E) (xBar g : E) : Prop :=
  ∃ β : ℝ, (∀ x ∈ Q, inner ℝ g x ≤ β) ∧ β < inner ℝ g xBar

namespace SeparatesByCuttingVector

/-- A strict cutting vector puts the whole feasible set on the lower side of the returned affine
functional. -/
-- Proof sketch: unpack the separating level `β`; combine `⟪g, x⟫ ≤ β` on `Q` with
-- `β < ⟪g, xBar⟫` to obtain `⟪g, x⟫ ≤ ⟪g, xBar⟫`.
theorem subset_cuttingHalfspace {Q : Set E} {xBar g : E}
    (hsep : SeparatesByCuttingVector Q xBar g) :
    Q ⊆ cuttingHalfspace xBar g := by
  rcases hsep with ⟨β, hβ, hlt⟩
  intro x hx
  exact le_trans (hβ x hx) (le_of_lt hlt)

/-- Over a nonempty feasible set, a strict cutting vector is nonzero. -/
theorem ne_zero {Q : Set E} {xBar g : E}
    (hsep : SeparatesByCuttingVector Q xBar g) (hQ : Q.Nonempty) :
    g ≠ 0 := by
  rintro rfl
  rcases hsep with ⟨β, hβ, hlt⟩
  rcases hQ with ⟨x, hx⟩
  have hβ_nonneg : 0 ≤ β := by simpa using hβ x hx
  exact (not_lt_of_ge hβ_nonneg) (by simpa using hlt)

/-- Over a nonempty feasible set, a strict cutting vector yields the canonical Chapter 3
point-versus-set separation owner at the retained offset `⟪g, xBar⟫`. -/
theorem separatesPointFromWith_inner {Q : Set E} {xBar g : E}
    (hsep : SeparatesByCuttingVector Q xBar g) (hQ : Q.Nonempty) :
    SeparatesPointFromWith Q xBar g (inner ℝ g xBar) :=
  (separatesPointFromWith_inner_iff).2
    ⟨hsep.ne_zero hQ, hsep.subset_cuttingHalfspace⟩

/-- Over a nonempty feasible set, a strict cutting vector also yields a strict affine-hyperplane
separator in the earlier Chapter 3 owner form. -/
theorem exists_strictlySeparatesPointFromWith {Q : Set E} {xBar g : E}
    (hsep : SeparatesByCuttingVector Q xBar g) (hQ : Q.Nonempty) :
    ∃ β : ℝ, StrictlySeparatesPointFromWith Q xBar g β := by
  have hg : g ≠ 0 := by
    rintro rfl
    rcases hsep with ⟨β, hβ, hlt⟩
    rcases hQ with ⟨x, hx⟩
    have hβ_nonneg : 0 ≤ β := by simpa using hβ x hx
    exact (not_lt_of_ge hβ_nonneg) (by simpa using hlt)
  rcases hsep with ⟨β, hβ, hlt⟩
  refine ⟨β, ?_⟩
  refine ⟨hg, ?_⟩
  · refine ⟨?_, Or.inr hlt⟩
    constructor
    · intro x hx
      exact hβ x hx
    · exact le_of_lt hlt

end SeparatesByCuttingVector

/-- A separation oracle for minimizing `f` over `Q` returns a subgradient at feasible query
points and a strict separating vector at infeasible query points. -/
structure ConvexMinimizationSeparationOracle (Q : Set E) (f : E → ℝ) where
  /-- The vector returned by the oracle at the query point. -/
  oracle : E → E
  /-- On feasible query points, the returned vector is a subgradient of `f`. -/
  subgradient_spec :
    ∀ ⦃xBar : E⦄, xBar ∈ Q →
      IsSubgradientAt (fun x ↦ (f x : WithTop ℝ)) xBar (oracle xBar)
  /-- On infeasible query points, the returned vector strictly separates the query point from
  `Q`. -/
  separating_spec :
    ∀ ⦃xBar : E⦄, xBar ∉ Q → SeparatesByCuttingVector Q xBar (oracle xBar)

namespace ConvexMinimizationSeparationOracle

variable {Q : Set E} {f : E → ℝ}

/-- A convex minimization separation oracle can be used as the returned query-to-vector map. -/
instance : CoeFun (ConvexMinimizationSeparationOracle Q f) (fun _ ↦ E → E) where
  coe oracle := oracle.oracle

/-- Evaluating a convex minimization separation oracle returns its query vector. -/
@[simp] theorem coe_apply
    (oracle : ConvexMinimizationSeparationOracle Q f) (xBar : E) :
    oracle xBar = oracle.oracle xBar :=
  rfl

/-- Forgetting the feasible-point subgradient branch turns a convex minimization separation oracle
into the earlier Chapter 3 feasibility separation oracle on `Q`. -/
def toSeparationOracle
    (oracle : ConvexMinimizationSeparationOracle Q f) (hQ : Q.Nonempty) :
    SeparationOracle Q :=
  let _ : DecidablePred (fun xBar : E ↦ xBar ∈ Q) := Classical.decPred _
  fun xBar ↦
    if hxBar : xBar ∈ Q then
      .feasible hxBar
    else
      .separatingVector
        (oracle.oracle xBar)
        hxBar
        ((oracle.separating_spec hxBar).separatesPointFromWith_inner hQ)

@[simp] theorem toSeparationOracle_of_mem
    (oracle : ConvexMinimizationSeparationOracle Q f) (hQ : Q.Nonempty)
    {xBar : E} (hxBar : xBar ∈ Q) :
    toSeparationOracle oracle hQ xBar = SeparationOracleAnswer.feasible hxBar := by
  classical
  simp [toSeparationOracle, hxBar]

@[simp] theorem toSeparationOracle_of_not_mem
    (oracle : ConvexMinimizationSeparationOracle Q f) (hQ : Q.Nonempty)
    {xBar : E} (hxBar : xBar ∉ Q) :
    ∃ hsep,
      toSeparationOracle oracle hQ xBar =
        SeparationOracleAnswer.separatingVector (oracle.oracle xBar) hxBar hsep := by
  classical
  refine ⟨(oracle.separating_spec hxBar).separatesPointFromWith_inner hQ, ?_⟩
  simp [toSeparationOracle, hxBar]

end ConvexMinimizationSeparationOracle

/-- Definition 3.51: a convex minimization problem with set constraint and separation oracle
consists of a convex real-valued objective on a real inner-product space, a bounded closed convex
feasible set with nonempty interior, and an oracle returning subgradients on feasible points and
strict separating vectors outside the feasible set. -/
structure ConvexMinimizationWithSeparationOracle
    (E : Type u) [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    extends SetConstrainedMinimizationProblem E where
  /-- The objective is convex on the whole ambient space. -/
  objective_convex : ConvexOn ℝ univ objective
  /-- The feasible set is bounded. -/
  feasibleSet_bounded : Bornology.IsBounded feasibleSet
  /-- The feasible set is closed. -/
  feasibleSet_closed : IsClosed feasibleSet
  /-- The feasible set is convex. -/
  feasibleSet_convex : Convex ℝ feasibleSet
  /-- The feasible set has nonempty interior. -/
  feasibleSet_interior_nonempty : (interior feasibleSet).Nonempty
  /-- A separation oracle for the constrained minimization problem. -/
  oracle : ConvexMinimizationSeparationOracle feasibleSet objective

namespace ConvexMinimizationWithSeparationOracle

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A convex minimization problem with separation oracle can be used as its objective function. -/
instance : CoeFun (ConvexMinimizationWithSeparationOracle E) (fun _ ↦ E → ℝ) where
  coe problem := problem.toSetConstrainedMinimizationProblem

/-- Evaluating a convex minimization problem with separation oracle returns its objective value. -/
@[simp] theorem coe_apply
    (problem : ConvexMinimizationWithSeparationOracle E) (x : E) :
    problem x = problem.objective x :=
  rfl

/-- The feasible set is nonempty because a point in its interior is feasible. -/
-- Proof sketch: choose a point of `interior feasibleSet` and use `interior_subset`.
theorem feasibleSet_nonempty (problem : ConvexMinimizationWithSeparationOracle E) :
    problem.feasibleSet.Nonempty := by
  rcases problem.feasibleSet_interior_nonempty with ⟨x, hx⟩
  exact ⟨x, interior_subset hx⟩

/-- Forgetting the objective and feasible-point subgradient branch yields the earlier Chapter 3
feasibility problem with separation oracle on the same feasible set. -/
def toFeasibilityProblemWithSeparationOracle
    (problem : ConvexMinimizationWithSeparationOracle E) :
    FeasibilityProblemWithSeparationOracle E where
  feasibleSet := problem.feasibleSet
  feasibleSet_nonempty := problem.feasibleSet_nonempty
  feasibleSet_closed := problem.feasibleSet_closed
  feasibleSet_convex := problem.feasibleSet_convex
  oracle :=
    ConvexMinimizationSeparationOracle.toSeparationOracle
      problem.oracle
      problem.feasibleSet_nonempty

@[simp] theorem toFeasibilityProblemWithSeparationOracle_feasibleSet
    (problem : ConvexMinimizationWithSeparationOracle E) :
    problem.toFeasibilityProblemWithSeparationOracle.feasibleSet = problem.feasibleSet :=
  rfl

end ConvexMinimizationWithSeparationOracle

end Ambient

end

/-! ### Proposition_3_51 (from Chap03) -/
noncomputable section

universe u

open scoped ConstrainedArgmin LevelMethodNotation

variable {E : Type u} [NormedAddCommGroup E]

/- Proposition 3.51 lies in the chapter's complete-level-method / sampled-prefix-value domain.

Mandatory domain-style sampling before refinement:
- `CompleteLevelMethod` and `CompleteLevelMethod.history` in `Algorithm_3_10`, the source-facing
  owner of a level-method run together with its canonical scalar history;
- `levelMethodHistoryFromApproximateValues_optimalValue_eq` in `Proposition_3_50`, the bridge
  identifying the history
  coordinate `f_k^*` with the chapter owner `bestFunctionValueUpTo`;
- `SetConstrainedMinimizationProblem.optimalValue` and
  `SetConstrainedMinimizationProblem.IsApproximateMinimizer` in `Chap01/Definition_1_3_7`, the
  Chapter 1 owner abstraction for constrained `ε`-solutions;
- `argmin[problem.feasibleSet] problem` in `Chap01/Definition_1_3_3`, the canonical owner of a
  minimizing comparison point for the constrained problem.

Best owner abstraction:
- source-facing: a `CompleteLevelMethod problem`;
- core/canonical: `problem.IsApproximateMinimizer ε x` together with `problem.optimalValue`;
- bridge/view: the sampled-prefix bound on `fstar(method.history, N)` and the optional
  comparison-point reformulation relative to `xStar ∈ argmin[problem.feasibleSet] problem`.

Primitive data:
- the constrained problem `problem` and a complete level-method run `method`;
- the comparison point `xStar`, now required only as a minimizing point in the canonical owner set
  `argmin[problem.feasibleSet] problem`;
- the constant `Mf`, the tolerance `ε`, and the iteration budget `N`;
- the level-method estimate stated directly on the owner value `fstar(method.history, N)`.

Derived API:
- the owner bound `(fstar(method.history, N) : EReal) ≤ problem.optimalValue + ε`;
- an index `k ≤ N` with `problem.IsApproximateMinimizer ε (method k)`;
- the comparison-point bridge `IsApproximateSolution problem xStar ε (method k)`.

Source/core/bridge triage:
- source-facing: the finite-horizon level-method guarantee for a run with prescribed initial point;
- core/canonical: `CompleteLevelMethod`, `problem.optimalValue`, and
  `problem.IsApproximateMinimizer`;
- bridge/view: `levelMethodHistoryFromApproximateValues_optimalValue_eq`, the argmin witness
  `xStar`, and the
  comparison-point extraction.

The previous version already restored the run owner `CompleteLevelMethod problem`, but its main
result still stopped at the comparison-point predicate
`IsApproximateSolution problem xStar ε (method k)`. This refinement keeps the sampled-prefix
estimate as a bridge, but moves the public conclusion back to the Chapter 1 constrained owner
`problem.IsApproximateMinimizer ε (method k)`, using `xStar ∈ argmin[problem.feasibleSet] problem`
only to identify `problem.optimalValue` with `problem xStar`.
-/

namespace CompleteLevelMethod

variable {problem : SetConstrainedMinimizationProblem E}

/-- Helper for Proposition 3.51: rewrite the textbook budget into the square-threshold form
needed for the square-root comparison step. -/
private lemma complexity_square_threshold_of_budget
    {Mf D ε : ℝ} {N : ℕ}
    (hε : 0 < ε)
    (hN : (4 * Mf ^ (2 : ℕ) * D ^ (2 : ℕ)) / ε ^ (2 : ℕ) ≤ (N : ℝ)) :
    ((2 * Mf * D) / ε) ^ (2 : ℕ) ≤ (N : ℝ) := by
  have hε_ne : ε ≠ 0 := ne_of_gt hε
  -- Clear the denominator `ε²` and expand the numerator into the source constant `4 M_f² D²`.
  have hrewrite :
      ((2 * Mf * D) / ε) ^ (2 : ℕ) =
        (4 * Mf ^ (2 : ℕ) * D ^ (2 : ℕ)) / ε ^ (2 : ℕ) := by
    field_simp [pow_two, hε_ne]
    ring
  rw [hrewrite]
  exact hN

/-- Helper for Proposition 3.51: a square-threshold bound implies the corresponding
`1 / √n` estimate needed in the complexity proof. -/
private lemma div_sqrt_le_epsilon_of_square_threshold
    {c ε n : ℝ}
    (hε : 0 < ε)
    (hn : 0 ≤ n)
    (hthreshold : (c / ε) ^ (2 : ℕ) ≤ n) :
    c / Real.sqrt n ≤ ε := by
  by_cases hc : c ≤ 0
  · -- If the numerator is nonpositive, the square-root term is already below `0 ≤ ε`.
    have hdiv_nonpos : c / Real.sqrt n ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg hc (Real.sqrt_nonneg n)
    exact hdiv_nonpos.trans hε.le
  · have hc_pos : 0 < c := lt_of_not_ge hc
    have hdiv_nonneg : 0 ≤ c / ε := div_nonneg hc_pos.le hε.le
    -- Compare squares to move from the threshold on `(c / ε)^2` to a bound on `c / ε`.
    have hdiv_le_sqrt : c / ε ≤ Real.sqrt n := by
      refine (sq_le_sq₀ hdiv_nonneg (Real.sqrt_nonneg n)).1 ?_
      simpa [pow_two, Real.sq_sqrt hn] using hthreshold
    have hsq_pos : 0 < (c / ε) ^ (2 : ℕ) := by
      have hdiv_pos : 0 < c / ε := div_pos hc_pos hε
      nlinarith [sq_pos_of_pos hdiv_pos]
    have hn_pos : 0 < n := lt_of_lt_of_le hsq_pos hthreshold
    have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
    -- Divide by the positive square root to recover the desired bound.
    exact (div_le_iff₀ hsqrt_pos).2 <| by
      simpa [mul_comm] using (div_le_iff₀ hε).1 hdiv_le_sqrt

/-- Helper for Proposition 3.51: combine the level-method gap estimate with the inverted
iteration budget to obtain an `ε`-gap bound. -/
private lemma comparison_gap_le_epsilon_of_complexity_estimate
    (method : CompleteLevelMethod problem) {Mf : ℝ} {xStar : E} {ε : ℝ} {N : ℕ}
    (h_level_estimate :
      fstar(method.history, N) - problem xStar ≤
        2 * Mf * ‖method.initialPoint - xStar‖ / Real.sqrt (N : ℝ))
    (hε : 0 < ε)
    (hN :
      (4 * Mf ^ (2 : ℕ) * ‖method.initialPoint - xStar‖ ^ (2 : ℕ)) / ε ^ (2 : ℕ) ≤ (N : ℝ)) :
    fstar(method.history, N) - problem xStar ≤ ε := by
  let D : ℝ := ‖method.initialPoint - xStar‖
  -- Rewrite the budget into the square-threshold shape dictated by the source proof.
  have hthreshold : ((2 * Mf * D) / ε) ^ (2 : ℕ) ≤ (N : ℝ) := by
    simpa [D] using complexity_square_threshold_of_budget hε hN
  -- Convert the threshold into the square-root estimate appearing in the level-method bound.
  have hscalar : (2 * Mf * D) / Real.sqrt (N : ℝ) ≤ ε := by
    exact div_sqrt_le_epsilon_of_square_threshold hε (by positivity) hthreshold
  -- Chain the sampled-prefix gap estimate with the scalar bound.
  simpa [D] using h_level_estimate.trans hscalar

/-- Proposition 3.51, owner form: if a complete level-method run satisfies the standard estimate
`f_N^* - f(x*) ≤ 2 M_f ‖x₀ - x*‖ / √N` on the owner sampled-prefix value
`f_N^* = fstar(method.history, N)`, then every budget `N` above
`4 M_f² ‖x₀ - x*‖² / ε²` forces `f_N^* ≤ f(x*) + ε`. -/
theorem optimalValue_le_comparison_add_of_complexity_estimate
    (method : CompleteLevelMethod problem) {Mf : ℝ} {xStar : E} {ε : ℝ} {N : ℕ}
    (h_level_estimate :
      fstar(method.history, N) - problem xStar ≤
        2 * Mf * ‖method.initialPoint - xStar‖ / Real.sqrt (N : ℝ))
    (hε : 0 < ε)
    (hN :
      (4 * Mf ^ (2 : ℕ) * ‖method.initialPoint - xStar‖ ^ (2 : ℕ)) / ε ^ (2 : ℕ) ≤ (N : ℝ)) :
    fstar(method.history, N) ≤ problem xStar + ε := by
  -- The source proof first inverts the budget into a direct `ε`-gap estimate.
  have hgap : fstar(method.history, N) - problem xStar ≤ ε := by
    exact comparison_gap_le_epsilon_of_complexity_estimate
      (method := method) h_level_estimate hε hN
  -- Rewriting the gap inequality gives the desired additive form.
  exact sub_le_iff_le_add'.mp hgap

/-- Proposition 3.51, owner form: if `x*` is a constrained minimizer and the complete level
method satisfies the standard comparison-point complexity estimate, then the sampled-prefix owner
value `f_N^*` is within `ε` of the Chapter 1 constrained optimal value. -/
theorem historyOptimalValue_le_optimalValue_add_of_complexity_estimate
    (method : CompleteLevelMethod problem) {Mf : ℝ} {xStar : E} {ε : ℝ} {N : ℕ}
    (hxStar : xStar ∈ argmin[problem.feasibleSet] problem)
    (h_level_estimate :
      fstar(method.history, N) - problem xStar ≤
        2 * Mf * ‖method.initialPoint - xStar‖ / Real.sqrt (N : ℝ))
    (hε : 0 < ε)
    (hN :
      (4 * Mf ^ (2 : ℕ) * ‖method.initialPoint - xStar‖ ^ (2 : ℕ)) / ε ^ (2 : ℕ) ≤ (N : ℝ)) :
    (fstar(method.history, N) : EReal) ≤ problem.optimalValue + ε := by
  rw [problem.optimalValue_eq_of_mem_argmin hxStar]
  exact_mod_cast
    method.optimalValue_le_comparison_add_of_complexity_estimate
      h_level_estimate hε hN

/-- Proposition 3.51: under the same complexity budget, one of the iterates `x₀, …, x_N` of the
complete level-method run is an `ε`-approximate minimizer of the constrained problem in the
canonical Chapter 1 sense. -/
theorem exists_isApproximateMinimizer_of_complexity_estimate
    (method : CompleteLevelMethod problem) {Mf : ℝ} {xStar : E} {ε : ℝ} {N : ℕ}
    (hxStar : xStar ∈ argmin[problem.feasibleSet] problem)
    (h_level_estimate :
      fstar(method.history, N) - problem xStar ≤
        2 * Mf * ‖method.initialPoint - xStar‖ / Real.sqrt (N : ℝ))
    (hε : 0 < ε)
    (hN :
      (4 * Mf ^ (2 : ℕ) * ‖method.initialPoint - xStar‖ ^ (2 : ℕ)) / ε ^ (2 : ℕ) ≤ (N : ℝ)) :
    ∃ k ≤ N, problem.IsApproximateMinimizer ε (method k) := by
  have hbest :
      (fstar(method.history, N) : EReal) ≤ problem.optimalValue + ε :=
    method.historyOptimalValue_le_optimalValue_add_of_complexity_estimate
      hxStar h_level_estimate hε hN
  obtain ⟨j, hjbest⟩ :=
    bestFunctionValueUpTo_exists_eq (fun i ↦ problem (method i)) N
  have hjbest : problem (method j) ≤ fstar(method.history, N) := by
    rw [show fstar(method.history, N) =
        bestFunctionValueUpTo (fun i ↦ problem (method i)) N by
          simpa [CompleteLevelMethod.history] using
            levelMethodHistoryFromApproximateValues_optimalValue_eq
              method.approximateOptimalValue
              problem
              method.iterate
              N]
    rw [hjbest]
  have hjbest' : (problem (method j) : EReal) ≤ fstar(method.history, N) := by
    exact_mod_cast hjbest
  refine ⟨j, Nat.lt_succ_iff.mp j.2, ?_⟩
  rw [problem.isApproximateMinimizer_iff ε (method j)]
  exact ⟨method.iterate_mem j, hjbest'.trans hbest⟩

/-- The owner `ε`-minimizer conclusion of Proposition 3.51 recovers the textbook comparison-point
form once the comparison point `x*` is known to lie in the constrained argmin set. -/
theorem exists_isApproximateSolution_of_complexity_estimate
    (method : CompleteLevelMethod problem) {Mf : ℝ} {xStar : E} {ε : ℝ} {N : ℕ}
    (hxStar : xStar ∈ argmin[problem.feasibleSet] problem)
    (h_level_estimate :
      fstar(method.history, N) - problem xStar ≤
        2 * Mf * ‖method.initialPoint - xStar‖ / Real.sqrt (N : ℝ))
    (hε : 0 < ε)
    (hN :
      (4 * Mf ^ (2 : ℕ) * ‖method.initialPoint - xStar‖ ^ (2 : ℕ)) / ε ^ (2 : ℕ) ≤ (N : ℝ)) :
    ∃ k ≤ N, IsApproximateSolution problem xStar ε (method k) := by
  obtain ⟨k, hkN, hk⟩ :=
    method.exists_isApproximateMinimizer_of_complexity_estimate
      hxStar h_level_estimate hε hN
  rw [problem.isApproximateMinimizer_iff ε (method k)] at hk
  refine ⟨k, hkN, sub_le_iff_le_add'.mpr ?_⟩
  have hk' : (problem (method k) : EReal) ≤ (problem xStar : EReal) + ε := by
    simpa [problem.optimalValue_eq_of_mem_argmin hxStar] using hk.2
  exact_mod_cast hk'

end CompleteLevelMethod

end

/-! ### Theorem_3_51 (from Chap03) -/
noncomputable section

open MeasureTheory

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable {μ : Measure E} [μ.IsAddHaarMeasure]

local notation "dim" => Module.finrank ℝ E

/- Primary domain: intrinsic volume comparison for convex subsets of a closed ball in a
finite-dimensional real normed space.

Sampled owner-style declarations:
- `Convex.nullMeasurableSet`
- `MeasureTheory.measureReal_mono`
- `MeasureTheory.Measure.addHaar_real_closedBall`
- `Module.finrank_pos`

Owner abstraction:
- the ambient additive Haar measure owner `μ` together with its real-valued evaluation `μ.real`
  on an arbitrary finite-dimensional real normed space.

Layer of this file:
- `source-facing`. The theorem is the chapter's direct radius-volume comparison, while its owner
  layer is the intrinsic finite-dimensional real-space volume API rather than the coordinate model
  `EuclideanSpace ℝ (Fin n)`.

Primitive data:
- the convex set `Q`, the comparison set `Sk`, the center `xStar`, and the radii `D`, `vkStar`
- the positive-dimension hypothesis `0 < dim`
- convexity and outer-ball containment for `Q`
- positivity of `μ.real Q`
- finite measure of `Sk`
- the inclusion `Metric.closedBall xStar vkStar ∩ Q ⊆ Sk`

Derived API:
- positivity of `D`, forced by `xStar ∈ Q`, `Q ⊆ Metric.closedBall xStar D`, and
  `0 < μ.real Q`
- positivity of `dim`, supplied directly by the public hypothesis
- the real-valued bound on `vkStar` in terms of the measure ratio `μ.real Sk / μ.real Q`, with
  the exponent written canonically as `1 / dim`.
-/

/-- Helper for Theorem 3.51: if a positive-volume set `Q` contains the center `xStar` and is
contained in `Metric.closedBall xStar D`, then the outer radius `D` must be positive. -/
lemma outer_radius_pos_of_positive_measure
    (hdim : 0 < dim)
    {Q : Set E} {xStar : E} {D : ℝ}
    (hxStar : xStar ∈ Q)
    (hQ_pos : 0 < μ.real Q)
    (hQ_subset : Q ⊆ Metric.closedBall xStar D) :
    0 < D := by
  -- The center belongs to the closed ball, so the radius is at least `0`.
  have hD_nonneg : 0 ≤ D := by
    have hxBall : xStar ∈ Metric.closedBall xStar D := hQ_subset hxStar
    simpa [Metric.mem_closedBall] using hxBall
  by_contra hD_pos
  have hD_zero : D = 0 := le_antisymm (le_of_not_gt hD_pos) hD_nonneg
  have hQ_subset_zero : Q ⊆ Metric.closedBall xStar 0 := by
    simpa [hD_zero] using hQ_subset
  have hmono : μ.real Q ≤ μ.real (Metric.closedBall xStar 0) :=
    measureReal_mono hQ_subset_zero measure_closedBall_lt_top.ne
  -- A zero-radius closed ball is a singleton, hence has zero Haar measure in positive dimension.
  have hclosed_zero : μ.real (Metric.closedBall xStar 0) = 0 := by
    rw [Measure.addHaar_real_closedBall μ xStar (show 0 ≤ (0 : ℝ) by simp)]
    simp [zero_pow (Nat.ne_of_gt hdim)]
  rw [hclosed_zero] at hmono
  linarith

/-- Helper for Theorem 3.51: if the inner radius strictly exceeds the outer one, then the
inclusion hypothesis already forces `Q ⊆ Sk`. -/
lemma comparison_set_contains_domain_of_outer_radius_lt
    {Q Sk : Set E} {xStar : E} {D vkStar : ℝ}
    (hQ_subset : Q ⊆ Metric.closedBall xStar D)
    (hball : Metric.closedBall xStar vkStar ∩ Q ⊆ Sk)
    (hDv : D < vkStar) :
    Q ⊆ Sk := by
  intro y hy
  have hyD : y ∈ Metric.closedBall xStar D := hQ_subset hy
  have hyv : y ∈ Metric.closedBall xStar vkStar := by
    rw [Metric.mem_closedBall] at hyD ⊢
    exact le_of_lt (lt_of_le_of_lt hyD hDv)
  exact hball ⟨hyv, hy⟩

/-- Helper for Theorem 3.51: the homothety of `Q` centered at `xStar` with factor `α ∈ [0, 1]`
stays inside the smaller closed ball and inside `Q` itself. -/
lemma homothety_image_subset_closedBall_inter_of_convex
    {Q : Set E} {xStar : E} {α D : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hQ_convex : Convex ℝ Q) (hxStar : xStar ∈ Q)
    (hQ_subset : Q ⊆ Metric.closedBall xStar D) :
    AffineMap.homothety xStar α '' Q ⊆ Metric.closedBall xStar (α * D) ∩ Q := by
  rintro z ⟨y, hy, rfl⟩
  constructor
  · -- The outer-ball hypothesis contracts to radius `α * D` under homothety.
    rw [Metric.mem_closedBall]
    have hyD : dist y xStar ≤ D := by
      simpa [Metric.mem_closedBall] using hQ_subset hy
    calc
      dist ((AffineMap.homothety xStar α) y) xStar = ‖α‖ * dist xStar y :=
        dist_homothety_center xStar y α
      _ = α * dist y xStar := by
        rw [Real.norm_of_nonneg hα0, dist_comm]
      _ ≤ α * D := mul_le_mul_of_nonneg_left hyD hα0
  · -- Convexity keeps the entire segment from `xStar` to `y` inside `Q`.
    rw [AffineMap.homothety_eq_lineMap]
    exact hQ_convex.lineMap_mem hxStar hy ⟨hα0, hα1⟩

/-- Helper for Theorem 3.51: the real-valued Haar measure of a homothety image scales by
`α ^ dim` when `α ≥ 0`. -/
lemma measureReal_homothety_image
    {Q : Set E} {xStar : E} {α : ℝ}
    (hα0 : 0 ≤ α) :
    μ.real (AffineMap.homothety xStar α '' Q) = α ^ dim * μ.real Q := by
  -- Rewrite the owner-level ENNReal scaling law through `μ.real`.
  rw [MeasureTheory.Measure.real, Measure.addHaar_image_homothety]
  rw [ENNReal.toReal_ofReal_mul]
  · simp [MeasureTheory.Measure.real, abs_of_nonneg, hα0]
  · positivity

/-- Helper for Theorem 3.51: a lower bound on `α ^ dim * μ.real Q` turns into the claimed
`dim`-th-root bound on `α`. -/
lemma alpha_le_volume_ratio_rpow_of_measure_bound
    (hdim : 0 < dim)
    {Q Sk : Set E} {α : ℝ}
    (hQ_pos : 0 < μ.real Q)
    (hα0 : 0 ≤ α)
    (hmeasure : α ^ dim * μ.real Q ≤ μ.real Sk) :
    α ≤ Real.rpow (μ.real Sk / μ.real Q) (1 / (dim : ℝ)) := by
  have hratio_nonneg : 0 ≤ μ.real Sk / μ.real Q := by
    positivity
  have hpow_le : α ^ dim ≤ μ.real Sk / μ.real Q := by
    exact (le_div_iff₀ hQ_pos).2 hmeasure
  have hdim_pos_real : 0 < (dim : ℝ) := by
    exact_mod_cast hdim
  -- Take the `dim`-th root after dividing by the positive denominator.
  have hroot :=
    (Real.le_rpow_inv_iff_of_pos hα0 hratio_nonneg hdim_pos_real).2 (by
      simpa [Real.rpow_natCast] using hpow_le)
  simpa [one_div] using hroot

/-- Theorem 3.51, stated at the intrinsic owner level: if `0 < Module.finrank ℝ E`, if a convex
set `Q` of positive `μ`-volume in a finite-dimensional real normed space is contained in the
closed ball `B(xStar, D)`, if `xStar ∈ Q`, and if a finite-`μ`-volume set `Sk` contains
`B(xStar, vkStar) ∩ Q`, then the radius `vkStar` is bounded by `D` times the `dim`-th root of the
Haar-measure ratio `μ.real Sk / μ.real Q`. Specializing to the canonical choice
`μ = Measure.addHaar` gives the chapter owner used downstream, and in Euclidean space this differs
from textbook Lebesgue volume only by a global positive normalization factor, so the displayed
ratio is unchanged. The textbook `ℝⁿ` statement is therefore recovered by specializing to
`E = EuclideanSpace ℝ (Fin n)` with `0 < n`.
-/
-- Proof sketch: if `vkStar > D`, then `Metric.closedBall xStar vkStar` already contains
-- `Metric.closedBall xStar D`, hence contains `Q`, so `Q ⊆ Sk` and the displayed bound is
-- immediate. The hypotheses force `0 < D`, and the public dimension hypothesis gives
-- `0 < dim`, so one may set
-- `α = vkStar / D ∈ [0, 1]`. Since `xStar ∈ Q` and `Q` is convex, the homothetic copy
-- `(1 - α) • xStar + α • Q` lies in `Q`; because `Q ⊆ Metric.closedBall xStar D`,
-- that same set also lies in `Metric.closedBall xStar vkStar`. Hence it is contained in `Sk`.
-- Taking volumes and using translation invariance together with the scaling rule yields
-- `μ.real Sk ≥ α ^ dim * μ.real Q`, which rearranges to the claimed bound.
theorem inner_ball_radius_le_outer_radius_mul_volume_ratio_rpow_of_convex
    (hdim : 0 < dim)
    {Q Sk : Set E} {xStar : E} {D vkStar : ℝ}
    (hQ_convex : Convex ℝ Q) (hxStar : xStar ∈ Q)
    (hQ_pos : 0 < μ.real Q)
    (hQ_subset : Q ⊆ Metric.closedBall xStar D)
    (hSk_finite : μ Sk ≠ ⊤)
    (hball : Metric.closedBall xStar vkStar ∩ Q ⊆ Sk) :
    vkStar ≤
      D *
        Real.rpow
          (μ.real Sk / μ.real Q)
          (1 / (dim : ℝ)) := by
  -- Route correction: the source proof's large-radius branch needs the missing textbook
  -- containment `Sk ⊆ Q`; the normalized homothety branch below is still valid as stated.
  have hD_pos : 0 < D :=
    outer_radius_pos_of_positive_measure hdim hxStar hQ_pos hQ_subset
  have hD_nonneg : 0 ≤ D := le_of_lt hD_pos
  by_cases hvk_nonpos : vkStar ≤ 0
  · -- If the claimed inner radius is nonpositive, the right-hand side is already nonnegative.
    have hratio_nonneg : 0 ≤ μ.real Sk / μ.real Q := by
      positivity
    have hbound_nonneg :
        0 ≤
          D *
            Real.rpow
              (μ.real Sk / μ.real Q)
              (1 / (dim : ℝ)) := by
      exact mul_nonneg hD_nonneg (Real.rpow_nonneg hratio_nonneg _)
    exact hvk_nonpos.trans hbound_nonneg
  · have hvk_nonneg : 0 ≤ vkStar := le_of_lt (lt_of_not_ge hvk_nonpos)
    by_cases hDv : D < vkStar
    · -- This is the source proof's overlarge-radius branch. As stated, it only yields `Q ⊆ Sk`.
      have hQ_in_Sk : Q ⊆ Sk :=
        comparison_set_contains_domain_of_outer_radius_lt hQ_subset hball hDv
      have hQ_le : μ.real Q ≤ μ.real Sk := measureReal_mono hQ_in_Sk hSk_finite
      have hratio_ge_one : 1 ≤ μ.real Sk / μ.real Q := by
        exact (one_le_div₀ hQ_pos).2 hQ_le
      have hrpow_ge_one :
          1 ≤
            Real.rpow
              (μ.real Sk / μ.real Q)
              (1 / (dim : ℝ)) := by
        calc
          1 = Real.rpow (1 : ℝ) (1 / (dim : ℝ)) := by
            simp
          _ ≤
              Real.rpow
                (μ.real Sk / μ.real Q)
                (1 / (dim : ℝ)) := by
            exact Real.rpow_le_rpow (by positivity) hratio_ge_one (by positivity)
      have hD_le :
          D ≤
            D *
              Real.rpow
                (μ.real Sk / μ.real Q)
                (1 / (dim : ℝ)) := by
        simpa [one_mul] using mul_le_mul_of_nonneg_left hrpow_ge_one hD_nonneg
      -- TODO: to finish this branch one needs the missing source hypothesis `Sk ⊆ Q`
      -- (or an equivalent measure upper bound on `Sk`), which would force `μ.real Sk = μ.real Q`
      -- after `Q ⊆ Sk` and hence reduce the bound to `vkStar ≤ D`.
      sorry
    · have hvk_le_D : vkStar ≤ D := le_of_not_gt hDv
      let α : ℝ := vkStar / D
      have hα0 : 0 ≤ α := by
        exact div_nonneg hvk_nonneg hD_nonneg
      have hα1 : α ≤ 1 := by
        exact (div_le_iff₀ hD_pos).2 (by simpa using hvk_le_D)
      have hα_mul : α * D = vkStar := by
        dsimp [α]
        field_simp [hD_pos.ne']
      -- The normalized homothety image is the exact source object controlling the measure.
      have himage_subset :
          AffineMap.homothety xStar α '' Q ⊆ Metric.closedBall xStar vkStar ∩ Q := by
        have hsubset :=
          homothety_image_subset_closedBall_inter_of_convex
            hα0 hα1 hQ_convex hxStar hQ_subset
        simpa [hα_mul] using hsubset
      have hmeasure_mono : μ.real (AffineMap.homothety xStar α '' Q) ≤ μ.real Sk :=
        measureReal_mono (fun z hz => hball (himage_subset hz)) hSk_finite
      have hmeasure : α ^ dim * μ.real Q ≤ μ.real Sk := by
        simpa [measureReal_homothety_image hα0] using hmeasure_mono
      have hα_le :
          α ≤
            Real.rpow
              (μ.real Sk / μ.real Q)
              (1 / (dim : ℝ)) :=
        alpha_le_volume_ratio_rpow_of_measure_bound hdim hQ_pos hα0 hmeasure
      calc
        vkStar = α * D := by
          rw [hα_mul]
        _ ≤
            Real.rpow
              (μ.real Sk / μ.real Q)
              (1 / (dim : ℝ)) *
              D := by
          exact mul_le_mul_of_nonneg_right hα_le hD_nonneg
        _ =
            D *
              Real.rpow
                (μ.real Sk / μ.real Q)
                (1 / (dim : ℝ)) := by
          ring

end
