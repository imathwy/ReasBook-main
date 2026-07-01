import Mathlib
import Nesterov.Chap01.Algorithm_1_10_11
import Nesterov.Chap01.Definition_1_4_8

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Set
open scoped LevelSetNotation

universe u

variable {X : Type u} [PseudoMetricSpace X] [ProperSpace X] {m : ℕ}

namespace PenaltyFunctionMethod

variable {problem : FunctionalConstraintsMinimizationProblem X m}

/-- Helper for Theorem 1.10.22: the bounded penalized `tBar`-sublevel set that eventually traps
the iterates. -/
private def tbarSublevel
    (method : PenaltyFunctionMethod problem) (xStar : problem.feasibleSet) (tBar : ℝ) :
    Set problem.basicFeasibleSet :=
  𝓛[(method.penalizedObjective tBar)]((problem xStar))

/-- Helper for Theorem 1.10.22: the pair consisting of the objective value and the penalty value
at a point of the basic feasible set. -/
private def objectivePenaltyPair
    (method : PenaltyFunctionMethod problem) :
    problem.basicFeasibleSet → ℝ × ℝ :=
  fun x ↦ (problem x, method.penalty x)

/-- Helper for Theorem 1.10.22: the sequence of objective/penalty pairs evaluated along the
penalty-method iterates. -/
private def iteratePair
    (method : PenaltyFunctionMethod problem) :
    ℕ+ → ℝ × ℝ :=
  fun k ↦ (problem (method k), method.penalty (method k))

/-- Helper for Theorem 1.10.22: the compact image of the closure of the bounded penalized
sublevel set under the objective/penalty pair map. -/
private def pairClosureImage
    (method : PenaltyFunctionMethod problem) (xStar : problem.feasibleSet) (tBar : ℝ) :
    Set (ℝ × ℝ) :=
  objectivePenaltyPair method '' closure (tbarSublevel method xStar tBar)

/-- Helper for Theorem 1.10.22: every iterate has penalized value bounded above by the feasible
optimal value `f₀(xStar)`. -/
private lemma iterate_penalized_value_le_optimal_value
    (method : PenaltyFunctionMethod problem)
    (xStar : problem.feasibleSet) (k : ℕ+) :
    problem (method k) +
      method.penaltyCoefficients k * method.penalty (method k) ≤
      problem xStar := by
  -- Compare the minimizing iterate with the feasible optimizer `xStar`.
  have hmin := method.isMinOn_auxiliaryObjective k
  rw [isMinOn_univ_iff] at hmin
  have hxStar_zero : method.penalty xStar = 0 := by
    exact (method.isPenalty.mem_iff_eq_zero).mp xStar.property
  -- Unfold the auxiliary objective and simplify the feasible comparison value.
  simpa [PenaltyFunctionMethod.auxiliaryObjective,
    PenaltyFunctionMethod.penalizedObjective, hxStar_zero] using hmin xStar

/-- Helper for Theorem 1.10.22: once the penalty coefficients dominate `tBar`, the iterates lie
in the bounded `tBar`-sublevel set. -/
private lemma eventually_iterate_mem_tbar_sublevel
    (method : PenaltyFunctionMethod problem)
    (xStar : problem.feasibleSet) (tBar : ℝ) :
    ∀ᶠ k : ℕ+ in atTop, method k ∈ tbarSublevel method xStar tBar := by
  -- Large penalty coefficients dominate the fixed coefficient `tBar`.
  filter_upwards [Filter.tendsto_atTop.1 method.penaltyCoefficients_tendsto_atTop tBar] with k hk
  have hpenalty_nonneg : 0 ≤ method.penalty (method k) :=
    method.isPenalty.nonneg (method k)
  have hscale :
      tBar * method.penalty (method k) ≤
        method.penaltyCoefficients k * method.penalty (method k) :=
    mul_le_mul_of_nonneg_right hk hpenalty_nonneg
  -- Replace the varying penalty weight by `tBar` inside the common upper bound.
  have hvalue :
      problem (method k) + tBar * method.penalty (method k) ≤ problem xStar := by
    linarith [hscale, iterate_penalized_value_le_optimal_value method xStar k]
  simpa [tbarSublevel, PenaltyFunctionMethod.penalizedObjective, mem_levelSet_iff] using hvalue

/-- Helper for Theorem 1.10.22: any cluster point of the objective/penalty pair sequence inside
the compact trapping set has zero penalty coordinate. -/
private lemma cluster_penalty_eq_zero
    (method : PenaltyFunctionMethod problem)
    (xStar : problem.feasibleSet) (tBar : ℝ) {y : ℝ × ℝ}
    (hyK : y ∈ pairClosureImage method xStar tBar)
    (hy : MapClusterPt y atTop (iteratePair method)) :
    y.2 = 0 := by
  have hy_nonneg : 0 ≤ y.2 := by
    rcases hyK with ⟨x, _, rfl⟩
    simpa [pairClosureImage, objectivePenaltyPair] using method.isPenalty.nonneg x
  by_contra hy_zero
  have hy_pos : 0 < y.2 := by
    exact lt_of_le_of_ne hy_nonneg (by simpa [eq_comm] using hy_zero)
  obtain ⟨ψ, hpair_tendsto, hψ_tendsto⟩ := hy.exists_seq_tendsto
  -- Project the pair convergence to the objective and penalty coordinates.
  have hobjective_tendsto :
      Tendsto (fun n ↦ problem (method (ψ n))) atTop (nhds y.1) := by
    simpa [iteratePair] using
      (continuous_fst.continuousAt.tendsto.comp hpair_tendsto)
  have hpenalty_tendsto :
      Tendsto (fun n ↦ method.penalty (method (ψ n))) atTop (nhds y.2) := by
    simpa [iteratePair] using
      (continuous_snd.continuousAt.tendsto.comp hpair_tendsto)
  have hcoeff_tendsto :
      Tendsto (fun n ↦ method.penaltyCoefficients (ψ n)) atTop atTop :=
    method.penaltyCoefficients_tendsto_atTop.comp hψ_tendsto
  have hy_half_pos : 0 < y.2 / 2 := by
    linarith
  have hobjective_eventually :
      ∀ᶠ n in atTop, y.1 - 1 < problem (method (ψ n)) := by
    simpa using hobjective_tendsto (Ioi_mem_nhds (by linarith : y.1 - 1 < y.1))
  have hpenalty_eventually :
      ∀ᶠ n in atTop, y.2 / 2 < method.penalty (method (ψ n)) := by
    simpa using hpenalty_tendsto (Ioi_mem_nhds (by linarith : y.2 / 2 < y.2))
  have hcoeff_eventually :
      ∀ᶠ n in atTop,
        (problem xStar - (y.1 - 1)) / (y.2 / 2) ≤ method.penaltyCoefficients (ψ n) := by
    exact Filter.tendsto_atTop.1 hcoeff_tendsto
      ((problem xStar - (y.1 - 1)) / (y.2 / 2))
  -- A positive penalty limit would force the penalized values to diverge to `+∞`.
  have hcombined :
      ∀ᶠ n : ℕ in atTop,
        y.1 - 1 < problem (method (ψ n)) ∧
          y.2 / 2 < method.penalty (method (ψ n)) ∧
          (problem xStar - (y.1 - 1)) / (y.2 / 2) ≤ method.penaltyCoefficients (ψ n) := by
    filter_upwards [hobjective_eventually, hpenalty_eventually, hcoeff_eventually] with n hnObj
      hnPen hnCoeff
    exact ⟨hnObj, hnPen, hnCoeff⟩
  rcases Filter.eventually_atTop.1 hcombined with ⟨N, hN⟩
  rcases hN N le_rfl with ⟨hnObj, hnPen, hnCoeff⟩
  have hmul_bound :
      problem xStar - (y.1 - 1) ≤
        method.penaltyCoefficients (ψ N) * (y.2 / 2) := by
    exact (div_le_iff₀ hy_half_pos).mp hnCoeff
  have hmul_lt :
      method.penaltyCoefficients (ψ N) * (y.2 / 2) <
        method.penaltyCoefficients (ψ N) * method.penalty (method (ψ N)) := by
    exact mul_lt_mul_of_pos_left hnPen (method.penaltyCoefficients_pos (ψ N))
  have hpenalized_lt :
      problem xStar - (y.1 - 1) <
        method.penaltyCoefficients (ψ N) * method.penalty (method (ψ N)) :=
    lt_of_le_of_lt hmul_bound hmul_lt
  have hstrict :
      problem xStar <
        problem (method (ψ N)) +
          method.penaltyCoefficients (ψ N) * method.penalty (method (ψ N)) := by
    linarith
  exact (not_lt_of_ge (iterate_penalized_value_le_optimal_value method xStar (ψ N))) hstrict

/-- Helper for Theorem 1.10.22: every cluster point of the trapped objective/penalty pair
sequence is exactly `(f₀(xStar), 0)`. -/
private lemma cluster_pair_eq_optimal_pair
    (method : PenaltyFunctionMethod problem)
    (xStar : problem.feasibleSet)
    (hoptimal : IsMinOn problem problem.feasibleSet xStar)
    (tBar : ℝ) {y : ℝ × ℝ}
    (hyK : y ∈ pairClosureImage method xStar tBar)
    (hy : MapClusterPt y atTop (iteratePair method)) :
    y = (problem xStar, 0) := by
  have hyPenaltyZero : y.2 = 0 :=
    cluster_penalty_eq_zero method xStar tBar hyK hy
  rcases hyK with ⟨x, _, rfl⟩
  -- Zero penalty identifies the witness as a feasible point.
  have hxFeasible : x ∈ problem.feasibleSet := by
    exact (method.isPenalty.eq_zero_iff_mem).mp <| by
      simpa [objectivePenaltyPair] using hyPenaltyZero
  have hoptimal' := isMinOn_iff.mp hoptimal
  have hlower : problem xStar ≤ problem x :=
    hoptimal' x hxFeasible
  have hclosed_first : IsClosed {p : ℝ × ℝ | p.1 ≤ problem xStar} :=
    isClosed_le continuous_fst continuous_const
  have hfirst_eventually :
      ∀ᶠ k : ℕ+ in atTop, iteratePair method k ∈ {p : ℝ × ℝ | p.1 ≤ problem xStar} := by
    refine Filter.Eventually.of_forall ?_
    intro k
    have hpenalty_nonneg :
        0 ≤ method.penaltyCoefficients k * method.penalty (method k) := by
      exact mul_nonneg (method.penaltyCoefficients_pos k).le
        (method.isPenalty.nonneg (method k))
    have hobjective_le : problem (method k) ≤ problem xStar := by
      linarith [iterate_penalized_value_le_optimal_value method xStar k]
    simpa [iteratePair] using hobjective_le
  -- Closedness of the half-space transfers the objective upper bound to every cluster point.
  have hupper : problem x ≤ problem xStar := by
    have hyMem := hclosed_first.mem_of_mapClusterPt hy hfirst_eventually
    simpa [objectivePenaltyPair] using hyMem
  have hobjective_eq : problem x = problem xStar :=
    le_antisymm hupper hlower
  refine Prod.ext hobjective_eq ?_
  simpa [objectivePenaltyPair] using hyPenaltyZero

/- Theorem 1.10.22 sits in the penalty-method / constrained-optimization domain.

Sampled owner-style declarations:
* `PenaltyFunctionMethod` in `Chap01/Algorithm_1_10_11`, the source-facing owner of the iterates,
  penalty map, and penalty coefficients;
* `𝓛[f](a)` / `mem_levelSet_iff` in `Chap01/Definition_1_4_8`, the chapter's source-facing owner
  notation for sublevel sets;
* `IsPenaltyFunction` in `Chap01/Definition_1_10_14`, the canonical owner predicate for a
  continuous penalty detecting the feasible set by its zero locus;
* `FunctionalConstraintsMinimizationProblem.IsFunctionalConstraintProblem` in
  `Chap01/Definition_1_10_21`, whose fields show that closedness of `problem.basicFeasibleSet` and
  continuity of `problem.objective` are separate ambient hypotheses rather than primitive method
  data.

Best owner abstraction:
* source-facing: `PenaltyFunctionMethod problem`;
* core/canonical: the bundled continuous penalty `method.penalty : C(problem.basicFeasibleSet, ℝ)`
  together with `method.isPenalty`;
* bridge/view: the packaged regularity class `problem.IsFunctionalConstraintProblem` and the raw
  lower-interval preimage behind `𝓛[(method.penalizedObjective tBar)]((problem xStar))`.

Primitive data:
* the penalty method `method`;
* the feasible minimizer `xStar`;
* the bounded penalized sublevel hypothesis.

Derived API already bundled by the owner:
* continuity of `method.penalty`;
* exact identification of `problem.feasibleSet` with the zero set of `method.penalty`.

The public theorem therefore uses only the ambient regularity actually needed here, namely
closedness of `problem.basicFeasibleSet` and continuity of `problem.objective`, instead of the
larger `problem.IsFunctionalConstraintProblem` package. -/

/-- Theorem 1.10.22: if some penalized sublevel set
`{x ∈ Q | f₀(x) + tBar * Φ(x) ≤ f₀(xStar)}` with `tBar > 0` is bounded, then along the iterates
`xₖ` of the penalty function method the pair `(f₀(xₖ), Φ(xₖ))` converges to `(f₀(xStar), 0)`,
where `xStar` is a feasible global optimizer. -/
-- Proof sketch: compare the penalized objective at minimizing iterates with its value at the
-- feasible optimizer `xStar`; once the penalty parameters are larger than `tBar`, the iterates lie
-- in the bounded sublevel set, so they admit cluster points. Closedness of `Q`, continuity of
-- `f₀`, and the penalty-function axioms show each cluster point lies in the feasible set and has
-- objective value `f₀(xStar)`, which identifies the only possible limit of
-- `(f₀(xₖ), Φ(xₖ))` as `(f₀(xStar), 0)`.
theorem tendsto_objective_and_penalty_of_bounded_penalized_sublevel
    (method : PenaltyFunctionMethod problem)
    (hbasicFeasibleSet : IsClosed problem.basicFeasibleSet)
    (hobjective : Continuous problem.objective)
    (xStar : problem.feasibleSet)
    (hoptimal : IsMinOn problem problem.feasibleSet xStar)
    (tBar : ℝ) (htBar : 0 < tBar)
    (hbounded :
      Bornology.IsBounded
        (𝓛[(method.penalizedObjective tBar)]((problem xStar)))) :
    Tendsto
      (fun k ↦ (problem (method k), method.penalty (method k)))
      atTop
      (nhds (problem xStar, 0)) := by
  have _ : 0 ≤ tBar := le_of_lt htBar
  letI : ProperSpace problem.basicFeasibleSet := ProperSpace.of_isClosed hbasicFeasibleSet
  have hpair_continuous : Continuous (objectivePenaltyPair method) := by
    -- Continuity of the pair map comes from the two continuous coordinates.
    change Continuous (fun x : problem.basicFeasibleSet ↦ (problem x, method.penalty x))
    exact Continuous.prodMk hobjective method.penalty.continuous
  have hcompactK : IsCompact (pairClosureImage method xStar tBar) := by
    have hcompact_closure :
        IsCompact (closure (tbarSublevel method xStar tBar)) := by
      simpa [tbarSublevel] using hbounded.isCompact_closure
    -- The bounded sublevel closure stays compact after applying the pair map.
    simpa [pairClosureImage] using hcompact_closure.image hpair_continuous
  have hmemK :
      ∀ᶠ k : ℕ+ in atTop, iteratePair method k ∈ pairClosureImage method xStar tBar := by
    -- Eventual entry into the bounded sublevel gives eventual membership in the compact image.
    filter_upwards [eventually_iterate_mem_tbar_sublevel method xStar tBar] with k hk
    exact ⟨method k, subset_closure hk, rfl⟩
  have htendsto :
      Tendsto (iteratePair method) atTop (nhds (problem xStar, 0)) := by
    -- Every cluster point inside the compact trapping set is the optimal pair.
    refine hcompactK.tendsto_nhds_of_unique_mapClusterPt hmemK ?_
    intro y hyK hy
    exact cluster_pair_eq_optimal_pair method xStar hoptimal tBar hyK hy
  simpa [iteratePair] using htendsto

end PenaltyFunctionMethod
