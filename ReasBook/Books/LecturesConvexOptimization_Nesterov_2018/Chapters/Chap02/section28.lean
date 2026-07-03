import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_28 (from Chap02) -/
open Set
open PointedCone

local notation "Q" => reciprocalEpigraphOnPositiveRay

/- Definition 2.28 is source-facing in the convex-geometry domain of pointed cone hulls in `ℝ²`.

Sampled owner-style declarations:
- `reciprocalEpigraphOnPositiveRay`
- `mem_reciprocalEpigraphOnPositiveRay_iff`
- `PointedCone.hull`
- `PointedCone.ofConeComb`

Best owner abstraction:
- `PointedCone.hull ℝ reciprocalEpigraphOnPositiveRay`

Primitive data:
- the owner set `Q = reciprocalEpigraphOnPositiveRay`

Derived API:
- the product-set description `Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)` of the open positive quadrant;
- the coordinate membership view of the underlying set of `𝒦(Q)`.

Source/core/bridge triage:
- source-facing: the textbook set equality for `𝒦(Q)`;
- core/canonical: `PointedCone.hull ℝ reciprocalEpigraphOnPositiveRay`;
- bridge/view: the membership theorem below. -/

/-- Definition 2.28: the pointed conic hull `𝒦(Q)` of
`Q = reciprocalEpigraphOnPositiveRay` is the open positive quadrant together with the origin. -/
theorem conicHull_reciprocalEpigraphOnPositiveRay_eq_openPositiveQuadrant_or_origin :
    (hull ℝ Q : Set (ℝ × ℝ)) =
      (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) ∪ ({0} : Set (ℝ × ℝ)) := by
  let positiveQuadrantOrOrigin : PointedCone ℝ (ℝ × ℝ) :=
    PointedCone.ofConeComb
      ({x : ℝ × ℝ | x = 0 ∨ 0 < x.1 ∧ 0 < x.2})
      ⟨0, Or.inl rfl⟩
      (fun x hx y hy a ha b hb ↦ by
        rcases hx with rfl | hx
        · rcases hy with rfl | hy
          · exact Or.inl (by simp)
          · rcases eq_or_lt_of_le hb with rfl | hb
            · exact Or.inl (by simp)
            · exact Or.inr (by
                simpa using And.intro (mul_pos hb hy.1) (mul_pos hb hy.2))
        · rcases hy with rfl | hy
          · rcases eq_or_lt_of_le ha with rfl | ha
            · exact Or.inl (by simp)
            · exact Or.inr (by
                simpa using And.intro (mul_pos ha hx.1) (mul_pos ha hx.2))
          · rcases eq_or_lt_of_le ha with rfl | ha
            · rcases eq_or_lt_of_le hb with rfl | hb
              · exact Or.inl (by simp)
              · exact Or.inr (by
                  simpa using And.intro (mul_pos hb hy.1) (mul_pos hb hy.2))
            · rcases eq_or_lt_of_le hb with rfl | hb
              · exact Or.inr (by
                  simpa using And.intro (mul_pos ha hx.1) (mul_pos ha hx.2))
              · exact Or.inr
                  ⟨add_pos (mul_pos ha hx.1) (mul_pos hb hy.1),
                    add_pos (mul_pos ha hx.2) (mul_pos hb hy.2)⟩)
  have hHull :
      hull ℝ Q ≤ positiveQuadrantOrOrigin := by
    refine Submodule.span_le.mpr ?_
    intro y hy
    have hy' := (mem_reciprocalEpigraphOnPositiveRay_iff y).1 hy
    exact Or.inr ⟨hy'.1, lt_of_lt_of_le (one_div_pos.mpr hy'.1) hy'.2⟩
  ext x
  constructor
  · intro hx
    rcases hHull hx with rfl | hx
    · exact Or.inr (by simp)
    · exact Or.inl (by simpa using hx)
  · rintro (hx | rfl)
    · have hx : 0 < x.1 ∧ 0 < x.2 := by simpa using hx
      let r : ℝ := Real.sqrt (x.1 * x.2)
      have hr_pos : 0 < r := by
        dsimp [r]
        exact Real.sqrt_pos.2 (mul_pos hx.1 hx.2)
      let y : ℝ × ℝ := (x.1 / r, x.2 / r)
      have hy_mem : y ∈ Q := by
        refine (mem_reciprocalEpigraphOnPositiveRay_iff y).2 ?_
        constructor
        · dsimp [y]
          exact div_pos hx.1 hr_pos
        · dsimp [y]
          have hr_sq : r ^ 2 = x.1 * x.2 := by
            dsimp [r]
            rw [Real.sq_sqrt (mul_nonneg hx.1.le hx.2.le)]
          have hInv : 1 / (x.1 / r) = r / x.1 := by
            field_simp [hr_pos.ne', hx.1.ne']
          rw [hInv]
          have hEq : r ^ 2 / x.1 = x.2 := by
            field_simp [hx.1.ne']
            nlinarith [hr_sq]
          have hdiv : r / x.1 ≤ x.2 / r := by
            rw [le_div_iff₀ hr_pos]
            have hmul : r / x.1 * r = r ^ 2 / x.1 := by
              field_simp [hx.1.ne']
            rw [hmul]
            exact hEq.le
          exact hdiv
      have hy_hull : y ∈ (hull ℝ Q : Set (ℝ × ℝ)) :=
        subset_hull hy_mem
      have hx_eq : x = r • y := by
        ext <;> dsimp [y] <;> field_simp [hr_pos.ne']
      rw [hx_eq]
      exact (hull ℝ Q).smul_mem hr_pos.le hy_hull
    · exact (hull ℝ Q).zero_mem

/-- Membership in `𝒦(Q)` means either being the origin or having both coordinates strictly
positive. -/
theorem mem_conicHull_reciprocalEpigraphOnPositiveRay_iff (x : ℝ × ℝ) :
    x ∈ (hull ℝ Q : Set (ℝ × ℝ)) ↔
      x = 0 ∨ 0 < x.1 ∧ 0 < x.2 := by
  rw [conicHull_reciprocalEpigraphOnPositiveRay_eq_openPositiveQuadrant_or_origin]
  simp [or_comm]

/-! ### Lemma_2_28 (from Chap02) -/
section

/-
Primary domain: scalar logarithmic stopping-index bounds coming from one-step exponential
comparisons.

Owner abstractions sampled before refining:
- `stoppingIndex_le_one_add_sqrt_condition_log_ratio` in `Lemma_2_27.lean`, the Chapter 2 owner
  theorem for one-step logarithmic stopping-index bounds;
- the accumulated-sum helper later used in `Proposition_2_33.lean`, which consumes the same
  one-step logarithmic bound termwise;
- `Real.log_mul` for the canonical combination of the constant logarithm
  `log (2 * (Qf - 1) / κ)` with the terminal ratio `log (ΔNext / ε)`;
- `Nat.cast_add` together with the standard cast arithmetic reducing the predecessor relation
  `jStar = jPrev + 1` to the owner exponent `((jStar : ℝ) - 1)`.

Best owner abstraction:
- the source-facing owner theorem
  `stoppingIndex_le_one_add_sqrt_condition_log_ratio`.

Source/core/bridge triage:
- source-facing: the textbook terminal stopping-index estimate of Lemma 2.28;
- core/canonical: `stoppingIndex_le_one_add_sqrt_condition_log_ratio`;
- bridge/view: the comparison chain through `previousInternalValue` and `objectiveGap`, which is
  kept only as proof input and not packaged as a parallel owner API.

Primitive data:
- the predecessor index `jPrev`, the terminal gap `ΔNext`, and the target accuracy `ε`;
- the source comparison data `previousInternalValue` and `objectiveGap`.

Derived API:
- the displayed logarithmic bound for `jStar`, obtained by deriving the one-step estimate on `ε`
  and then specializing the owner theorem to the single step `k = 0`.

The positivity of `ΔNext` needed for the terminal logarithm is derived from `ε > 0` and the
comparison chain `ε ≤ previousInternalValue ≤ ((Qf - 1) / κ) * objectiveGap ≤ ... * ΔNext`, so no
separate terminal-gap positivity hypothesis is kept as primitive data.
-/

/-- Lemma 2.28: if `Q_f > 1`, `κ > 0`, `ε > 0`, and if for the predecessor
index `j = j^* - 1` one has
`ε ≤ f^*(t_{N+1}; x_{N+1}, j; L) ≤ ((Q_f - 1) / κ) * (f(t_{N+1}; x_{N+1}, j) - f^*(t_{N+1}))`
and
`((Q_f - 1) / κ) * (f(t_{N+1}; x_{N+1}, j) - f^*(t_{N+1}))`
`≤ (2 * (Q_f - 1) / κ) * e^{-j / √Q_f} * Δ_{N+1}`,
then `j^* ≤ 1 + √Q_f * log (2 (Q_f - 1) Δ_{N+1} / (κ ε))`. -/
-- Proof sketch: specialize Lemma 2.27 to the one-step sequence with `Δ 0 = ΔNext` and
-- `Δ 1 = ε`. The assumed comparison chain gives the one-step estimate required by the owner
-- theorem from Lemma 2.27. The same chain forces `ΔNext > 0`, and then `Real.log_mul` combines
-- `log (2 * (Qf - 1) / κ)` with `log (ΔNext / ε)`.
lemma accuracyStoppingIndex_le_one_add_sqrt_condition_log_ratio
    (Qf κ ε ΔNext : ℝ) (jStar jPrev : ℕ)
    {previousInternalValue objectiveGap : ℝ}
    (hQf : 1 < Qf) (hκ : 0 < κ) (hε : 0 < ε)
    (hjStar : jStar = jPrev + 1)
    (hLower : ε ≤ previousInternalValue)
    (hMiddle : previousInternalValue ≤ ((Qf - 1) / κ) * objectiveGap)
    (hUpper :
      ((Qf - 1) / κ) * objectiveGap ≤
        (2 * (Qf - 1) / κ) * Real.exp (-((jPrev : ℝ) / Real.sqrt Qf)) * ΔNext) :
    (jStar : ℝ) ≤
      1 + Real.sqrt Qf * Real.log ((2 * (Qf - 1) * ΔNext) / (κ * ε)) := by
  let c : ℝ := 2 * (Qf - 1) / κ
  let j : ℕ → ℝ := fun _ ↦ jStar
  let Δ : ℕ → ℝ := fun k ↦ if k = 0 then ΔNext else ε
  have hΔ_pos : ∀ ⦃k : ℕ⦄, k ≤ 0 → 0 < Δ (k + 1) := by
    intro k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst hk0
    simp [Δ, hε]
  have hjPrev : (jPrev : ℝ) = (jStar : ℝ) - 1 := by
    norm_num [hjStar]
  have hstep_bound :
      ε ≤
        c *
          Real.exp (-(((jStar : ℝ) - 1) / Real.sqrt Qf)) *
          ΔNext := by
    calc
      ε ≤ previousInternalValue := hLower
      _ ≤ ((Qf - 1) / κ) * objectiveGap := hMiddle
      _ ≤ c * Real.exp (-((jPrev : ℝ) / Real.sqrt Qf)) * ΔNext := by
            simpa [c] using hUpper
      _ = c * Real.exp (-(((jStar : ℝ) - 1) / Real.sqrt Qf)) * ΔNext := by
            rw [hjPrev]
  have hΔ_succ_bound :
      ∀ ⦃k : ℕ⦄, k ≤ 0 →
        Δ (k + 1) ≤
          c *
            Real.exp (-((j k - 1) / Real.sqrt Qf)) *
            Δ k := by
    intro k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst hk0
    simpa [j, Δ] using hstep_bound
  have hbound :
      j 0 ≤
        1 + Real.sqrt Qf * Real.log c +
          Real.sqrt Qf * Real.log (Δ 0 / Δ (0 + 1)) :=
    stoppingIndex_le_one_add_sqrt_condition_log_ratio
      Qf κ 0 j Δ hQf hκ hΔ_pos hΔ_succ_bound (by simp)
  have hQf_sub_pos : 0 < Qf - 1 := sub_pos.mpr hQf
  have hconst_pos : 0 < c := by
    dsimp [c]
    exact div_pos (mul_pos (show (0 : ℝ) < 2 by norm_num) hQf_sub_pos) hκ
  have hterminal_pos :
      0 < c * Real.exp (-((jPrev : ℝ) / Real.sqrt Qf)) * ΔNext := by
    exact lt_of_lt_of_le hε <| le_trans hLower <| le_trans hMiddle hUpper
  have hterminal_factor_pos : 0 < c * Real.exp (-((jPrev : ℝ) / Real.sqrt Qf)) := by
    exact mul_pos hconst_pos (Real.exp_pos _)
  have hΔNext : 0 < ΔNext := by
    exact pos_of_mul_pos_right
      (by simpa [c, mul_assoc] using hterminal_pos)
      hterminal_factor_pos.le
  have hratio_pos : 0 < ΔNext / ε := div_pos hΔNext hε
  have hlog : Real.log c + Real.log (ΔNext / ε) =
        Real.log ((2 * (Qf - 1) * ΔNext) / (κ * ε)) := by
    calc
      Real.log c + Real.log (ΔNext / ε) =
          Real.log (c * (ΔNext / ε)) := by
            symm
            rw [Real.log_mul hconst_pos.ne' hratio_pos.ne']
      _ = Real.log ((2 * (Qf - 1) * ΔNext) / (κ * ε)) := by
            congr 1
            dsimp [c]
            field_simp [hκ.ne', hε.ne']
  calc
    (jStar : ℝ) ≤
        1 + Real.sqrt Qf * Real.log c +
          Real.sqrt Qf * Real.log (ΔNext / ε) := by
            simpa [c, j, Δ] using hbound
    _ = 1 + Real.sqrt Qf * (Real.log c + Real.log (ΔNext / ε)) := by
          ring
    _ = 1 + Real.sqrt Qf * Real.log ((2 * (Qf - 1) * ΔNext) / (κ * ε)) := by
          rw [hlog]

end

/-! ### Proposition_2_28 (from Chap02) -/
noncomputable section

universe u

namespace LagrangianProblem

variable {Q : Type u} {m : ℕ}

/- Proposition 2.28 lies in the auxiliary max-violation value-function domain for
inequality-constrained problems.

Sampled owner declarations before refining:
- `LagrangianProblem.constrainedAuxiliaryObjective` in `Lemma_2_21`, the canonical owner
  `x ↦ max {f₀(x) - t, f₁(x), …, fₘ(x)}`;
- `LagrangianProblem.constrainedAuxiliaryOptimalValue` in `Lemma_2_21`, the owner value
  `f^*(t)` as an `EReal` infimum;
- `LagrangianProblem.constrainedAuxiliaryOptimalValue_eq_of_isMinOn` in `Lemma_2_21`, the
  attained-value bridge from the owner infimum to a real minimizer evaluation;
- `LagrangianProblem.objective_sub_le_constrainedAuxiliaryObjective` and
  `LagrangianProblem.constraint_le_constrainedAuxiliaryObjective` in `Lemma_2_21`, the canonical
  component bounds extracted from the owner auxiliary objective.

Best owner abstraction:
- core/canonical: `problem : LagrangianProblem Q m` together with its derived auxiliary objective
  and auxiliary optimal value;
- source-facing: Proposition 2.28's bounds for an exact minimizer of the owner auxiliary
  objective;
- bridge/view: the attained-minimum identity
  `problem.constrainedAuxiliaryOptimalValue_eq_of_isMinOn`.

Primitive data:
- the owner problem `problem : LagrangianProblem Q m`;
- the parameter `t`;
- an exact minimizer witness `hx : IsMinOn (problem.constrainedAuxiliaryObjective t) Set.univ x`.

Derived API:
- the real inequality `problem.constrainedAuxiliaryObjective t x ≤ ε` obtained from the owner
  value bound `problem.constrainedAuxiliaryOptimalValue t ≤ ε`;
- the source-facing Proposition 2.28 bounds extracted directly from the owner component
  inequalities in `Lemma_2_21`.

The refined API keeps Proposition 2.28 at the owner level and avoids a parallel global wrapper.
The trivial attained-value step is the only companion theorem kept here; the proposition itself
uses the owner component inequalities directly rather than introducing extra wrapper lemmas for
their arithmetic consequences. The source-facing proposition keeps the explicit side condition
`t ≤ tStar` as a theorem input rather than a nested implication in the conclusion.
-/

section ExactMinimizerBounds

variable (problem : LagrangianProblem Q m)

/-- An exact minimizer of the auxiliary objective inherits any upper bound on the owner auxiliary
optimal value. -/
theorem constrainedAuxiliaryObjective_le_of_optimalValue_le_of_isMinOn
    {t ε : ℝ} {x : Q}
    (hx : IsMinOn (problem.constrainedAuxiliaryObjective t) Set.univ x)
    (hopt : problem.constrainedAuxiliaryOptimalValue t ≤ ε) :
    problem.constrainedAuxiliaryObjective t x ≤ ε := by
  simpa [problem.constrainedAuxiliaryOptimalValue_eq_of_isMinOn hx] using hopt

/-- Proposition 2.28: if the owner auxiliary optimal value at `tk` is at most `ε`, then any exact
minimizer `xStar` of the owner auxiliary objective at `tk` satisfies `f₀(xStar) ≤ tStar + ε` and
every constraint value `fᵢ(xStar)` is at most `ε`, provided `tk ≤ tStar`. The companion theorem
`constrainedAuxiliaryObjective_le_of_optimalValue_le_of_isMinOn` records the attained-value bound
on the auxiliary objective itself. -/
theorem objective_and_constraint_bounds_of_constrainedAuxiliaryOptimalValue_le
    {tk ε tStar : ℝ} {xStar : Q}
    (hxStar : IsMinOn (problem.constrainedAuxiliaryObjective tk) Set.univ xStar)
    (hopt : problem.constrainedAuxiliaryOptimalValue tk ≤ ε)
    (htk : tk ≤ tStar) :
    problem xStar ≤ tStar + ε ∧
      ∀ i : Fin m, problem.constraints i xStar ≤ ε := by
  have haux :
      problem.constrainedAuxiliaryObjective tk xStar ≤ ε :=
    problem.constrainedAuxiliaryObjective_le_of_optimalValue_le_of_isMinOn hxStar hopt
  constructor
  · have hobjective : problem xStar - tk ≤ ε :=
      (problem.objective_sub_le_constrainedAuxiliaryObjective tk xStar).trans haux
    linarith
  · intro i
    exact (problem.constraint_le_constrainedAuxiliaryObjective tk xStar i).trans haux

end ExactMinimizerBounds

end LagrangianProblem

/-! ### Theorem_2_28 (from Chap02) -/
open AffineMap
open PointedCone (hull)
open scoped Pointwise

/-!
Theorem 2.28 lies in the convex-geometry and topological-closure domain for subsets of
finite-dimensional real normed spaces.

Sampled owner-style declarations:
* `PointedCone.hull` together with `PointedCone.convex`
* `IsClosed.add_left_of_isCompact` and `IsClosed.add_right_of_isCompact`
* `Convex.convexJoin`, `segment_eq_image_lineMap`, and
  `AffineMap.lineMap_continuous_uncurry`
* `Convex.affine_image`, `Convex.affine_preimage`, `IsClosed.preimage`,
  `Metric.isCompact_iff_isClosed_bounded`, and `IsCompact.image`

Best owner abstractions:
* `PointedCone ℝ E` for conic hulls
* `IsCompact Q` for the compact-source bridge items
* `Convex ℝ s` for convexity-preservation items
* `IsClosed s` and `IsCompact s` for the finite-dimensional closedness bridges
* affine maps `E₁ →ᵃ[ℝ] E₂` for the image/preimage items, with compactness supplying the
  closed-image bridge

Primitive data:
* finite-dimensional real normed spaces `E`, `E₁`
* real normed codomains `E₂`
* sets `Q₁`, `Q₂`
* an affine map `f`

Derived API:
* direct owner recalls for the intersection, product, convex-join, and affine image/preimage
  closure rules
* the compact-source bridge theorem for item (8)
* the source-facing finite-dimensional bridge statements in items (4), (8), (10), and (12)

Source/core/bridge triage:
* direct owner recall/use: items (1), (2), (3), (5), (6), (7), (9), (11), (13), and (14)
* source-facing bridge items: (4), (10), and (12)
* bridge/view compact-source core: item (8) as `isClosed_hull_of_isCompact_of_zero_not_mem`
* derived source-facing corollary: the Euclidean-style closed-and-bounded form of item (8)

This file therefore reuses direct owner recalls wherever the exact API already exists, keeps the
compact-source core visible where compactness is the real primitive input, and derives the
textbook closed-and-bounded corollaries from that core.
-/

/- Theorem 2.28 (1), (2), (3), and (9) are direct owner recalls. -/
recall Convex.inter
recall IsClosed.inter
recall Convex.add
recall Convex.convexJoin

section FiniteDimensionalReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {Q₁ Q₂ : Set E}

/-- Theorem 2.28 (1): source item (4). The Minkowski sum of two closed subsets of `ℝⁿ` is closed
if one summand is bounded. -/
-- Proof sketch: in finite dimensions, the closed bounded summand is compact, so apply
-- `IsClosed.add_left_of_isCompact` or `IsClosed.add_right_of_isCompact`.
theorem isClosed_add_of_isClosed_of_isBounded
    (hQ₁_closed : IsClosed Q₁) (hQ₂_closed : IsClosed Q₂)
    (hbounded : Bornology.IsBounded Q₁ ∨ Bornology.IsBounded Q₂) :
    IsClosed (Q₁ + Q₂) := by
  rcases hbounded with hQ₁_bounded | hQ₂_bounded
  · simpa using hQ₂_closed.add_left_of_isCompact
      (Metric.isCompact_of_isClosed_isBounded hQ₁_closed hQ₁_bounded)
  · simpa using hQ₁_closed.add_right_of_isCompact
      (Metric.isCompact_of_isClosed_isBounded hQ₂_closed hQ₂_bounded)

end FiniteDimensionalReal

/- Theorem 2.28 (7) is the direct owner declaration `PointedCone.convex`
specialized to `hull ℝ Q₁`. -/
recall PointedCone.convex

section RealNormed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Q₁ : Set E}

/-- Helper for Theorem 2.28: a point in the pointed hull of a convex set is either `0` or a
positive multiple of a point of the set. -/
theorem mem_pointed_hull_of_convex_iff (hQ₁_convex : Convex ℝ Q₁) {z : E} :
    z ∈ ((hull ℝ Q₁ : PointedCone ℝ E) : Set E) ↔
      z = 0 ∨ ∃ r : ℝ, 0 < r ∧ z ∈ r • Q₁ := by
  constructor
  · intro hz
    -- Expand pointed-hull membership into a finite conical combination.
    have hz' := (PointedCone.mem_hull_set (R := ℝ) (s := Q₁) (x := z)).1 hz
    rcases hz' with ⟨c, hcQ₁, hnonneg, rfl⟩
    let r : ℝ := c.sum fun x a => a
    by_cases hr : r = 0
    · left
      -- If the total coefficient sum vanishes, every nonnegative coefficient vanishes.
      have hzero : ∀ x ∈ c.support, c x = 0 := by
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun x hx => hnonneg x)).1 (by
          simpa [r, Finsupp.sum] using hr)
      change ∑ x ∈ c.support, c x • x = 0
      apply Finset.sum_eq_zero
      intro x hx
      simp [hzero x hx]
    · right
      -- Otherwise, normalize by the positive total weight and use convexity.
      have hrpos : 0 < r := by
        exact lt_of_le_of_ne (Finsupp.sum_nonneg' (fun x => hnonneg x)) (Ne.symm hr)
      refine ⟨r, hrpos, ?_⟩
      refine Set.mem_smul_set.mpr ?_
      refine ⟨c.support.centerMass (fun x => c x) id, ?_, ?_⟩
      · apply hQ₁_convex.centerMass_mem
        · intro x hx
          exact hnonneg x
        · simpa [r, Finsupp.sum] using hrpos
        · intro x hx
          exact hcQ₁ hx
      · have hr' : (∑ x ∈ c.support, c x) ≠ 0 := by
          simpa [r, Finsupp.sum] using hr
        simp [r, Finsupp.sum, Finset.centerMass, hr', smul_smul]
  · intro hz
    rcases hz with rfl | ⟨r, hr, x, hxQ₁, rfl⟩
    · exact (hull ℝ Q₁).zero_mem
    · exact (hull ℝ Q₁).smul_mem hr.le (PointedCone.subset_hull hxQ₁)

omit [NormedSpace ℝ E] in
/-- Helper for Theorem 2.28: a compact set away from the origin has uniform positive and finite
norm bounds. -/
theorem exists_norm_bounds_of_isCompact_of_zero_not_mem
    (hQ₁_compact : IsCompact Q₁) (hQ₁_zero : (0 : E) ∉ Q₁) :
    ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ ∀ x ∈ Q₁, δ ≤ ‖x‖ ∧ ‖x‖ ≤ R := by
  -- The minimum norm is positive because `0` is excluded from the compact set.
  obtain ⟨δ, hδpos, hδ⟩ := hQ₁_compact.exists_forall_le' (f := fun x : E => ‖x‖)
    (by simpa using continuous_norm.continuousOn) (a := (0 : ℝ)) (by
      intro x hx
      exact norm_pos_iff.mpr (by exact fun hx0 => hQ₁_zero (hx0 ▸ hx)))
  -- Compactness also gives a uniform upper norm bound.
  obtain ⟨R, hRpos, hR⟩ := Bornology.IsBounded.exists_pos_norm_le (s := Q₁) hQ₁_compact.isBounded
  refine ⟨δ, R, hδpos, hRpos, ?_⟩
  intro x hx
  exact ⟨hδ x hx, hR x hx⟩

/-- Helper for Theorem 2.28: a point in `r • Q₁` bounds the scalar `r` once `Q₁` is uniformly away
from the origin. -/
theorem scalar_le_of_mem_smul_of_norm_lower_bound {δ r : ℝ} {z : E}
    (hδpos : 0 < δ) (hδ : ∀ x ∈ Q₁, δ ≤ ‖x‖)
    (hz : z ∈ r • Q₁) (hr : 0 ≤ r) :
    r ≤ ‖z‖ / δ := by
  rcases Set.mem_smul_set.mp hz with ⟨x, hxQ₁, rfl⟩
  -- Compare `1` with `‖x‖ / δ`, then scale the inequality by `r`.
  have hunit : 1 ≤ ‖x‖ / δ := (one_le_div hδpos).2 (hδ x hxQ₁)
  calc
    r = r * 1 := by ring
    _ ≤ r * (‖x‖ / δ) := by gcongr
    _ = ‖r • x‖ / δ := by
      rw [norm_smul, Real.norm_of_nonneg hr]
      field_simp [hδpos.ne']

/-- Helper for Theorem 2.28: the cone hull of a compact convex subset of a real normed space that
avoids the origin is closed. -/
theorem isClosed_hull_of_isCompact_of_zero_not_mem
    (hQ₁_compact : IsCompact Q₁) (hQ₁_convex : Convex ℝ Q₁) (hQ₁_zero : (0 : E) ∉ Q₁) :
    IsClosed ((hull ℝ Q₁ : PointedCone ℝ E) : Set E) := by
  -- Route correction: normalize pointed-hull membership to positive scalar multiples of `Q₁`,
  -- then run the source-faithful compactness/subsequence argument on those parameters.
  refine IsSeqClosed.isClosed ?_
  intro u z huzmem huz
  by_cases hzero_freq : ∃ᶠ n in Filter.atTop, u n = 0
  · -- If zeros occur frequently, the limit must itself be zero.
    have hz_zero_mem : z ∈ ({0} : Set E) := by
      exact isClosed_singleton.mem_of_frequently_of_tendsto
        (hzero_freq.mono fun n hn => by simp [hn]) huz
    have hz0 : z = 0 := by
      simpa using hz_zero_mem
    exact hz0 ▸ (hull ℝ Q₁).zero_mem
  · obtain ⟨δ, _, hδpos, _, hnorms⟩ :=
      exists_norm_bounds_of_isCompact_of_zero_not_mem hQ₁_compact hQ₁_zero
    have hnonzero : ∀ᶠ n in Filter.atTop, u n ≠ 0 := by
      simpa [Filter.Frequently] using hzero_freq
    rcases (Filter.eventually_atTop.mp hnonzero) with ⟨N, hN⟩
    let v : ℕ → E := fun n ↦ u (n + N)
    have hv_tendsto : Filter.Tendsto v Filter.atTop (nhds z) := by
      simpa [v] using (Filter.tendsto_add_atTop_iff_nat N).2 huz
    have hv_nonzero : ∀ n, v n ≠ 0 := by
      intro n
      exact hN (n + N) (Nat.le_add_left N n)
    have hv_repr : ∀ n, ∃ r : ℝ, ∃ x : E, 0 < r ∧ x ∈ Q₁ ∧ r • x = v n := by
      intro n
      rcases (mem_pointed_hull_of_convex_iff hQ₁_convex).1 (huzmem (n + N)) with hv0 | hmem
      · exact False.elim (hv_nonzero n hv0)
      · rcases hmem with ⟨r, hr, hmem⟩
        rcases Set.mem_smul_set.mp hmem with ⟨x, hxQ₁, hx⟩
        exact ⟨r, x, hr, hxQ₁, hx⟩
    choose r x hrpos hxQ₁ hrepr using hv_repr
    -- Convergence bounds the represented sequence, hence also the scalar parameters.
    obtain ⟨C, _, hC⟩ := Bornology.IsBounded.exists_pos_norm_le (s := Set.range v)
      (Metric.isBounded_range_of_tendsto v hv_tendsto)
    let K : Set (ℝ × E) := Set.Icc (0 : ℝ) (C / δ) ×ˢ Q₁
    have hK_compact : IsCompact K := isCompact_Icc.prod hQ₁_compact
    have hw_mem : ∀ n, (r n, x n) ∈ K := by
      intro n
      refine ⟨⟨(hrpos n).le, ?_⟩, hxQ₁ n⟩
      have hmem : v n ∈ r n • Q₁ := Set.mem_smul_set.mpr ⟨x n, hxQ₁ n, hrepr n⟩
      have hrle := scalar_le_of_mem_smul_of_norm_lower_bound
        hδpos (fun y hy => (hnorms y hy).1) hmem (hrpos n).le
      exact hrle.trans (div_le_div_of_nonneg_right (hC (v n) ⟨n, rfl⟩) hδpos.le)
    obtain ⟨p, hpK, φ, hφmono, hφtendsto⟩ := hK_compact.tendsto_subseq (fun n => hw_mem n)
    rcases p with ⟨β, y⟩
    -- Extract convergent scalar and point subsequences from the compact parameter space.
    have hφtendsto' :
        Filter.Tendsto ((fun n ↦ (r n, x n)) ∘ φ) Filter.atTop (nhds β ×ˢ nhds y) := by
      simpa [nhds_prod_eq] using hφtendsto
    have hr_tendsto : Filter.Tendsto (fun n ↦ r (φ n)) Filter.atTop (nhds β) := hφtendsto'.fst
    have hx_tendsto : Filter.Tendsto (fun n ↦ x (φ n)) Filter.atTop (nhds y) := hφtendsto'.snd
    have hv_sub_tendsto : Filter.Tendsto (v ∘ φ) Filter.atTop (nhds z) :=
      hv_tendsto.comp hφmono.tendsto_atTop
    have hsmul_tendsto :
        Filter.Tendsto (fun n ↦ r (φ n) • x (φ n)) Filter.atTop (nhds (β • y)) :=
      hr_tendsto.smul hx_tendsto
    have hp_eq_z : β • y = z := by
      exact tendsto_nhds_unique_of_eventuallyEq hsmul_tendsto hv_sub_tendsto
        (Filter.Eventually.of_forall fun n => hrepr (φ n))
    rcases hpK with ⟨hβIcc, hyQ₁⟩
    by_cases hβ0 : β = 0
    · have hz0 : z = 0 := by
        simpa [hβ0] using hp_eq_z.symm
      exact hz0 ▸ (hull ℝ Q₁).zero_mem
    · exact (mem_pointed_hull_of_convex_iff hQ₁_convex).2 <|
        Or.inr ⟨β, lt_of_le_of_ne hβIcc.1 (Ne.symm hβ0), Set.mem_smul_set.mpr ⟨y, hyQ₁, hp_eq_z⟩⟩

end RealNormed

section FiniteDimensionalReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {Q₁ Q₂ : Set E}

/-- Theorem 2.28 (2): source item (8). The cone hull of a closed bounded subset of `ℝⁿ` that
avoids the origin is closed. -/
-- Proof sketch: in finite dimensions, a closed bounded set is compact, so apply the compact-source
-- bridge theorem.
theorem isClosed_hull_of_isClosed_of_isBounded_of_zero_not_mem
    (hQ₁_closed : IsClosed Q₁) (hQ₁_bounded : Bornology.IsBounded Q₁)
    (hQ₁_convex : Convex ℝ Q₁) (hQ₁_zero : (0 : E) ∉ Q₁) :
    IsClosed ((hull ℝ Q₁ : PointedCone ℝ E) : Set E) :=
  isClosed_hull_of_isCompact_of_zero_not_mem
    (Metric.isCompact_of_isClosed_isBounded hQ₁_closed hQ₁_bounded) hQ₁_convex hQ₁_zero

omit [FiniteDimensional ℝ E] in
/-- Compact-source bridge for Theorem 2.28 (10): the convex join of two compact subsets of a real
normed space is compact. -/
theorem isCompact_convexJoin
    (hQ₁_compact : IsCompact Q₁) (hQ₂_compact : IsCompact Q₂) :
    IsCompact (convexJoin ℝ Q₁ Q₂) := by
  let K := Q₁ ×ˢ (Q₂ ×ˢ Set.Icc (0 : ℝ) 1)
  let interpolate : E × (E × ℝ) → E := fun pqt ↦ lineMap pqt.1 pqt.2.1 pqt.2.2
  have hK_compact : IsCompact K := by
    simpa [K] using hQ₁_compact.prod (hQ₂_compact.prod isCompact_Icc)
  have hinterpolate_compact : IsCompact (interpolate '' K) := by
    refine hK_compact.image_of_continuousOn ?_
    fun_prop
  have hinterpolate :
      interpolate '' K = convexJoin ℝ Q₁ Q₂ := by
    ext x
    constructor
    · rintro ⟨⟨a, b, t⟩, hmem, rfl⟩
      rcases hmem with ⟨ha, hb, ht⟩
      rw [mem_convexJoin]
      refine ⟨a, ha, b, hb, ?_⟩
      rw [segment_eq_image_lineMap]
      exact ⟨t, ht, rfl⟩
    · rw [mem_convexJoin]
      rintro ⟨a, ha, b, hb, hx⟩
      rw [segment_eq_image_lineMap] at hx
      rcases hx with ⟨t, ht, rfl⟩
      exact ⟨⟨a, b, t⟩, ⟨ha, hb, ht⟩, rfl⟩
  rw [← hinterpolate]
  exact hinterpolate_compact

/-- Theorem 2.28 (3): source item (10). The convex join of two closed bounded subsets of `ℝⁿ` is
closed. -/
-- Proof sketch: realize `convexJoin ℝ Q₁ Q₂` as the image of
-- `Set.Icc (0 : ℝ) 1 ×ˢ Q₁ ×ˢ Q₂` under the continuous interpolation map
-- `(t, x, y) ↦ (1 - t) • x + t • y`, then use compactness of the domain.
theorem isClosed_convexJoin_of_isClosed_of_isBounded
    (hQ₁_closed : IsClosed Q₁) (hQ₂_closed : IsClosed Q₂)
    (hQ₁_bounded : Bornology.IsBounded Q₁) (hQ₂_bounded : Bornology.IsBounded Q₂) :
    IsClosed (convexJoin ℝ Q₁ Q₂) :=
  (isCompact_convexJoin
    (Metric.isCompact_of_isClosed_isBounded hQ₁_closed hQ₁_bounded)
    (Metric.isCompact_of_isClosed_isBounded hQ₂_closed hQ₂_bounded)).isClosed

end FiniteDimensionalReal

/- Theorem 2.28 (5) and (6) are direct owner recalls. -/
recall Convex.prod
recall IsClosed.prod

section Affine

variable {E₁ E₂ : Type*}
variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

variable {Q₁ : Set E₁}
variable (f : E₁ →ᵃ[ℝ] E₂)

/- Theorem 2.28 (11), (13), and (14) are direct owner recalls. For item (14), the textbook
boundedness assumption is auxiliary and does not affect the canonical closed-preimage statement.
For item (12), the local bridge keeps the valid compact-source closed-image consequence. -/
recall Convex.affine_image
recall Convex.affine_preimage
recall IsClosed.preimage

/-- Theorem 2.28 (4): source item (12). The affine image of a closed bounded subset of `ℝⁿ` is
closed in `ℝᵐ`. -/
-- Proof sketch: a closed bounded subset of a finite-dimensional real normed space is compact, and
-- the image of a compact set under a continuous affine map is compact, hence closed.
theorem isClosed_affine_image_of_isClosed_of_isBounded
    (hQ₁_closed : IsClosed Q₁) (hQ₁_bounded : Bornology.IsBounded Q₁) :
    IsClosed (f '' Q₁) := by
  simpa using
    (Metric.isCompact_of_isClosed_isBounded hQ₁_closed hQ₁_bounded).image
      f.continuous_of_finiteDimensional |>.isClosed

end Affine
