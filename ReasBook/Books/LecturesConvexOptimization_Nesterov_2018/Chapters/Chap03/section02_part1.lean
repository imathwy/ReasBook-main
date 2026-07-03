import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_3_2_1 (from Chap03) -/
/-
Corollary 3.2.1 lies in the constrained strong-convexity / relative-subdifferential domain.

Sampled owner-style declarations:
- mathlib `StrongConvexOn`
- `subdifferentialWithin` in `Theorem_3_44`
- `mem_subdifferentialWithin_iff` in `Theorem_3_44`
- `StrongConvexOn.lower_bound_of_mem_subdifferentialWithin` in `Theorem_3_44`

Best owner abstraction:
- core/canonical: the generic lower-bound theorem
  `StrongConvexOn.lower_bound_of_mem_subdifferentialWithin`
- supporting owner notions: `StrongConvexOn Q μ f` and `g ∈ ∂[Q] f(x)`

Source/core/bridge triage:
- source-facing: Corollary 3.2.1, the quadratic affine lower bound produced by a feasible
  subgradient of a strongly convex function
- core/canonical: `StrongConvexOn.lower_bound_of_mem_subdifferentialWithin`
- bridge/view: none; this file is a direct recall of the owner theorem

Primitive data:
- an inner-product space, feasible set `Q`, objective `f`, modulus `μ`, base point `x`,
  comparison point `y`, and vector `g`
- the owner hypotheses `StrongConvexOn Q μ f`, `g ∈ ∂[Q] f(x)`, and `y ∈ Q`

Derived API:
- the quadratic affine lower bound at `y`

The earlier chapter duplicates of `subdifferentialWithin` are Euclidean-specialized, while
`Theorem_3_44` is the generic inner-product-space owner needed here. This corollary therefore
keeps the owner theorem itself as the public center and adds no parallel local wrapper.
-/
recall StrongConvexOn.lower_bound_of_mem_subdifferentialWithin

/-! ### Definition_3_2_1 (from Chap03) -/
/- Definition 3.2.1 lies in the cutting-plane localization-set / localization-radius domain.

Primary mathematical domain:
- cutting-plane localization sets in real inner-product spaces together with their associated
  pointwise and best localization radii.

Sampled owner-style declarations:
- `localizationSet`
- `mem_localizationSet_iff`
- `subgradientLocalizationMeasure`
- `localization_radius`

Best owner abstraction for this file:
- `source-facing`: the stage localization set `localizationSet Q xSeq gSeq k`, the associated
  pointwise radii `subgradientLocalizationMeasure g xStar (xSeq i)`, and their minimum
  `localization_radius xStar g xSeq k`
- `core/canonical`: the same project owners from `Lemma_3_2_1` and `Theorem_3_2_9`
- `bridge/view`: `localization_radius_le_measure` and the closed-ball comparison theorems
  `closedBall_subset_localizationSet_of_le_localization_radius` and
  `le_localization_radius_of_closedBall_subset_localizationSet`

Primitive data:
- a feasible region `Q`
- a reference point `xStar`
- a query-point sequence `xSeq`
- either a cut sequence `gSeq` for `S_k`, or the chosen subgradient selection `g` feeding the
  generic owner `subgradientLocalizationMeasure` behind `v_i` and `v_k^*`
- a stage index `k`

Derived API:
- the defining expansion of `S_k` via `mem_localizationSet_iff`
- the comparison `v_k^* ≤ v_i` via `localization_radius_le_measure`
- the centered-ball characterization of `v_k^*` via the closed-ball inclusion and converse
  theorems

This file stays at the source-facing layer: it recalls the canonical owners for `S_k`, the
associated radii `v_i` and `v_k^*`, and the ball characterization of `v_k^*`, without introducing
any local wrapper or parallel chapter API. -/

recall localizationSet

recall mem_localizationSet_iff

recall subgradientLocalizationMeasure

recall localization_radius

recall localization_radius_le_measure

recall closedBall_subset_localizationSet_of_le_localization_radius

recall le_localization_radius_of_closedBall_subset_localizationSet

/-! ### Lemma_3_2_1 (from Chap03) -/
noncomputable section

universe u

section

variable {X : Type u} [MetricSpace X]

/-- The pointwise growth function `ω_f(xBar; t)` is the supremum of the increments
`f y - f xBar` over the closed ball of radius `t` around `xBar`, recorded in `WithTop ℝ` so that
unbounded growth is represented by `⊤`; it is set to `0` for negative radii. -/
def pointwiseGrowthFunction (f : X → ℝ) (xBar : X) (t : ℝ) : WithTop ℝ :=
  if 0 ≤ t then
    sSup ((fun y : X ↦ ((f y - f xBar : ℝ) : WithTop ℝ)) '' Metric.closedBall xBar t)
  else
    0

/- Source-facing Lean notation for the textbook growth profile `ω_f(xBar; t)`. -/
scoped[PointwiseGrowthFunction] notation:max "ω[" f ";" xBar "]" =>
  pointwiseGrowthFunction f xBar

open scoped PointwiseGrowthFunction

/-- The growth function is `0` at every negative radius. -/
-- Proof sketch: unfold `pointwiseGrowthFunction` and simplify the defining `if` using `t < 0`.
theorem pointwiseGrowthFunction_eq_zero_of_neg
    {f : X → ℝ} {xBar : X} {t : ℝ} (ht : t < 0) :
    ω[f; xBar] t = 0 := by
  simp [pointwiseGrowthFunction, not_le_of_gt ht]

end

section

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {f : V → ℝ} {g : V → V}

open scoped PointwiseGrowthFunction

/-- The localization measure `v_f(xBar; x)` associated to a chosen subgradient selection `g`,
generalized from the textbook Euclidean setting to an arbitrary real inner product space. It is
the signed projection of `x - xBar` onto the normalized subgradient direction at `x`, and it is
defined to be `0` when the chosen subgradient vanishes. -/
def subgradientLocalizationMeasure (g : V → V) (xBar x : V) : ℝ :=
  by
    classical
    exact if g x = 0 then 0 else inner ℝ (g x) (x - xBar) / ‖g x‖

/- Source-facing Lean notation for the textbook localization measure `v_f(xBar; x)`, with the
chosen subgradient selection `g` supplying the formalized owner data. -/
scoped[SubgradientLocalizationMeasure] notation:max "v[" g ";" xBar "]" =>
  subgradientLocalizationMeasure g xBar

open scoped SubgradientLocalizationMeasure

/-- The localization measure vanishes whenever the chosen subgradient at `x` is `0`. -/
-- Proof sketch: unfold `subgradientLocalizationMeasure` and simplify the defining `if` by the
-- assumption `g x = 0`.
theorem subgradientLocalizationMeasure_eq_zero_of_eq_zero
    {xBar x : V} (hg : g x = 0) :
    v[g; xBar] x = 0 := by
  classical
  simp [subgradientLocalizationMeasure, hg]

/-- For a nonzero chosen subgradient, the localization measure is the normalized inner product
`⟪g x, x - xBar⟫ / ‖g x‖`. -/
-- Proof sketch: unfold `subgradientLocalizationMeasure`; the defining `if` reduces to its
-- nonzero branch under the hypothesis `g x ≠ 0`.
theorem subgradientLocalizationMeasure_eq_inner_div_norm_of_ne_zero
    {xBar x : V} (hg : g x ≠ 0) :
    v[g; xBar] x = inner ℝ (g x) (x - xBar) / ‖g x‖ := by
  classical
  simp [subgradientLocalizationMeasure, hg]

/-- If `g x` is a subgradient at `x` and `xBar` does not have larger function value than `x`,
then the localization measure relative to `xBar` is nonnegative. -/
theorem subgradientLocalizationMeasure_nonneg_of_isSubgradientAt
    {xBar x : V}
    (hgx : IsSubgradientAt (fun y ↦ (f y : WithTop ℝ)) x (g x))
    (hfx : f xBar ≤ f x) :
    0 ≤ v[g; xBar] x := by
  classical
  by_cases hzero : g x = 0
  · simp [subgradientLocalizationMeasure, hzero]
  · rw [subgradientLocalizationMeasure_eq_inner_div_norm_of_ne_zero hzero]
    exact
      div_nonneg
        (hgx.nonneg_inner_sub_of_le (by exact_mod_cast hfx))
        (norm_nonneg _)

/-- Helper for Lemma 3.2.1: evaluating the subgradient inequality at `xBar` bounds the increment
`f x - f xBar` by the pairing with `x - xBar`. -/
theorem subgradient_gap_le_inner_sub
    {xBar x : V}
    (hgx : IsSubgradientAt (fun y ↦ (f y : WithTop ℝ)) x (g x)) :
    f x - f xBar ≤ inner ℝ (g x) (x - xBar) := by
  -- Evaluate the real-valued subgradient inequality at the comparison point `xBar`.
  have hgx' : ∀ y : V, f y ≥ f x + inner ℝ (g x) (y - x) :=
    IsSubgradientAt.coe_real_iff.mp hgx
  have hbar : f x + inner ℝ (g x) (xBar - x) ≤ f xBar := by
    linarith [hgx' xBar]
  -- Rewrite the pairing against `xBar - x` as the negative of the pairing against `x - xBar`.
  have hinner : inner ℝ (g x) (xBar - x) = -inner ℝ (g x) (x - xBar) := by
    rw [show xBar - x = -(x - xBar) by
      rw [sub_eq_neg_add, sub_eq_add_neg, neg_add_rev, neg_neg, add_comm]]
    rw [inner_neg_right]
  linarith

/-- Helper for Lemma 3.2.1: the growth function is nonnegative at every nonnegative radius
because `xBar` itself contributes the increment `0` to the defining supremum. -/
theorem pointwiseGrowthFunction_nonneg_of_nonneg_radius
    {xBar : V} {t : ℝ} (ht : 0 ≤ t) :
    ((0 : ℝ) : WithTop ℝ) ≤ ω[f; xBar] t := by
  -- Insert the center point `xBar` into the image set defining the supremum.
  rw [pointwiseGrowthFunction, if_pos ht]
  have hzero_mem :
      (0 : WithTop ℝ) ∈
        (fun y : V ↦ ((f y - f xBar : ℝ) : WithTop ℝ)) '' Metric.closedBall xBar t := by
    simpa using Set.mem_image_of_mem
      (fun y : V ↦ ((f y - f xBar : ℝ) : WithTop ℝ))
      (Metric.mem_closedBall_self ht)
  exact le_csSup ⟨⊤, fun _ _ ↦ le_top⟩ hzero_mem

/-- Helper for Lemma 3.2.1: when the localization measure is nonnegative and the chosen
subgradient is nonzero, the source proof's ray point lies on the radius-`v_f(xBar; x)` sphere
and has function value at least `f x`. -/
theorem exists_localization_contact_point
    {xBar x : V}
    (hgx : IsSubgradientAt (fun y ↦ (f y : WithTop ℝ)) x (g x))
    (hgz : g x ≠ 0)
    (hv : 0 ≤ v[g; xBar] x) :
    ∃ yBar : V, yBar ∈ Metric.closedBall xBar (v[g; xBar] x) ∧ f x ≤ f yBar := by
  let yBar : V := xBar + (v[g; xBar] x / ‖g x‖) • g x
  have hnorm_pos : 0 < ‖g x‖ := norm_pos_iff.mpr hgz
  have hloc :
      v[g; xBar] x = inner ℝ (g x) (x - xBar) / ‖g x‖ :=
    subgradientLocalizationMeasure_eq_inner_div_norm_of_ne_zero (g := g) (xBar := xBar) (x := x) hgz
  -- The chosen point is exactly at distance `v[g; xBar] x` from `xBar`.
  have hyBall : yBar ∈ Metric.closedBall xBar (v[g; xBar] x) := by
    rw [Metric.mem_closedBall]
    have hdist :
        dist yBar xBar = v[g; xBar] x := by
      have hshift :
          ‖(v[g; xBar] x / ‖g x‖) • g x‖ = v[g; xBar] x := by
        rw [norm_smul, Real.norm_of_nonneg (div_nonneg hv (norm_nonneg _))]
        field_simp [hnorm_pos.ne']
      simpa [yBar, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hshift
    exact le_of_eq hdist
  -- The ray point makes the pairing with `g x` vanish, so the subgradient inequality gives
  -- `f x ≤ f yBar`.
  have hy_inner : inner ℝ (g x) (yBar - x) = 0 := by
    calc
      inner ℝ (g x) (yBar - x)
          = inner ℝ (g x) (xBar - x) + inner ℝ (g x) ((v[g; xBar] x / ‖g x‖) • g x) := by
              simp [yBar, sub_eq_add_neg, inner_add_right, add_comm, add_left_comm, add_assoc]
      _ = inner ℝ (g x) (xBar - x) + v[g; xBar] x * ‖g x‖ := by
            rw [inner_smul_right, real_inner_self_eq_norm_sq]
            field_simp [hnorm_pos.ne']
      _ = inner ℝ (g x) (xBar - x) + inner ℝ (g x) (x - xBar) := by
            rw [hloc]
            have hcancel :
                (inner ℝ (g x) (x - xBar) / ‖g x‖) * ‖g x‖ =
                  inner ℝ (g x) (x - xBar) := by
              field_simp [hnorm_pos.ne']
            rw [hcancel]
      _ = 0 := by
            rw [show inner ℝ (g x) (xBar - x) = -inner ℝ (g x) (x - xBar) by
              rw [show xBar - x = -(x - xBar) by
                rw [sub_eq_neg_add, sub_eq_add_neg, neg_add_rev, neg_neg, add_comm]]
              rw [inner_neg_right]]
            ring
  have hgx' : ∀ y : V, f y ≥ f x + inner ℝ (g x) (y - x) :=
    IsSubgradientAt.coe_real_iff.mp hgx
  have hvalue : f x ≤ f yBar := by
    linarith [hgx' yBar, hy_inner]
  exact ⟨yBar, hyBall, hvalue⟩

/-- Lemma 3.2.1, generalized from the textbook Euclidean setting: if `g x` is a subgradient of
`f` at `x`, then the increment `f x - f xBar` is bounded by the growth function
`ω_f(xBar; v_f(xBar; x))` built from the same chosen value `g x`, i.e. formula `(3.2.11)`. -/
-- Proof sketch: if `g x = 0`, the subgradient inequality at `x` already gives `f x ≤ f xBar`.
-- Otherwise split on the sign of `⟪g x, x - xBar⟫`. In the negative case one again gets
-- `f x ≤ f xBar`, and the radius is negative so the growth function is `0`. In the nonnegative
-- case, set `yBar = xBar + v_f(xBar; x) • (g x / ‖g x‖)`, check that `⟪g x, yBar - x⟫ = 0`,
-- deduce `f yBar ≥ f x` from the subgradient inequality at `x`, and then bound
-- `f yBar - f xBar` by the defining supremum of the growth function at radius `v_f(xBar; x)`.
theorem sub_le_pointwiseGrowthFunction_of_localizationMeasure
    (xBar x : V)
    (hgx : IsSubgradientAt (fun y ↦ (f y : WithTop ℝ)) x (g x)) :
    f x - f xBar ≤ ω[f; xBar] (v[g; xBar] x) := by
  by_cases hzero : g x = 0
  · -- If the chosen subgradient vanishes, the subgradient gap is already nonpositive.
    rw [subgradientLocalizationMeasure_eq_zero_of_eq_zero (g := g) (xBar := xBar) hzero]
    have hgap : f x - f xBar ≤ 0 := by
      simpa [hzero] using subgradient_gap_le_inner_sub (f := f) (g := g) (xBar := xBar) hgx
    exact
      le_trans
        (by exact_mod_cast hgap)
        (pointwiseGrowthFunction_nonneg_of_nonneg_radius (f := f) (xBar := xBar) (t := 0) le_rfl)
  by_cases hv_nonneg : 0 ≤ v[g; xBar] x
  · -- In the source's geometric branch, the ray point gives a witness for the defining supremum.
    obtain ⟨yBar, hyBall, hxyBar⟩ :=
      exists_localization_contact_point (f := f) (g := g) (xBar := xBar) hgx hzero hv_nonneg
    have hgap : f x - f xBar ≤ f yBar - f xBar := by
      linarith
    rw [pointwiseGrowthFunction, if_pos hv_nonneg]
    have hy_mem :
        ((f yBar - f xBar : ℝ) : WithTop ℝ) ∈
          (fun y : V ↦ ((f y - f xBar : ℝ) : WithTop ℝ)) ''
            Metric.closedBall xBar (v[g; xBar] x) := by
      exact Set.mem_image_of_mem (fun y : V ↦ ((f y - f xBar : ℝ) : WithTop ℝ)) hyBall
    exact
      le_trans
        (by exact_mod_cast hgap)
        (le_csSup ⟨⊤, fun _ _ ↦ le_top⟩ hy_mem)
  · -- A negative localization measure forces `f x < f xBar`, so the growth bound is trivial.
    have hv_neg : v[g; xBar] x < 0 := lt_of_not_ge hv_nonneg
    have hlt : f x < f xBar := by
      by_contra hfx
      exact hv_nonneg <|
        subgradientLocalizationMeasure_nonneg_of_isSubgradientAt
          (f := f) (g := g) hgx (le_of_not_gt hfx)
    have hgap : f x - f xBar ≤ 0 := by
      linarith
    rw [pointwiseGrowthFunction_eq_zero_of_neg (f := f) (xBar := xBar) hv_neg]
    exact by exact_mod_cast hgap

/-- If `f` is Lipschitz on the closed ball `Metric.closedBall xBar R` with constant `M`, then the
same increment is bounded by `M` times the positive part of the localization measure whenever
`g x` is a subgradient at `x` and `v_f(xBar; x) ≤ R`, i.e. formula `(3.2.12)`. -/
-- Proof sketch: use the previous geometric construction of `yBar`. When
-- `subgradientLocalizationMeasure g xBar x ≤ 0`, the first inequality gives the claim because the
-- positive part is `0`. When `0 ≤ subgradientLocalizationMeasure g xBar x ≤ R`, the point `yBar`
-- lies in `Metric.closedBall xBar R`, so the Lipschitz estimate bounds `f yBar - f xBar` by
-- `M * subgradientLocalizationMeasure g xBar x`, and hence by `M * max (v_f(xBar; x)) 0`.
theorem sub_le_lipschitz_mul_max_localizationMeasure
    {R : ℝ} {M : NNReal} (xBar x : V)
    (hgx : IsSubgradientAt (fun y ↦ (f y : WithTop ℝ)) x (g x))
    (hLip : LipschitzOnWith M f (Metric.closedBall xBar R))
    (hv : v[g; xBar] x ≤ R) :
    f x - f xBar ≤ (M : ℝ) * max (v[g; xBar] x) 0 := by
  by_cases hzero : g x = 0
  · -- With a zero chosen subgradient, the localization measure is zero and the gap is nonpositive.
    rw [subgradientLocalizationMeasure_eq_zero_of_eq_zero (g := g) (xBar := xBar) hzero]
    have hgap : f x - f xBar ≤ 0 := by
      simpa [hzero] using subgradient_gap_le_inner_sub (f := f) (g := g) (xBar := xBar) hgx
    simpa using hgap
  by_cases hv_nonneg : 0 ≤ v[g; xBar] x
  · -- Reuse the source's contact point and then apply the Lipschitz estimate on the larger ball.
    obtain ⟨yBar, hyBall, hxyBar⟩ :=
      exists_localization_contact_point (f := f) (g := g) (xBar := xBar) hgx hzero hv_nonneg
    have hxBarR : xBar ∈ Metric.closedBall xBar R := Metric.mem_closedBall_self (le_trans hv_nonneg hv)
    have hyR : yBar ∈ Metric.closedBall xBar R :=
      Metric.closedBall_subset_closedBall hv hyBall
    have hdist_le : dist yBar xBar ≤ v[g; xBar] x := by
      simpa [Metric.mem_closedBall] using hyBall
    have hyLip : f yBar - f xBar ≤ (M : ℝ) * v[g; xBar] x := by
      have hbound : f yBar ≤ f xBar + M * dist yBar xBar := hLip.le_add_mul hyR hxBarR
      have hmul :
          (M : ℝ) * dist yBar xBar ≤ (M : ℝ) * v[g; xBar] x := by
        gcongr
      linarith
    have hgap : f x - f xBar ≤ f yBar - f xBar := by
      linarith
    rw [max_eq_left hv_nonneg]
    exact le_trans hgap hyLip
  · -- A negative localization measure again forces a nonpositive gap, while the positive part is `0`.
    have hlt : f x < f xBar := by
      by_contra hfx
      exact hv_nonneg <|
        subgradientLocalizationMeasure_nonneg_of_isSubgradientAt
          (f := f) (g := g) hgx (le_of_not_gt hfx)
    have hgap : f x - f xBar ≤ 0 := by
      linarith
    rw [max_eq_right (le_of_not_ge hv_nonneg)]
    simpa using hgap

end

/-! ### Theorem_3_2_1 (from Chap03) -/
noncomputable section

universe u

/- Theorem 3.2.1 lies in the chapter's nonsmooth first-order black-box complexity domain.

Mandatory domain-style sampling before refinement:
* `IsSubgradientAt` in `Definition_3_1_5`, the chapter owner for valid first-order replies;
* mathlib `ConvexOn`, `IsMinOn`, and `LipschitzOnWith`, the canonical owner predicates for the
  problem-class data;
* mathlib `AffineSubspace.mk'` and `AffineSubspace.mem_mk'`, the canonical owner for an affine
  translate of a linear span;
* `coordinateSubspace k n` with notation `ℝ^{k,n}` in `Chap02/Definition_2_12`, the chapter owner
  for prefix coordinate subspaces in `ℝⁿ`;
* `FirstOrderConvexMinimizationProblem` in `Definition_3_40`, the downstream chapter owner that
  reuses the oracle surface introduced here.

Best owner abstraction:
* source-facing: the class `𝒫(x₀, R, M)`, the oracle owner `FirstOrderOracle`, the
  prefix-support-growth predicate, and the span-based iterate predicate;
* core/canonical: `IsSubgradientAt`, `ConvexOn`, `IsMinOn`, `LipschitzOnWith`, and the affine
  subspace `AffineSubspace.mk' x₀ (...)`, together with the coordinate-subspace owner
  `coordinateSubspace`;
* bridge/view: the pair-valued oracle reply `FirstOrderOracle.answer` and the projection lemmas
  from the source-facing owners.

Primitive data:
* the objective `f`;
* the chosen minimizer `xStar`;
* the oracle reply map `subgradient`;
* the oracle-side prefix-support-growth condition;
* the iterate sequence `xSeq`.

Derived API:
* the component accessors for `𝒫(x₀, R, M)`;
* the pair-valued oracle answer and its coordinate lemmas;
* the zero-step consequence of the affine linear-span owner.

The owner layer is intentionally split by the actual mathematics it uses:
* `IsInLipschitzConvexProblemClass` only needs the normed-space layer for convexity, minimizers,
  closed balls, and Lipschitz continuity;
* `FirstOrderOracle` lives on the chapter's real inner-product-space subgradient owner from
  `Definition_3_1_5`;
* `HasCoordinateSupportGrowth` lives on the chapter coordinate-subspace owner `ℝ^{i,n}`;
* `SatisfiesLinearSpanCondition` only needs affine/span structure.

The hard lower-bound theorem itself remains the textbook `ℝⁿ` specialization on
`EuclideanSpace ℝ (Fin n)`. -/

section LipschitzConvexProblemClass

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A function together with a chosen minimizer lies in the Lipschitz convex class
`𝒫(x₀, R, M)` when the objective is convex on the whole space, the chosen point globally
minimizes it, the starting point `x₀` lies in the closed ball `B₂(x*, R)`, and the objective is
`M`-Lipschitz on that ball. -/
def IsInLipschitzConvexProblemClass
    (x0 : V) (R M : NNReal) (f : V → ℝ) (xStar : V) : Prop :=
  ConvexOn ℝ Set.univ f ∧
    IsMinOn f Set.univ xStar ∧
    x0 ∈ Metric.closedBall xStar R ∧
    LipschitzOnWith M f (Metric.closedBall xStar R)

scoped[LipschitzConvexProblemClass] notation "𝒫(" x0 ", " R ", " M ")" =>
  IsInLipschitzConvexProblemClass x0 R M

open scoped LipschitzConvexProblemClass

namespace IsInLipschitzConvexProblemClass

variable {x0 xStar : V} {R M : NNReal} {f : V → ℝ}

/-- Membership in `𝒫(x₀, R, M)` records whole-space convexity of the objective. -/
theorem convexOn_univ
    (hf : 𝒫(x0, R, M) f xStar) :
    ConvexOn ℝ Set.univ f :=
  hf.1

/-- Membership in `𝒫(x₀, R, M)` records that the chosen point globally minimizes the objective. -/
theorem isMinOn
    (hf : 𝒫(x0, R, M) f xStar) :
    IsMinOn f Set.univ xStar :=
  hf.2.1

/-- Membership in `𝒫(x₀, R, M)` records that `x₀` lies in the controlling closed ball. -/
theorem start_mem_closedBall
    (hf : 𝒫(x0, R, M) f xStar) :
    x0 ∈ Metric.closedBall xStar R :=
  hf.2.2.1

/-- Membership in `𝒫(x₀, R, M)` records the Lipschitz bound on the controlling closed ball. -/
theorem lipschitzOn_closedBall
    (hf : 𝒫(x0, R, M) f xStar) :
    LipschitzOnWith M f (Metric.closedBall xStar R) :=
  hf.2.2.2

end IsInLipschitzConvexProblemClass

end LipschitzConvexProblemClass

section FirstOrderOracle

open scoped WithTopConvexAnalysis

variable {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A first-order black-box oracle for a problem returns a subgradient at each query point. -/
structure FirstOrderOracle (f : V → ℝ) where
  /-- The subgradient returned by the oracle at the query point. -/
  subgradient : V → V
  /-- The returned vector is a genuine subgradient of the objective. -/
  subgradient_spec :
    ∀ x : V, IsSubgradientAt (fun y ↦ (f y : WithTop ℝ)) x (subgradient x)

namespace FirstOrderOracle

variable {f : V → ℝ}

/-- The reply of a first-order black-box oracle at `x` is the pair `(f(x), g(x))` consisting of
the objective value and the returned subgradient. -/
def answer (oracle : FirstOrderOracle f) (x : V) : ℝ × V :=
  (f x, oracle.subgradient x)

/-- The first component of the oracle reply is the objective value at the query point. -/
@[simp] theorem answer_fst (oracle : FirstOrderOracle f) (x : V) :
    (oracle.answer x).1 = f x :=
  rfl

/-- The second component of the oracle reply is the returned subgradient. -/
@[simp] theorem answer_snd (oracle : FirstOrderOracle f) (x : V) :
    (oracle.answer x).2 = oracle.subgradient x :=
  rfl

end FirstOrderOracle

end FirstOrderOracle

section LinearSpanCondition

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- A sequence `x₀, x₁, …, x_k` satisfies the linear-span condition for a subgradient map `g`
when it starts at `x₀` and every iterate `x_t` with `t ≤ k` lies in
`x₀ + Lin{g(x₀), …, g(x_{t-1})}`. -/
def SatisfiesLinearSpanCondition
    (x0 : V) (g : V → V) (xSeq : ℕ → V) (k : ℕ) : Prop :=
  ∀ t ≤ k,
    xSeq t ∈
      AffineSubspace.mk' x0
        (Submodule.span ℝ (Set.range fun i : Fin t ↦ g (xSeq i)))

/-- A sequence satisfying the linear-span condition starts from the prescribed point `x₀`. -/
theorem SatisfiesLinearSpanCondition.zero_eq
    {x0 : V} {g : V → V} {xSeq : ℕ → V} {k : ℕ}
    (hx : SatisfiesLinearSpanCondition x0 g xSeq k) :
    xSeq 0 = x0 := by
  have hx0 :
      xSeq 0 ∈
        AffineSubspace.mk' x0
          (Submodule.span ℝ (Set.range fun i : Fin 0 ↦ g (xSeq i))) :=
    hx 0 (Nat.zero_le k)
  rw [AffineSubspace.mem_mk'] at hx0
  simpa [sub_eq_zero] using hx0

end LinearSpanCondition

section EuclideanLowerBound

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "e[" i "]" => EuclideanSpace.single i (1 : ℝ)

open scoped LipschitzConvexProblemClass CoordinateSubspace

/-- A subgradient map satisfies the resisting-oracle prefix-support rule up to step `k` when each
query point lying in the affine translate `x₀ + ℝ^{i,n}` with `i < k` receives a subgradient in
the next prefix coordinate subspace `ℝ^{i+1,n}`. -/
def HasCoordinateSupportGrowth
    (x0 : E) (g : E → E) (k : ℕ) : Prop :=
  ∀ i < k, ∀ ⦃x : E⦄, x ∈ AffineSubspace.mk' x0 ℝ^{i,n} → g x ∈ ℝ^{i + 1,n}

/-- Helper for Theorem 3.2.1: every coordinate of a vector in `ℝⁿ` is bounded by the ambient
Euclidean norm. -/
theorem abs_coordinate_le_norm (v : E) (j : Fin n) :
    |v j| ≤ ‖v‖ := by
  have hinner : inner ℝ v e[j] = v j := by
    simpa using EuclideanSpace.inner_single_right j (1 : ℝ) v
  -- Re-express the chosen coordinate as an inner product against the standard basis vector.
  calc
    |v j| = |inner ℝ v e[j]| := by rw [hinner]
    _ ≤ ‖v‖ * ‖e[j]‖ := abs_real_inner_le_norm _ _
    _ = ‖v‖ := by simp [EuclideanSpace.single]

/-- Helper for Theorem 3.2.1: the span-condition iterates stay in the affine translate of the
corresponding prefix coordinate subspace whenever the oracle replies satisfy support growth. -/
theorem iterates_mem_affine_coordinateSubspace_under_support_growth
    {x0 : E} {g : E → E} {xSeq : ℕ → E} {k : ℕ}
    (hgrow : HasCoordinateSupportGrowth x0 g k)
    (hxSeq : SatisfiesLinearSpanCondition x0 g xSeq k)
    (i : ℕ) (hi : i ≤ k) :
    xSeq i ∈ AffineSubspace.mk' x0 ℝ^{i,n} := by
  refine Nat.strong_induction_on i ?_ hi
  intro i ih hik
  cases i with
  | zero =>
      -- At time `0`, the span condition already forces `x₀ = x0`.
      rw [SatisfiesLinearSpanCondition.zero_eq hxSeq]
      rw [AffineSubspace.mem_mk']
      simp
  | succ i =>
      have hstep :
          xSeq (i + 1) - x0 ∈
            Submodule.span ℝ (Set.range fun t : Fin (i + 1) ↦ g (xSeq t)) := by
        -- The span condition expresses `x_{i+1}` as `x0` plus a span combination.
        have hxSeq_step :
            xSeq (i + 1) ∈
              AffineSubspace.mk' x0
                (Submodule.span ℝ (Set.range fun t : Fin (i + 1) ↦ g (xSeq t))) :=
          hxSeq (i + 1) hik
        rwa [AffineSubspace.mem_mk'] at hxSeq_step
      have hspan :
          Submodule.span ℝ (Set.range fun t : Fin (i + 1) ↦ g (xSeq t)) ≤ ℝ^{i + 1,n} :=
        prefix_span_le_coordinateSubspace (fun t ↦ g (xSeq t)) fun j ↦
          hgrow j (lt_of_lt_of_le j.is_lt hik)
            (ih j j.is_lt (Nat.le_of_lt (lt_of_lt_of_le j.is_lt hik)))
      -- Push the span membership through the prefix-span inclusion.
      rw [AffineSubspace.mem_mk']
      exact hspan hstep

/-- Helper for Theorem 3.2.1: points in the affine translate `x0 + ℝ^{k,n}` agree with `x0` on
every coordinate of index at least `k`. -/
theorem coordinate_eq_start_of_mem_affine_coordinateSubspace
    {x0 x : E} {k : ℕ} {j : Fin n}
    (hx : x ∈ AffineSubspace.mk' x0 ℝ^{k,n})
    (hj : k ≤ j.1) :
    x j = x0 j := by
  -- Membership in the affine translate means the tail coordinates of `x - x0` vanish.
  rw [AffineSubspace.mem_mk'] at hx
  exact sub_eq_zero.mp ((mem_coordinateSubspace_iff.mp hx) j hj)

/-- Helper for Theorem 3.2.1: shifting the minimizer by radius `R` in a fresh coordinate forces
every point in `x0 + ℝ^{k,n}` to stay at distance at least `R` from that minimizer. -/
theorem shifted_coordinate_distance_lower_bound
    (x0 : E) (R : NNReal) {k : ℕ} {x : E} {j : Fin n}
    (hx : x ∈ AffineSubspace.mk' x0 ℝ^{k,n})
    (hj : k ≤ j.1) :
    (R : ℝ) ≤ dist x (x0 + (R : ℝ) • e[j]) := by
  have hxj : x j = x0 j :=
    coordinate_eq_start_of_mem_affine_coordinateSubspace hx hj
  -- The fresh coordinate of `x - xStar` is exactly `-R`, so the whole norm is at least `R`.
  have hcoord :=
    abs_coordinate_le_norm (x - (x0 + (R : ℝ) • e[j])) j
  simpa [dist_eq_norm, hxj, EuclideanSpace.single] using hcoord

/-- Helper for Theorem 3.2.1: the shifted-point distance witness belongs to
`𝒫(x₀, R, M)`. -/
theorem scaled_shifted_distance_witness_mem_problemClass
    (x0 : E) (R M : NNReal) {k : ℕ} {j : Fin n} :
    𝒫(x0, R, M)
      (fun x ↦ ((M : ℝ) / (2 * (2 + Real.sqrt (k + 1 : ℝ)))) * dist x (x0 + (R : ℝ) • e[j]))
      (x0 + (R : ℝ) • e[j]) := by
  let scale : ℝ := (M : ℝ) / (2 * (2 + Real.sqrt (k + 1 : ℝ)))
  let xStar : E := x0 + (R : ℝ) • e[j]
  have hscale_nonneg : 0 ≤ scale := by
    dsimp [scale]
    positivity
  have hscale_le_M : scale ≤ M := by
    dsimp [scale]
    have hden_pos : 0 < 2 * (2 + Real.sqrt (k + 1 : ℝ)) := by
      positivity
    rw [div_le_iff₀ hden_pos]
    nlinarith [show 0 ≤ (M : ℝ) by exact M.2, Real.sqrt_nonneg (k + 1 : ℝ)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The witness is a nonnegative scalar multiple of the convex distance function.
    simpa [scale, xStar, smul_eq_mul] using
      (convexOn_univ_dist xStar).smul hscale_nonneg
  · -- The shifted point is a global minimizer because the distance is minimized there.
    intro y _hy
    change scale * dist xStar xStar ≤ scale * dist y xStar
    simpa [hscale_nonneg] using mul_nonneg hscale_nonneg (dist_nonneg : 0 ≤ dist y xStar)
  · -- The chosen minimizer sits exactly at distance `R` from the starting point.
    rw [Metric.mem_closedBall]
    change dist x0 xStar ≤ R
    rw [dist_eq_norm]
    have hsub : x0 - xStar = -((R : ℝ) • e[j]) := by
      dsimp [xStar]
      abel
    rw [hsub, norm_neg, norm_smul]
    simp [EuclideanSpace.single]
  · -- The witness is globally `scale`-Lipschitz, and `scale ≤ M`.
    refine LipschitzOnWith.of_le_add_mul M ?_
    intro x _hx y _hy
    change scale * dist x xStar ≤ scale * dist y xStar + M * dist x y
    calc
      scale * dist x xStar ≤ scale * (dist x y + dist y xStar) := by
        gcongr
        exact dist_triangle x y xStar
      _ = scale * dist y xStar + scale * dist x y := by ring
      _ ≤ scale * dist y xStar + M * dist x y := by
        gcongr

/-- Theorem 3.2.1: for every `k` with `0 ≤ k ≤ n - 1`, there exist an objective `f` and a chosen
minimizer `x*` in the class `𝒫(x₀, R, M)` such that every first-order oracle whose replies satisfy
the resisting-oracle prefix-support rule, together with every iterate sequence satisfying the span
condition for that oracle, has objective gap at least `MR / (2 (2 + √(k + 1)))` at step `k`. -/
-- Proof sketch: choose the Nemirovski hard instance with `k + 1` active coordinates and tune its
-- parameters so that the chosen minimizer is exactly at distance `R` from `x₀` and the objective
-- is `M`-Lipschitz on the relevant ball. The oracle-side prefix-support hypothesis and the span
-- condition then trap the first `k` iterates in the coordinate-prefix subspace where the hard
-- instance still has objective value at least the displayed lower bound above the optimum.
theorem exists_problem_with_nonsmooth_firstOrder_lower_bound
    (n : ℕ) (x0 : EuclideanSpace ℝ (Fin n)) (R M : NNReal) {k : ℕ} (hk : k + 1 ≤ n) :
    ∃ f : EuclideanSpace ℝ (Fin n) → ℝ, ∃ xStar : EuclideanSpace ℝ (Fin n),
      𝒫(x0, R, M) f xStar ∧
        ∀ oracle : FirstOrderOracle f,
          HasCoordinateSupportGrowth x0 oracle.subgradient k →
          ∀ xSeq : ℕ → EuclideanSpace ℝ (Fin n),
            SatisfiesLinearSpanCondition x0 oracle.subgradient xSeq k →
              f (xSeq k) - f xStar ≥
                ((M : ℝ) * (R : ℝ)) / (2 * (2 + Real.sqrt (k + 1 : ℝ))) := by
  let j : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
  let scale : ℝ := (M : ℝ) / (2 * (2 + Real.sqrt (k + 1 : ℝ)))
  let xStar : EuclideanSpace ℝ (Fin n) :=
    x0 + (R : ℝ) • (EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin n))
  let f : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦ scale * dist x xStar
  refine ⟨f, xStar, ?_, ?_⟩
  · -- Package the shifted-distance witness into the chapter's problem class.
    simpa [f, xStar, j] using
      (scaled_shifted_distance_witness_mem_problemClass (n := n) x0 R M (k := k) (j := j))
  · intro oracle hgrow xSeq hxSeq
    have hxk :
        xSeq k ∈ AffineSubspace.mk' x0 ℝ^{k,n} :=
      iterates_mem_affine_coordinateSubspace_under_support_growth
        (n := n) hgrow hxSeq k le_rfl
    have hdist : (R : ℝ) ≤ dist (xSeq k) xStar := by
      -- The `k`-th iterate still agrees with `x0` on the fresh coordinate `j = k`.
      simpa [xStar, j] using
        (shifted_coordinate_distance_lower_bound (n := n) x0 R hxk
          (show k ≤ j.1 by simp [j]))
    have hscale_nonneg : 0 ≤ scale := by
      dsimp [scale]
      positivity
    have hgap : scale * (R : ℝ) ≤ scale * dist (xSeq k) xStar :=
      mul_le_mul_of_nonneg_left hdist hscale_nonneg
    -- Convert the distance lower bound into the objective-gap estimate.
    calc
      f (xSeq k) - f xStar = scale * dist (xSeq k) xStar := by
        simp [f, xStar, scale]
      _ ≥ scale * (R : ℝ) := hgap
      _ = ((M : ℝ) * (R : ℝ)) / (2 * (2 + Real.sqrt (k + 1 : ℝ))) := by
        dsimp [scale]
        ring

end EuclideanLowerBound

end

/-! ### Corollary_3_2_2 (from Chap03) -/
noncomputable section

universe u

/-
Corollary 3.2.2 is a source-facing consequence in the chapter's constrained strong-convexity
domain on proper real normed spaces. The textbook finite-dimensional real inner-product-space case
is recovered by the canonical finite-dimensional properness instance.

Sampled owner-style declarations:
- mathlib `StrongConvexOn`
- `StrongConvexOn.isBounded_constrainedSublevelSet` in `Theorem_3_45`
- `StrongConvexOn.existsUnique_isMinOn_of_isClosed` in `Theorem_3_45`

Best owner abstraction:
- source-facing: existence of a feasible minimizer on a nonempty closed feasible set
- core/canonical: `StrongConvexOn Q μ f`
- bridge/view: projection from the unique-minimizer owner theorem to the existence-only statement

Primitive data:
- a feasible set `Q`, an objective `f`, and a strong-convexity modulus `μ`
- the owner predicate `StrongConvexOn Q μ f`
- continuity of `f` on the feasible set

Derived API:
- boundedness of constrained sublevel sets
- under closed/nonempty feasible-set hypotheses, existence and uniqueness of a feasible minimizer
- the source-facing existence-only consequence extracted from the unique-minimizer owner theorem

Source/core/bridge triage:
- source-facing: Corollary 3.2.2, which stops at boundedness of constrained level sets and the
  resulting existence of an optimal solution
- core/canonical: `StrongConvexOn Q μ f`
- bridge/view: projection from the unique-minimizer owner theorem to the existence-only statement

The stronger uniqueness consequence is deferred to `Corollary_3_2_3`, so this file keeps the
bounded-sublevel owner theorem as the public center and exposes only the existence bridge needed
for the source text.
-/

recall StrongConvexOn.isBounded_constrainedSublevelSet

namespace StrongConvexOn

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- Corollary 3.2.2: under the standing closed/nonempty feasible-set hypotheses of problem
`(3.2.13)`, a `μ`-strongly convex real-valued objective that is continuous on a closed nonempty
feasible set admits a feasible optimal solution. The textbook finite-dimensional Euclidean case is
the canonical specialization. -/
theorem exists_isMinOn_of_isClosed
    {Q : Set E} {f : E → ℝ} {μ : ℝ}
    (hf : StrongConvexOn Q μ f) (hμ : 0 < μ)
    (hf_cont : ContinuousOn f Q)
    (hQ_nonempty : Q.Nonempty) (hQ_closed : IsClosed Q) :
    ∃ x : E, x ∈ Q ∧ IsMinOn f Q x :=
  (hf.existsUnique_isMinOn_of_isClosed hμ hf_cont hQ_nonempty hQ_closed).exists

end StrongConvexOn

end

/-! ### Definition_3_2 (from Chap03) -/
open scoped ConvexAnalysis

/-
Definition 3.2 is a source-facing recall of the finite-value domain of an extended-real-valued
function together with the standing assumption that this domain is nonempty.

Primary domain:
- convex analysis of `EReal`-valued functions through their finite-value domain.

Relevant declarations and owner-style recall sampled before refinement:
- `extendedRealEffectiveDomain`
- `extendedRealEffectiveDomain_nonempty_iff`
- `mem_extendedRealEffectiveDomain_iff`
- `(dom f).Nonempty`
- `Set.Nonempty`

Best owner abstraction:
- `extendedRealEffectiveDomain`

Primitive data:
- the owner set `dom f`

Derived API:
- `(dom f).Nonempty`
- `extendedRealEffectiveDomain_nonempty_iff`
- `mem_extendedRealEffectiveDomain_iff`
- the existential expansion of `Set.Nonempty`

Source/core/bridge triage:
- source-facing: the domain object `dom f` together with its standing nonemptiness assumption
- core/canonical: `extendedRealEffectiveDomain`
- bridge/view: `mem_extendedRealEffectiveDomain_iff`, `extendedRealEffectiveDomain_nonempty_iff`

This item therefore targets the source-facing owner layer directly: it recalls
`extendedRealEffectiveDomain` as the main entry and keeps the nonemptiness condition only as the
companion standing assumption. Since neither declaration uses Euclidean structure, the public
surface stays at the owner's arbitrary-domain level.
-/

recall extendedRealEffectiveDomain
    {X : Type _} (f : X → EReal) :
    Set X

recall extendedRealEffectiveDomain_nonempty_iff
    {X : Type _} {f : X → EReal} :
    (dom f).Nonempty ↔ ∃ x, f x ≠ ⊤ ∧ f x ≠ ⊥

section

variable {X : Type _} (f : X → EReal)

#check (dom f).Nonempty

end

/-! ### Definition_3_2_2 (from Chap03) -/
universe u

/-
Definition 3.2.2 lies in the positive-parameter strong-convexity domain for real-valued
functions on a feasible set.

Sampled owner-style declarations:
- mathlib `StrongConvexOn`
- mathlib `strongConvexOn_iff_convex`
- project `strongConvexOn_iff_quadratic_jensen_bound` in `Chap02/Theorem_2_10`

Best owner abstraction:
- source-facing: positive strong convexity on `Q`, expressed as `∃ μ > 0, StrongConvexOn Q μ f`
- core/canonical: `StrongConvexOn Q μ f`
- bridge/view: `strongConvexOn_iff_quadratic_jensen_bound`

Primitive data:
- the feasible set `Q`
- the objective `f`

Derived API:
- existence of a positive strong-convexity modulus `μ`
- convexity of `Q`
- the textbook quadratic segment inequality for that modulus

Source/core/bridge triage:
- source-facing main entry: `∃ μ > 0, StrongConvexOn Q μ f`
- core/canonical companion: `StrongConvexOn Q μ f`
- bridge/view companion: the fixed-modulus quadratic Jensen equivalence

Definition 3.2.2 adds only the positive-existential layer on top of the fixed-modulus owner.
This file therefore keeps that existential surface as the main statement and reuses the canonical
bridge `strongConvexOn_iff_quadratic_jensen_bound`, rather than introducing a parallel local
strong-convexity definition.
-/

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Q : Set E} {μ : ℝ} {f : E → ℝ}

/- Definition 3.2.2: a real-valued function is strongly convex on the feasible set `Q` exactly
when there exists a positive modulus `μ` such that `StrongConvexOn Q μ f`. The textbook segment
inequality is recorded below as the canonical bridge for this positive-existential owner. -/
#check (∃ μ > 0, StrongConvexOn Q μ f)

/-- The positive-modulus strong-convexity condition is equivalent to the textbook quadratic
segment upper bound on a convex feasible set. -/
-- Proof sketch: apply `strongConvexOn_iff_quadratic_jensen_bound` for each fixed modulus `μ`,
-- move the positive witness through that fixed-parameter equivalence, and keep `Convex ℝ Q` as
-- the explicit source-side hypothesis because the textbook states the segment inequality only on
-- convex feasible sets.
theorem exists_pos_strongConvexOn_iff_forall_segment_upper_bound :
    (∃ μ > 0, StrongConvexOn Q μ f) ↔
      Convex ℝ Q ∧
        ∃ μ > 0,
          ∀ x ∈ Q, ∀ y ∈ Q, ∀ α ∈ Set.Icc (0 : ℝ) 1,
            f (α • x + (1 - α) • y) ≤
              α * f x + (1 - α) * f y -
                (μ / 2) * α * (1 - α) * ‖x - y‖ ^ (2 : ℕ) := by
  constructor
  · rintro ⟨μ, hμ, hf⟩
    refine ⟨hf.1, μ, hμ, ?_⟩
    intro x hx y hy α hα
    simpa [le_sub_iff_add_le, mul_assoc, mul_left_comm, mul_comm] using
      (strongConvexOn_iff_quadratic_jensen_bound hf.1).mp hf hx hy hα
  · rintro ⟨hQ, μ, hμ, hbound⟩
    refine ⟨μ, hμ, ?_⟩
    refine (strongConvexOn_iff_quadratic_jensen_bound hQ).mpr ?_
    intro x y hx hy α hα
    simpa [le_sub_iff_add_le, mul_assoc, mul_left_comm, mul_comm] using
      hbound x hx y hy α hα

end

/-! ### Lemma_3_2 (from Chap03) -/
universe u

section

variable {X : Type u} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]

/- Lemma 3.2 lies in the chapter's constrained-epigraph convex-analysis domain.

Primary domain:
- restriction of a closed convex constrained epigraph to a closed convex subset of the base domain
  in a real topological module.

Sampled owner-style declarations:
- `constrainedEpigraph` in `Definition_3_3`, the chapter owner for the constrained epigraph;
- `mem_constrainedEpigraph_iff` in `Definition_3_3`, the atomic membership view for that owner;
- `constrainedEpigraph_eq_prod_univ_inter_of_subset` in `Definition_3_3`, the canonical bridge
  from restriction to intersection with the base cylinder;
- mathlib `Convex.prod`, the canonical convex-product constructor used by the bridge proof;
- `ClosedConvexOn.restrict` in `Definition_3_1_1_5`, the stronger owner theorem obtained from the
  same bridge once one also has the primitive domain-finiteness data `Q ⊆ dom f`.

Best owner abstraction:
- `constrainedEpigraph Q f`.

Primitive data:
- the constrained epigraph `constrainedEpigraph Q f`;
- the closed/convex subset data `Q₁ ⊆ Q`, `IsClosed Q₁`, and `Convex ℝ Q₁`.

Derived API:
- the restricted closedness/convexity conclusion for `constrainedEpigraph Q₁ f`, obtained from the
  owner bridge `constrainedEpigraph_eq_prod_univ_inter_of_subset`.

Source/core/bridge triage:
- source-facing: Lemma 3.2 as the restricted-epigraph closedness/convexity statement;
- core/canonical: `constrainedEpigraph` from `Definition_3_3`;
- bridge/view: `constrainedEpigraph_eq_prod_univ_inter_of_subset`.

This file therefore reuses the chapter owner `constrainedEpigraph` directly and does not keep a
parallel local definition or membership lemma. Since Lemma 3.2 assumes only closedness and
convexity of the constrained epigraph, and not the stronger owner datum `Q ⊆ dom f`, the theorem
remains source-facing rather than collapsing to `ClosedConvexOn.restrict`; the refinement is the
ambient generalization from the textbook model `ℝⁿ` to an arbitrary real topological module. -/

/-- Lemma 3.2: if the epigraph of `f` over `Q` is a closed convex subset of `X × ℝ` and
`Q₁ ⊆ Q` is closed and convex, then the epigraph of the restriction of `f` to `Q₁` is also closed
and convex. -/
theorem isClosed_convex_constrainedEpigraph_restrict
    {Q Q₁ : Set X} {f : X → WithTop ℝ}
    (hf_closed : IsClosed (constrainedEpigraph Q f))
    (hf_convex : Convex ℝ (constrainedEpigraph Q f))
    (hQ₁_subset : Q₁ ⊆ Q)
    (hQ₁_closed : IsClosed Q₁)
    (hQ₁_convex : Convex ℝ Q₁) :
    IsClosed (constrainedEpigraph Q₁ f) ∧ Convex ℝ (constrainedEpigraph Q₁ f) := by
  -- Rewrite the restricted epigraph as the original epigraph intersected with the base cylinder.
  have hEpigraph :
      constrainedEpigraph Q₁ f = (Q₁ ×ˢ (Set.univ : Set ℝ)) ∩ constrainedEpigraph Q f :=
    constrainedEpigraph_eq_prod_univ_inter_of_subset hQ₁_subset
  constructor
  · rw [hEpigraph]
    -- Closedness is inherited from the closed cylinder `Q₁ × ℝ` and the closed original epigraph.
    exact (hQ₁_closed.prod isClosed_univ).inter hf_closed
  · rw [hEpigraph]
    -- Convexity is inherited from the convex cylinder `Q₁ × ℝ` and the convex original epigraph.
    exact (hQ₁_convex.prod convex_univ).inter hf_convex

end

/-! ### Lemma_3_2_2 (from Chap03) -/
noncomputable section

universe u

section

variable {X : Type u}

/- Lemma 3.2.2 lies in the finite best-value / monotone-modulus domain.

Sampled owner declarations:
- `bestFunctionValueUpTo` and `bestRadiusUpTo` in `Definition_3_55`, the source-facing objective
  and radius owners for finite sampled prefix minima;
- mathlib `Finite.map_iInf_of_monotone`, the finite-infimum transport rule for monotone maps;
- mathlib `iInf_le`, the pointwise lower-bound rule for a finite indexed infimum;
- `bestFunctionValueUpTo_sub_le_pointwiseGrowthFunction_at_bestRadius` in `Lemma_3_26`, the
  direct downstream specialization of the present lemma.

Best owner abstraction:
- core/canonical: the finite infima underlying `bestFunctionValueUpTo` and `bestRadiusUpTo`,
  together with finite-infimum monotonicity;
- bridge/view: the later specialization to pointwise growth functions in `Lemma_3_26`.

Primitive data:
- a sample sequence `xSeq : ℕ → X`;
- a real radius sequence `radii : ℕ → ℝ`;
- a reference point `xStar`;
- a monotone modulus `ω`;
- the pointwise estimates `f (xSeq i) - f xStar ≤ ω (radii i)` on `Fin (k + 1)`.

Derived API:
- the best-value gap bound at the best sampled radius.

Source/core/bridge triage:
- source-facing: Lemma 3.2.2's best sampled gap inequality;
- core/canonical: `bestFunctionValueUpTo`, `bestRadiusUpTo`, and finite-infimum monotonicity;
- bridge/view: `bestFunctionValueUpTo` on the objective side and `bestRadiusUpTo` on the radius
  side;
- bridge/view: downstream specializations where the radius sequence is built from distances or
  localization measures.

The chapter's public owners for finite sampled minima are `bestFunctionValueUpTo` and
`bestRadiusUpTo`, with the raw finite infimum kept as the underlying canonical expression rather
than a separate neutral wrapper. This file keeps the source-facing objective notation on the
left-hand side and the source-facing radius notation on the right-hand side, rather than reusing
the objective-value owner for both roles.
-/

/-- Lemma 3.2.2: if `f_k^* = min_{0 ≤ i ≤ k} f(x_i)` and `v_k^* = min_{0 ≤ i ≤ k} v_i`, then the
best function-value gap up to step `k` is bounded by the modulus value at the best radius. This
specializes to `ω_f(x^*; v_k^*)` when `ω = ω_f(x^*; ·)`, with `ω` allowed to take the value `⊤`
when the growth profile is unbounded. -/
-- Proof sketch: for each `i ≤ k`, apply the pointwise bound
-- `f (xSeq i) - f xStar ≤ ω (radii i)`. Since
-- `Fin (k + 1)` is finite, the minima defining `f_k^*` and `v_k^*` are attained; monotonicity of
-- `ω` then identifies `ω (min_i radii i)` with `min_i ω (radii i)`, and taking minima on both
-- sides gives the claim.
theorem bestFunctionValueGapUpTo_le_modulusAtBestRadius
    (f : X → ℝ) (ω : ℝ → WithTop ℝ) (hω_mono : Monotone ω)
    (xSeq : ℕ → X) (xStar : X) (radii : ℕ → ℝ) (k : ℕ)
    (hbound : ∀ i : Fin (k + 1), f (xSeq i) - f xStar ≤ ω (radii i)) :
    bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k - f xStar ≤
      ω (bestRadiusUpTo radii k) := by
  let gap : ℕ → ℝ := fun i ↦ f (xSeq i) - f xStar
  have hsub_mono : Monotone (fun y : ℝ ↦ ((y - f xStar : ℝ) : WithTop ℝ)) := by
    intro a b hab
    simpa using sub_le_sub_right hab (f xStar)
  have hgap_eq :
      ((bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k - f xStar : ℝ) : WithTop ℝ) =
        ⨅ i : Fin (k + 1), (gap i : WithTop ℝ) := by
    simpa [gap, bestFunctionValueUpTo] using
      Finite.map_iInf_of_monotone (fun i : Fin (k + 1) ↦ f (xSeq i)) hsub_mono
  have hgap_le :
      (⨅ i : Fin (k + 1), (gap i : WithTop ℝ)) ≤
        ⨅ i : Fin (k + 1), ω (radii i) :=
    Finite.ciInf_mono hbound
  have hω_eq :
      ω (bestRadiusUpTo radii k) =
        ⨅ i : Fin (k + 1), ω (radii i) := by
    simpa [bestRadiusUpTo] using
      Finite.map_iInf_of_monotone (fun i : Fin (k + 1) ↦ radii i) hω_mono
  calc
    ((bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k - f xStar : ℝ) : WithTop ℝ) =
        ⨅ i : Fin (k + 1), (gap i : WithTop ℝ) := hgap_eq
    _ ≤ ⨅ i : Fin (k + 1), ω (radii i) := hgap_le
    _ = ω (bestRadiusUpTo radii k) := hω_eq.symm

end

/-! ### Proposition_3_2 (from Chap03) -/
universe u

open scoped ConvexAnalysis

/- Proposition 3.2 lies in the chapter's extended-real epigraph-closedness bridge.

Primary domain:
- closedness of the effective real epigraph of an `EReal`-valued function on a topological space.

Sampled owner-style declarations:
- chapter `dom f` from `Definition_3_1_1_2`, the canonical finite-value owner;
- chapter `effectiveEpigraph f`, `extendedRealRealPart f`, and
  `effectiveEpigraph_eq_epigraph_extendedRealRealPart` from `Definition_3_1_1_3`,
  the canonical owner/bridge surface from `EReal` values to real epigraph inequalities on
  `dom f`;
- mathlib `ContinuousOn.lowerSemicontinuousOn`, the canonical continuity-to-lower-semicontinuity
  bridge;
- mathlib `LowerSemicontinuousOn.isClosed_re_epigraph`, the owner closedness theorem for real
  epigraphs over a closed set.

Best owner abstraction:
- source-facing: the effective epigraph `effectiveEpigraph f`;
- core/canonical: the real epigraph
  `{p : X × ℝ | p.1 ∈ dom f ∧ extendedRealRealPart f p.1 ≤ p.2}` of
  `extendedRealRealPart f` on `dom f`;
- bridge/view: `ContinuousOn.lowerSemicontinuousOn` and
  `effectiveEpigraph_eq_epigraph_extendedRealRealPart`.

Primitive data:
- the `EReal`-valued function `f`;
- continuity of `extendedRealRealPart f` on `dom f`;
- closedness of the chapter owner `dom f`.

Derived API:
- closedness of `effectiveEpigraph f`.
- companion strengthening: the same conclusion under the weaker lower-semicontinuity hypothesis.

Source/core/bridge triage:
- source-facing: the effective-epigraph closedness statement below on `effectiveEpigraph f`
  from continuity on `dom f`;
- core/canonical: `LowerSemicontinuousOn.isClosed_re_epigraph`;
- bridge/view: `dom f`, `extendedRealRealPart f`,
  `ContinuousOn.lowerSemicontinuousOn`, and
  `effectiveEpigraph_eq_epigraph_extendedRealRealPart`.

The source-facing proposition uses continuity of the finite real part on `dom f`. The canonical
owner theorem behind it is the lower-semicontinuous real-epigraph closedness result, so the file
keeps the continuity statement as the main proposition and records the lower-semicontinuity
version only as a strengthening companion.
-/

variable {X : Type u} [TopologicalSpace X]

/-- Proposition 3.2, generalized from the textbook `ℝⁿ` setting: if the finite real part of
`f : X → ℝ ∪ {±∞}` is continuous on its finite-value domain `dom f`, and `dom f` is closed, then
the effective epigraph of `f` is a closed subset of `X × ℝ`. -/
-- Proof sketch: continuity on `dom f` implies lower semicontinuity there. Then
-- `effectiveEpigraph f` is definitionally the real epigraph of `extendedRealRealPart f` over
-- `dom f`, so `LowerSemicontinuousOn.isClosed_re_epigraph` applies and the bridge rewrites the
-- conclusion back to the source-facing effective epigraph.
theorem isClosed_effectiveEpigraph_of_continuousOn_of_isClosed_dom
    {f : X → EReal}
    (hf_cont : ContinuousOn (extendedRealRealPart f) (dom f))
    (hdom_closed : IsClosed (dom f)) :
    IsClosed (effectiveEpigraph f) := by
  simpa [effectiveEpigraph_eq_epigraph_extendedRealRealPart] using
    hf_cont.lowerSemicontinuousOn.isClosed_re_epigraph hdom_closed

/-- Companion strengthening of Proposition 3.2: continuity on `dom f` can be weakened to lower
semicontinuity of the finite real part on `dom f`. -/
theorem isClosed_effectiveEpigraph_of_lowerSemicontinuousOn_of_isClosed_dom
    {f : X → EReal}
    (hf_lower : LowerSemicontinuousOn (extendedRealRealPart f) (dom f))
    (hdom_closed : IsClosed (dom f)) :
    IsClosed (effectiveEpigraph f) := by
  simpa [effectiveEpigraph_eq_epigraph_extendedRealRealPart] using
    hf_lower.isClosed_re_epigraph hdom_closed

/-! ### Theorem_3_2 (from Chap03) -/
section

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

/- Theorem 3.2 lies in convex analysis on sets in affine modules over a linearly ordered field.

Sampled owner-style declarations:
- mathlib `ConvexOn`
- mathlib `convexOn_iff_forall_pos`
- mathlib `convexOn_iff_div`
- Chapter 2 `convexOn_iff_segment_inequality`

Best owner abstraction:
- `ConvexOn 𝕜 s f`

Primitive data:
- a set `s`
- a `𝕜`-valued function `f`

Derived API:
- the segment Jensen inequality on points of `s`
- the equivalent affine-ray secant lower bound on points of `s`
- under `Convex 𝕜 s`, the owner-level equivalence with `ConvexOn 𝕜 s f`

Source/core/bridge triage:
- source-facing: the affine-ray secant criterion on a fixed set
- core/canonical: `ConvexOn 𝕜 s f`
- bridge/view: the segment-form and affine-ray-form inequalities compared below

The bridge theorem below does not own convexity of the set. That owner-level role belongs to
`ConvexOn 𝕜 s f`, and Chapter 2 already provides the canonical bridge from `ConvexOn` to the
one-parameter segment inequality. This file therefore keeps the segment-vs-ray equivalence as
bridge API and derives the owner-level corollary separately.
-/

/-- Theorem 3.2: for a function considered on a set `s`, the usual two-point convexity
inequality along segments in `s` is equivalent to the forward affine-ray secant lower bound.
Specializing to `𝕜 = ℝ` and `E = EuclideanSpace ℝ (Fin n)` recovers the textbook statement on
`ℝⁿ`. -/
-- Proof sketch: for the forward direction, write `y` as a convex combination of the extrapolation
-- point `u = y + β • (y - x)` and `x` using the weight `α = β / (1 + β)`, then rearrange the
-- usual convexity inequality. For the converse, given a convex-combination point
-- `u = α • x + (1 - α) • y`, rewrite `x` as `u + ((1 - α) / α) • (u - y)` for `α ∈ (0, 1]`,
-- apply the affine-ray inequality to the pair `(y, u)`, and rearrange.
theorem segment_inequality_iff_affine_ray_inequality
    (s : Set E) (f : E → 𝕜) :
    (∀ ⦃x y : E⦄, x ∈ s → y ∈ s →
      ∀ ⦃α : 𝕜⦄, α ∈ Set.Icc (0 : 𝕜) 1 →
        α • x + (1 - α) • y ∈ s →
          f (α • x + (1 - α) • y) ≤ α * f x + (1 - α) * f y) ↔
    (∀ ⦃x y : E⦄, x ∈ s → y ∈ s →
      ∀ ⦃β : 𝕜⦄, 0 ≤ β →
        y + β • (y - x) ∈ s →
          f (y + β • (y - x)) ≥ f y + β * (f y - f x)) := by
  constructor
  · intro hseg x y hx hy β hβ hz
    let z : E := y + β • (y - x)
    have hz' : z ∈ s := hz
    have hβ1 : 0 < 1 + β := by
      linarith
    have hα :
        (1 / (1 + β) : 𝕜) ∈ Set.Icc (0 : 𝕜) 1 := by
      refine ⟨div_nonneg zero_le_one hβ1.le, ?_⟩
      field_simp [hβ1.ne']
      linarith
    have hy_repr :
        (1 / (1 + β) : 𝕜) • z + (1 - 1 / (1 + β)) • x = y := by
      have hs :
          (1 + β) • ((1 / (1 + β) : 𝕜) • z + (1 - 1 / (1 + β)) • x) = (1 + β) • y := by
        dsimp [z]
        have hβx : (1 + β - 1 : 𝕜) = β := by
          ring
        calc
          (1 + β) • ((1 / (1 + β) : 𝕜) • (y + β • (y - x)) + (1 - 1 / (1 + β)) • x)
              = ((1 + β) * (1 / (1 + β))) • (y + β • (y - x)) +
                  ((1 + β) * (1 - 1 / (1 + β))) • x := by
                    rw [smul_add, smul_smul, smul_smul]
          _ = y + β • (y - x) + (1 + β - 1) • x := by
                field_simp [hβ1.ne']
                simp [one_smul]
          _ = (1 + β) • y := by
                rw [hβx, smul_sub]
                abel_nf
                rw [add_smul, one_smul]
      exact smul_right_injective E hβ1.ne' hs
    have hsegment :
        f y ≤ (1 / (1 + β)) * f z + (1 - 1 / (1 + β)) * f x := by
      have hy' : (1 / (1 + β) : 𝕜) • z + (1 - 1 / (1 + β)) • x ∈ s := by
        rw [hy_repr]
        exact hy
      have hsegment' := hseg hz' hx hα hy'
      rw [hy_repr] at hsegment'
      exact hsegment'
    have hcoeff : (1 - 1 / (1 + β) : 𝕜) = β / (1 + β) := by
      field_simp [hβ1.ne']
      ring
    rw [hcoeff] at hsegment
    have hmult := mul_le_mul_of_nonneg_left hsegment hβ1.le
    field_simp [hβ1.ne'] at hmult
    dsimp [z] at hmult ⊢
    nlinarith
  · intro hray x y hx hy α hα hu
    let u : E := α • x + (1 - α) • y
    have hu' : u ∈ s := hu
    by_cases hα0 : α = 0
    · simp [hα0]
    · have hαpos : 0 < α := lt_of_le_of_ne hα.1 (by simpa [eq_comm] using hα0)
      have hy_sub : (1 - α) • y - y = (-α) • y := by
        calc
          (1 - α) • y - y = (1 - α) • y + (-1 : 𝕜) • y := by
            rw [sub_eq_add_neg, neg_one_smul]
          _ = ((1 - α) + (-1 : 𝕜)) • y := by
            rw [← add_smul]
          _ = (-α) • y := by
            congr 1
            ring
      have hu_sub : u - y = α • (x - y) := by
        calc
          u - y = α • x + (-α) • y := by
            dsimp [u]
            rw [add_sub_assoc, hy_sub]
          _ = α • x + -(α • y) := by
            rw [neg_smul]
          _ = α • x - α • y := by
            rw [sub_eq_add_neg]
          _ = α • (x - y) := by
            rw [smul_sub]
      have hx_repr : u + ((1 - α) / α) • (u - y) = x := by
        have hcoeff : (((1 - α) / α) * α : 𝕜) = 1 - α := by
          field_simp [hαpos.ne']
        calc
          u + ((1 - α) / α) • (u - y)
              = α • x + (1 - α) • y + (((1 - α) / α) * α) • (x - y) := by
                  dsimp [u]
                  rw [hu_sub, mul_smul]
          _ = α • x + (1 - α) • y + (1 - α) • (x - y) := by
                simp [hcoeff]
          _ = x := by
                rw [smul_sub]
                abel_nf
                have hone : (α + (1 + -1 * α) : 𝕜) = 1 := by
                  ring
                rw [← add_smul]
                simp
      have hβ : 0 ≤ (1 - α) / α := by
        exact div_nonneg (sub_nonneg.mpr hα.2) hαpos.le
      have hray' :
          f x ≥ f u + ((1 - α) / α) * (f u - f y) := by
        have hx' : u + ((1 - α) / α) • (u - y) ∈ s := by
          simpa [hx_repr] using hx
        simpa [hx_repr] using hray hy hu' hβ hx'
      have hmult := mul_le_mul_of_nonneg_left hray' hαpos.le
      field_simp [hαpos.ne'] at hmult
      dsimp [u] at hmult ⊢
      nlinarith

/-- On a convex set `s`, the affine-ray secant lower bound is equivalent to the canonical owner
predicate `ConvexOn 𝕜 s f`. -/
-- Proof sketch: combine Chapter 2's equivalence between `ConvexOn` and the one-parameter segment
-- inequality with `segment_inequality_iff_affine_ray_inequality`.
theorem convexOn_iff_affine_ray_inequality
    (s : Set E) (f : E → 𝕜) (hs : Convex 𝕜 s) :
    ConvexOn 𝕜 s f ↔
    (∀ ⦃x y : E⦄, x ∈ s → y ∈ s →
      ∀ ⦃β : 𝕜⦄, 0 ≤ β →
        y + β • (y - x) ∈ s →
          f (y + β • (y - x)) ≥ f y + β * (f y - f x)) := by
  have howner :
      ConvexOn 𝕜 s f ↔
        ∀ ⦃x : E⦄, x ∈ s →
          ∀ ⦃y : E⦄, y ∈ s →
            ∀ ⦃α : 𝕜⦄, α ∈ Set.Icc (0 : 𝕜) 1 →
              f (α • x + (1 - α) • y) ≤ α * f x + (1 - α) * f y :=
    convexOn_iff_segment_inequality hs
  have hsegment :
      ConvexOn 𝕜 s f ↔
        ∀ ⦃x y : E⦄, x ∈ s → y ∈ s →
          ∀ ⦃α : 𝕜⦄, α ∈ Set.Icc (0 : 𝕜) 1 →
            α • x + (1 - α) • y ∈ s →
              f (α • x + (1 - α) • y) ≤ α * f x + (1 - α) * f y := by
    constructor
    · intro hf x y hx hy α hα _
      exact howner.mp hf hx hy hα
    · intro h
      refine howner.mpr ?_
      intro x hx y hy α hα
      have hxy : α • x + (1 - α) • y ∈ s := by
        refine hs hx hy hα.1 (sub_nonneg.mpr hα.2) ?_
        ring
      exact h hx hy hα hxy
  exact hsegment.trans (segment_inequality_iff_affine_ray_inequality s f)

end
