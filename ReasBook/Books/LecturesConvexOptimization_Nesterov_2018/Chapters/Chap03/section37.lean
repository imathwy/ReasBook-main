import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_37 (from Chap03) -/
/-
Definition 3.37 lies in the cutting-plane localization-measure domain.

Primary mathematical domain:
- subgradient-based localization radii around a reference point in finite-dimensional Euclidean
  cutting-plane analysis.

Sampled owner-style declarations:
- `subgradientLocalizationMeasure` in `Lemma_3_2_1`, the chapter owner for `v_f(xBar; x)`
- `subgradientLocalizationMeasure_eq_zero_of_eq_zero` in `Lemma_3_2_1`, the owner-level
  zero-branch simplification
- `subgradientLocalizationMeasure_eq_inner_div_norm_of_ne_zero` in `Lemma_3_2_1`, the owner-level
  nonzero-branch simplification
- `sub_le_pointwiseGrowthFunction_of_localizationMeasure` in `Lemma_3_2_1`, the first comparison
  theorem built from the same owner

Best owner abstraction for this file:
- `subgradientLocalizationMeasure`

Primitive data:
- a reference point `xBar`
- a chosen subgradient selection `g`
- an evaluation point `x`

Derived API:
- the zero-case simplification theorem
  `subgradientLocalizationMeasure_eq_zero_of_eq_zero`
- the nonzero-case simplification theorem
  `subgradientLocalizationMeasure_eq_inner_div_norm_of_ne_zero`
- the comparison
  `sub_le_pointwiseGrowthFunction_of_localizationMeasure`

Source/core/bridge triage:
- source-facing: the pointwise localization measure `subgradientLocalizationMeasure g xBar x`
- core/canonical: `subgradientLocalizationMeasure`
- bridge/view: the zero/nonzero branch simplifications and the growth-function comparison obtained
  by unfolding the owner

The owner declaration `subgradientLocalizationMeasure` in `Lemma_3_2_1` already carries the exact
mathematical content of Definition 3.37. This file therefore recalls that owner directly instead
of keeping a parallel local copy. The branch simplification theorems stay with the owner file
rather than being re-recalled from this definition-only item.
-/

recall subgradientLocalizationMeasure

/-! ### Lemma_3_37 (from Chap03) -/
noncomputable section

universe u v

section

variable {Index : Type u} {Param : Type v}
variable (estimatedValue : Index → Param → ℝ → ℝ)
variable (k : Index) (X : Param)

local notation "value" => estimatedValue k X

/- Lemma 3.37 is a bridge/view item in the chapter's one-variable convex value-function domain.

Relevant owner declarations sampled before refining:
- `ConvexOn.secant_lower_bound_left_shift` in `Chap02/Proposition_2_26`, the canonical one-variable
  secant owner for convex scalar slices;
- `ConvexOn.strict_lt_and_secant_lower_bound_of_nonpos_right` in `Chap02/Proposition_2_26`, the
  shared owner bridge from convexity plus sign data at a right endpoint to the secant lower bound;
- `secant_lower_bound_left_shift_of_finite_values` in `Chap02/Proposition_2_26`, the chapter's
  finite-value bridge for extended-real convex slices.

Best owner abstraction:
- the fixed scalar slice `estimatedValue k X : ℝ → ℝ` under the shared owner theorem
  `ConvexOn.strict_lt_and_secant_lower_bound_of_nonpos_right`.

Primitive data:
- the scalar function `estimatedValue k X`;
- a real right endpoint `τ`;
- the order comparison `t0 < t1 ≤ τ`;
- the sign data `0 < estimatedValue k X t1` and `estimatedValue k X τ ≤ 0`.

Derived API:
- the strict inequality and displayed secant lower bound from the shared owner theorem.

Source/core/bridge triage:
- source-facing: the chapter statement for the fixed scalar slice `estimatedValue k X` at a chosen
  real right endpoint `τ`;
- core/canonical: `ConvexOn.strict_lt_and_secant_lower_bound_of_nonpos_right`;
- bridge/view: the specialization of that owner theorem to the chapter notation on
  `Set.Iic τ`.
-/

/-- A nonpositive terminal value at the chosen right endpoint still yields the same
strict-right-endpoint conclusion and secant lower bound. -/
-- Proof sketch: apply
-- `ConvexOn.strict_lt_and_secant_lower_bound_of_nonpos_right` directly to the convex slice on
-- `Set.Iic τ`.
theorem estimatedValue_strict_lt_right_and_secant_lower_bound_of_nonpos_right
    {t0 t1 τ : ℝ}
    (ht01 : t0 < t1)
    (ht1_le_right : t1 ≤ τ)
    (hpositive : 0 < value t1)
    (hright_nonpos : value τ ≤ 0)
    (hconvex : ConvexOn ℝ (Set.Iic τ) value) :
    t1 < τ ∧
      value t0 ≥
        value t1 +
          ((t1 - t0) / (τ - t1)) * value t1 := by
  have ht0_mem : t0 ∈ Set.Iic τ := ht01.le.trans ht1_le_right
  exact
    hconvex.strict_lt_and_secant_lower_bound_of_nonpos_right
      ht0_mem
      (by simp)
      ht01
      ht1_le_right
      hpositive
      hright_nonpos

/-- Lemma 3.37: if `t₀ < t₁ ≤ τ`, the scalar model value `\hat f_k^*(X; t₁)` is positive,
`\hat f_k^*(X; τ) = 0`, and `t ↦ \hat f_k^*(X; t)` is convex on `(-∞, τ]`, then `τ > t₁` and
the displayed secant lower bound holds. -/
-- Proof sketch: this is the nonpositive-right-endpoint secant estimate above, specialized using
-- the stronger endpoint condition `value τ = 0`.
theorem estimatedValue_strict_lt_right_and_secant_lower_bound_of_eq_zero
    {t0 t1 τ : ℝ}
    (ht01 : t0 < t1)
    (ht1_le_right : t1 ≤ τ)
    (hpositive : 0 < value t1)
    (hright_zero : value τ = 0)
    (hconvex : ConvexOn ℝ (Set.Iic τ) value) :
    τ > t1 ∧
      value t0 ≥
        value t1 +
          ((t1 - t0) / (τ - t1)) * value t1 := by
  simpa [gt_iff_lt] using
    (estimatedValue_strict_lt_right_and_secant_lower_bound_of_nonpos_right
      estimatedValue
      k
      X
      ht01
      ht1_le_right
      hpositive
      (by simp [hright_zero])
      hconvex)

end

/-! ### Proposition_3_37 (from Chap03) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace FunctionalConstraintSubgradientMethod

variable {problem : ProjectedMultipleConstraintFirstOrderProblem E 1}

/- Proposition 3.37 is a bridge/view item in the single-constraint subgradient-method domain.

Sampled owner-style declarations:
- `FunctionalConstraintSubgradientMethod.takesObjectiveStep` in `Algorithm_3_3`, the owner
  objective-branch predicate;
- `FunctionalConstraintSubgradientMethod.admissibleIndices` and
  `FunctionalConstraintSubgradientMethod.mem_admissibleIndices_iff` in `Algorithm_3_3`, the
  method-owned textbook family `𝒜(N)` and its canonical membership criterion;
- `ConstrainedSubgradientMethod324.admissibleIndices` in `Theorem_3_2_3` and
  `ApproximateLagrangeMultiplierSwitchingMethod.inactiveConstraintIndices` in `Definition_3_45`,
  the chapter pattern for finite prefix index families on `Fin (N + 1)`.

Best owner abstraction:
- source-facing: the family `method.admissibleIndices N`;
- core/canonical: `takesObjectiveStep`;
- bridge/view: Proposition 3.37 itself, extracting the displayed inequality from membership in
  `𝒜(N)`.

Primitive data:
- the run `method : FunctionalConstraintSubgradientMethod problem`;
- the finite prefix length `N`.

Derived API:
- the owner-level family `method.admissibleIndices N`;
- the canonical membership criterion
  `k ∈ method.admissibleIndices N ↔ problem.constraints 0 (method k) ≤ method.ε`;
- the implication below.

This file no longer re-owns `𝒜(N)` or its membership lemma. Those belong to the method owner in
`Algorithm_3_3`; Proposition 3.37 is the downstream source-facing consequence theorem. -/

/-- Proposition 3.37: every index in `𝒜(N)` is a Case A iteration, hence its iterate satisfies
`f̄(x_k) ≤ ε`. -/
theorem constraint_le_epsilon_of_mem_admissibleIndices
    (method : FunctionalConstraintSubgradientMethod problem) (N : ℕ) {k : Fin (N + 1)}
    (hk : k ∈ method.admissibleIndices N) :
    problem.constraints 0 (method k) ≤ method.ε := by
  -- Membership in the owner-level admissible-index family is exactly the Case A inequality.
  exact (method.mem_admissibleIndices_iff N).1 hk

end FunctionalConstraintSubgradientMethod

end

/-! ### Theorem_3_37 (from Chap03) -/
noncomputable section

universe u v

section Minimax

variable {X : Type u} {U : Type v}

variable [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
variable [TopologicalSpace U] [AddCommGroup U] [Module ℝ U]
  [IsTopologicalAddGroup U] [ContinuousSMul ℝ U]

/-
Theorem 3.37 lies in the chapter's compact convex-concave minimax domain.

Sampled owner-style declarations:
- mathlib `Sion.exists_isSaddlePointOn`, the real-valued compact convex-concave saddle-point
  owner;
- mathlib `ContinuousOn.lowerSemicontinuousOn` and `ContinuousOn.upperSemicontinuousOn`, the
  canonical slice-semicontinuity bridges extracted from continuity on `P × S`;
- mathlib `ConvexOn.quasiconvexOn` and `ConcaveOn.quasiconcaveOn`, the standard bridges from the
  source convex/concave slice hypotheses to the Sion owner assumptions.
- mathlib `IsLeast.csInf_eq` and `IsGreatest.csSup_eq`, the canonical order-theoretic bridges from
  attained extrema to the source `sInf`/`sSup` expressions.

Best owner abstraction:
- source-facing: the minimax equality between the upper and lower slice-value expressions on `P`
  and `S`;
- core/canonical: `Sion.exists_isSaddlePointOn`;
- bridge/view: the slice semicontinuity and quasiconvexity/quasiconcavity consequences of the
  source continuity and convexity/concavity hypotheses, together with the `IsLeast`/`IsGreatest`
  extremum identifications of the two value images.

Primitive data:
- the compact nonempty primal set `P`;
- the compact nonempty dual set `S`;
- the payoff `Ψ`;
- continuity of `Ψ` on `P × S`;
- convexity of the `x`-slices and concavity of the `u`-slices.

Derived API:
- convexity of `P` and `S`, recovered from one primal slice and one dual slice because the slice
  owners `ConvexOn` and `ConcaveOn` already bundle convexity of the feasible set;
- the upper slice-value function `x ↦ sSup ((fun u ↦ Ψ x u) '' S)`;
- the lower slice-value function `u ↦ sInf ((fun x ↦ Ψ x u) '' P)`;
- the minimax equality below.

This refinement keeps the source-facing equality but replaces the local proof-level wheel with a
direct specialization of the canonical owner `Sion.exists_isSaddlePointOn`. The only extra work
is to derive the owner hypotheses already latent in the source data, then collapse the resulting
saddle point to the textbook `sInf`/`sSup` equality through the canonical attained-extremum
bridges `IsLeast.csInf_eq` and `IsGreatest.csSup_eq`.
-/

/-- Theorem 3.37: for a continuous convex-concave payoff on compact nonempty sets `P` and `S`,
the infimum of the upper slice-value function `x ↦ sSup ((fun u ↦ Ψ x u) '' S)` over `P` equals
the supremum of the lower slice-value function `u ↦ sInf ((fun x ↦ Ψ x u) '' P)` over `S`. -/
theorem compact_convex_concave_minimax
    {P : Set X} {S : Set U} (hP_nonempty : P.Nonempty) (hS_nonempty : S.Nonempty)
    (hP_compact : IsCompact P) (hS_compact : IsCompact S)
    {Ψ : X → U → ℝ}
    (hΨ_cont : ContinuousOn (fun z : X × U ↦ Ψ z.1 z.2) (Set.prod P S))
    (hΨ_convex : ∀ u ∈ S, ConvexOn ℝ P (fun x ↦ Ψ x u))
    (hΨ_concave : ∀ x ∈ P, ConcaveOn ℝ S (fun u ↦ Ψ x u)) :
    sInf ((fun x ↦ sSup ((fun u ↦ Ψ x u) '' S)) '' P) =
      sSup ((fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) '' S) := by
  let u0 : U := hS_nonempty.choose
  have hu0 : u0 ∈ S := hS_nonempty.choose_spec
  let x0 : X := hP_nonempty.choose
  have hx0 : x0 ∈ P := hP_nonempty.choose_spec
  have hP_convex : Convex ℝ P := (hΨ_convex u0 hu0).1
  have hS_convex : Convex ℝ S := (hΨ_concave x0 hx0).1
  have hcont_x : ∀ u ∈ S, ContinuousOn (fun x ↦ Ψ x u) P := by
    intro u hu
    simpa using
      hΨ_cont.comp
        (show ContinuousOn (fun x : X ↦ (x, u)) P from continuousOn_id.prodMk continuousOn_const)
        (show Set.MapsTo (fun x : X ↦ (x, u)) P (Set.prod P S) from
          fun x hx ↦ ⟨hx, hu⟩)
  have hcont_u : ∀ x ∈ P, ContinuousOn (fun u ↦ Ψ x u) S := by
    intro x hx
    simpa using
      hΨ_cont.comp
        (show ContinuousOn (fun u : U ↦ (x, u)) S from continuousOn_const.prodMk continuousOn_id)
        (show Set.MapsTo (fun u : U ↦ (x, u)) S (Set.prod P S) from
          fun u hu ↦ ⟨hx, hu⟩)
  obtain ⟨xStar, hxStar, uStar, huStar, hsaddle⟩ :=
    Sion.exists_isSaddlePointOn
      hP_nonempty hP_convex hP_compact
      (fun u hu ↦ (hcont_x u hu).lowerSemicontinuousOn)
      (fun u hu ↦ (hΨ_convex u hu).quasiconvexOn)
      hS_convex hS_nonempty hS_compact
      (fun x hx ↦ (hcont_u x hx).upperSemicontinuousOn)
      (fun x hx ↦ (hΨ_concave x hx).quasiconcaveOn)
  have hupper_xStar : sSup ((fun u ↦ Ψ xStar u) '' S) = Ψ xStar uStar := by
    exact (show IsGreatest ((fun u ↦ Ψ xStar u) '' S) (Ψ xStar uStar) from by
      refine ⟨⟨uStar, huStar, rfl⟩, ?_⟩
      intro z hz
      rcases hz with ⟨u, hu, rfl⟩
      exact hsaddle xStar hxStar u hu).csSup_eq
  have hlower_uStar : sInf ((fun x ↦ Ψ x uStar) '' P) = Ψ xStar uStar := by
    exact (show IsLeast ((fun x ↦ Ψ x uStar) '' P) (Ψ xStar uStar) from by
      refine ⟨⟨xStar, hxStar, rfl⟩, ?_⟩
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact hsaddle x hx uStar huStar).csInf_eq
  have hupper_least :
      IsLeast ((fun x ↦ sSup ((fun u ↦ Ψ x u) '' S)) '' P) (Ψ xStar uStar) := by
    refine ⟨⟨xStar, hxStar, hupper_xStar⟩, ?_⟩
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    have hmem : Ψ x uStar ∈ (fun u ↦ Ψ x u) '' S := ⟨uStar, huStar, rfl⟩
    have hbdd : BddAbove ((fun u ↦ Ψ x u) '' S) :=
      (hS_compact.image_of_continuousOn (hcont_u x hx)).bddAbove
    exact le_trans (hsaddle x hx uStar huStar) (le_csSup hbdd hmem)
  have hlower_greatest :
      IsGreatest ((fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) '' S) (Ψ xStar uStar) := by
    refine ⟨⟨uStar, huStar, hlower_uStar⟩, ?_⟩
    intro z hz
    rcases hz with ⟨u, hu, rfl⟩
    have hmem : Ψ xStar u ∈ (fun x ↦ Ψ x u) '' P := ⟨xStar, hxStar, rfl⟩
    have hbdd : BddBelow ((fun x ↦ Ψ x u) '' P) :=
      (hP_compact.image_of_continuousOn (hcont_x u hu)).bddBelow
    exact le_trans (csInf_le hbdd hmem) (hsaddle xStar hxStar u hu)
  calc
    sInf ((fun x ↦ sSup ((fun u ↦ Ψ x u) '' S)) '' P) = Ψ xStar uStar := hupper_least.csInf_eq
    _ = sSup ((fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) '' S) := hlower_greatest.csSup_eq.symm

end Minimax

end
