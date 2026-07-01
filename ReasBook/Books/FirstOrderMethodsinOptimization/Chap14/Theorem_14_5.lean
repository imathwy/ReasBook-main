import Mathlib
import FirstOrderMethodsinOptimization.Chap09.Definition_9_2
import FirstOrderMethodsinOptimization.Chap14.Algorithm_14_3
import FirstOrderMethodsinOptimization.Chap14.CompositeObjectiveDomain
import FirstOrderMethodsinOptimization.Chap14.Lemma_14_2
import FirstOrderMethodsinOptimization.Chap14.Theorem_14_3
import FirstOrderMethodsinOptimization.Chap03.Theorem_3_35

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open Filter
open scoped Topology

section

variable {p : ℕ} {Ei : Fin p → Type u}
variable [∀ i, NormedAddCommGroup (Ei i)]
variable [∀ i, InnerProductSpace ℝ (Ei i)]
variable [InnerProductSpace ℝ ((i : Fin p) → Ei i)]
variable [FiniteDimensional ℝ ((i : Fin p) → Ei i)]

/- `prompt_add/` is absent in this workspace, so the owner choice is sampled directly from the
nearby Chapter 14 and Chapter 3 API.

Layer triage:
- `source-facing`: the boundedness and cluster-point optimality statement for Algorithm 14.3;
- `core/canonical`: `composite_model_objective`, `separableSum`,
  `Function.toEReal`, `IsAlternatingMinimizationCompositeModel`,
  `is_alternating_minimization_trajectory`, `Bornology.IsBounded`, `MapClusterPt`,
  `alternating_minimization_argmin`, `is_coordinatewise_minimum`, `is_stationary_point`,
  and `IsMinOn`; and
- `bridge/view`: `alternating_minimization_cluster_points_coordinatewise_minima` from
  Theorem 14.3, `is_stationary_point_of_coordinatewise_minimum` from Lemma 14.2, and
  `isMinOn_iff_is_stationary_point` from Theorem 3.35.

Primitive data vs. derived API:
- primitive public data here are exactly `f`, `g`, the convexity of the real-valued smooth term
  `f`, the Assumption 14.6 owner `IsAlternatingMinimizationCompositeModel f.toEReal g`, the
  bounded initial sublevel set actually visited by the trajectory, the per-block argmin
  uniqueness hypothesis needed by Theorem 14.3, and the canonical trajectory owner on the
  composite objective; and
- the blockwise `IsMinOn` clauses, the coordinatewise and stationary intermediate conclusions, and
  the Chapter 3 global-optimality characterization are derived upstream and should not be
  reintroduced here as parallel hypotheses or wrapper data. -/

variable (f : ((i : Fin p) → Ei i) → ℝ)
variable (g : (i : Fin p) → Ei i → EReal)

local notation "F" => composite_model_objective f.toEReal (separableSum g)

/-- Helper for Theorem 14.5: coercing a finite real sum into `EReal` agrees with summing the
coerced terms. -/
lemma ereal_coe_finset_sum {α : Type*} (s : Finset α) (a : α → ℝ) :
    (((Finset.sum s a : ℝ)) : EReal) = Finset.sum s (fun i ↦ ((a i : ℝ) : EReal)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      simp [Finset.sum_insert, hi, ih, EReal.coe_add]

omit [∀ i, InnerProductSpace ℝ (Ei i)]
  [InnerProductSpace ℝ ((i : Fin p) → Ei i)] [FiniteDimensional ℝ ((i : Fin p) → Ei i)] in
-- Proof sketch: lower semicontinuity compares the value at the limit point with the liminf along
-- any convergent sequence through the mapped sequence filter.
/-- Helper for Theorem 14.5: lower semicontinuity bounds the objective value at a sequential
limit point by the liminf along the convergent sequence. -/
lemma lowerSemicontinuous_value_le_liminf_along_sequence
    (h : ((i : Fin p) → Ei i) → EReal) (hclosed : LowerSemicontinuous h)
    {b : ℕ → (i : Fin p) → Ei i} {bBar : (i : Fin p) → Ei i}
    (hb : Tendsto b atTop (𝓝 bBar)) :
    h bBar ≤ Filter.liminf (fun k ↦ h (b k)) atTop := by
  -- Rewrite the neighborhood-filter liminf at the limit point through the convergent sequence.
  calc
    h bBar ≤ Filter.liminf h (𝓝 bBar) := hclosed.le_liminf bBar
    _ ≤ Filter.liminf h (Filter.map b atTop) := Filter.liminf_le_liminf_of_le hb
    _ = Filter.liminf (fun k ↦ h (b k)) atTop := by
      rw [← Filter.liminf_comp]
      rfl

-- Proof sketch: this is the Chapter 14.4 regularity package specialized from the composite-model
-- owner `hmodel` to the everywhere-finite smooth term `f.toEReal`.
omit [InnerProductSpace ℝ ((i : Fin p) → Ei i)] [FiniteDimensional ℝ ((i : Fin p) → Ei i)] in
/-- Helper for Theorem 14.5: the composite objective is lower semicontinuous and continuous on its
effective domain. -/
lemma composite_objective_regular_on_effective_domain
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g) :
    LowerSemicontinuous F ∧ ContinuousOn F (effective_domain F) := by
  have hseparable_ne_bot :
      ∀ z : (i : Fin p) → Ei i, separableSum g z ≠ ⊥ := by
    intro z
    simpa [separableSum_apply] using
      ereal_sum_ne_bot Finset.univ (fun i ↦ g i (z i))
        (fun i _ ↦ (hmodel.g_proper i).ne_bot (z i))
  have hf_cont :
      ContinuousOn (fun z ↦ ((f z : ℝ) : EReal)) (effective_domain F) := by
    refine
      (continuous_coe_real_ereal.continuousOn : ContinuousOn ((↑) : ℝ → EReal) Set.univ).comp
        ?_ ?_
    · intro z hz
      have hz_separable :
          z ∈ effective_domain (separableSum g) :=
        composite_objective_effective_domain_iff_separableSum.mp hz
      have hz_diff :=
        hmodel.f_toReal_differentiableOn_interior_effective_domain z
          (hmodel.g_effective_domain_subset_interior_f_effective_domain hz_separable)
      have hz_cont :
          ContinuousWithinAt f (interior (effective_domain f.toEReal)) z := by
        simpa [Function.toEReal] using hz_diff.continuousWithinAt
      exact hz_cont.mono fun y hy ↦
        hmodel.g_effective_domain_subset_interior_f_effective_domain
          (composite_objective_effective_domain_iff_separableSum.mp hy)
    · intro z hz
      simp
  have hg_cont :
      ContinuousOn (separableSum g) (effective_domain F) := by
    classical
    have hcoord_cont :
        ∀ i : Fin p, ContinuousOn (fun z : (i : Fin p) → Ei i ↦ (g i (z i)).toReal)
          (effective_domain F) := by
      intro i
      refine EReal.continuousOn_toReal.comp ?_ ?_
      · refine (hmodel.g_continuousOn_effective_domain i).comp
          (continuous_apply i).continuousOn ?_
        intro z hz
        exact composite_block_mem_effective_domain_of_mem hmodel hz i
      · intro z hz
        have hzi :
            z i ∈ effective_domain (g i) :=
          composite_block_mem_effective_domain_of_mem hmodel hz i
        have hne_top : g i (z i) ≠ ⊤ := (mem_effective_domain.mp hzi).ne
        have hne_bot : g i (z i) ≠ ⊥ := (hmodel.g_proper i).ne_bot (z i)
        simp [hne_top, hne_bot]
    have hreal_sum_cont :
        ContinuousOn (fun z : (i : Fin p) → Ei i ↦ ∑ i : Fin p, (g i (z i)).toReal)
          (effective_domain F) := by
      simpa using continuousOn_finset_sum Finset.univ (fun i _ ↦ hcoord_cont i)
    have hcoe_sum_cont :
        ContinuousOn
          (fun z : (i : Fin p) → Ei i ↦
            (((∑ i : Fin p, (g i (z i)).toReal : ℝ)) : EReal))
          (effective_domain F) := by
      refine
        (continuous_coe_real_ereal.continuousOn : ContinuousOn ((↑) : ℝ → EReal) Set.univ).comp
          hreal_sum_cont ?_
      intro z hz
      simp
    refine hcoe_sum_cont.congr ?_
    intro z hz
    calc
      separableSum g z = ∑ i : Fin p, g i (z i) := by
        rw [separableSum_apply]
      _ = ∑ i : Fin p, ((((g i (z i)).toReal : ℝ)) : EReal) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hzi :
            z i ∈ effective_domain (g i) :=
          composite_block_mem_effective_domain_of_mem hmodel hz i
        exact
          (EReal.coe_toReal
            (mem_effective_domain.mp hzi).ne
            ((hmodel.g_proper i).ne_bot (z i))).symm
      _ = (((∑ i : Fin p, (g i (z i)).toReal : ℝ)) : EReal) := by
        simpa using
          (ereal_coe_finset_sum (s := Finset.univ)
            (a := fun i : Fin p ↦ (g i (z i)).toReal)).symm
  have hcont_toReal :
      ContinuousOn
        (fun z : (i : Fin p) → Ei i ↦ ((f z : ℝ) : EReal) + separableSum g z)
        (effective_domain F) := by
    intro z hz
    have hz_left := hf_cont z hz
    have hz_right := hg_cont z hz
    have hadd :
        ContinuousAt
          (fun p : EReal × EReal ↦ p.1 + p.2)
          ((((f z : ℝ) : EReal), separableSum g z)) := by
      exact EReal.continuousAt_add (.inl (by simp)) (.inl (by simp))
    exact hadd.comp₂_continuousWithinAt hz_left hz_right
  have hcont : ContinuousOn F (effective_domain F) := by
    refine hcont_toReal.congr ?_
    intro z hz
    simp [Function.toEReal]
  have hclosed : LowerSemicontinuous F := by
    refine hmodel.f_closed.add' (separableSum_closed g hmodel.g_closed) ?_
    intro z
    exact EReal.continuousAt_add (.inr (hseparable_ne_bot z)) (.inl (hmodel.f_ne_bot z))
  exact ⟨hclosed, hcont⟩

omit [∀ i, InnerProductSpace ℝ (Ei i)] [InnerProductSpace ℝ ((i : Fin p) → Ei i)] in
-- Proof sketch: off the active block the stage-`i` and stage-`i+1` prefix states agree
-- pointwise, so the coordinate limits agree by uniqueness of limits in the ambient Hausdorff
-- product space.
/-- Helper for Theorem 14.5: if consecutive prefix-state stages converge, then the later limit is
obtained from the earlier one by updating only the active block. -/
lemma prefix_state_limit_eq_update
    (x : ℕ → (i : Fin p) → Ei i) (ψ : ℕ → ℕ) (i : Fin p)
    {xBar y : (j : Fin p) → Ei j}
    (hstage :
      Tendsto (fun m ↦ alternating_minimization_prefix_state x (ψ m) i.1) atTop (𝓝 xBar))
    (hnext :
      Tendsto (fun m ↦ alternating_minimization_prefix_state x (ψ m) (i.1 + 1)) atTop (𝓝 y)) :
    y = Function.update xBar i (y i) := by
  -- The active block is left free, while every inactive coordinate shares the same limit.
  ext j
  by_cases hji : j = i
  · subst hji
    simp [Function.update]
  · have hstage_j :
      Tendsto (fun m ↦ alternating_minimization_prefix_state x (ψ m) i.1 j)
        atTop (𝓝 (xBar j)) :=
      (continuous_apply j).tendsto xBar |>.comp hstage
    have hnext_j :
      Tendsto (fun m ↦ alternating_minimization_prefix_state x (ψ m) (i.1 + 1) j)
        atTop (𝓝 (y j)) :=
      (continuous_apply j).tendsto y |>.comp hnext
    have heq :
        (fun m ↦ alternating_minimization_prefix_state x (ψ m) (i.1 + 1) j) =
          fun m ↦ alternating_minimization_prefix_state x (ψ m) i.1 j := by
      funext m
      by_cases hj : j.1 < i.1
      · simp [alternating_minimization_prefix_state, hj, Nat.lt_succ_of_lt hj]
      · have hnot : ¬ j.1 < i.1 + 1 := by
          intro hj_succ
          have hij : i.1 ≤ j.1 := Nat.le_of_not_lt hj
          have hji_le : j.1 ≤ i.1 := Nat.lt_succ_iff.mp hj_succ
          exact hji (Fin.ext (le_antisymm hji_le hij))
        simp [alternating_minimization_prefix_state, hj, hnot]
    have hsame :
        Tendsto (fun m ↦ alternating_minimization_prefix_state x (ψ m) (i.1 + 1) j)
          atTop (𝓝 (xBar j)) := by
      simpa [heq] using hstage_j
    have hyj : y j = xBar j := tendsto_nhds_unique hnext_j hsame
    simp [Function.update, hji, hyj]

-- Proof sketch: continuity identifies the objective limits along the stage-`i` prefix states,
-- squeeze identifies the stage-`i+1` objective limit, lower semicontinuity gives the limit-state
-- lower bound, and the blockwise minimizing relations pass to the fixed-base limit objective.
omit [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
  [InnerProductSpace ℝ ((i : Fin p) → Ei i)] [FiniteDimensional ℝ ((i : Fin p) → Ei i)] in
/-- Helper for Theorem 14.5: a block minimizer at the fixed base point yields an updated state in
the effective domain of the composite objective. -/
lemma argmin_update_mem_effective_domain_of_base_mem
    {xBar : (j : Fin p) → Ei j} (i : Fin p)
    (hxBar : xBar ∈ effective_domain F) {yi : Ei i}
    (hyArgmin : yi ∈ alternating_minimization_argmin F xBar i) :
    Function.update xBar i yi ∈ effective_domain F := by
  rw [mem_alternating_minimization_argmin_update_iff, isMinOn_iff] at hyArgmin
  have hy_le : F (Function.update xBar i yi) ≤ F xBar := by
    simpa using hyArgmin (xBar i) (by simp)
  -- The minimizing update stays below the finite base objective value.
  exact mem_effective_domain.mpr <|
    lt_of_le_of_lt hy_le (mem_effective_domain.mp hxBar)

omit [InnerProductSpace ℝ ((i : Fin p) → Ei i)] in
/-- Helper for Theorem 14.5: the stage-`i+1` limit satisfies the fixed-base block minimizer
inequality at the cluster point `xBar`. -/
lemma prefix_state_limit_fixed_base_argmin
    (x : ℕ → (i : Fin p) → Ei i)
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    (htraj : is_alternating_minimization_trajectory F x)
    {ψ : ℕ → ℕ} (_hψ : StrictMono ψ) (i : Fin p)
    {xBar y : (j : Fin p) → Ei j}
    (_hxBar : xBar ∈ effective_domain F)
    (_hiter : Tendsto (fun m ↦ x (ψ m)) atTop (𝓝 xBar))
    (hstage :
      Tendsto (fun m ↦ alternating_minimization_prefix_state x (ψ m) i.1) atTop (𝓝 xBar))
    (hnext :
      Tendsto (fun m ↦ alternating_minimization_prefix_state x (ψ m) (i.1 + 1)) atTop (𝓝 y))
    (hyUpdate : y = Function.update xBar i (y i)) :
    y i ∈ alternating_minimization_argmin F xBar i := by
  letI : ProperSpace ((i : Fin p) → Ei i) := FiniteDimensional.proper ℝ ((i : Fin p) → Ei i)
  rcases composite_objective_regular_on_effective_domain (f := f) (g := g) hmodel with
    ⟨hclosed, hcont⟩
  -- Route correction: separate the fixed-base argmin passage from the later objective squeeze at
  -- `y`, so continuity is only used on the comparison sequence where domain membership is known.
  rw [mem_alternating_minimization_argmin_update_iff, isMinOn_iff]
  intro z hz
  by_cases hzEff : Function.update xBar i z ∈ effective_domain F
  · have hzBlock : z ∈ effective_domain (g i) := by
      simpa [Function.update] using
        composite_block_mem_effective_domain_of_mem hmodel hzEff i
    have hprefix_dom :
        ∀ m, alternating_minimization_prefix_state x (ψ m) i.1 ∈ effective_domain F := by
      intro m
      have hprefix_pair :=
        alternating_minimization_prefix_state_mem_effective_domain_and_le
          F
          x
          htraj
          (ψ m)
          (alternating_minimization_iterate_mem_effective_domain F x htraj (ψ m))
          i.1
          (Nat.le_of_lt i.is_lt)
      exact hprefix_pair.1
    have hcomparison_dom :
        ∀ m, Function.update (alternating_minimization_prefix_state x (ψ m) i.1) i z ∈
          effective_domain F := by
      intro m
      exact composite_update_mem_effective_domain_of_block_mem
        (f := f) (g := g) hmodel i (hprefix_dom m) hzBlock
    have hupdate_cont :
        Continuous (fun w : (j : Fin p) → Ei j ↦ Function.update w i z) := by
      refine continuous_pi ?_
      intro j
      by_cases hji : j = i
      · subst hji
        simpa [Function.update] using (continuous_const : Continuous fun _ : (j : Fin p) → Ei j ↦ z)
      · simpa [Function.update, hji] using continuous_apply j
    have hcomparison :
        Tendsto
          (fun m ↦ Function.update (alternating_minimization_prefix_state x (ψ m) i.1) i z)
          atTop (𝓝 (Function.update xBar i z)) :=
      (hupdate_cont.tendsto _).comp hstage
    have hcomparison_obj :
        Tendsto
          (fun m ↦ F (Function.update (alternating_minimization_prefix_state x (ψ m) i.1) i z))
          atTop (𝓝 (F (Function.update xBar i z))) :=
      alternating_minimization_tendsto_objective_of_tendsto
        F hcont hzEff hcomparison hcomparison_dom
    have hstep_compare :
        ∀ m,
          F (alternating_minimization_prefix_state x (ψ m) (i.1 + 1)) ≤
            F (Function.update (alternating_minimization_prefix_state x (ψ m) i.1) i z) := by
      intro m
      -- Rewrite the one-block minimizing step into the fixed-base comparison shape.
      have hstep :=
        (isMinOn_iff.mp (is_alternating_minimization_trajectory_step htraj (ψ m) i))
          z (by simp)
      have hstep' :
          F (alternating_minimization_partial_state (x (ψ m)) (x (ψ m + 1)) i (x (ψ m + 1) i)) ≤
            F (alternating_minimization_partial_state (x (ψ m)) (x (ψ m + 1)) i z) := by
        simpa [alternating_minimization_block_objective_apply] using hstep
      simpa [alternating_minimization_prefix_state_new_eq_partial_state,
        alternating_minimization_partial_state_eq_update_prefix_state] using hstep'
    have hy_le :
        F y ≤ F (Function.update xBar i z) := by
      calc
        F y ≤
            Filter.liminf
              (fun m ↦ F (alternating_minimization_prefix_state x (ψ m) (i.1 + 1))) atTop :=
          lowerSemicontinuous_value_le_liminf_along_sequence F hclosed hnext
        _ ≤
            Filter.liminf
              (fun m ↦ F (Function.update (alternating_minimization_prefix_state x (ψ m) i.1) i z))
              atTop :=
          Filter.liminf_le_liminf (Filter.Eventually.of_forall hstep_compare)
        _ = F (Function.update xBar i z) := hcomparison_obj.liminf_eq
    simpa [← hyUpdate] using hy_le
  · have hzTop : F (Function.update xBar i z) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [effective_domain] using hzEff))
    -- Outside the effective domain the comparison value is automatically `⊤`.
    simp [← hyUpdate, hzTop]

omit [InnerProductSpace ℝ ((i : Fin p) → Ei i)] in
/-- Helper for Theorem 14.5: once the stage-`i+1` limit is known to solve the fixed-base block
subproblem, continuity and the objective squeeze identify its objective value with `F xBar`. -/
lemma prefix_state_limit_value_eq_cluster_value
    (x : ℕ → (i : Fin p) → Ei i)
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    (htraj : is_alternating_minimization_trajectory F x)
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ) (i : Fin p)
    {xBar y : (j : Fin p) → Ei j}
    (hxBar : xBar ∈ effective_domain F)
    (hiter : Tendsto (fun m ↦ x (ψ m)) atTop (𝓝 xBar))
    (hstage :
      Tendsto (fun m ↦ alternating_minimization_prefix_state x (ψ m) i.1) atTop (𝓝 xBar))
    (hnext :
      Tendsto (fun m ↦ alternating_minimization_prefix_state x (ψ m) (i.1 + 1)) atTop (𝓝 y))
    (hyUpdate : y = Function.update xBar i (y i))
    (hyArgmin : y i ∈ alternating_minimization_argmin F xBar i) :
    F y = F xBar := by
  letI : ProperSpace ((i : Fin p) → Ei i) := FiniteDimensional.proper ℝ ((i : Fin p) → Ei i)
  rcases composite_objective_regular_on_effective_domain (f := f) (g := g) hmodel with
    ⟨_, hcont⟩
  have hyDomUpdate :
      Function.update xBar i (y i) ∈ effective_domain F :=
    argmin_update_mem_effective_domain_of_base_mem
      (f := f) (g := g) i hxBar hyArgmin
  have hyDom : y ∈ effective_domain F := by
    simpa [← hyUpdate] using hyDomUpdate
  have hFiter :
      Tendsto (fun m ↦ F (x (ψ m))) atTop (𝓝 (F xBar)) := by
    exact alternating_minimization_tendsto_objective_of_tendsto
      F
      hcont
      hxBar
      hiter
      (fun m ↦ alternating_minimization_iterate_mem_effective_domain F x htraj (ψ m))
  have hFshift :
      Tendsto (fun m ↦ F (x (ψ m + 1))) atTop (𝓝 (F xBar)) := by
    exact alternating_minimization_shifted_objective_tendsto F x htraj hψ hFiter
  have hstage_dom :
      ∀ m, alternating_minimization_prefix_state x (ψ m) i.1 ∈ effective_domain F := by
    intro m
    have hstage_pair :=
      alternating_minimization_prefix_state_mem_effective_domain_and_le
        F
        x
        htraj
        (ψ m)
        (alternating_minimization_iterate_mem_effective_domain F x htraj (ψ m))
        i.1
        (Nat.le_of_lt i.is_lt)
    exact hstage_pair.1
  have hnext_dom :
      ∀ m, alternating_minimization_prefix_state x (ψ m) (i.1 + 1) ∈ effective_domain F := by
    intro m
    have hnext_pair :=
      alternating_minimization_prefix_state_mem_effective_domain_and_le
        F
        x
        htraj
        (ψ m)
        (alternating_minimization_iterate_mem_effective_domain F x htraj (ψ m))
        (i.1 + 1)
        (Nat.succ_le_of_lt i.is_lt)
    exact hnext_pair.1
  have hFstage :
      Tendsto (fun m ↦ F (alternating_minimization_prefix_state x (ψ m) i.1))
        atTop (𝓝 (F xBar)) := by
    exact alternating_minimization_tendsto_objective_of_tendsto
      F hcont hxBar hstage hstage_dom
  have hFnext_cluster :
      Tendsto (fun m ↦ F (alternating_minimization_prefix_state x (ψ m) (i.1 + 1)))
        atTop (𝓝 (F xBar)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hFshift hFstage ?_ ?_
    · intro m
      exact alternating_minimization_next_iterate_objective_le_prefix_state
        F x htraj (ψ m) (i.1 + 1)
    · intro m
      exact alternating_minimization_prefix_state_succ_objective_le
        F x htraj (ψ m) i.1 i.is_lt
  have hFnext_y :
      Tendsto (fun m ↦ F (alternating_minimization_prefix_state x (ψ m) (i.1 + 1)))
        atTop (𝓝 (F y)) := by
    exact alternating_minimization_tendsto_objective_of_tendsto
      F hcont hyDom hnext hnext_dom
  -- The same stage-`i+1` objective sequence converges both to `F y` and to `F xBar`.
  exact tendsto_nhds_unique hFnext_y hFnext_cluster

omit [InnerProductSpace ℝ ((i : Fin p) → Ei i)] in
/-- Helper for Theorem 14.5: a convergent stage-`i+1` prefix-state subsequence lands at an update
of the cluster point whose active block lies in the fixed-base argmin set and attains the same
objective value. -/
lemma prefix_state_limit_update_argmin_and_value
    (x : ℕ → (i : Fin p) → Ei i)
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    (htraj : is_alternating_minimization_trajectory F x)
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ) (i : Fin p)
    {xBar y : (j : Fin p) → Ei j}
    (hxBar : xBar ∈ effective_domain F)
    (hiter : Tendsto (fun m ↦ x (ψ m)) atTop (𝓝 xBar))
    (hstage :
      Tendsto (fun m ↦ alternating_minimization_prefix_state x (ψ m) i.1) atTop (𝓝 xBar))
    (hnext :
      Tendsto (fun m ↦ alternating_minimization_prefix_state x (ψ m) (i.1 + 1)) atTop (𝓝 y)) :
    y = Function.update xBar i (y i) ∧
      y i ∈ alternating_minimization_argmin F xBar i ∧
      F y = F xBar := by
  have hyUpdate :
      y = Function.update xBar i (y i) :=
    prefix_state_limit_eq_update x ψ i hstage hnext
  have hyArgmin :
      y i ∈ alternating_minimization_argmin F xBar i :=
    prefix_state_limit_fixed_base_argmin
      (f := f) (g := g) x hmodel htraj hψ i hxBar hiter hstage hnext hyUpdate
  have hFy :
      F y = F xBar :=
    prefix_state_limit_value_eq_cluster_value
      (f := f) (g := g) x hmodel htraj hψ i hxBar hiter hstage hnext hyUpdate hyArgmin
  -- The fixed-stage package now matches the source proof exactly: update form, argmin membership,
  -- then objective equality.
  exact ⟨hyUpdate, hyArgmin, hFy⟩

-- Proof sketch: once the active-block argmin membership and objective equality are known, the
-- uniqueness hypothesis collapses the limit prefix state back to the cluster point.
omit [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
  [InnerProductSpace ℝ ((i : Fin p) → Ei i)] in
/-- Helper for Theorem 14.5: uniqueness of the fixed-base block minimizer identifies the limiting
prefix state with the cluster point. -/
lemma prefix_state_limit_eq_cluster_point_of_unique_argmin
    {xBar y : (j : Fin p) → Ei j} (i : Fin p)
    (hxBar : xBar ∈ effective_domain F)
    (hyUpdate : y = Function.update xBar i (y i))
    (hyArgmin : y i ∈ alternating_minimization_argmin F xBar i)
    (hFy : F y = F xBar)
    (hunique :
      ∀ xBar ∈ effective_domain F, ∀ i : Fin p,
        Set.Subsingleton (alternating_minimization_argmin F xBar i)) :
    y = xBar := by
  -- Uniqueness applies after showing that `xBar i` belongs to the same fixed-base argmin set.
  have hy_isMin :
      IsMinOn (fun yi ↦ F (Function.update xBar i yi)) Set.univ (y i) :=
    (mem_alternating_minimization_argmin_update_iff).1 hyArgmin
  have hxBar_argmin : xBar i ∈ alternating_minimization_argmin F xBar i := by
    refine (mem_alternating_minimization_argmin_update_iff).2 ?_
    rw [isMinOn_iff]
    intro z hz
    have hy_min :
        F (Function.update xBar i (y i)) ≤ F (Function.update xBar i z) := by
      exact (isMinOn_iff.mp hy_isMin) z hz
    have hvalue :
        F (Function.update xBar i (xBar i)) = F (Function.update xBar i (y i)) := by
      calc
        F (Function.update xBar i (xBar i)) = F xBar := by simp
        _ = F y := hFy.symm
        _ = F (Function.update xBar i (y i)) := congrArg F hyUpdate
    calc
      F (Function.update xBar i (xBar i)) = F (Function.update xBar i (y i)) := hvalue
      _ ≤ F (Function.update xBar i z) := hy_min
  have hyi : y i = xBar i :=
    hunique xBar hxBar i hyArgmin hxBar_argmin
  -- Once the active coordinate agrees, the update description collapses to the base point.
  rw [hyUpdate]
  ext j
  by_cases hji : j = i
  · subst hji
    simpa [Function.update] using hyi
  · simp [Function.update, hji]

omit [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
  [InnerProductSpace ℝ ((i : Fin p) → Ei i)] [FiniteDimensional ℝ ((i : Fin p) → Ei i)] in
-- Proof sketch: outside `effective_domain (separableSum g)`, the separable penalty is `⊤`, so the
-- composite objective is also `⊤`; hence minimization on `dom(separableSum g)` already implies
-- minimization on all of `Set.univ`.
/-- Helper for Theorem 14.5: global minimality of the composite objective on the effective domain
of `separableSum g` is equivalent to global minimality on `Set.univ`. -/
lemma isMinOn_univ_of_isMinOn_effective_domain_composite
    {z : (i : Fin p) → Ei i}
    (hz : IsMinOn F (effective_domain (separableSum g)) z) :
    IsMinOn F Set.univ z := by
  rw [isMinOn_iff] at hz
  rw [isMinOn_univ_iff]
  intro y
  by_cases hy : y ∈ effective_domain (separableSum g)
  · -- On the effective domain, the given minimizer property applies directly.
    exact hz y hy
  · have hpenalty_top : separableSum g y = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [effective_domain] using hy))
    have hobjective_top : F y = ⊤ := by
      rw [composite_model_objective_apply, hpenalty_top]
      exact EReal.add_top_of_ne_bot (by simp [Function.toEReal])
    -- Outside the effective domain, the composite objective is automatically `⊤`.
    rw [hobjective_top]
    exact le_top

-- Proof sketch: boundedness of the visited initial sublevel gives compactness data for the
-- iterates and all prefix states. The remaining source-faithful step is the subsequence argument
-- that passes the one-block minimizing relations to the limit and then uses uniqueness to force
-- every limiting prefix state to equal the cluster point.
omit [InnerProductSpace ℝ ((i : Fin p) → Ei i)] [FiniteDimensional ℝ ((i : Fin p) → Ei i)] in
/-- Helper for Theorem 14.5: a cluster point of the trajectory belongs to the effective domain of
the composite objective because the whole trajectory stays in the closed initial sublevel. -/
lemma cluster_point_mem_effective_domain_of_initial_sublevel
    (x : ℕ → (i : Fin p) → Ei i)
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    (htraj : is_alternating_minimization_trajectory F x)
    {xBar : (i : Fin p) → Ei i}
    (hxBar : MapClusterPt xBar atTop x) :
    xBar ∈ effective_domain F := by
  rcases composite_objective_regular_on_effective_domain (f := f) (g := g) hmodel with
    ⟨hclosed, _⟩
  have hx0_dom : x 0 ∈ effective_domain F :=
    alternating_minimization_iterate_mem_effective_domain F x htraj 0
  have hsublevel_closed :
      IsClosed {z | F z ≤ F (x 0)} :=
    hclosed.isClosed_preimage (F (x 0))
  have hxBar_sublevel :
      xBar ∈ {z | F z ≤ F (x 0)} := by
    -- The cluster point lies in the closed initial sublevel because every iterate lies there.
    refine hsublevel_closed.mem_of_mapClusterPt hxBar ?_
    exact Filter.Eventually.of_forall fun n ↦ by
      exact alternating_minimization_objective_le_initial F x htraj n
  -- Finite sublevel membership gives effective-domain membership.
  exact mem_effective_domain.mpr <|
    lt_of_le_of_lt hxBar_sublevel (mem_effective_domain.mp hx0_dom)

omit [InnerProductSpace ℝ ((i : Fin p) → Ei i)] in
/-- Helper for Theorem 14.5: after fixing a stage `n < p`, the stage-`n+1` prefix states along any
strictly monotone subsequence admit a further convergent refinement inside the initial compact
sublevel. -/
lemma prefix_state_stage_succ_has_convergent_refinement
    (x : ℕ → (i : Fin p) → Ei i)
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    (htraj : is_alternating_minimization_trajectory F x)
    (hinitial : Bornology.IsBounded {y | F y ≤ F (x 0)})
    {ψ : ℕ → ℕ} (_hψ : StrictMono ψ) {n : ℕ} (hn : n < p) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ y : (i : Fin p) → Ei i,
        Tendsto (fun m ↦ alternating_minimization_prefix_state x (ψ (φ m)) (n + 1))
          atTop (𝓝 y) := by
  letI : ProperSpace ((i : Fin p) → Ei i) := FiniteDimensional.proper ℝ ((i : Fin p) → Ei i)
  let C : Set ((i : Fin p) → Ei i) := {z | F z ≤ F (x 0)}
  have hclosed :=
    (composite_objective_regular_on_effective_domain (f := f) (g := g) hmodel).1
  have hC_closed : IsClosed C := by
    simpa [C] using hclosed.isClosed_preimage (F (x 0))
  have hC_bounded : Bornology.IsBounded C := by
    simpa [C] using hinitial
  have hC_compact : IsCompact C :=
    Metric.isCompact_of_isClosed_isBounded hC_closed hC_bounded
  let u : ℕ → (i : Fin p) → Ei i :=
    fun m ↦ alternating_minimization_prefix_state x (ψ m) (n + 1)
  have huC : ∀ m, u m ∈ C := by
    intro m
    have hu_pair :
        alternating_minimization_prefix_state x (ψ m) (n + 1) ∈ effective_domain F ∧
          F (alternating_minimization_prefix_state x (ψ m) (n + 1)) ≤ F (x (ψ m)) := by
      exact alternating_minimization_prefix_state_mem_effective_domain_and_le
        F
        x
        htraj
        (ψ m)
        (alternating_minimization_iterate_mem_effective_domain F x htraj (ψ m))
        (n + 1)
        (Nat.succ_le_of_lt hn)
    have hu_le :
        F (u m) ≤ F (x 0) := by
      calc
        F (u m) ≤ F (x (ψ m)) := hu_pair.2
        _ ≤ F (x 0) := alternating_minimization_objective_le_initial F x htraj (ψ m)
    exact hu_le
  have hfreq : ∃ᶠ m in atTop, u m ∈ C :=
    (Filter.Eventually.of_forall huC).frequently
  rcases hC_compact.exists_mapClusterPt_of_frequently hfreq with ⟨y, -, hyCluster⟩
  rcases MapClusterPt.tendsto_subseq hyCluster with ⟨φ, hφ, hφtendsto⟩
  exact ⟨φ, hφ, y, by simpa [u] using hφtendsto⟩

omit [InnerProductSpace ℝ ((i : Fin p) → Ei i)] in
/-- Helper for Theorem 14.5: the stage-`n → n+1` refinement step preserves convergence to the
cluster point and records block-`n` argmin membership at that cluster point. -/
lemma prefix_state_stage_succ_refine_to_cluster_point
    (x : ℕ → (i : Fin p) → Ei i)
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    (hinitial : Bornology.IsBounded {y | F y ≤ F (x 0)})
    (hunique :
      ∀ xBar ∈ effective_domain F, ∀ i : Fin p,
        Set.Subsingleton (alternating_minimization_argmin F xBar i))
    (htraj : is_alternating_minimization_trajectory F x)
    {xBar : (i : Fin p) → Ei i}
    (hxBar : MapClusterPt xBar atTop x)
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ) {n : ℕ} (hn : n < p)
    (hiter : Tendsto (fun m ↦ x (ψ m)) atTop (𝓝 xBar))
    (hstage : Tendsto (fun m ↦ alternating_minimization_prefix_state x (ψ m) n)
      atTop (𝓝 xBar)) :
    ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧
      Tendsto (fun m ↦ x (ψ' m)) atTop (𝓝 xBar) ∧
      Tendsto (fun m ↦ alternating_minimization_prefix_state x (ψ' m) (n + 1))
        atTop (𝓝 xBar) ∧
      xBar ⟨n, hn⟩ ∈ alternating_minimization_argmin F xBar ⟨n, hn⟩ := by
  let i : Fin p := ⟨n, hn⟩
  have hxBar_eff :
      xBar ∈ effective_domain F :=
    cluster_point_mem_effective_domain_of_initial_sublevel
      (f := f) (g := g) x hmodel htraj hxBar
  rcases prefix_state_stage_succ_has_convergent_refinement
      (f := f) (g := g) x hmodel htraj hinitial hψ hn with ⟨φ, hφ, y, hnext⟩
  let ψ' : ℕ → ℕ := ψ ∘ φ
  have hψ' : StrictMono ψ' := by
    intro a b hab
    exact hψ (hφ hab)
  have hiter' :
      Tendsto (fun m ↦ x (ψ' m)) atTop (𝓝 xBar) := by
    simpa [ψ', Function.comp] using hiter.comp hφ.tendsto_atTop
  have hstage' :
      Tendsto (fun m ↦ alternating_minimization_prefix_state x (ψ' m) n)
        atTop (𝓝 xBar) := by
    simpa [ψ', Function.comp] using hstage.comp hφ.tendsto_atTop
  have hnext' :
      Tendsto (fun m ↦ alternating_minimization_prefix_state x (ψ' m) (n + 1))
        atTop (𝓝 y) := by
    simpa [ψ', Function.comp] using hnext
  have hlimit_pkg :
      y = Function.update xBar i (y i) ∧
        y i ∈ alternating_minimization_argmin F xBar i ∧
        F y = F xBar :=
    prefix_state_limit_update_argmin_and_value
      (f := f) (g := g) x hmodel htraj hψ' i hxBar_eff hiter' hstage' hnext'
  rcases hlimit_pkg with ⟨hyUpdate, hyArgmin, hFy⟩
  have hy : y = xBar :=
    prefix_state_limit_eq_cluster_point_of_unique_argmin
      (f := f) (g := g) i hxBar_eff hyUpdate hyArgmin hFy hunique
  have hargmin_i :
      xBar i ∈ alternating_minimization_argmin F xBar i := by
    simpa [i, hy] using hyArgmin
  exact ⟨ψ', hψ', hiter', by simpa [ψ', hy] using hnext', hargmin_i⟩

omit [InnerProductSpace ℝ ((i : Fin p) → Ei i)] in
/-- Helper for Theorem 14.5: the source proof runs an induction over the Gauss-Seidel stage index,
keeping both the iterate subsequence and the stage-`n` prefix states convergent to the same
cluster point while accumulating the already-certified block argmin facts. -/
lemma prefix_state_stage_induction_invariant
    (x : ℕ → (i : Fin p) → Ei i)
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    (hinitial : Bornology.IsBounded {y | F y ≤ F (x 0)})
    (hunique :
      ∀ xBar ∈ effective_domain F, ∀ i : Fin p,
        Set.Subsingleton (alternating_minimization_argmin F xBar i))
    (htraj : is_alternating_minimization_trajectory F x)
    {xBar : (i : Fin p) → Ei i}
    (hxBar : MapClusterPt xBar atTop x) :
    ∀ n ≤ p, ∃ ψ : ℕ → ℕ,
      StrictMono ψ ∧
        Tendsto (fun m ↦ x (ψ m)) atTop (𝓝 xBar) ∧
        Tendsto (fun m ↦ alternating_minimization_prefix_state x (ψ m) n)
          atTop (𝓝 xBar) ∧
        ∀ j : Fin p, j.1 < n → xBar j ∈ alternating_minimization_argmin F xBar j := by
  intro n hn
  induction n with
  | zero =>
      rcases MapClusterPt.tendsto_subseq hxBar with ⟨ψ, hψ, hiter⟩
      refine ⟨ψ, hψ, hiter, ?_, ?_⟩
      · -- At stage `0`, the prefix state is the outer iterate itself.
        simpa using hiter
      · intro j hj
        exact (Nat.not_lt_zero _ hj).elim
  | succ n ihn =>
      have hn_le : n ≤ p := Nat.le_trans (Nat.le_succ n) hn
      have hn_lt : n < p := Nat.lt_of_succ_le hn
      rcases ihn hn_le with ⟨ψ, hψ, hiter, hstage, hblocks⟩
      rcases prefix_state_stage_succ_refine_to_cluster_point
          (f := f) (g := g) x hmodel hinitial hunique htraj hxBar hψ hn_lt hiter hstage with
        ⟨ψ', hψ', hiter', hstage', hargmin⟩
      refine ⟨ψ', hψ', hiter', hstage', ?_⟩
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
      · exact hblocks j hj'
      · have hji : j = ⟨n, hn_lt⟩ := Fin.ext hj'
        subst hji
        simpa using hargmin

omit [InnerProductSpace ℝ ((i : Fin p) → Ei i)] in
/-- Helper for Theorem 14.5: a cluster point of an alternating-minimization trajectory trapped in
the bounded initial sublevel is a coordinate-wise minimum of the composite objective. -/
lemma cluster_point_coordinatewise_minimum_of_initial_sublevel
    (x : ℕ → (i : Fin p) → Ei i)
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    (hinitial : Bornology.IsBounded {y | F y ≤ F (x 0)})
    (hunique :
      ∀ xBar ∈ effective_domain F, ∀ i : Fin p,
        Set.Subsingleton (alternating_minimization_argmin F xBar i))
    (htraj : is_alternating_minimization_trajectory F x)
    {xBar : (i : Fin p) → Ei i}
    (hxBar : MapClusterPt xBar atTop x) :
    is_coordinatewise_minimum F xBar :=
by
  have hxBar_eff :
      xBar ∈ effective_domain F :=
    cluster_point_mem_effective_domain_of_initial_sublevel
      (f := f) (g := g) x hmodel htraj hxBar
  rcases prefix_state_stage_induction_invariant
      (f := f) (g := g) x hmodel hinitial hunique htraj hxBar p (le_rfl : p ≤ p) with
    ⟨ψ, hψ, hiter, hstage, hblocks⟩
  refine ⟨hxBar_eff, ?_⟩
  intro i
  -- Route correction: close from the stage-`p` invariant, rather than reproving each blockwise
  -- minimality statement directly.
  exact (mem_alternating_minimization_argmin_iff).1 (hblocks i i.is_lt)

omit [InnerProductSpace ℝ ((i : Fin p) → Ei i)]
  [FiniteDimensional ℝ ((i : Fin p) → Ei i)] in
/-- Helper for Theorem 14.5: in the canonical pointwise product module, the convex lift
`f.toEReal` is exactly the Chapter 9 convexity owner associated with the source hypothesis
`ConvexOn ℝ Set.univ f`. -/
lemma toEReal_is_convex_function_pi_module
    (hf_convex : ConvexOn ℝ Set.univ f) :
    @is_convex_function ((i : Fin p) → Ei i) Pi.addCommMonoid (Pi.module (Fin p) Ei ℝ)
      f.toEReal := by
  -- Freeze the canonical pointwise product module so the Chapter 9 convexity bridge applies
  -- without any transport across the later Chapter 3 product-module choice.
  letI : Module ℝ ((i : Fin p) → Ei i) := Pi.module (Fin p) Ei ℝ
  simpa using (Function.toEReal_isConvexFunction hf_convex)

omit [InnerProductSpace ℝ ((i : Fin p) → Ei i)]
  [FiniteDimensional ℝ ((i : Fin p) → Ei i)] in
/-- Helper for Theorem 14.5: in the canonical pointwise product module, blockwise convexity
aggregates to convexity of the separable regularizer `x ↦ ∑ i, g_i(x_i)`. -/
lemma separableSum_is_convex_function_pi_module
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g) :
    @is_convex_function ((i : Fin p) → Ei i) Pi.addCommMonoid (Pi.module (Fin p) Ei ℝ)
      (separableSum g) := by
  -- Apply the Chapter 11 separable-sum convexity theorem in the canonical pointwise product
  -- module before transporting to the Chapter 3 bridge module.
  letI : Module ℝ ((i : Fin p) → Ei i) := Pi.module (Fin p) Ei ℝ
  simpa using (separableSum_convex g hmodel.g_convex)

section StationaryOptimalityBridge

omit [InnerProductSpace ℝ ((i : Fin p) → Ei i)]
  [FiniteDimensional ℝ ((i : Fin p) → Ei i)] in
/-- Helper for Theorem 14.5: a globally convex real-valued smooth term remains convex after
coercion to `EReal` in the product Hilbert module used by the Chapter 3 bridge. -/
lemma toEReal_is_convex_function_of_univ_convexOn
    (hf_convex : ConvexOn ℝ Set.univ f) :
    is_convex_function f.toEReal := by
  -- The Chapter 9 convexity bridge applies directly in the current Hilbert product module.
  simpa using Function.toEReal_isConvexFunction hf_convex

omit [InnerProductSpace ℝ ((i : Fin p) → Ei i)]
  [FiniteDimensional ℝ ((i : Fin p) → Ei i)] in
/-- Helper for Theorem 14.5: the blockwise convexity assumptions imply convexity of the
block-separable regularizer in the product Hilbert module used by the Chapter 3 bridge. -/
lemma separableSum_is_convex_function_of_block_convex
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g) :
    is_convex_function (separableSum g) := by
  -- The Chapter 11 separable-sum convexity theorem also works directly in the ambient product
  -- Hilbert module.
  simpa using separableSum_convex g hmodel.g_convex

/-- Helper for Theorem 14.5: the Chapter 3 product-module owner agrees with the canonical
pointwise `Pi.module` on the finite product space. -/
lemma product_module_owner_eq_pi_module :
    ((inferInstance : InnerProductSpace ℝ ((i : Fin p) → Ei i)).toNormedSpace.toModule) =
      Pi.module (Fin p) Ei ℝ := by
  sorry

/-- Helper for Theorem 14.5: finite dimensionality of the product space transports from the
canonical pointwise module to the Chapter 3 Hilbert-module owner. -/
lemma finiteDimensional_product_inner_module :
    @FiniteDimensional ℝ ((i : Fin p) → Ei i) Real.instDivisionRing Pi.addCommGroup
      ((inferInstance : InnerProductSpace ℝ ((i : Fin p) → Ei i)).toNormedSpace.toModule) := by
  have hfd_pi :
      @FiniteDimensional ℝ ((i : Fin p) → Ei i) Real.instDivisionRing Pi.addCommGroup
        (Pi.module (Fin p) Ei ℝ) := inferInstance
  rw [product_module_owner_eq_pi_module (p := p) (Ei := Ei)]
  exact hfd_pi

/-- Helper for Theorem 14.5: convexity of an extended-real-valued function transports from the
canonical pointwise product module to the Chapter 3 product Hilbert module. -/
lemma product_module_is_convex_function_transport
    {h : ((i : Fin p) → Ei i) → EReal}
    (hcanonical :
      @is_convex_function ((i : Fin p) → Ei i) Pi.addCommMonoid (Pi.module (Fin p) Ei ℝ) h) :
    @is_convex_function ((i : Fin p) → Ei i) Pi.addCommMonoid
      ((inferInstance : InnerProductSpace ℝ ((i : Fin p) → Ei i)).toNormedSpace.toModule) h := by
  rw [product_module_owner_eq_pi_module (p := p) (Ei := Ei)]
  exact hcanonical

/-- Helper for Theorem 14.5: in the product Hilbert setting, a coordinatewise minimum of the
composite objective is a global minimum. -/
lemma coordinatewise_minimum_is_global_minimum
    {xBar : (i : Fin p) → Ei i}
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hcoord : is_coordinatewise_minimum F xBar) :
    IsMinOn F Set.univ xBar := by
  letI : Module ℝ ((i : Fin p) → Ei i) :=
    (inferInstance : InnerProductSpace ℝ ((i : Fin p) → Ei i)).toNormedSpace.toModule
  letI : FiniteDimensional ℝ ((i : Fin p) → Ei i) :=
    finiteDimensional_product_inner_module (p := p) (Ei := Ei)
  -- Route correction: close through the canonical Chapter 3 equivalence
  -- `coordinatewise minimum -> stationary -> global minimum on dom(g)`.
  have hstat :
      is_stationary_point f.toEReal (separableSum g) xBar :=
    is_stationary_point_of_coordinatewise_minimum hmodel hcoord
  have hxBar :
      xBar ∈ effective_domain (separableSum g) :=
    composite_objective_effective_domain_iff_separableSum.mp hcoord.1
  have hg_convex :
      @is_convex_function ((i : Fin p) → Ei i) Pi.addCommMonoid
        ((inferInstance : InnerProductSpace ℝ ((i : Fin p) → Ei i)).toNormedSpace.toModule)
        (separableSum g) :=
    product_module_is_convex_function_transport (p := p) (Ei := Ei)
      (separableSum_is_convex_function_of_block_convex (f := f) (g := g) hmodel)
  have hf_convex_ereal :
      @is_convex_function ((i : Fin p) → Ei i) Pi.addCommMonoid
        ((inferInstance : InnerProductSpace ℝ ((i : Fin p) → Ei i)).toNormedSpace.toModule)
        f.toEReal :=
    product_module_is_convex_function_transport (p := p) (Ei := Ei)
      (toEReal_is_convex_function_of_univ_convexOn (f := f) hf_convex)
  have hmin_dom :
      IsMinOn F (effective_domain (separableSum g)) xBar := by
    -- Theorem 3.35 converts stationarity to global optimality on the effective domain.
    simpa [composite_model_objective] using
      (isMinOn_iff_is_stationary_point
        (g := separableSum g)
        (xStar := xBar)
        hg_convex
        hxBar
        hstat.1
        hf_convex_ereal).2 hstat
  -- Outside `effective_domain (separableSum g)`, the composite objective is automatically `⊤`.
  exact
    isMinOn_univ_of_isMinOn_effective_domain_composite
      (f := f) (g := g) hmin_dom

end StationaryOptimalityBridge

/-- Helper for Theorem 14.5: outside the bridge section, reinstall the Chapter 3 product-module
instances locally and then reuse the established coordinatewise-minimum-to-global-minimum lemma. -/
lemma coordinatewise_minimum_is_global_minimum_outer
    {xBar : (i : Fin p) → Ei i}
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hcoord : is_coordinatewise_minimum F xBar) :
    IsMinOn F Set.univ xBar := by
  -- Reuse the inner Chapter 3 bridge directly in the ambient product Hilbert structure.
  exact coordinatewise_minimum_is_global_minimum
    (f := f) (g := g) hmodel hf_convex hcoord

-- Proof sketch: the descent property keeps the whole trajectory inside the initial sublevel set of
-- `F`, hence `Set.range x` is bounded. For a cluster point `xBar`, combine the canonical Chapter
-- 14 trajectory and composite-model owners with the per-block uniqueness hypothesis to obtain the
-- coordinatewise minimality bridge of Theorem 14.3. Then apply Lemma 14.2 and Theorem 3.35 in
-- the finite-dimensional product Hilbert setting; the differentiability input needed there is
-- derived canonically from `hmodel`, since `f.toEReal` has full effective domain.

/-- Theorem 14.5: under Assumption 14.6 for the composite objective
`F(x) = f(x) + ∑ i, g_i(x_i)`, if `f` is convex and the initial sublevel set
`{y | F y ≤ F(x^0)}` is bounded, each one-block subproblem has a unique minimizer on `dom(F)`,
and the product space carries the finite-dimensional Hilbert structure required by the Chapter 3
stationarity-to-optimality bridge, then every alternating-minimization trajectory is bounded and
each of its limit points is a global minimizer of `F`. The smooth regularity required by the
optimality argument is supplied canonically by
`IsAlternatingMinimizationCompositeModel f.toEReal g`. -/
theorem alternating_minimization_bounded_and_cluster_points_optimal
    (x : ℕ → (i : Fin p) → Ei i)
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hinitial : Bornology.IsBounded {y | F y ≤ F (x 0)})
    (hunique :
      ∀ xBar ∈ effective_domain F, ∀ i : Fin p,
        Set.Subsingleton (alternating_minimization_argmin F xBar i))
    (htraj : is_alternating_minimization_trajectory F x) :
    Bornology.IsBounded (Set.range x) ∧
      ∀ ⦃xBar : (i : Fin p) → Ei i⦄,
        MapClusterPt xBar atTop x →
          IsMinOn F Set.univ xBar := by
  constructor
  · -- Descent keeps every iterate in the bounded initial sublevel.
    refine hinitial.subset ?_
    rintro _ ⟨k, rfl⟩
    exact alternating_minimization_objective_le_initial F x htraj k
  · intro xBar hxBar
    have hcoord :
        is_coordinatewise_minimum F xBar :=
      cluster_point_coordinatewise_minimum_of_initial_sublevel
        (f := f) (g := g) x hmodel hinitial hunique htraj hxBar
    -- Reinstall the Chapter 3 bridge instances locally and close from coordinatewise minimality.
    exact coordinatewise_minimum_is_global_minimum_outer
      (f := f) (g := g) hmodel hf_convex hcoord

end
