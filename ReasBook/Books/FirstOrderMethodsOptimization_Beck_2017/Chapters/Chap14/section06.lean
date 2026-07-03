import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_14_6 (from Chap14) -/
universe u

noncomputable section

variable {p : ℕ} {Ei : Fin p → Type u}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, NormedSpace ℝ (Ei i)]

/- `prompt_add/` is absent in this workspace, so the owner selection is sampled directly from the
nearby optimization files.

Layer triage:
- `source-facing`: the theorem-level `O(1 / k)` rate statement for alternating minimization with an
  explicit initial-sublevel radius witness;
- `core/canonical`: `IsAlternatingMinimizationCompositeModel`,
  `composite_model_objective`, `separableSum`, and the Chapter 10 convex-composite owner; and
- `bridge/view`: the source Assumption 14.10 data packaged below, together with the conversion
  theorems back to the Chapter 10 owner.

Domain sampling against the local project identifies the relevant owners:
- `IsAlternatingMinimizationCompositeModel` from Algorithm 14.3 for the standing blockwise
  regularity assumptions;
- `separableSum`, `composite_model_objective`, and `unconstrained_problem_solutions` for the
  aggregate objective and optimizer set;
- `IsFastProximalGradientProblem` from Chapter 10 as the local pattern for a smaller
  source-facing owner with composite-model bridges; and
- `IsConvexCompositeSmoothMinimizationProblem` as the Chapter 10 `core/canonical` owner for the
  aggregate convex composite problem; and
- `ConvexOn ℝ Set.univ` and `is_l_smooth_on _ Set.univ` for the real-valued smooth term.

Primitive data vs. derived API:
- the primitive source data reused by the rate theorem are exactly the Assumption 14.10 clauses
  below; and
- the Chapter 10 convex-composite owner and the weaker distance-to-optimal-set reformulations are
  derived bridge API.

Accordingly, this file keeps Assumption 14.10 as an auxiliary source-facing owner because later
rate theorems use it directly. Its primitive fields are only the textbook Assumption 14.10 data,
while the Chapter 14 and Chapter 10 composite-model owners are recovered below as bridge/view
API. The main public entry remains theorem-shaped rather than presenting that assumption class
itself as “Theorem 14.6”. -/

/-- Assumption 14.10 for the general `p`-block alternating-minimization problem: each block
penalty `g_i : E_i → (-∞, ∞]` is proper, closed, convex, and continuous on its effective domain,
the smooth term `f : E → ℝ` is convex and globally `L_f`-smooth, `XStar = X^*` is the nonempty
optimal set of `F(x) = f(x) + ∑ i, g_i(x_i)` with optimal value `FOpt = F_opt`, and every
positive sublevel of `F` stays within a uniformly bounded distance of every optimal point. The
Chapter 14 and Chapter 10 composite-model owners for `f.toEReal` are recovered below as derived
bridge API rather than stored as primitive data. -/
class IsAlternatingMinimizationConvexRateProblem
    (f : ((i : Fin p) → Ei i) → ℝ) (g : ∀ i : Fin p, Ei i → EReal)
    (XStar : outParam (Set ((i : Fin p) → Ei i))) (FOpt : outParam ℝ)
    (Lf : outParam NNReal) : Prop where
  g_proper (i : Fin p) : IsProperExtendedRealFunction (g i)
  g_closed (i : Fin p) : LowerSemicontinuous (g i)
  g_convex (i : Fin p) : is_convex_function (g i)
  g_continuousOn_effective_domain (i : Fin p) :
    ContinuousOn (g i) (effective_domain (g i))
  f_convex : ConvexOn ℝ Set.univ f
  f_smooth : is_l_smooth_on f Set.univ Lf
  optimal_set_eq :
    XStar = unconstrained_problem_solutions
      (composite_model_objective f.toEReal (separableSum g))
  optimal_set_nonempty : XStar.Nonempty
  optimal_value_isGLB :
    IsGLB (Set.range (composite_model_objective f.toEReal (separableSum g))) (FOpt : EReal)
  bounded_sublevel_distance_to_each_optimal_point (α : PosReal) :
    ∃ Rα : PosReal, ∀ {x xStar : (i : Fin p) → Ei i},
      composite_model_objective f.toEReal (separableSum g) x ≤ ((α : ℝ) : EReal) →
      xStar ∈ XStar →
      ‖x - xStar‖ ≤ (Rα : ℝ)

namespace IsAlternatingMinimizationConvexRateProblem

open Metric

variable {f : ((i : Fin p) → Ei i) → ℝ} {g : ∀ i : Fin p, Ei i → EReal}
variable {XStar : Set ((i : Fin p) → Ei i)} {FOpt : ℝ} {Lf : NNReal}

local notation "F" => composite_model_objective f.toEReal (separableSum g)

/-- Assumption 14.10 canonically induces the Chapter 14 alternating-minimization composite-model
owner for the smooth term `f.toEReal` and the block penalties `g_i`. -/
theorem toIsAlternatingMinimizationCompositeModel
    (h : IsAlternatingMinimizationConvexRateProblem f g XStar FOpt Lf) :
    IsAlternatingMinimizationCompositeModel f.toEReal g where
  g_proper := h.g_proper
  g_closed := h.g_closed
  g_convex := h.g_convex
  g_continuousOn_effective_domain := h.g_continuousOn_effective_domain
  f_ne_bot x := by
    simp [Function.toEReal]
  f_closed := by
    have hcont : Continuous f := by
      refine continuous_iff_continuousAt.2 ?_
      intro x
      exact (h.f_smooth.1 x (by simp)).continuousAt
    exact Function.toEReal_lowerSemicontinuous_of_continuous hcont
  f_effective_domain_convex := by
    simpa [effective_domain, Function.toEReal] using
      (convex_univ : Convex ℝ (Set.univ : Set ((i : Fin p) → Ei i)))
  f_toReal_differentiableOn_interior_effective_domain := by
    intro x hx
    simpa [effective_domain, Function.toEReal] using
      (h.f_smooth.1 x (by simp)).differentiableWithinAt
  g_effective_domain_subset_interior_f_effective_domain := by
    intro x hx
    simp [effective_domain, Function.toEReal]

/-- Assumption 14.10 canonically induces the Chapter 10 composite smooth minimization owner for
the aggregate regularizer `x ↦ ∑ i, g_i(x_i)`. -/
theorem toIsCompositeSmoothMinimizationProblem
    (h : IsAlternatingMinimizationConvexRateProblem f g XStar FOpt Lf) :
    IsCompositeSmoothMinimizationProblem f.toEReal (separableSum g) XStar FOpt Lf := by
  let hmodel := h.toIsAlternatingMinimizationCompositeModel
  exact
    { f_ne_bot := hmodel.f_ne_bot
      g_proper := separableSum_proper g h.g_proper
      f_closed := hmodel.f_closed
      g_closed := separableSum_closed g h.g_closed
      g_convex := separableSum_convex g h.g_convex
      f_effective_domain_convex := hmodel.f_effective_domain_convex
      g_effective_domain_subset_interior_f_effective_domain :=
        hmodel.g_effective_domain_subset_interior_f_effective_domain
      f_toReal_smooth_on_interior_effective_domain := by
        simpa [effective_domain, Function.toEReal] using h.f_smooth
      optimal_set_eq := h.optimal_set_eq
      optimal_set_nonempty := h.optimal_set_nonempty
      optimal_value_isGLB := h.optimal_value_isGLB }

/-- Assumption 14.10 canonically induces the Chapter 10 convex composite smooth minimization owner
for the aggregate regularizer `x ↦ ∑ i, g_i(x_i)`. -/
theorem toIsConvexCompositeSmoothMinimizationProblem
    (h : IsAlternatingMinimizationConvexRateProblem f g XStar FOpt Lf) :
    IsConvexCompositeSmoothMinimizationProblem f.toEReal (separableSum g) XStar FOpt Lf := by
  let hcomposite := h.toIsCompositeSmoothMinimizationProblem
  exact
    { f_ne_bot := hcomposite.f_ne_bot
      g_proper := hcomposite.g_proper
      f_closed := hcomposite.f_closed
      g_closed := hcomposite.g_closed
      f_convex := Function.toEReal_isConvexFunction h.f_convex
      g_convex := hcomposite.g_convex
      g_effective_domain_subset_interior_f_effective_domain :=
        hcomposite.g_effective_domain_subset_interior_f_effective_domain
      f_toReal_smooth_on_interior_effective_domain :=
        hcomposite.f_toReal_smooth_on_interior_effective_domain
      optimal_set_eq := hcomposite.optimal_set_eq
      optimal_set_nonempty := hcomposite.optimal_set_nonempty
      optimal_value_isGLB := hcomposite.optimal_value_isGLB }

/-- The source-facing pairwise sublevel-radius bound in Assumption 14.10 implies the weaker
distance-to-optimal-set estimate on the same composite objective. -/
theorem bounded_sublevel_distance_to_optimal_set
    (h : IsAlternatingMinimizationConvexRateProblem f g XStar FOpt Lf)
    (α : PosReal) :
    ∃ Rα : PosReal,
      ∀ ⦃x : (i : Fin p) → Ei i⦄, F x ≤ ((α : ℝ) : EReal) → infDist x XStar ≤ Rα := by
  rcases h.bounded_sublevel_distance_to_each_optimal_point α with ⟨Rα, hRα⟩
  refine ⟨Rα, ?_⟩
  intro x hx
  rcases h.optimal_set_nonempty with ⟨xStar, hxStar⟩
  refine (infDist_le_dist_of_mem hxStar).trans ?_
  simpa [dist_eq_norm] using hRα hx hxStar

/-- If the initial objective value is bounded by a positive level `α`, then the same Assumption
14.10 radius controls the whole initial sublevel set in the weaker distance-to-optimal-set form
used by the rate analysis. -/
theorem bounded_initial_sublevel_distance_to_optimal_set
    (h : IsAlternatingMinimizationConvexRateProblem f g XStar FOpt Lf)
    {x0 : (i : Fin p) → Ei i} {α : PosReal}
    (hx0 : F x0 ≤ ((α : ℝ) : EReal)) :
    ∃ Rα : PosReal,
      ∀ ⦃x : (i : Fin p) → Ei i⦄, F x ≤ F x0 → infDist x XStar ≤ Rα := by
  rcases h.bounded_sublevel_distance_to_optimal_set α with ⟨Rα, hRα⟩
  refine ⟨Rα, ?_⟩
  intro x hx
  exact hRα (hx.trans hx0)

end IsAlternatingMinimizationConvexRateProblem

section

variable {f : ((i : Fin p) → Ei i) → ℝ} {g : ∀ i : Fin p, Ei i → EReal}
variable {XStar : Set ((i : Fin p) → Ei i)} {FOpt : ℝ} {Lf : NNReal}

local notation "F" => composite_model_objective f.toEReal (separableSum g)

/-- Helper for Theorem 14.6: every alternating-minimization iterate stays in the effective domain
of `F`, and every iterate remains in the initial sublevel set. -/
lemma trajectory_iterates_mem_effective_domain_and_initial_sublevel
    [IsAlternatingMinimizationConvexRateProblem f g XStar FOpt Lf]
    (x : ℕ → (i : Fin p) → Ei i)
    (htraj : is_alternating_minimization_trajectory F x) :
    ∀ k : ℕ, x k ∈ effective_domain F ∧ F (x k) ≤ F (x 0) := by
  let prefixState : ℕ → ℕ → ((i : Fin p) → Ei i) :=
    fun k n j ↦ if j.1 < n then x (k + 1) j else x k j
  -- The old mixed state in the `i`-th block subproblem is exactly the `n = i.1` prefix state.
  have hprefix_old_eq (k : ℕ) (i : Fin p) :
      prefixState k i.1 =
        alternating_minimization_partial_state (x k) (x (k + 1)) i (x k i) := by
    funext j
    by_cases hj : j.1 < i.1
    · simp [prefixState, alternating_minimization_partial_state, hj]
    · by_cases hji : j = i
      · subst hji
        simp [prefixState, alternating_minimization_partial_state, Function.update]
      · simp [prefixState, alternating_minimization_partial_state, hj, hji, Function.update]
  -- The updated mixed state after block `i` is the `n = i.1 + 1` prefix state.
  have hprefix_new_eq (k : ℕ) (i : Fin p) :
      prefixState k (i.1 + 1) =
        alternating_minimization_partial_state (x k) (x (k + 1)) i (x (k + 1) i) := by
    funext j
    by_cases hj : j.1 < i.1
    · simp [prefixState, alternating_minimization_partial_state, hj, Nat.lt_succ_of_lt hj]
    · by_cases hji : j = i
      · subst hji
        simp [prefixState, alternating_minimization_partial_state, Function.update]
      · have hnot : ¬ j.1 < i.1 + 1 := by
          intro hlt
          have hle : i.1 ≤ j.1 := Nat.le_of_not_lt hj
          have hge : j.1 ≤ i.1 := Nat.lt_succ_iff.mp hlt
          exact hji (Fin.ext (le_antisymm hge hle))
        simp [prefixState, alternating_minimization_partial_state, hj, hji, hnot, Function.update]
  -- The Gauss-Seidel prefixes stay finite and descend from the start of the outer iteration.
  have hprefix_mem_le :
      ∀ k : ℕ, x k ∈ effective_domain F →
        ∀ n ≤ p, prefixState k n ∈ effective_domain F ∧ F (prefixState k n) ≤ F (x k) := by
    intro k hxk n hn
    induction n with
    | zero =>
        refine ⟨by simpa [prefixState] using hxk, ?_⟩
        simp [prefixState]
    | succ n ihn =>
        have hn_lt : n < p := Nat.lt_of_succ_le hn
        let i : Fin p := ⟨n, hn_lt⟩
        have hold : prefixState k n ∈ effective_domain F ∧ F (prefixState k n) ≤ F (x k) :=
          ihn (Nat.le_of_lt hn_lt)
        -- Compare the newly updated block with the old block value using the trajectory argmin.
        have hcompare :
            F (prefixState k (n + 1)) ≤ F (prefixState k n) := by
          have hstep_compare :=
            (isMinOn_iff.mp (htraj.step_isMinOn k i)) (x k i) (by simp)
          rw [hprefix_new_eq k i, hprefix_old_eq k i]
          exact hstep_compare
        -- Finiteness propagates because the new prefix value is no larger than the old finite value.
        have hnew_mem : prefixState k (n + 1) ∈ effective_domain F := by
          refine mem_effective_domain.mpr ?_
          exact lt_of_le_of_lt hcompare (mem_effective_domain.mp hold.1)
        exact ⟨hnew_mem, le_trans hcompare hold.2⟩
  -- Iterate finiteness and global descent follow by closing the whole `p`-block cycle.
  have hx_mem_le : ∀ k : ℕ, x k ∈ effective_domain F ∧ F (x k) ≤ F (x 0) := by
    intro k
    induction k with
    | zero =>
        exact ⟨htraj.zero_mem_effective_domain, le_rfl⟩
    | succ k ih =>
        have hcycle : prefixState k p ∈ effective_domain F ∧ F (prefixState k p) ≤ F (x k) :=
          hprefix_mem_le k ih.1 p (le_rfl : p ≤ p)
        have hxnext_eq : prefixState k p = x (k + 1) := by
          funext j
          simp [prefixState, j.2]
        refine ⟨?_, ?_⟩
        · simpa [hxnext_eq] using hcycle.1
        · exact le_trans (by simpa [hxnext_eq] using hcycle.2) ih.2
  intro k
  exact hx_mem_le k

/-- Helper for Theorem 14.6: every iterate objective gap is nonnegative because each iterate is
finite and the optimal value is the greatest lower bound of the objective range. -/
lemma alternating_minimization_objective_gap_nonneg
    [hproblem : IsAlternatingMinimizationConvexRateProblem f g XStar FOpt Lf]
    (x : ℕ → (i : Fin p) → Ei i)
    (htraj : is_alternating_minimization_trajectory F x) :
    ∀ k : ℕ, 0 ≤ (F (x k)).toReal - FOpt := by
  let hconvex :
      IsConvexCompositeSmoothMinimizationProblem f.toEReal (separableSum g) XStar FOpt Lf :=
    IsAlternatingMinimizationConvexRateProblem.toIsConvexCompositeSmoothMinimizationProblem
      (f := f) (g := g) (XStar := XStar) (FOpt := FOpt) (Lf := Lf) hproblem
  have hiterates :=
    trajectory_iterates_mem_effective_domain_and_initial_sublevel
      (f := f) (g := g) (XStar := XStar) (FOpt := FOpt) (Lf := Lf) x htraj
  intro k
  have hxk_mem : x k ∈ effective_domain F := (hiterates k).1
  have hsum_ne_bot : separableSum g (x k) ≠ ⊥ := by
    simpa [separableSum_apply] using
      ereal_sum_ne_bot Finset.univ (fun i ↦ g i (x k i))
        (fun i _ ↦ hproblem.g_proper i |>.ne_bot (x k i))
  have hFx_ne_bot : F (x k) ≠ ⊥ := by
    rw [composite_model_objective_apply, EReal.add_ne_bot_iff]
    exact ⟨by simp [Function.toEReal], hsum_ne_bot⟩
  have hFx_coe :
      (((F (x k)).toReal : ℝ) : EReal) = F (x k) := by
    exact EReal.coe_toReal (lt_top_iff_ne_top.mp (mem_effective_domain.mp hxk_mem)) hFx_ne_bot
  have hlowerE : (FOpt : EReal) ≤ F (x k) := by
    exact hconvex.optimal_value_isGLB.1 ⟨x k, rfl⟩
  have hlowerE' : (FOpt : EReal) ≤ (((F (x k)).toReal : ℝ) : EReal) := by
    rwa [← hFx_coe] at hlowerE
  have hlower : FOpt ≤ (F (x k)).toReal := by
    exact_mod_cast hlowerE'
  linarith

/-- Helper for Theorem 14.6: the number of halving steps among the first `m` transitions of a
nonnegative scalar recurrence. -/
private abbrev halvingCount (a : ℕ → ℝ) (m : ℕ) : ℕ :=
  ((Finset.range m).filter fun k ↦ a (k + 1) ≤ a k / 2).card

/-- Helper for Theorem 14.6: the number of strict-half-ratio steps among the first `m`
transitions of a nonnegative scalar recurrence. -/
private abbrev strictHalfRatioCount (a : ℕ → ℝ) (m : ℕ) : ℕ :=
  ((Finset.range m).filter fun k ↦ a k / 2 < a (k + 1)).card

section ScalarRecurrence

variable {a : ℕ → ℝ} {γ : PosReal}

/-- Helper for Theorem 14.6: the quadratic step recurrence forces the scalar sequence to be
antitone. -/
private lemma quadratic_step_recurrence_antitone
    (hstep : ∀ k : ℕ, a k - a (k + 1) ≥ (1 / (γ : ℝ)) * (a (k + 1)) ^ (2 : ℕ)) :
    Antitone a := by
  -- Each step decreases because the quadratic term on the right-hand side is nonnegative.
  have hsucc : ∀ k : ℕ, a (k + 1) ≤ a k := by
    intro k
    have hsq_nonneg : 0 ≤ (1 / (γ : ℝ)) * (a (k + 1)) ^ (2 : ℕ) := by
      exact mul_nonneg (one_div_nonneg.mpr (PosReal.coe_pos γ).le) (sq_nonneg (a (k + 1)))
    linarith [hstep k]
  exact antitone_nat_of_succ_le hsucc

/-- Helper for Theorem 14.6: the halving count gains one exactly when the latest step halves. -/
private lemma halvingCount_succ (m : ℕ) :
    halvingCount a (m + 1) =
      halvingCount a m + if a (m + 1) ≤ a m / 2 then 1 else 0 := by
  classical
  by_cases hm : a (m + 1) ≤ a m / 2
  · rw [halvingCount, halvingCount, Finset.range_add_one, Finset.filter_insert]
    simp [hm]
  · rw [halvingCount, halvingCount, Finset.range_add_one, Finset.filter_insert]
    simp [hm]

/-- Helper for Theorem 14.6: the strict-half-ratio count gains one exactly when the latest step
stays above the half ratio. -/
private lemma strictHalfRatioCount_succ (m : ℕ) :
    strictHalfRatioCount a (m + 1) =
      strictHalfRatioCount a m + if a m / 2 < a (m + 1) then 1 else 0 := by
  classical
  by_cases hm : a m / 2 < a (m + 1)
  · rw [strictHalfRatioCount, strictHalfRatioCount, Finset.range_add_one, Finset.filter_insert]
    simp [hm]
  · rw [strictHalfRatioCount, strictHalfRatioCount, Finset.range_add_one, Finset.filter_insert]
    simp [hm]

/-- Helper for Theorem 14.6: each step is either halving or strict-half-ratio, so the two counts
partition the prefix. -/
private lemma halvingCount_add_strictHalfRatioCount_eq (m : ℕ) :
    halvingCount a m + strictHalfRatioCount a m = m := by
  classical
  -- The two predicates are exact complements on `ℝ`.
  simpa [halvingCount, strictHalfRatioCount, not_le] using
    (Finset.card_filter_add_card_filter_not
      (s := Finset.range m) (p := fun k ↦ a (k + 1) ≤ a k / 2))

/-- Helper for Theorem 14.6: a strict-half-ratio step yields a reciprocal increment bounded below
by `1 / (2γ)`. -/
private lemma reciprocal_increment_ge_one_div_two_gamma_of_strict_half_ratio
    (hstep : ∀ k : ℕ, a k - a (k + 1) ≥ (1 / (γ : ℝ)) * (a (k + 1)) ^ (2 : ℕ))
    (k : ℕ)
    (hak : 0 < a k)
    (hak_succ : 0 < a (k + 1))
    (hhalf : a k / 2 < a (k + 1)) :
    1 / (2 * (γ : ℝ)) ≤ 1 / a (k + 1) - 1 / a k := by
  have hγ_ne : (γ : ℝ) ≠ 0 := (PosReal.coe_pos γ).ne'
  have hrecip :
      1 / a (k + 1) - 1 / a k = (a k - a (k + 1)) / (a k * a (k + 1)) := by
    field_simp [hak.ne', hak_succ.ne']
  rw [hrecip]
  -- Divide the quadratic decrease inequality by the positive denominator.
  have hden_pos : 0 < a k * a (k + 1) := mul_pos hak hak_succ
  have hstep_div :
      ((1 / (γ : ℝ)) * (a (k + 1)) ^ (2 : ℕ)) / (a k * a (k + 1)) ≤
        (a k - a (k + 1)) / (a k * a (k + 1)) := by
    exact div_le_div_of_nonneg_right (hstep k) (le_of_lt hden_pos)
  have hsimpl :
      ((1 / (γ : ℝ)) * (a (k + 1)) ^ (2 : ℕ)) / (a k * a (k + 1)) =
        (1 / (γ : ℝ)) * (a (k + 1) / a k) := by
    field_simp [hak.ne', hak_succ.ne', hγ_ne]
  rw [hsimpl] at hstep_div
  have hratio : (1 / 2 : ℝ) < a (k + 1) / a k := by
    have hhalf' : (1 / 2 : ℝ) * a k < a (k + 1) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hhalf
    rw [lt_div_iff₀ hak]
    exact hhalf'
  have hleft :
      1 / (2 * (γ : ℝ)) = (1 / (γ : ℝ)) * (1 / 2 : ℝ) := by
    field_simp [hγ_ne]
  have hratio_mul :
      (1 / (γ : ℝ)) * (1 / 2 : ℝ) ≤ (1 / (γ : ℝ)) * (a (k + 1) / a k) := by
    exact mul_le_mul_of_nonneg_left hratio.le (one_div_nonneg.mpr (PosReal.coe_pos γ).le)
  calc
    1 / (2 * (γ : ℝ)) = (1 / (γ : ℝ)) * (1 / 2 : ℝ) := hleft
    _ ≤ (1 / (γ : ℝ)) * (a (k + 1) / a k) := hratio_mul
    _ ≤ (a k - a (k + 1)) / (a k * a (k + 1)) := hstep_div

/-- Helper for Theorem 14.6: every halving step contributes a factor `1 / 2` to the prefix
bound. -/
private lemma geometric_prefix_bound_of_halving_count
    (hstep : ∀ k : ℕ, a k - a (k + 1) ≥ (1 / (γ : ℝ)) * (a (k + 1)) ^ (2 : ℕ))
    (m : ℕ) :
    a m ≤ ((1 / 2 : ℝ) ^ halvingCount a m) * a 0 := by
  -- Induct on the prefix length and record whether the last step halves.
  induction m with
  | zero =>
      simp [halvingCount]
  | succ m ih =>
      have ha_anti := quadratic_step_recurrence_antitone (a := a) (γ := γ) hstep
      have hcount := halvingCount_succ (a := a) (m := m)
      by_cases hhalf : a (m + 1) ≤ a m / 2
      · -- A halving step adds one more factor `1 / 2`.
        rw [hcount, if_pos hhalf]
        calc
          a (m + 1) ≤ a m / 2 := hhalf
          _ ≤ (((1 / 2 : ℝ) ^ halvingCount a m) * a 0) / 2 := by
            exact div_le_div_of_nonneg_right ih (by norm_num)
          _ = ((1 / 2 : ℝ) ^ (halvingCount a m + 1)) * a 0 := by
            rw [div_eq_mul_inv, show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num, pow_succ]
            ring
      · -- Otherwise the halving count is unchanged, and monotonicity controls the last step.
        rw [hcount, if_neg hhalf]
        calc
          a (m + 1) ≤ a m := ha_anti (Nat.le_succ m)
          _ ≤ ((1 / 2 : ℝ) ^ halvingCount a m) * a 0 := ih

/-- Helper for Theorem 14.6: every strict-half-ratio step contributes a reciprocal increment of
size at least `1 / (2γ)`. -/
private lemma reciprocal_prefix_bound_of_strict_half_ratio_count
    (hstep : ∀ k : ℕ, a k - a (k + 1) ≥ (1 / (γ : ℝ)) * (a (k + 1)) ^ (2 : ℕ))
    (m : ℕ) (hm_pos : 0 < a m) :
    (strictHalfRatioCount a m : ℝ) / (2 * (γ : ℝ)) ≤ 1 / a m - 1 / a 0 := by
  -- Induct on the prefix length and split according to the final step of the dichotomy.
  induction m with
  | zero =>
      simp [strictHalfRatioCount]
  | succ m ih =>
      have ha_anti := quadratic_step_recurrence_antitone (a := a) (γ := γ) hstep
      have hcount := strictHalfRatioCount_succ (a := a) (m := m)
      have hm_prev_pos : 0 < a m := lt_of_lt_of_le hm_pos (ha_anti (Nat.le_succ m))
      by_cases hstrict : a m / 2 < a (m + 1)
      · -- A strict-half-ratio step adds one more reciprocal increment.
        have hprefix := ih hm_prev_pos
        have hinc :=
          reciprocal_increment_ge_one_div_two_gamma_of_strict_half_ratio
            (a := a) (γ := γ) hstep m hm_prev_pos hm_pos hstrict
        rw [hcount, if_pos hstrict]
        have hcast :
            ((strictHalfRatioCount a m + 1 : ℕ) : ℝ) / (2 * (γ : ℝ)) =
              (strictHalfRatioCount a m : ℝ) / (2 * (γ : ℝ)) + 1 / (2 * (γ : ℝ)) := by
          rw [Nat.cast_add, Nat.cast_one, add_div]
        rw [hcast]
        linarith
      · -- Without a strict-half-ratio step, the count stays fixed and reciprocals still increase.
        rw [hcount, if_neg hstrict]
        have hprefix := ih hm_prev_pos
        have hrecip_mono : 1 / a m ≤ 1 / a (m + 1) := by
          exact one_div_le_one_div_of_le hm_pos (ha_anti (Nat.le_succ m))
        have htarget : 1 / a m - 1 / a 0 ≤ 1 / a (m + 1) - 1 / a 0 := by
          linarith
        exact le_trans hprefix htarget

/-- Helper for Theorem 14.6: if two nonnegative counts partition a prefix, then at least one of
them is at least half of the prefix length. -/
private lemma half_count_dichotomy_of_partition {h r m : ℕ} (hsum : h + r = m) :
    ((m : ℝ) / 2 ≤ h) ∨ ((m : ℝ) / 2 ≤ r) := by
  -- Cast the exact partition identity to `ℝ` and split by whether the first count already
  -- reaches half of the prefix length.
  have hsum_real : (h : ℝ) + r = m := by
    exact_mod_cast hsum
  by_cases hh : ((m : ℝ) / 2 ≤ h)
  · exact Or.inl hh
  · right
    linarith

/-- Helper for Theorem 14.6: if at least half of the first `m` steps are halving steps, then the
geometric prefix estimate is bounded by the textbook target. -/
private lemma geometric_branch_le_target_of_halving_count
    {a0 : ℝ} (ha0 : 0 ≤ a0) {h m : ℕ}
    (hhalf : ((m : ℝ) / 2 ≤ h)) :
    ((1 / 2 : ℝ) ^ h) * a0 ≤ ((1 / 2 : ℝ) ^ ((m : ℝ) / 2)) * a0 := by
  -- Since `0 < 1 / 2 < 1`, increasing the exponent only decreases the real power.
  have hpow :
      ((1 / 2 : ℝ) ^ h) ≤ (1 / 2 : ℝ) ^ ((m : ℝ) / 2) := by
    rw [← Real.rpow_natCast (1 / 2 : ℝ) h]
    exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hhalf
  exact mul_le_mul_of_nonneg_right hpow ha0

/-- Helper for Theorem 14.6: if at least half of the first `m` steps are strict-half-ratio
steps, then the reciprocal estimate inverts to the textbook sublinear target. -/
private lemma sublinear_branch_le_target_of_strict_half_ratio_count
    {x : ℝ} (hx : 0 < x) {r m : ℕ} (hm : 1 ≤ m)
    (hhalf : ((m : ℝ) / 2 ≤ r))
    (hrecip : (r : ℝ) / (2 * (γ : ℝ)) ≤ 1 / x) :
    x ≤ 4 * (γ : ℝ) / (m : ℝ) := by
  -- First turn the count lower bound into `m ≤ 2r`.
  have hm_real_pos : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (Nat.succ_pos 0) hm)
  have hx_nonneg : 0 ≤ x := le_of_lt hx
  have htwoγ_pos : 0 < 2 * (γ : ℝ) := by
    nlinarith [PosReal.coe_pos γ]
  have hm_le_two_r : (m : ℝ) ≤ 2 * (r : ℝ) := by
    linarith
  -- Next clear the reciprocal inequality to bound `r * x`.
  have hr_le_div : (r : ℝ) ≤ (2 * (γ : ℝ)) / x := by
    have hdiv := (div_le_iff₀ htwoγ_pos).mp hrecip
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
  have hrx_le : (r : ℝ) * x ≤ 2 * (γ : ℝ) := by
    calc
      (r : ℝ) * x ≤ ((2 * (γ : ℝ)) / x) * x := by
        exact mul_le_mul_of_nonneg_right hr_le_div hx_nonneg
      _ = 2 * (γ : ℝ) := by
        field_simp [hx.ne']
  -- Finally combine `m ≤ 2r` with the estimate on `r * x` and divide by the positive `m`.
  have hmx_le : (m : ℝ) * x ≤ 4 * (γ : ℝ) := by
    calc
      (m : ℝ) * x ≤ (2 * (r : ℝ)) * x := by
        exact mul_le_mul_of_nonneg_right hm_le_two_r hx_nonneg
      _ = 2 * ((r : ℝ) * x) := by ring
      _ ≤ 2 * (2 * (γ : ℝ)) := by gcongr
      _ = 4 * (γ : ℝ) := by ring
  exact (le_div_iff₀ hm_real_pos).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmx_le)

/-- Helper for Theorem 14.6: the Chapter 11 scalar dichotomy yields the maximum of geometric and
sublinear bounds for any nonnegative sequence satisfying the quadratic step recurrence. -/
private lemma nonnegative_sequence_le_max_geometric_or_sublinear_of_quadratic_step_recurrence
    (ha_nonneg : ∀ k : ℕ, 0 ≤ a k)
    (hstep : ∀ k : ℕ, a k - a (k + 1) ≥ (1 / (γ : ℝ)) * (a (k + 1)) ^ (2 : ℕ))
    {n : ℕ} (hn : 2 ≤ n) :
    a n ≤
      max (((1 / 2 : ℝ) ^ (((n - 1 : ℕ) : ℝ) / 2)) * a 0)
        (4 * (γ : ℝ) / ((n - 1 : ℕ) : ℝ)) := by
  -- Route correction: keep the source count-partition proof and isolate the cast-heavy closing
  -- steps in the dedicated branch lemmas above.
  by_cases han_zero : a n = 0
  · -- If the terminal value vanishes, the bound is immediate from the nonnegative sublinear term.
    have hm_nat : 1 ≤ n - 1 := by
      omega
    have hm_pos : 0 < (((n - 1 : ℕ) : ℝ)) := by
      exact_mod_cast hm_nat
    have hsub_nonneg : 0 ≤ 4 * (γ : ℝ) / ((n - 1 : ℕ) : ℝ) := by
      exact div_nonneg (mul_nonneg (by norm_num) (PosReal.coe_pos γ).le) hm_pos.le
    rw [han_zero]
    exact le_trans (by norm_num) (le_trans hsub_nonneg (le_max_right _ _))
  · -- Otherwise `a n > 0`, so the reciprocal branch can be evaluated at the prefix `n - 1`.
    have ha_anti := quadratic_step_recurrence_antitone (a := a) (γ := γ) hstep
    have han_pos : 0 < a n := lt_of_le_of_ne (ha_nonneg n) (Ne.symm han_zero)
    have hprev_pos : 0 < a (n - 1) := by
      exact lt_of_lt_of_le han_pos (ha_anti (Nat.sub_le n 1))
    have hprefix_mono : a n ≤ a (n - 1) := ha_anti (Nat.sub_le n 1)
    have hpartition :
        halvingCount a (n - 1) + strictHalfRatioCount a (n - 1) = n - 1 :=
      halvingCount_add_strictHalfRatioCount_eq (a := a) (m := n - 1)
    have hcount_split :
        ((((n - 1 : ℕ) : ℝ) / 2) ≤ halvingCount a (n - 1)) ∨
          ((((n - 1 : ℕ) : ℝ) / 2) ≤ strictHalfRatioCount a (n - 1)) :=
      half_count_dichotomy_of_partition
        (h := halvingCount a (n - 1))
        (r := strictHalfRatioCount a (n - 1))
        (m := n - 1) hpartition
    cases hcount_split with
    | inl hhalf =>
        -- Many halving steps immediately give the geometric target.
        have hgeo_prefix :
            a (n - 1) ≤ ((1 / 2 : ℝ) ^ halvingCount a (n - 1)) * a 0 :=
          geometric_prefix_bound_of_halving_count
            (a := a) (γ := γ) hstep (m := n - 1)
        have hgeo_target :
            ((1 / 2 : ℝ) ^ halvingCount a (n - 1)) * a 0 ≤
              ((1 / 2 : ℝ) ^ (((n - 1 : ℕ) : ℝ) / 2)) * a 0 :=
          geometric_branch_le_target_of_halving_count
            (a0 := a 0) (ha0 := ha_nonneg 0) hhalf
        calc
          a n ≤ a (n - 1) := hprefix_mono
          _ ≤ ((1 / 2 : ℝ) ^ halvingCount a (n - 1)) * a 0 := hgeo_prefix
          _ ≤ ((1 / 2 : ℝ) ^ (((n - 1 : ℕ) : ℝ) / 2)) * a 0 := hgeo_target
          _ ≤
              max (((1 / 2 : ℝ) ^ (((n - 1 : ℕ) : ℝ) / 2)) * a 0)
                (4 * (γ : ℝ) / ((n - 1 : ℕ) : ℝ)) := le_max_left _ _
    | inr hstrict =>
        -- Otherwise at least half of the steps are strict-half-ratio, so reciprocals grow
        -- linearly and invert to the sublinear target.
        have hm : 1 ≤ n - 1 := by
          omega
        have hrecip_prefix :
            (strictHalfRatioCount a (n - 1) : ℝ) / (2 * (γ : ℝ)) ≤
              1 / a (n - 1) - 1 / a 0 :=
          reciprocal_prefix_bound_of_strict_half_ratio_count
            (a := a) (γ := γ) hstep (m := n - 1) hprev_pos
        have hrecip :
            (strictHalfRatioCount a (n - 1) : ℝ) / (2 * (γ : ℝ)) ≤ 1 / a (n - 1) := by
          have hrecip0_nonneg : 0 ≤ 1 / a 0 := one_div_nonneg.mpr (ha_nonneg 0)
          linarith
        have hsub_target :
            a (n - 1) ≤ 4 * (γ : ℝ) / ((n - 1 : ℕ) : ℝ) :=
          sublinear_branch_le_target_of_strict_half_ratio_count
            (γ := γ) (x := a (n - 1)) hprev_pos hm hstrict hrecip
        calc
          a n ≤ a (n - 1) := hprefix_mono
          _ ≤ 4 * (γ : ℝ) / ((n - 1 : ℕ) : ℝ) := hsub_target
          _ ≤
              max (((1 / 2 : ℝ) ^ (((n - 1 : ℕ) : ℝ) / 2)) * a 0)
                (4 * (γ : ℝ) / ((n - 1 : ℕ) : ℝ)) := le_max_right _ _

end ScalarRecurrence

/-- Helper for Theorem 14.6: once the objective-gap sequence satisfies the Chapter 11 quadratic
recurrence with coefficient `γ`, the scalar recurrence lemma yields the displayed
geometric-or-sublinear bound. -/
lemma alternating_minimization_objective_gap_le_of_quadratic_recurrence
    [IsAlternatingMinimizationConvexRateProblem f g XStar FOpt Lf]
    (x : ℕ → (i : Fin p) → Ei i)
    (R : PosReal)
    (γ : PosReal)
    (hγ :
      4 * (γ : ℝ) ≤ 8 * (Lf : ℝ) * (p : ℝ) ^ (2 : ℕ) * (R : ℝ) ^ (2 : ℕ))
    (ha_nonneg : ∀ n : ℕ, 0 ≤ (F (x n)).toReal - FOpt)
    (hstep :
      ∀ n : ℕ,
        ((F (x n)).toReal - FOpt) - ((F (x (n + 1))).toReal - FOpt) ≥
          (1 / (γ : ℝ)) * (((F (x (n + 1))).toReal - FOpt) ^ (2 : ℕ)))
    (k : ℕ) (hk : 2 ≤ k) :
    (F (x k)).toReal - FOpt ≤
      max
        (((1 / 2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) *
          ((F (x 0)).toReal - FOpt))
        ((8 * (Lf : ℝ) * (p : ℝ) ^ (2 : ℕ) * (R : ℝ) ^ (2 : ℕ)) /
          ((k - 1 : ℕ) : ℝ)) := by
  -- Apply the local scalar recurrence lemma to the objective-gap sequence.
  have hmain :=
    nonnegative_sequence_le_max_geometric_or_sublinear_of_quadratic_step_recurrence
      (a := fun n ↦ (F (x n)).toReal - FOpt)
      (γ := γ)
      ha_nonneg
      hstep
      hk
  -- Then enlarge the sublinear branch using the coefficient comparison `hγ`.
  have hsub :
      4 * (γ : ℝ) / ((k - 1 : ℕ) : ℝ) ≤
        (8 * (Lf : ℝ) * (p : ℝ) ^ (2 : ℕ) * (R : ℝ) ^ (2 : ℕ)) / ((k - 1 : ℕ) : ℝ) := by
    exact div_le_div_of_nonneg_right hγ (by positivity)
  exact hmain.trans (max_le_max le_rfl hsub)

/-- Helper for Theorem 14.6: every within-cycle Gauss-Seidel prefix state stays in the initial
sublevel set, so the initial radius witness bounds its distance to every optimal point. -/
lemma alternating_minimization_prefix_state_dist_le_initial_radius
    [IsAlternatingMinimizationConvexRateProblem f g XStar FOpt Lf]
    (x : ℕ → (i : Fin p) → Ei i)
    (htraj : is_alternating_minimization_trajectory F x)
    (R : PosReal)
    (hR :
      ∀ ⦃y xStar : (i : Fin p) → Ei i⦄,
        F y ≤ F (x 0) →
        xStar ∈ XStar →
        ‖y - xStar‖ ≤ (R : ℝ))
    {k n : ℕ} (hn : n ≤ p) {xStar : (i : Fin p) → Ei i}
    (hxStar : xStar ∈ XStar) :
    ‖alternating_minimization_prefix_state x k n - xStar‖ ≤ (R : ℝ) := by
  -- The imported prefix-state descent theorem keeps the whole Gauss-Seidel sweep below `F (x k)`.
  have hprefix_le :
      F (alternating_minimization_prefix_state x k n) ≤ F (x k) := by
    have hxk_mem :
        x k ∈ effective_domain F :=
      alternating_minimization_iterate_mem_effective_domain F x htraj k
    have hprefix_pair :=
      alternating_minimization_prefix_state_mem_effective_domain_and_le
        F
        x
        htraj
        k
        hxk_mem
        n
        hn
    exact hprefix_pair.2
  -- The outer objective sequence is itself bounded by the initial level.
  have hxk_le : F (x k) ≤ F (x 0) := by
    exact alternating_minimization_objective_le_initial F x htraj k
  exact
    hR
      (y := alternating_minimization_prefix_state x k n)
      (xStar := xStar)
      (le_trans hprefix_le hxk_le)
      hxStar

/-- Helper for Theorem 14.6: the admissible block trial point toward `xStar` is exactly the affine
combination of the current prefix state and the one-block optimizer replacement. -/
lemma alternating_minimization_trial_update_eq_affine_combo
    (z : (i : Fin p) → Ei i) (i : Fin p) (xStar : (i : Fin p) → Ei i) (t : ℝ) :
    Function.update z i ((1 - t) • z i + t • xStar i) =
      (1 - t) • z + t • Function.update z i (xStar i) := by
  classical
  -- Compare the trial point and the affine combination coordinatewise.
  ext j
  by_cases hji : j = i
  · -- On the active block, both sides are the same convex combination of `z i` and `xStar i`.
    subst hji
    simp [Function.update]
  · -- Off the active block, the update is unchanged and the coefficients add up to one.
    have hsum : (1 - t : ℝ) + t = 1 := by ring
    calc
      Function.update z i ((1 - t) • z i + t • xStar i) j = z j := by
        simp [Function.update, hji]
      _ = ((1 - t) + t) • z j := by
        simpa [hsum] using (one_smul ℝ (z j)).symm
      _ = (1 - t) • z j + t • z j := by
        rw [add_smul]
      _ = (1 - t) • z j + t • Function.update z i (xStar i) j := by
        simp [Function.update, hji]

/-- Helper for Theorem 14.6: every optimizer lies in the effective domain of the composite
objective. -/
lemma alternating_minimization_optimal_point_mem_effective_domain
    [hproblem : IsAlternatingMinimizationConvexRateProblem f g XStar FOpt Lf]
    {xStar : (i : Fin p) → Ei i} (hxStar : xStar ∈ XStar) :
    xStar ∈ effective_domain F := by
  let hconvex :
      IsConvexCompositeSmoothMinimizationProblem f.toEReal (separableSum g) XStar FOpt Lf :=
    IsAlternatingMinimizationConvexRateProblem.toIsConvexCompositeSmoothMinimizationProblem
      (f := f) (g := g) (XStar := XStar) (FOpt := FOpt) (Lf := Lf) hproblem
  -- An optimal point attains the finite optimal value `FOpt`, hence it belongs to `dom(F)`.
  have hvalue : F xStar = (FOpt : EReal) := by
    exact hconvex.objective_eq_optimalValue_of_mem_optimalSet hxStar
  -- The effective domain condition is exactly finiteness of this objective value.
  refine mem_effective_domain.mpr ?_
  simpa [hvalue]

/-- Helper for Theorem 14.6: the one-block convex-combination trial point toward an optimizer
stays in the effective domain of `F`. -/
lemma alternating_minimization_trial_update_mem_effective_domain
    [hproblem : IsAlternatingMinimizationConvexRateProblem f g XStar FOpt Lf]
    {z xStar : (i : Fin p) → Ei i} (i : Fin p) {t : ℝ}
    (hz : z ∈ effective_domain F)
    (hxStar : xStar ∈ XStar)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Function.update z i ((1 - t) • z i + t • xStar i) ∈ effective_domain F := by
  -- Route correction: the reusable block-domain API is now factored out of `Theorem_14_5`, so
  -- this lemma can stay a thin adapter from block convexity back to the full composite domain.
  let hmodel :
      IsAlternatingMinimizationCompositeModel f.toEReal g :=
    IsAlternatingMinimizationConvexRateProblem.toIsAlternatingMinimizationCompositeModel
      (f := f) (g := g) (XStar := XStar) (FOpt := FOpt) (Lf := Lf) hproblem
  have hzi :
      z i ∈ effective_domain (g i) :=
    composite_block_mem_effective_domain_of_mem hmodel hz i
  have hxStar_mem : xStar ∈ effective_domain F :=
    alternating_minimization_optimal_point_mem_effective_domain
      (f := f) (g := g) (XStar := XStar) (FOpt := FOpt) (Lf := Lf) hxStar
  have hxStar_i :
      xStar i ∈ effective_domain (g i) :=
    composite_block_mem_effective_domain_of_mem hmodel hxStar_mem i
  have ht_mem : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0, ht1⟩
  have hcombo :
      ((1 - t) • z i + t • xStar i) ∈ effective_domain (g i) := by
    -- Rewrite the active-block trial point as the standard convex-combination form.
    simpa [add_comm, add_left_comm, add_assoc] using
      combo_mem_effective_domain_of_is_convex_function
        (hproblem.g_convex i) hxStar_i hzi ht_mem
  -- Lift the finite block value back to the full composite objective by a one-coordinate update.
  exact
    composite_update_mem_effective_domain_of_block_mem
      hmodel i hz hcombo

/-- Helper for Theorem 14.6: the correct one-cycle source-faithful invariant is the Gauss-Seidel
convex-combination recurrence for the objective gap. -/
lemma alternating_minimization_cycle_convex_combo_recurrence
    [IsAlternatingMinimizationConvexRateProblem f g XStar FOpt Lf]
    (x : ℕ → (i : Fin p) → Ei i)
    (htraj : is_alternating_minimization_trajectory F x)
    (R : PosReal)
    (hR :
      ∀ ⦃y xStar : (i : Fin p) → Ei i⦄,
        F y ≤ F (x 0) →
        xStar ∈ XStar →
        ‖y - xStar‖ ≤ (R : ℝ)) :
    ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ((F (x (k + 1))).toReal - FOpt) ≤
        (1 - t) * ((F (x k)).toReal - FOpt) +
          ((((Lf : ℝ) * (p : ℝ) * (R : ℝ) ^ (2 : ℕ)) / 2) * t ^ (2 : ℕ)) := by
  -- Route correction: the old step-norm decrease scaffold is false for arbitrary exact block
  -- minimizers, so the proof must instead follow the source convex-combination comparison over one
  -- full Gauss-Seidel cycle.
  -- TODO: compare each exact block update to the convex-combination test point toward an optimizer,
  -- sum the resulting one-block upper bounds over the prefix states, and use the imported
  -- prefix-state radius bound to control the quadratic remainder by `((Lf : ℝ) * (p : ℝ) * R^2)/2`.
  sorry

/-- Helper for Theorem 14.6: combining the one-cycle sufficient decrease with the radius-times-step
estimate yields the scalar quadratic recurrence required by Lemma 11.7. -/
lemma alternating_minimization_gap_quadratic_recurrence
    [IsAlternatingMinimizationConvexRateProblem f g XStar FOpt Lf]
    (x : ℕ → (i : Fin p) → Ei i)
    (htraj : is_alternating_minimization_trajectory F x)
    (R : PosReal)
    (hR :
      ∀ ⦃y xStar : (i : Fin p) → Ei i⦄,
        F y ≤ F (x 0) →
        xStar ∈ XStar →
        ‖y - xStar‖ ≤ (R : ℝ))
    (hLf_pos : 0 < (Lf : ℝ))
    (hp : p ≠ 0) :
    ∀ k : ℕ,
      ((F (x k)).toReal - FOpt) - ((F (x (k + 1))).toReal - FOpt) ≥
        (1 / (2 * (Lf : ℝ) * (p : ℝ) ^ (2 : ℕ) * (R : ℝ) ^ (2 : ℕ))) *
          (((F (x (k + 1))).toReal - FOpt) ^ (2 : ℕ)) := by
  -- TODO: derive the stronger denominator `2 * (Lf : ℝ) * (p : ℝ) * (R : ℝ)^2` from the
  -- all-`t` cycle recurrence by setting
  -- `t = (((F (x (k + 1))).toReal - FOpt) / ((Lf : ℝ) * (p : ℝ) * (R : ℝ)^2))`, prove
  -- `t ∈ [0, 1]` using the `t = 0` and `t = 1` specializations, and then weaken from `p` to
  -- `p^2` using `hp`.
  sorry

/-- Theorem 14.6: if Assumption 14.10 holds, `x` is the sequence generated by the
alternating-minimization method for `F(x) = f(x) + ∑ i, g_i(x_i)`, and `R` bounds the distance
from every point of the initial sublevel set `{y | F(y) ≤ F(x^0)}` to every optimal point in
`X^*`, then for every `k ≥ 2` the objective gap satisfies
`F(x^k) - F_opt ≤ max {((1 / 2)^((k - 1) / 2)) (F(x^0) - F_opt), 8 L_f p^2 R^2 / (k - 1)}`. -/
theorem alternating_minimization_objective_gap_le_max_geometric_or_sublinear_of_initial_radius
    [IsAlternatingMinimizationConvexRateProblem f g XStar FOpt Lf]
    (x : ℕ → (i : Fin p) → Ei i)
    (htraj : is_alternating_minimization_trajectory F x)
    (R : PosReal)
    (hR :
      ∀ ⦃y xStar : (i : Fin p) → Ei i⦄,
        F y ≤ F (x 0) →
        xStar ∈ XStar →
        ‖y - xStar‖ ≤ (R : ℝ))
    (k : ℕ) (hk : 2 ≤ k) :
    (F (x k)).toReal - FOpt ≤
      max
        (((1 / 2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) *
          ((F (x 0)).toReal - FOpt))
        ((8 * (Lf : ℝ) * (p : ℝ) ^ (2 : ℕ) * (R : ℝ) ^ (2 : ℕ)) /
          ((k - 1 : ℕ) : ℝ)) := by
  have hgap_nonneg :=
    alternating_minimization_objective_gap_nonneg
      (f := f) (g := g) (XStar := XStar) (FOpt := FOpt) (Lf := Lf) x htraj
  by_cases hp : p = 0
  · have hproblem : IsAlternatingMinimizationConvexRateProblem f g XStar FOpt Lf :=
      inferInstance
    have hconvex :
        IsConvexCompositeSmoothMinimizationProblem f.toEReal (separableSum g) XStar FOpt Lf :=
      IsAlternatingMinimizationConvexRateProblem.toIsConvexCompositeSmoothMinimizationProblem
        (f := f) (g := g) (XStar := XStar) (FOpt := FOpt) (Lf := Lf) hproblem
    haveI : IsEmpty (Fin p) := by
      exact Fintype.card_eq_zero_iff.mp (by simpa using hp)
    rcases hproblem.optimal_set_nonempty with ⟨xStar, hxStar⟩
    -- In the zero-block case the ambient product space is a singleton, so every iterate is
    -- exactly the optimal point.
    have hxk_eq : x k = xStar := Subsingleton.elim _ _
    have hx0_eq : x 0 = xStar := Subsingleton.elim _ _
    have hgapk_zero : (F (x k)).toReal - FOpt = 0 := by
      have hFxk :
          F (x k) = (FOpt : EReal) := by
        simpa [hxk_eq] using
          hconvex.objective_eq_optimalValue_of_mem_optimalSet hxStar
      simpa [hFxk]
    have hgap0_zero : (F (x 0)).toReal - FOpt = 0 := by
      have hFx0 :
          F (x 0) = (FOpt : EReal) := by
        simpa [hx0_eq] using
          hconvex.objective_eq_optimalValue_of_mem_optimalSet hxStar
      simpa [hFx0]
    have hfirst_nonneg :
        0 ≤
          (((1 / 2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) *
            ((F (x 0)).toReal - FOpt)) := by
      simpa [hgap0_zero] using mul_nonneg (by positivity) (hgap_nonneg 0)
    rw [hgapk_zero]
    exact le_trans hfirst_nonneg (le_max_left _ _)
  · by_cases hLf_zero : (Lf : ℝ) = 0
    · have hk_one : 1 ≤ k := by
        omega
      -- Evaluate the cycle recurrence at `t = 1` one step before `k`; when `Lf = 0` the
      -- quadratic remainder vanishes and forces the gap at `k` to be zero.
      have hgapk_le_zero :
          (F (x k)).toReal - FOpt ≤ 0 := by
        simpa [Nat.sub_add_cancel hk_one, hLf_zero] using
          alternating_minimization_cycle_convex_combo_recurrence
            (f := f) (g := g) (XStar := XStar) (FOpt := FOpt) (Lf := Lf)
            x htraj R hR (k - 1) 1 (by norm_num) (by norm_num)
      have hgapk_zero : (F (x k)).toReal - FOpt = 0 := by
        exact le_antisymm hgapk_le_zero (hgap_nonneg k)
      have hfirst_nonneg :
          0 ≤
            (((1 / 2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) *
              ((F (x 0)).toReal - FOpt)) := by
        exact mul_nonneg (by positivity) (hgap_nonneg 0)
      rw [hgapk_zero]
      exact le_trans hfirst_nonneg (le_max_left _ _)
    · have hLf_pos : 0 < (Lf : ℝ) := by
        exact lt_of_le_of_ne (by positivity : 0 ≤ (Lf : ℝ)) (Ne.symm hLf_zero)
      have hp_pos : 0 < (p : ℝ) := by
        exact_mod_cast Nat.pos_iff_ne_zero.mpr hp
      have hγ_pos :
          0 < 2 * (Lf : ℝ) * (p : ℝ) ^ (2 : ℕ) * (R : ℝ) ^ (2 : ℕ) := by
        have hp_sq_pos : 0 < (p : ℝ) ^ (2 : ℕ) := by
          simpa [pow_two] using sq_pos_of_pos hp_pos
        have hR_sq_pos : 0 < (R : ℝ) ^ (2 : ℕ) := by
          simpa [pow_two] using sq_pos_of_pos (PosReal.coe_pos R)
        exact mul_pos (mul_pos (mul_pos (by norm_num) hLf_pos) hp_sq_pos) hR_sq_pos
      let γ : PosReal :=
        ⟨2 * (Lf : ℝ) * (p : ℝ) ^ (2 : ℕ) * (R : ℝ) ^ (2 : ℕ), hγ_pos⟩
      have hstep_base :=
        alternating_minimization_gap_quadratic_recurrence
          (f := f) (g := g) (XStar := XStar) (FOpt := FOpt) (Lf := Lf)
          x htraj R hR hLf_pos hp
      have hstep :
          ∀ n : ℕ,
            ((F (x n)).toReal - FOpt) - ((F (x (n + 1))).toReal - FOpt) ≥
              (1 / (γ : ℝ)) * (((F (x (n + 1))).toReal - FOpt) ^ (2 : ℕ)) := by
        intro n
        simpa [γ] using hstep_base n
      have hγ :
          4 * (γ : ℝ) ≤ 8 * (Lf : ℝ) * (p : ℝ) ^ (2 : ℕ) * (R : ℝ) ^ (2 : ℕ) := by
        have hγ_eq :
            4 * (γ : ℝ) =
              8 * (Lf : ℝ) * (p : ℝ) ^ (2 : ℕ) * (R : ℝ) ^ (2 : ℕ) := by
          dsimp [γ]
          ring
        exact hγ_eq.le
      exact
        alternating_minimization_objective_gap_le_of_quadratic_recurrence
          (f := f) (g := g) (XStar := XStar) (FOpt := FOpt) (Lf := Lf)
          x R γ hγ hgap_nonneg hstep k hk

end

end
