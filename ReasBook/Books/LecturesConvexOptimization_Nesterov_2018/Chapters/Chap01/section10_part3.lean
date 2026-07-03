import Mathlib
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_1_10_17 (from Chap01) -/
open ContinuousMap Filter Set Topology
open scoped BigOperators

noncomputable section

universe u v

variable {α : Type u} [TopologicalSpace α]
variable {ι : Type v}

/-- The feasible set cut out by the continuous inequalities `f j x ≤ 0`. -/
def constraintSet (f : ι → C(α, ℝ)) : Set α :=
  {x | ∀ j : ι, f j x ≤ 0}

/-- Membership in `constraintSet f` means that every constraint value is nonpositive. -/
@[simp] theorem mem_constraintSet_iff
    (f : ι → C(α, ℝ)) {x : α} :
    x ∈ constraintSet f ↔ ∀ j : ι, f j x ≤ 0 :=
  Iff.rfl

/-- The strict feasible locus cut out by the same inequalities. -/
def strictConstraintSet (f : ι → C(α, ℝ)) : Set α :=
  {x | ∀ j : ι, f j x < 0}

/-- Membership in `strictConstraintSet f` means that every constraint value is strictly negative.
-/
@[simp] theorem mem_strictConstraintSet_iff
    (f : ι → C(α, ℝ)) {x : α} :
    x ∈ strictConstraintSet f ↔ ∀ j : ι, f j x < 0 :=
  Iff.rfl

private theorem continuous_neg_constraint
    (f : ι → C(α, ℝ)) (j : ι) :
    Continuous fun x : strictConstraintSet f ↦ -f j x :=
  ((f j).continuous.comp continuous_subtype_val).neg

private theorem neg_constraint_pos
    (f : ι → C(α, ℝ)) (j : ι) (x : strictConstraintSet f) :
    0 < -f j x :=
  neg_pos.mpr (x.property j)

/-- The feasible set cut out by continuous nonstrict inequalities is closed. -/
private theorem isClosed_constraintSet (f : ι → C(α, ℝ)) :
    IsClosed (constraintSet f) := by
  simpa [constraintSet, Set.setOf_forall] using
    isClosed_iInter fun j ↦ isClosed_le (f j).continuous continuous_const

section FiniteIndex

variable [Finite ι]

/-- Every point satisfying all constraints strictly lies in the interior of the feasible set. -/
theorem strictConstraintSet_subset_interior_constraintSet
    (f : ι → C(α, ℝ)) :
    strictConstraintSet f ⊆ interior (constraintSet f) :=
  (by
    simpa [strictConstraintSet, Set.setOf_forall] using
      (isOpen_iInter_of_finite fun j ↦ isOpen_lt (f j).continuous continuous_const) :
    IsOpen (strictConstraintSet f)).subset_interior_iff.mpr <| by
      intro x hx j
      exact le_of_lt (hx j)

/-- The bridge hypothesis `interior (constraintSet f) ⊆ strictConstraintSet f` says exactly that
the chosen inequality presentation recovers the intrinsic interior of the feasible set. -/
theorem strictConstraintSet_eq_interior_constraintSet
    (f : ι → C(α, ℝ))
    (hinterior : interior (constraintSet f) ⊆ strictConstraintSet f) :
    strictConstraintSet f = interior (constraintSet f) :=
  subset_antisymm
    (strictConstraintSet_subset_interior_constraintSet f)
    hinterior

/-- A frontier point of `constraintSet f` has an active constraint `f j x = 0`. -/
private theorem exists_eq_zero_of_mem_frontier_constraintSet
    (f : ι → C(α, ℝ)) {x : α}
    (hx : x ∈ frontier (constraintSet f)) :
    ∃ j : ι, f j x = 0 := by
  have hx' : x ∈ constraintSet f \ interior (constraintSet f) := by
    simpa [(isClosed_constraintSet f).frontier_eq] using hx
  have hxle : ∀ j : ι, f j x ≤ 0 := by
    simpa [constraintSet] using hx'.1
  have hxnotstrict : x ∉ strictConstraintSet f := by
    intro hxstrict
    exact hx'.2 (strictConstraintSet_subset_interior_constraintSet f hxstrict)
  simp only [mem_strictConstraintSet_iff] at hxnotstrict
  push Not at hxnotstrict
  rcases hxnotstrict with ⟨j, hj⟩
  exact ⟨j, le_antisymm (hxle j) hj⟩

/-- Along a sequence in `interior (constraintSet f)` converging to a frontier point, some
constraint slack tends to `0`. -/
private theorem exists_constraint_tendsto_zero_of_tendsto_frontier_constraintSet
    (f : ι → C(α, ℝ))
    (x : ℕ → interior (constraintSet f)) {xBar : α}
    (hx : Tendsto (fun k ↦ (x k : α)) atTop (nhds xBar))
    (hxBar : xBar ∈ frontier (constraintSet f)) :
    ∃ j : ι, Tendsto (fun k ↦ f j (x k : α)) atTop (nhds 0) := by
  rcases exists_eq_zero_of_mem_frontier_constraintSet f hxBar with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  have ht : Tendsto (fun k ↦ f j (x k : α)) atTop (nhds (f j xBar)) :=
    ((f j).continuousAt xBar).tendsto.comp hx
  simpa [hj] using ht

section ConstraintBarrierExamples

noncomputable local instance : Fintype ι := Fintype.ofFinite ι

/-
Source/core/bridge triage for Proposition 1.10.17:
- source-facing: the three explicit formulas on `strictConstraintSet f` and the proposition that,
  after identifying that strict locus with `interior (constraintSet f)`, they are barrier
  functions for `constraintSet f`;
- core/canonical: `IsBarrierFunctionOn (constraintSet f)`, whose owner is a continuous map on
  `interior (constraintSet f)`;
- bridge/view: the frontier-to-vanishing-slack lemma and the restriction of a strict-locus
  formula along `ContinuousMap.inclusion hinterior` once the chosen inequality presentation
  recovers the intrinsic interior of `constraintSet f`.

This keeps Proposition 1.10.17 at the source-facing layer. The canonical
`IsBarrierFunctionOn` results below are bridge theorems derived from the same strict-locus
formulas after identifying `strictConstraintSet f` with `interior (constraintSet f)`. The
vanishing-slack growth lemmas remain auxiliary companions; they do not replace the main
barrier-function statement.
-/

/-- The reciprocal-power barrier formula on the strict locus `strictConstraintSet f`. -/
def powerBarrier (f : ι → C(α, ℝ)) (p : ℝ) :
    C(strictConstraintSet f, ℝ) where
  toFun x := ∑ j : ι, 1 / Real.rpow (-f j x) p
  continuous_toFun := by
    refine continuous_finset_sum _ fun j _ ↦ ?_
    have hpow : Continuous fun x : strictConstraintSet f ↦ Real.rpow (-f j x) p :=
      (continuous_neg_constraint f j).rpow_const fun x ↦
        Or.inl <| ne_of_gt <| neg_constraint_pos f j x
    exact continuous_const.div hpow fun x ↦
      ne_of_gt <| Real.rpow_pos_of_pos (neg_constraint_pos f j x) p

/-- The logarithmic barrier formula on `strictConstraintSet f`. -/
def logarithmicBarrier (f : ι → C(α, ℝ)) :
    C(strictConstraintSet f, ℝ) where
  toFun x := -∑ j : ι, Real.log (-f j x)
  continuous_toFun := by
    have hsum : Continuous fun x : strictConstraintSet f ↦
        ∑ j : ι, Real.log (-f j x) := by
      refine continuous_finset_sum _ fun j _ ↦ ?_
      exact (continuous_neg_constraint f j).log fun x ↦
        ne_of_gt <| neg_constraint_pos f j x
    simpa using hsum.neg

/-- The exponential barrier formula on `strictConstraintSet f`. -/
def exponentialBarrier (f : ι → C(α, ℝ)) :
    C(strictConstraintSet f, ℝ) where
  toFun x := ∑ j : ι, Real.exp (1 / (-f j x))
  continuous_toFun := by
    refine continuous_finset_sum _ fun j _ ↦ ?_
    have hrecip : Continuous fun x : strictConstraintSet f ↦ 1 / (-f j x) :=
      continuous_const.div (continuous_neg_constraint f j) fun x ↦
        ne_of_gt <| neg_constraint_pos f j x
    simpa using Real.continuous_exp.comp hrecip

/-- Evaluating `powerBarrier f p` reproduces the reciprocal-power sum of the slacks. -/
@[simp] theorem powerBarrier_apply
    (f : ι → C(α, ℝ)) (p : ℝ)
    (x : strictConstraintSet f) :
    powerBarrier f p x = ∑ j : ι, 1 / Real.rpow (-f j x) p :=
  rfl

/-- Evaluating `logarithmicBarrier f` reproduces the sum of negative logarithms of the slacks. -/
@[simp] theorem logarithmicBarrier_apply
    (f : ι → C(α, ℝ)) (x : strictConstraintSet f) :
    logarithmicBarrier f x = -∑ j : ι, Real.log (-f j x) :=
  rfl

/-- Evaluating `exponentialBarrier f` reproduces the exponential reciprocal-slack sum. -/
@[simp] theorem exponentialBarrier_apply
    (f : ι → C(α, ℝ)) (x : strictConstraintSet f) :
    exponentialBarrier f x = ∑ j : ι, Real.exp (1 / (-f j x)) :=
  rfl

section BoundaryGrowth

/-- Helper for Proposition 1.10.17: if each constraint image on the strict locus is bounded below,
then the inactive logarithmic summands admit a uniform lower bound. -/
private theorem logarithmicBarrier_lower_bound_of_bddBelow
    (f : ι → C(α, ℝ)) (j : ι)
    (hbounded : ∀ i : ι, BddBelow ((f i) '' strictConstraintSet f)) :
    ∃ C : ℝ, ∀ y : strictConstraintSet f,
      C + (-Real.log (-f j y)) ≤ logarithmicBarrier f y := by
  classical
  by_cases hnonempty : (strictConstraintSet f).Nonempty
  · rcases hnonempty with ⟨x0, hx0⟩
    let x0Strict : strictConstraintSet f := ⟨x0, hx0⟩
    choose c hc using fun i : ι => hbounded i
    let C : ℝ := Finset.sum (Finset.univ.erase j) (fun i ↦ -Real.log (-c i))
    refine ⟨C, ?_⟩
    intro y
    -- Evaluate each lower bound at one strict point to see that every `c i` is still negative.
    have hc_lt_zero : ∀ i : ι, c i < 0 := by
      intro i
      have hci : c i ≤ f i x0 := by
        exact (mem_lowerBounds.mp (hc i)) (f i x0) ⟨x0, hx0, rfl⟩
      exact lt_of_le_of_lt hci (x0Strict.property i)
    have hsum :
        C ≤ Finset.sum (Finset.univ.erase j) (fun i ↦ -Real.log (-f i y)) := by
      -- Each inactive logarithmic term is bounded below by the corresponding constant.
      unfold C
      refine Finset.sum_le_sum ?_
      intro i hi
      have hci : c i ≤ f i y := by
        exact (mem_lowerBounds.mp (hc i)) (f i y) ⟨y, y.property, rfl⟩
      have hy_pos : 0 < -f i y := neg_constraint_pos f i y
      have hc_pos : 0 < -c i := by
        linarith [hc_lt_zero i]
      have hneg_le : -f i y ≤ -c i := by
        linarith
      have hlog : Real.log (-f i y) ≤ Real.log (-c i) :=
        Real.log_le_log hy_pos hneg_le
      linarith
    calc
      C + (-Real.log (-f j y))
          ≤ Finset.sum (Finset.univ.erase j) (fun i ↦ -Real.log (-f i y))
              + (-Real.log (-f j y)) := by
            linarith
      _ = logarithmicBarrier f y := by
        rw [logarithmicBarrier_apply]
        calc
          Finset.sum (Finset.univ.erase j) (fun i ↦ -Real.log (-f i y))
              + (-Real.log (-f j y))
              = ∑ i : ι, -Real.log (-f i y) := by
                  simpa using
                    Finset.sum_erase_add
                      (Finset.univ : Finset ι)
                      (fun i ↦ -Real.log (-f i y))
                      (by simp : j ∈ (Finset.univ : Finset ι))
          _ = -∑ i : ι, Real.log (-f i y) := by
                simpa using
                  (Finset.neg_sum (fun i : ι ↦ Real.log (-f i y))).symm
  · refine ⟨0, ?_⟩
    intro y
    exact (hnonempty ⟨y, y.property⟩).elim

/-- For `p ≥ 1`, the reciprocal-power formula diverges to `+∞` whenever some constraint slack
along the sequence tends to `0`. -/
theorem powerBarrier_tendsto_atTop_of_exists_constraint_tendsto_zero
    (f : ι → C(α, ℝ))
    {x : ℕ → strictConstraintSet f}
    (p : ℝ) (hp : 1 ≤ p)
    (hvanish :
      ∃ j : ι,
        Tendsto (fun k ↦ f j (x k : α)) atTop (nhds 0)) :
    Tendsto (fun k ↦ powerBarrier f p (x k)) atTop atTop := by
  rcases hvanish with ⟨j, hj⟩
  let slack : ℕ → ℝ := fun k ↦ -f j (x k : α)
  -- The active slack tends to `0` from the positive side along the strict locus.
  have hslack : Tendsto slack atTop (nhds 0) := by
    simpa [slack] using hj.neg
  have hslack_pos : ∀ k : ℕ, 0 < slack k := by
    intro k
    simpa [slack] using neg_constraint_pos f j (x k)
  have hslack_within : Tendsto slack atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [nhdsWithin]
    refine Filter.tendsto_inf.2 ?_
    refine ⟨hslack, ?_⟩
    exact Filter.tendsto_principal.2 <|
      Filter.Eventually.of_forall hslack_pos
  -- The active reciprocal-power term already blows up to `+∞`.
  have hactive : Tendsto (fun k ↦ 1 / Real.rpow (slack k) p) atTop atTop := by
    have hneg : -p < 0 := by
      linarith
    have hpow : Tendsto (fun k ↦ Real.rpow (slack k) (-p)) atTop atTop :=
      (tendsto_rpow_neg_nhdsGT_zero hneg).comp hslack_within
    simpa [one_div, Real.rpow_neg, le_of_lt (hslack_pos _)] using hpow
  have hdom :
      ∀ k : ℕ, 1 / Real.rpow (slack k) p ≤ powerBarrier f p (x k) := by
    intro k
    -- The full finite sum dominates any one nonnegative summand.
    rw [powerBarrier_apply]
    simpa [slack] using
      (Finset.single_le_sum
        (fun i _ ↦ by
          have hpos : 0 < Real.rpow (-f i (x k)) p :=
            Real.rpow_pos_of_pos (neg_constraint_pos f i (x k)) p
          exact le_of_lt (one_div_pos.mpr hpos))
        (Finset.mem_univ j) :
        1 / Real.rpow (-f j (x k)) p ≤
          ∑ i ∈ (Finset.univ : Finset ι), 1 / Real.rpow (-f i (x k)) p)
  -- Domination transfers the single-summand divergence to the whole barrier.
  refine Filter.tendsto_atTop.2 ?_
  intro b
  filter_upwards [Filter.tendsto_atTop.1 hactive b] with k hk
  exact le_trans hk (hdom k)

/-- If the constraint family is bounded below on the strict locus, then the logarithmic formula
diverges to `+∞` whenever some constraint slack tends to `0`. -/
theorem logarithmicBarrier_tendsto_atTop_of_exists_constraint_tendsto_zero
    (f : ι → C(α, ℝ))
    {x : ℕ → strictConstraintSet f}
    (hbounded : ∀ j : ι, BddBelow ((f j) '' strictConstraintSet f))
    (hvanish :
      ∃ j : ι,
        Tendsto (fun k ↦ f j (x k : α)) atTop (nhds 0)) :
    Tendsto (fun k ↦ logarithmicBarrier f (x k)) atTop atTop := by
  rcases hvanish with ⟨j, hj⟩
  rcases logarithmicBarrier_lower_bound_of_bddBelow f j hbounded with ⟨C, hC⟩
  let slack : ℕ → ℝ := fun k ↦ -f j (x k : α)
  -- The active slack tends to `0` through positive values.
  have hslack : Tendsto slack atTop (nhds 0) := by
    simpa [slack] using hj.neg
  have hslack_pos : ∀ k : ℕ, 0 < slack k := by
    intro k
    simpa [slack] using neg_constraint_pos f j (x k)
  have hslack_within : Tendsto slack atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [nhdsWithin]
    refine Filter.tendsto_inf.2 ?_
    refine ⟨hslack, ?_⟩
    exact Filter.tendsto_principal.2 <|
      Filter.Eventually.of_forall hslack_pos
  -- `log` sends the active positive slack to `-∞`, so the negated logarithm goes to `+∞`.
  have hlog : Tendsto (fun k ↦ Real.log (slack k)) atTop atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hslack_within
  have hactive : Tendsto (fun k ↦ -Real.log (slack k)) atTop atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [Filter.tendsto_atBot.1 hlog (-b)] with k hk
    linarith
  have hshift : Tendsto (fun k ↦ -Real.log (slack k) + C) atTop atTop := by
    -- Adding a fixed constant preserves divergence to `+∞`.
    have hadd : Tendsto (fun t : ℝ ↦ t + C) atTop atTop := by
      rw [Filter.Tendsto]
      simpa [Filter.map_map] using le_of_eq (Filter.map_add_atTop_eq C)
    exact hadd.comp hactive
  have hdom :
      ∀ k : ℕ, -Real.log (slack k) + C ≤ logarithmicBarrier f (x k) := by
    intro k
    simpa [slack, add_comm, add_left_comm, add_assoc] using hC (x k)
  -- The lower bound from the inactive summands lets the active blow-up control the whole sum.
  refine Filter.tendsto_atTop.2 ?_
  intro b
  filter_upwards [Filter.tendsto_atTop.1 hshift b] with k hk
  exact le_trans hk (hdom k)

/-- The exponential formula diverges to `+∞` whenever some constraint slack tends to `0`. -/
theorem exponentialBarrier_tendsto_atTop_of_exists_constraint_tendsto_zero
    (f : ι → C(α, ℝ))
    {x : ℕ → strictConstraintSet f}
    (hvanish :
      ∃ j : ι,
        Tendsto (fun k ↦ f j (x k : α)) atTop (nhds 0)) :
    Tendsto (fun k ↦ exponentialBarrier f (x k)) atTop atTop := by
  rcases hvanish with ⟨j, hj⟩
  let slack : ℕ → ℝ := fun k ↦ -f j (x k : α)
  -- The active slack tends to `0` through positive values.
  have hslack : Tendsto slack atTop (nhds 0) := by
    simpa [slack] using hj.neg
  have hslack_pos : ∀ k : ℕ, 0 < slack k := by
    intro k
    simpa [slack] using neg_constraint_pos f j (x k)
  have hslack_within : Tendsto slack atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [nhdsWithin]
    refine Filter.tendsto_inf.2 ?_
    refine ⟨hslack, ?_⟩
    exact Filter.tendsto_principal.2 <|
      Filter.Eventually.of_forall hslack_pos
  -- The reciprocal slack tends to `+∞`, and then the exponential does as well.
  have hrecip : Tendsto (fun k ↦ 1 / slack k) atTop atTop := by
    simpa [one_div] using (tendsto_inv_nhdsGT_zero.comp hslack_within)
  have hactive : Tendsto (fun k ↦ Real.exp (1 / slack k)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hrecip
  have hdom :
      ∀ k : ℕ, Real.exp (1 / slack k) ≤ exponentialBarrier f (x k) := by
    intro k
    -- The full finite sum dominates the active exponential summand.
    rw [exponentialBarrier_apply]
    simpa [slack] using
      (Finset.single_le_sum
        (s := (Finset.univ : Finset ι))
        (a := j)
        (f := fun i ↦ Real.exp (1 / (-f i (x k : α))))
        (fun i _ ↦ le_of_lt (Real.exp_pos (1 / (-f i (x k : α)))))
        (Finset.mem_univ j) :
        Real.exp (1 / (-f j (x k : α))) ≤
          Finset.sum (Finset.univ : Finset ι) (fun i ↦ Real.exp (1 / (-f i (x k : α)))))
  refine Filter.tendsto_atTop.2 ?_
  intro b
  filter_upwards [Filter.tendsto_atTop.1 hactive b] with k hk
  exact le_trans hk (hdom k)

end BoundaryGrowth

section BarrierFunctionBridge

/-- Bridge a strict-locus growth criterion to the owner predicate `IsBarrierFunctionOn` once the
chosen strict constraints recover the intrinsic interior of `constraintSet f`. -/
private theorem isBarrierFunctionOn_of_tendsto_zero
    (f : ι → C(α, ℝ))
    (hinterior : interior (constraintSet f) ⊆ strictConstraintSet f)
    (hint : (interior (constraintSet f)).Nonempty)
    (F : C(strictConstraintSet f, ℝ))
    (hF :
      ∀ (x : ℕ → strictConstraintSet f),
        (∃ j : ι,
          Tendsto (fun k ↦ f j (x k : α)) atTop (nhds 0)) →
          Tendsto (fun k ↦ F (x k)) atTop atTop) :
    IsBarrierFunctionOn (constraintSet f) (F.comp (inclusion hinterior)) := by
  let _ : Fact (IsClosed (constraintSet f)) := ⟨isClosed_constraintSet f⟩
  refine IsBarrierFunctionOn.mk hint ?_
  intro x xBar hx hxBar
  rcases exists_constraint_tendsto_zero_of_tendsto_frontier_constraintSet f x hx hxBar with
    ⟨j, hj⟩
  change Tendsto (fun k ↦ F ⟨x k, hinterior (x k).property⟩) atTop atTop
  exact hF
    (fun k ↦ ⟨x k, hinterior (x k).property⟩)
    (by
      refine ⟨j, ?_⟩
      simpa using hj)

/-- Proposition 1.10.17 (1): if the chosen strict inequalities recover
`interior (constraintSet f)`, then the reciprocal-power formula, viewed on that interior via the
canonical inclusion, is a barrier function for `constraintSet f`. -/
theorem powerBarrier_isBarrierFunctionOn
    (f : ι → C(α, ℝ))
    (hinterior : interior (constraintSet f) ⊆ strictConstraintSet f)
    (hint : (interior (constraintSet f)).Nonempty)
    (p : ℝ) (hp : 1 ≤ p) :
    IsBarrierFunctionOn (constraintSet f)
      ((powerBarrier f p).comp (inclusion hinterior)) := by
  simpa using
    isBarrierFunctionOn_of_tendsto_zero f hinterior hint (powerBarrier f p)
      (fun x hvanish ↦
        powerBarrier_tendsto_atTop_of_exists_constraint_tendsto_zero f p hp hvanish)

/-- Along a sequence in `interior (constraintSet f)` converging to a frontier point, the
logarithmic barrier tends to `+∞`. -/
private theorem logarithmicBarrier_tendsto_atTop_of_tendsto_frontier_constraintSet
    (f : ι → C(α, ℝ))
    (hinterior : interior (constraintSet f) ⊆ strictConstraintSet f)
    (x : ℕ → interior (constraintSet f)) {xBar : α}
    (hx : Tendsto (fun k ↦ (x k : α)) atTop (nhds xBar))
    (hxBar : xBar ∈ frontier (constraintSet f)) :
    Tendsto
      (fun k ↦ logarithmicBarrier f ⟨x k, hinterior (x k).property⟩)
      atTop atTop := by
  classical
  rcases exists_constraint_tendsto_zero_of_tendsto_frontier_constraintSet f x hx hxBar with
    ⟨j, hj⟩
  let xStrict : ℕ → strictConstraintSet f := fun k ↦ ⟨x k, hinterior (x k).property⟩
  let slack : ℕ → ℝ := fun k ↦ -f j (x k : α)
  have hxBar_mem : xBar ∈ constraintSet f := by
    have hxBar' : xBar ∈ constraintSet f \ interior (constraintSet f) := by
      simpa [(isClosed_constraintSet f).frontier_eq] using hxBar
    exact hxBar'.1
  have hxBar_le : ∀ i : ι, f i xBar ≤ 0 := by
    simpa [constraintSet] using hxBar_mem
  -- The active logarithmic summand blows up exactly as in the source proof.
  have hslack : Tendsto slack atTop (nhds 0) := by
    simpa [slack] using hj.neg
  have hslack_pos : ∀ k : ℕ, 0 < slack k := by
    intro k
    simpa [slack, xStrict] using neg_constraint_pos f j (xStrict k)
  have hslack_within : Tendsto slack atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [nhdsWithin]
    refine Filter.tendsto_inf.2 ?_
    refine ⟨hslack, ?_⟩
    exact Filter.tendsto_principal.2 <|
      Filter.Eventually.of_forall hslack_pos
  have hlog : Tendsto (fun k ↦ Real.log (slack k)) atTop atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hslack_within
  have hactive : Tendsto (fun k ↦ -Real.log (slack k)) atTop atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [Filter.tendsto_atBot.1 hlog (-b)] with k hk
    linarith
  let c : ι → ℝ := fun i ↦
    if hzero : f i xBar = 0 then 0 else -Real.log (-f i xBar) - 1
  have hterm_lower :
      ∀ i : ι, i ≠ j →
        ∀ᶠ k in atTop, c i ≤ -Real.log (-f i (x k : α)) := by
    intro i hij
    have hfi : Tendsto (fun k ↦ f i (x k : α)) atTop (nhds (f i xBar)) :=
      ((f i).continuousAt xBar).tendsto.comp hx
    by_cases hzero : f i xBar = 0
    · let slacki : ℕ → ℝ := fun k ↦ -f i (x k : α)
      have hslacki : Tendsto slacki atTop (nhds 0) := by
        simpa [slacki, hzero] using hfi.neg
      have hlt_one : ∀ᶠ k in atTop, slacki k < 1 := by
        have hmem : Set.Iio (1 : ℝ) ∈ nhds (0 : ℝ) := Iio_mem_nhds (by norm_num)
        exact hslacki hmem
      filter_upwards
        [Filter.Eventually.of_forall (fun k ↦ neg_constraint_pos f i (xStrict k)), hlt_one] with
        k hkpos hkone
      have hlog_nonpos : Real.log (slacki k) ≤ 0 :=
        Real.log_nonpos (le_of_lt hkpos) (le_of_lt hkone)
      have hbound : 0 ≤ -Real.log (slacki k) := by
        linarith
      simpa [c, hzero, slacki] using hbound
    · have hi_neg : f i xBar < 0 :=
        lt_of_le_of_ne (hxBar_le i) hzero
      have hneg_term : Tendsto (fun k ↦ -f i (x k : α)) atTop (nhds (-f i xBar)) := by
        simpa using hfi.neg
      have hterm :
          Tendsto (fun k ↦ -Real.log (-f i (x k : α))) atTop
            (nhds (-Real.log (-f i xBar))) := by
        have hcont : ContinuousAt (fun t : ℝ ↦ -Real.log t) (-f i xBar) := by
          have hpos : 0 < -f i xBar := by
            linarith
          exact (Real.continuousAt_log (ne_of_gt hpos)).neg
        exact hcont.tendsto.comp hneg_term
      have hmem : Set.Ioi (-Real.log (-f i xBar) - 1) ∈ nhds (-Real.log (-f i xBar)) := by
        exact Ioi_mem_nhds (by linarith)
      filter_upwards [hterm hmem] with k hk
      have hbound : -Real.log (-f i xBar) - 1 ≤ -Real.log (-f i (x k : α)) :=
        le_of_lt hk
      simpa [c, hzero] using hbound
  have hsum_lower :
      ∀ᶠ k in atTop,
        Finset.sum (Finset.univ.erase j) c
          ≤ Finset.sum (Finset.univ.erase j) (fun i ↦ -Real.log (-f i (x k : α))) := by
    -- Every inactive constraint contributes an eventually bounded-below term.
    filter_upwards
      [(Finset.eventually_all (Finset.univ.erase j)).2
        (fun i hi ↦ hterm_lower i (Finset.mem_erase.mp hi).1)] with k hk
    exact Finset.sum_le_sum (fun i hi ↦ hk i hi)
  let C : ℝ := Finset.sum (Finset.univ.erase j) c
  have hshift : Tendsto (fun k ↦ C + (-Real.log (slack k))) atTop atTop := by
    -- Adding the finite lower-bound constant preserves divergence to `+∞`.
    have hshift' : Tendsto (fun k ↦ -Real.log (slack k) + C) atTop atTop := by
      have hadd : Tendsto (fun t : ℝ ↦ t + C) atTop atTop := by
        rw [Filter.Tendsto]
        simpa [Filter.map_map] using le_of_eq (Filter.map_add_atTop_eq C)
      exact hadd.comp hactive
    simpa [add_comm] using hshift'
  have hdom :
      ∀ᶠ k in atTop,
        C + (-Real.log (slack k)) ≤ logarithmicBarrier f (xStrict k) := by
    filter_upwards [hsum_lower] with k hk
    have hleft :
        C + (-Real.log (slack k))
          ≤ Finset.sum (Finset.univ.erase j) (fun i ↦ -Real.log (-f i (x k : α)))
              + (-Real.log (slack k)) := by
      have hk' :
          C ≤ Finset.sum (Finset.univ.erase j) (fun i ↦ -Real.log (-f i (x k : α))) := by
        simpa [C] using hk
      linarith
    calc
      C + (-Real.log (slack k))
          ≤ Finset.sum (Finset.univ.erase j) (fun i ↦ -Real.log (-f i (x k : α)))
              + (-Real.log (slack k)) := hleft
      _ = logarithmicBarrier f (xStrict k) := by
        rw [logarithmicBarrier_apply]
        calc
          Finset.sum (Finset.univ.erase j) (fun i ↦ -Real.log (-f i (x k : α)))
              + (-Real.log (slack k))
              = ∑ i : ι, -Real.log (-f i (x k : α)) := by
                  simpa [slack] using
                    Finset.sum_erase_add
                      (Finset.univ : Finset ι)
                      (fun i ↦ -Real.log (-f i (x k : α)))
                      (by simp : j ∈ (Finset.univ : Finset ι))
          _ = -∑ i : ι, Real.log (-f i (x k : α)) := by
                simpa using
                  (Finset.neg_sum (fun i : ι ↦ Real.log (-f i (x k : α)))).symm
  refine Filter.tendsto_atTop.2 ?_
  intro b
  filter_upwards [Filter.tendsto_atTop.1 hshift b, hdom] with k hk hk'
  exact le_trans hk hk'

/-- Proposition 1.10.17 (2): if the chosen strict inequalities recover
`interior (constraintSet f)`, then the logarithmic formula, viewed on that interior via the
canonical inclusion, is a barrier function for `constraintSet f`. -/
theorem logarithmicBarrier_isBarrierFunctionOn
    (f : ι → C(α, ℝ))
    (hinterior : interior (constraintSet f) ⊆ strictConstraintSet f)
    (hint : (interior (constraintSet f)).Nonempty) :
    IsBarrierFunctionOn (constraintSet f)
      ((logarithmicBarrier f).comp (inclusion hinterior)) := by
  let _ : Fact (IsClosed (constraintSet f)) := ⟨isClosed_constraintSet f⟩
  refine IsBarrierFunctionOn.mk hint ?_
  intro x xBar hx hxBar
  simpa using
    logarithmicBarrier_tendsto_atTop_of_tendsto_frontier_constraintSet
      f hinterior x hx hxBar

/-- Proposition 1.10.17 (3): if the chosen strict inequalities recover
`interior (constraintSet f)`, then the exponential formula, viewed on that interior via the
canonical inclusion, is a barrier function for `constraintSet f`. -/
theorem exponentialBarrier_isBarrierFunctionOn
    (f : ι → C(α, ℝ))
    (hinterior : interior (constraintSet f) ⊆ strictConstraintSet f)
    (hint : (interior (constraintSet f)).Nonempty) :
    IsBarrierFunctionOn (constraintSet f)
      ((exponentialBarrier f).comp (inclusion hinterior)) := by
  simpa using
    isBarrierFunctionOn_of_tendsto_zero f hinterior hint (exponentialBarrier f)
      (fun x hvanish ↦
        exponentialBarrier_tendsto_atTop_of_exists_constraint_tendsto_zero f hvanish)

end BarrierFunctionBridge

end ConstraintBarrierExamples
end FiniteIndex

/-! ### Definition_1_10_18 (from Chap01) -/
open Filter Set Topology

universe u

variable {α : Type u} [TopologicalSpace α]

/- Primary domain: barrier predicates for continuous real-valued functions on the interior of a
closed subset of a topological space.

Sampled owner-style declarations in the same domain:
* `C(interior 𝓕, ℝ)`, the canonical owner for continuous maps on the intrinsic domain;
* `TopologicalSpace.Closeds α`, the canonical mathlib owner for closed subsets;
* `liftedConeLogSumExpBarrier_restriction_isBarrierFunctionOn` in `Chap05/Theorem_5_4_7_7`,
  which expresses the same frontier growth condition after passing to the normalization-hyperplane
  relative ambient space;
* `IsSelfConcordantBarrierOnWith dom ν F` in `Chap05/Definition_5_3_2`, which keeps the owner
  function central and pushes auxiliary assumptions into parent structure data.

Best owner abstraction:
* source-facing: `IsBarrierFunctionOn 𝓕 F`;
* core/canonical: the bundled owner map `F : C(interior 𝓕, ℝ)`;
* bridge/view: the closed-set hypothesis should be carried canonically as a parent assumption,
  not repeated as a bespoke field, while the interior nonemptiness and frontier-divergence data
  remain part of the source-facing notion.

Primitive data:
* `Fact (IsClosed 𝓕)`;
* `(interior 𝓕).Nonempty`;
* the frontier growth condition for the owner map.

Derived API:
* `hF.isClosed : IsClosed 𝓕`;
* `hF.interior_ne_empty : interior 𝓕 ≠ ∅`. -/

/-- Definition 1.10.18: a barrier function for `𝓕` is a bundled continuous map
`F : C(interior 𝓕, ℝ)` on the interior of a closed set `𝓕` with nonempty interior, such that the
values of `F` along every sequence in `interior 𝓕` converging to a boundary point of `𝓕` tend to
`+∞`. The owner object is the continuous map on `interior 𝓕`; the closedness and nonempty-interior
hypotheses remain part of the public predicate because they are part of the textbook notion. -/
class IsBarrierFunctionOn (𝓕 : Set α) (F : C(interior 𝓕, ℝ)) : Prop
    extends Fact (IsClosed 𝓕) where
  interior_nonempty : (interior 𝓕).Nonempty
  tendsTo_atTop_of_tendsto_frontier (x : ℕ → interior 𝓕) {xBar : α}
      (hx : Tendsto (fun k ↦ (x k : α)) atTop (nhds xBar))
      (hxBar : xBar ∈ frontier 𝓕) :
      Tendsto (fun k ↦ F (x k)) atTop atTop

attribute [instance] IsBarrierFunctionOn.toFact

namespace IsBarrierFunctionOn

theorem isClosed {𝓕 : Set α} {F : C(interior 𝓕, ℝ)}
    (hF : IsBarrierFunctionOn 𝓕 F) :
    IsClosed 𝓕 := by
  let _ : IsBarrierFunctionOn 𝓕 F := hF
  exact Fact.out

theorem interior_ne_empty {𝓕 : Set α} {F : C(interior 𝓕, ℝ)}
    (hF : IsBarrierFunctionOn 𝓕 F) :
    interior 𝓕 ≠ ∅ :=
  hF.interior_nonempty.ne_empty

end IsBarrierFunctionOn

/-! ### Definition_1_10_21 (from Chap01) -/
universe u

namespace FunctionalConstraintsMinimizationProblem

variable {X : Type u} [TopologicalSpace X] {m : ℕ}

/- Definition 1.10.21 lies in the topological constrained-optimization domain.

Sampled owner-style declarations:
* `FunctionalConstraintsMinimizationProblem X m`, `problem.HasLeConstraints`, and
  `problem.mem_feasibleSet_iff` in `Chap01/Definition_1_1_1`
* `FunctionalConstraintsMinimizationProblem.IsLinearlyConstrained` and
  `problem.constraintVector_affineOn_iff_forall_constraint_affineOn` in
  `Chap01/Definition_1_1_4_5`
* `Continuous` and `IsClosed` from mathlib's topological API

Best owner abstraction:
* `FunctionalConstraintsMinimizationProblem X m`

Primitive data:
* `problem.basicFeasibleSet`
* `problem.objective`
* `problem.constraints`
* `problem.senses`

Derived API:
* closedness of `problem.basicFeasibleSet`
* continuity of `problem.objective`
* continuity of the packaged map `problem.constraintVector`
* continuity of each scalar constraint
* the inequality-only condition `problem.HasLeConstraints`

Source/core/bridge triage:
* source-facing: the textbook `GeneralMinimizationProblem n m` specialization
* core/canonical: `FunctionalConstraintsMinimizationProblem X m`
* bridge/view: `GeneralMinimizationProblem n m` as the Euclidean specialization

These hypotheses depend only on the topology of the feasible subtype and the finite real-valued
constraint family, so they belong to the ambient owner `FunctionalConstraintsMinimizationProblem`
rather than to the Euclidean specialization. -/

/- The packaged owner constraint map is continuous exactly when each scalar constraint function is
continuous. This is the canonical owner-level bridge from the coordinate family to the vector
constraint map. -/
theorem constraintVector_continuous_iff (problem : FunctionalConstraintsMinimizationProblem X m) :
    Continuous problem.constraintVector ↔ ∀ j : Fin m, Continuous (problem.constraints j) := by
  constructor
  · intro h j
    have hj : Continuous (fun x : EuclideanSpace ℝ (Fin m) ↦ x j) :=
      PiLp.continuous_apply (2 : ENNReal) (fun _ : Fin m ↦ ℝ) j
    simpa using hj.comp h
  · intro h
    simpa [FunctionalConstraintsMinimizationProblem.constraintVector] using
      (PiLp.continuous_toLp (2 : ENNReal) (fun _ : Fin m ↦ ℝ)).comp (continuous_pi h)

/-- Definition 1.10.21: a nonlinear optimization problem with functional constraints is a
functional-constraint minimization problem whose basic feasible set is closed, whose objective and
constraint functions are continuous on that feasible subtype, and whose scalar constraints are all
of the form `fⱼ(x) ≤ 0`. The textbook `GeneralMinimizationProblem n m` case is the Euclidean
specialization of this owner. The primitive continuity data are the scalar constraints; continuity
of the packaged owner map `problem.constraintVector` is derived. -/
class IsFunctionalConstraintProblem
    (problem : FunctionalConstraintsMinimizationProblem X m) : Prop where
  basicFeasibleSet_isClosed : IsClosed problem.basicFeasibleSet
  objective_continuous : Continuous problem.objective
  constraint_continuous (j : Fin m) : Continuous (problem.constraints j)
  hasLeConstraints : problem.HasLeConstraints

variable {problem : FunctionalConstraintsMinimizationProblem X m}

/-- A functional-constraint problem has a continuous packaged owner constraint map. -/
theorem IsFunctionalConstraintProblem.constraintVector_continuous
    (h : problem.IsFunctionalConstraintProblem) :
    Continuous problem.constraintVector :=
  problem.constraintVector_continuous_iff.2 h.constraint_continuous

instance [h : problem.IsFunctionalConstraintProblem] :
    IsClosed problem.basicFeasibleSet :=
  h.basicFeasibleSet_isClosed

instance [h : problem.IsFunctionalConstraintProblem] :
    Continuous problem.objective :=
  h.objective_continuous

instance [h : problem.IsFunctionalConstraintProblem] :
    Continuous problem.constraintVector :=
  h.constraintVector_continuous

instance [h : problem.IsFunctionalConstraintProblem] (j : Fin m) :
    Continuous (problem.constraints j) :=
  h.constraint_continuous j

instance [h : problem.IsFunctionalConstraintProblem] :
    problem.HasLeConstraints :=
  h.hasLeConstraints

end FunctionalConstraintsMinimizationProblem

namespace GeneralMinimizationProblem

variable {n m : ℕ} (problem : GeneralMinimizationProblem n m)

/- Definition 1.10.21 in the textbook Euclidean ambient space uses the same Chapter 1 owner
predicate, specialized from `FunctionalConstraintsMinimizationProblem X m` to
`GeneralMinimizationProblem n m`. -/
#check problem.IsFunctionalConstraintProblem

end GeneralMinimizationProblem

/-! ### Theorem_1_10_22 (from Chap01) -/
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

/-! ### Theorem_1_10_23 (from Chap01) -/
noncomputable section

open Filter Set Topology

universe u

variable {α : Type u} [TopologicalSpace α]

variable {Q 𝓕 : Set α}
variable {objective : ↥(Q ∩ interior 𝓕) → ℝ} {F : C(interior 𝓕, ℝ)}
variable [IsBarrierFunctionOn 𝓕 F]

local notation "Q₀" => {x // x ∈ Q ∩ interior 𝓕}
local notation "F₀" =>
  ((F.comp (ContinuousMap.inclusion inter_subset_right)) : Q₀ → ℝ)
local notation "primalProblem" =>
  SetConstrainedMinimizationProblem.unconstrained objective

namespace BarrierFunctionMethod

/-- Helper for Theorem 1.10.23: every auxiliary optimal value is bounded above by the auxiliary
objective at any comparison point in `Q ∩ interior 𝓕`. -/
theorem auxiliaryOptimalValue_le_value_at
    (method : BarrierFunctionMethod Q 𝓕 objective F) (k : ℕ) (x : Q₀) :
    method.auxiliaryOptimalValue k ≤ ((method.auxiliaryObjective k x : ℝ) : EReal) := by
  -- The selected iterate minimizes the `k`-th auxiliary objective over the whole feasible type.
  simpa [BarrierFunctionMethod.auxiliaryOptimalValue, BarrierFunctionMethod.auxiliaryProblem] using
    (method.auxiliaryProblem k).optimalValue_le_of_mem_feasibleSet (by simp)

/-- Helper for Theorem 1.10.23: a global lower bound for the barrier shifts the primal optimal
value below every auxiliary optimal value by the same scaled amount. -/
theorem lower_barrier_shift_le_auxiliaryOptimalValue
    (method : BarrierFunctionMethod Q 𝓕 objective F) {c : ℝ}
    (hc : c ∈ lowerBounds (Set.range F₀)) (k : ℕ) :
    (primalProblem).optimalValue + ((c / method.barrierParameters k : ℝ) : EReal) ≤
      method.auxiliaryOptimalValue k := by
  let Δ : ℝ := -(c / method.barrierParameters k)
  have hcompare :=
    SetConstrainedMinimizationProblem.optimalValue_sub_le_optimalValue_of_forall_sub_le
      primalProblem
      (method.auxiliaryProblem k)
      (Δ := Δ)
      (by
        change Set.univ =
          (method.toSequentialUnconstrainedMinimizationScheme.auxiliaryProblem k.succPNat).feasibleSet
        simp [SequentialUnconstrainedMinimizationScheme.auxiliaryProblem,
          SetConstrainedMinimizationProblem.unconstrained])
      (by
        intro x hx
        -- Compare the barrier term with the global lower bound `c`.
        change objective x - Δ ≤
          method.toSequentialUnconstrainedMinimizationScheme.auxiliaryObjectives k.succPNat x
        simp [BarrierFunctionMethod.toSequentialUnconstrainedMinimizationScheme,
          BarrierFunctionMethod.auxiliaryObjective]
        have hcx : c ≤ F₀ x := hc ⟨x, rfl⟩
        have hinv_nonneg : 0 ≤ 1 / method.barrierParameters k :=
          one_div_nonneg.mpr (method.barrierParameters_pos k).le
        have hdiv : c / method.barrierParameters k ≤
            (1 / method.barrierParameters k) * F₀ x := by
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
            mul_le_mul_of_nonneg_left hcx hinv_nonneg
        simpa [Δ, sub_eq_add_neg, div_eq_mul_inv, add_comm, add_left_comm, add_assoc,
          mul_comm, mul_left_comm, mul_assoc] using add_le_add_left hdiv (objective x))
  -- Re-express the optimal-value comparison in the textbook additive form.
  simpa [BarrierFunctionMethod.auxiliaryOptimalValue, Δ, sub_eq_add_neg, EReal.coe_add,
    EReal.coe_neg, add_assoc, add_left_comm, add_comm] using hcompare

/-- Helper for Theorem 1.10.23: the primal optimal value is finite from above because any iterate
provides a feasible comparison value. -/
theorem primal_optimalValue_ne_top
    (method : BarrierFunctionMethod Q 𝓕 objective F) :
    (primalProblem).optimalValue ≠ ⊤ := by
  -- Any feasible point bounds the optimal value away from `⊤`.
  refine ne_of_lt ?_
  refine lt_of_le_of_lt
    ((primalProblem).optimalValue_le_of_mem_feasibleSet (x := method 0) (by simp))
    (EReal.coe_lt_top _)

/-- Helper for Theorem 1.10.23: if the primal optimal value lies below a real threshold, then
some interior-feasible point already has objective value below that threshold. -/
theorem exists_objective_lt_of_optimalValue_lt
    (method : BarrierFunctionMethod Q 𝓕 objective F) (b : ℝ)
    (hb : (primalProblem).optimalValue < (b : EReal)) :
    ∃ x : Q₀, (objective x : EReal) < (b : EReal) := by
  -- The feasible-value image is nonempty because the method supplies interior-feasible iterates.
  rw [SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image] at hb
  have himage_nonempty :
      ((fun x ↦ (primalProblem x : EReal)) '' (primalProblem).feasibleSet).Nonempty := by
    refine ⟨(objective (method 0) : EReal), ?_⟩
    refine ⟨method 0, by simp, rfl⟩
  rcases exists_lt_of_csInf_lt himage_nonempty hb with ⟨v, hv, hvlt⟩
  rcases hv with ⟨x, hx, rfl⟩
  -- Unpack the image witness to recover the desired feasible point.
  exact ⟨x, by simpa using hvlt⟩

end BarrierFunctionMethod

/- Theorem 1.10.23 lies in the Chapter 1 barrier-method convergence domain.

Sampled owner declarations in this domain:
* `BarrierFunctionMethod` in `Algorithm_1_10_20`, the source-facing owner of the barrier iterates,
  auxiliary objectives, and auxiliary optimal values;
* `SetConstrainedMinimizationProblem.unconstrained` in `Definition_1_3_3`, the canonical owner
  problem attached to an objective on the whole feasible type;
* `SetConstrainedMinimizationProblem.optimalValue` in `Definition_1_3_7`, the canonical optimal
  value attached to that owner;
* `BddBelow (Set.range f)`, the project's canonical lower-boundedness interface when only the
  existence of a lower bound matters;
* `BarrierFunctionMethod.toSequentialUnconstrainedMinimizationScheme`, the bridge to the generic
  sequential-unconstrained owner.

Best owner abstraction:
* source-facing: `BarrierFunctionMethod Q 𝓕 objective F`;
* core/canonical: the owner problems `method.auxiliaryProblem k` and `primalProblem`;
* bridge/view: the lower-boundedness hypothesis on the canonical restriction `F₀ : Q₀ → ℝ`,
  expressed as `BddBelow (Set.range F₀)`.

Primitive data:
* the barrier method `method`;
* the lower-boundedness of the restricted barrier map `F₀ : Q₀ → ℝ`.

Derived API:
* `method.auxiliaryOptimalValue`;
* `primalProblem.optimalValue`;
* the auxiliary-problem optimal-value identities coming from the owner files.

The theorem therefore stays source-facing on `BarrierFunctionMethod`, but uses the owner
lower-boundedness predicate `BddBelow` applied to the canonical restriction `F₀`, and the weakest
ambient topological assumptions already supported by the barrier-method owner, instead of a
Euclidean-only ambient model or a bespoke existential lower-bound package.
-/

/-- Theorem 1.10.23: if the barrier `F` is bounded below on `𝓕₀ = Q ∩ interior 𝓕`, then the
global optimal values `Ψₖ*` of the auxiliary objectives
`x ↦ f₀(x) + (1 / tₖ) F(x)` converge to the optimal value `f*` of `f₀` on `𝓕₀`. -/
-- Proof sketch: for any interior-feasible comparison point `x̄`, the minimizing property gives
-- `Ψₖ* ≤ f₀(x̄) + tₖ⁻¹ F(x̄)`, and `tₖ → ∞` sends the barrier term to `0`, yielding the upper
-- bound by `f*`. A lower bound for `F` on `𝓕₀` gives `Ψₖ* ≥ f* + tₖ⁻¹ F_*`; passing to the
-- limit and squeezing the two bounds proves convergence.
theorem BarrierFunctionMethod.auxiliaryOptimalValue_tendsto_optimalValue
    (method : BarrierFunctionMethod Q 𝓕 objective F)
    (hF : BddBelow (Set.range F₀)) :
    Tendsto method.auxiliaryOptimalValue atTop (nhds (primalProblem).optimalValue) :=
  by
    rcases hF with ⟨c, hc⟩
    -- The source proof is a two-sided squeeze: a global barrier lower bound gives the lower
    -- comparison, and evaluation at a fixed feasible point gives the upper comparison.
    refine tendsto_order.2 ?_
    constructor
    · intro a ha
      by_cases ha_bot : a = ⊥
      · -- Lower neighborhoods of `⊥` are vacuous, so every auxiliary value lies above them.
        subst ha_bot
        filter_upwards [] with k
        rw [method.auxiliaryOptimalValue_eq_iterateValue]
        exact EReal.bot_lt_coe _
      · -- For a finite lower threshold, the scaled lower barrier shift eventually
        -- dominates the gap.
        have hp_ne_bot : (primalProblem).optimalValue ≠ ⊥ := by
          intro hp_bot
          have ha' := ha
          simp [hp_bot] at ha'
        let aReal : ℝ := a.toReal
        let pReal : ℝ := (primalProblem).optimalValue.toReal
        have ha_eq : ((aReal : ℝ) : EReal) = a := by
          exact EReal.coe_toReal (ne_of_lt (ha.trans_le le_top)) ha_bot
        have hp_eq : ((pReal : ℝ) : EReal) = (primalProblem).optimalValue := by
          exact EReal.coe_toReal (method.primal_optimalValue_ne_top) hp_ne_bot
        have haReal_lt : aReal < pReal := by
          have hcoe : ((aReal : ℝ) : EReal) < ((pReal : ℝ) : EReal) := by
            simpa [ha_eq, hp_eq] using ha
          exact (EReal.coe_lt_coe_iff.mp hcoe)
        have hshift_tendsto :
            Tendsto (fun k ↦ c / method.barrierParameters k) atTop (nhds 0) :=
          Filter.Tendsto.const_div_atTop method.barrierParameters_tendsto_atTop c
        have hgap_eventually :
            ∀ᶠ k : ℕ in atTop, aReal - pReal < c / method.barrierParameters k := by
          have hgap : aReal - pReal < 0 := by
            linarith
          exact hshift_tendsto (Ioi_mem_nhds hgap)
        filter_upwards [hgap_eventually] with k hk
        have hk' : aReal < pReal + c / method.barrierParameters k := by
          linarith
        have hlt_shift : a <
            (primalProblem).optimalValue + ((c / method.barrierParameters k : ℝ) : EReal) := by
          have hkE : a < ((pReal + c / method.barrierParameters k : ℝ) : EReal) := by
            rw [← ha_eq]
            exact_mod_cast hk'
          calc
            a < ((pReal + c / method.barrierParameters k : ℝ) : EReal) := hkE
            _ = (primalProblem).optimalValue + ((c / method.barrierParameters k : ℝ) : EReal) := by
              rw [EReal.coe_add, hp_eq]
        exact lt_of_lt_of_le hlt_shift
          (method.lower_barrier_shift_le_auxiliaryOptimalValue hc k)
    · intro a ha
      by_cases htop : a = ⊤
      · -- Every auxiliary optimal value is a realized real value, so it is automatically below `⊤`.
        subst htop
        filter_upwards [] with k
        rw [method.auxiliaryOptimalValue_eq_iterateValue]
        exact EReal.coe_lt_top _
      · -- Choose a feasible comparison point with objective below the target threshold.
        have ha_ne_bot : a ≠ ⊥ := by
          exact (bot_lt_iff_ne_bot.mp (lt_of_le_of_lt bot_le ha))
        let aReal : ℝ := a.toReal
        have ha_eq : ((aReal : ℝ) : EReal) = a := by
          exact EReal.coe_toReal htop ha_ne_bot
        obtain ⟨x, hxlt⟩ := method.exists_objective_lt_of_optimalValue_lt aReal (by
          simpa [ha_eq] using ha)
        have hbarrier_tendsto :
            Tendsto (fun k ↦ F (inclusion inter_subset_right x) / method.barrierParameters k) atTop
              (nhds 0) :=
          Filter.Tendsto.const_div_atTop method.barrierParameters_tendsto_atTop
            (F (inclusion inter_subset_right x))
        have hcomparison_tendsto :
            Tendsto
              (fun k ↦ objective x + F (inclusion inter_subset_right x) / method.barrierParameters k)
              atTop
              (nhds (objective x)) := by
          simpa using (tendsto_const_nhds.add hbarrier_tendsto)
        have hvalue_eventually :
            ∀ᶠ k : ℕ in atTop, method.auxiliaryObjective k x < aReal := by
          have hraw :
              ∀ᶠ k : ℕ in atTop,
                objective x + F (inclusion inter_subset_right x) / method.barrierParameters k <
                  aReal := by
            exact hcomparison_tendsto (Iio_mem_nhds (by simpa using hxlt))
          filter_upwards [hraw] with k hk
          simpa [BarrierFunctionMethod.auxiliaryObjective, div_eq_mul_inv, mul_comm] using hk
        filter_upwards [hvalue_eventually] with k hk
        have haux_lt : ((method.auxiliaryObjective k x : ℝ) : EReal) < a := by
          rw [← ha_eq]
          exact_mod_cast hk
        exact lt_of_le_of_lt (method.auxiliaryOptimalValue_le_value_at k x) haux_lt
