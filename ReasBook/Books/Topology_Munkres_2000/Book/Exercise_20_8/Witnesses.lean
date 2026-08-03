module

public import Topology_Munkres_2000.Book.Exercise_20_8.EventuallyZero
public import Topology_Munkres_2000.Book.Exercise_20_4

public noncomputable section

open scoped lp Topology

/-- Helper for Exercise 20.8: the zero sequence as an eventually-zero sequence. -/
@[expose]
def eventuallyZeroZero : eventuallyZeroRealSequences :=
  ⟨0, mem_eventuallyZeroRealSequences.mpr Function.hasFiniteSupport_zero⟩

/-- Helper for Exercise 20.8: the eventually-zero zero sequence vanishes coordinatewise. -/
@[simp]
lemma eventuallyZeroZero_apply (n : ℕ) : eventuallyZeroZero.1 n = 0 := rfl

/-- Helper for Exercise 20.8: the underlying function of the eventually-zero zero sequence
is the zero function. -/
lemma eventuallyZeroZero_val : eventuallyZeroZero.1 = 0 := by
  -- Extensionality reduces the statement to the coordinate computation lemma.
  funext n
  exact eventuallyZeroZero_apply n

/-- Helper for Exercise 20.8: the canonical inclusion sends the eventually-zero zero
sequence to zero in `ℓ²`. -/
@[simp]
lemma eventuallyZeroToL2_zero : eventuallyZeroToL2 eventuallyZeroZero = 0 := by
  -- Equality follows directly from the coordinate formula.
  apply lp.ext
  rfl

/-- Helper for Exercise 20.8: a finite initial segment, represented canonically in `ℓ²`. -/
def initialSegmentL2 (a : ℕ → ℝ) (n : ℕ) : ℓ²(ℕ, ℝ) :=
  ∑ i ∈ Finset.range (n + 1), lp.single 2 i (a n)

/-- Helper for Exercise 20.8: the canonical finite initial segment has the expected
coordinate formula. -/
@[simp]
lemma initialSegmentL2_apply (a : ℕ → ℝ) (n i : ℕ) :
    initialSegmentL2 a n i = if i ≤ n then a n else 0 := by
  -- Evaluate the finite sum of single-coordinate vectors at `i`.
  simp only [initialSegmentL2, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single,
    Finset.sum_pi_single]
  simp only [Finset.mem_range, Nat.lt_add_one_iff]

/-- Helper for Exercise 20.8: finite initial segments have the expected squared `ℓ²` norm. -/
lemma initialSegmentL2_norm_sq (a : ℕ → ℝ) (n : ℕ) :
    ‖initialSegmentL2 a n‖ ^ 2 = (n + 1 : ℝ) * |a n| ^ 2 := by
  -- Apply the disjoint-singleton norm formula and simplify the constant finite sum.
  have h := lp.norm_sum_single (E := fun _ : ℕ ↦ ℝ) (p := (2 : ENNReal))
    (by norm_num) (fun _ ↦ a n) (Finset.range (n + 1))
  simp only [show (2 : ENNReal).toReal = 2 by norm_num, Real.rpow_two] at h
  simpa only [initialSegmentL2,
    Real.norm_eq_abs, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one] using h

/-- Helper for Exercise 20.8: the coordinate function of a finite initial segment has
finite support. -/
lemma initialSegmentL2_hasFiniteSupport (a : ℕ → ℝ) (n : ℕ) :
    (fun i ↦ initialSegmentL2 a n i).HasFiniteSupport := by
  -- Its support is contained in the finite set of coordinates through `n`.
  rw [Function.HasFiniteSupport]
  refine (Finset.range (n + 1)).finite_toSet.subset fun i hi ↦ ?_
  simp only [Function.mem_support, initialSegmentL2_apply] at hi
  simp only [Finset.mem_coe, Finset.mem_range, Nat.lt_add_one_iff]
  by_contra hin
  exact hi (if_neg hin)

/-- Helper for Exercise 20.8: package a canonical finite initial segment as an
eventually-zero sequence. -/
@[expose]
def initialSegmentEventuallyZero (a : ℕ → ℝ) (n : ℕ) : eventuallyZeroRealSequences :=
  ⟨fun i ↦ initialSegmentL2 a n i,
    mem_eventuallyZeroRealSequences.mpr (initialSegmentL2_hasFiniteSupport a n)⟩

/-- Helper for Exercise 20.8: the packaged initial segment has the expected coordinate
formula. -/
@[simp]
lemma initialSegmentEventuallyZero_apply (a : ℕ → ℝ) (n i : ℕ) :
    (initialSegmentEventuallyZero a n).1 i = if i ≤ n then a n else 0 := by
  -- Reduce to the canonical `ℓ²` coordinate formula.
  exact initialSegmentL2_apply a n i

/-- Helper for Exercise 20.8: the eventually-zero inclusion recovers the canonical `ℓ²`
finite initial segment. -/
@[simp]
lemma eventuallyZeroToL2_initialSegment (a : ℕ → ℝ) (n : ℕ) :
    eventuallyZeroToL2 (initialSegmentEventuallyZero a n) = initialSegmentL2 a n := by
  -- Equality follows coordinatewise from the packaging definition.
  apply lp.ext
  rfl

/-- Helper for Exercise 20.8: a single-coordinate spike in `ℓ²`. -/
@[expose]
def coordinateSpikeL2 (a : ℕ → ℝ) (n : ℕ) : ℓ²(ℕ, ℝ) :=
  lp.single 2 n (a n)

/-- Helper for Exercise 20.8: a coordinate spike has its prescribed value at its center. -/
@[simp]
lemma coordinateSpikeL2_apply_self (a : ℕ → ℝ) (n : ℕ) :
    coordinateSpikeL2 a n n = a n := by
  -- Evaluate the canonical single-coordinate vector at its selected coordinate.
  simp only [coordinateSpikeL2, lp.coeFn_single, Pi.single_eq_same]

/-- Helper for Exercise 20.8: a coordinate spike vanishes away from its center. -/
@[simp]
lemma coordinateSpikeL2_apply_ne (a : ℕ → ℝ) {n i : ℕ} (h : i ≠ n) :
    coordinateSpikeL2 a n i = 0 := by
  -- Evaluate the canonical single-coordinate vector off its selected coordinate.
  simp only [coordinateSpikeL2, lp.coeFn_single, Pi.single_eq_of_ne h]

/-- Helper for Exercise 20.8: the norm of a coordinate spike is its scalar magnitude. -/
@[simp]
lemma coordinateSpikeL2_norm (a : ℕ → ℝ) (n : ℕ) :
    ‖coordinateSpikeL2 a n‖ = |a n| := by
  -- Use the canonical norm formula for `lp.single`.
  have h := lp.norm_single (E := fun _ : ℕ ↦ ℝ) (p := (2 : ENNReal))
    (by norm_num) n (a n)
  simpa only [coordinateSpikeL2, Real.norm_eq_abs] using h

/-- Helper for Exercise 20.8: the uniform distance from a coordinate spike to zero is the
truncated magnitude of its scalar. -/
lemma coordinateSpike_uniformDist_zero (a : ℕ → ℝ) (n : ℕ) :
    (UniformMetric.metricSpace ℕ).dist (fun i ↦ coordinateSpikeL2 a n i) 0 =
      min |a n| 1 := by
  -- Bound the defining supremum above, then attain that bound at coordinate `n`.
  rw [UniformMetric.dist_eq]
  apply le_antisymm
  · refine ciSup_le fun i ↦ ?_
    by_cases hi : i = n
    · subst i
      simp only [coordinateSpikeL2_apply_self, Pi.zero_apply, Real.dist_eq, sub_zero]
      rfl
    · simp only [coordinateSpikeL2_apply_ne a hi, Pi.zero_apply, dist_self]
      norm_num
  · have hle := le_ciSup (f := fun i : ℕ ↦
      min (dist (coordinateSpikeL2 a n i) ((0 : ℕ → ℝ) i)) 1)
      (⟨1, Set.forall_mem_range.mpr fun i ↦ min_le_right _ _⟩) n
    simpa only [coordinateSpikeL2_apply_self, Pi.zero_apply, Real.dist_eq, sub_zero] using hle

/-- Helper for Exercise 20.8: moving coordinate spikes converge coordinatewise to zero. -/
lemma coordinateSpike_tendsto_product (a : ℕ → ℝ) :
    Filter.Tendsto (fun n i ↦ coordinateSpikeL2 a n i) Filter.atTop (nhds 0) := by
  -- At each fixed coordinate, all sufficiently late spikes vanish there.
  rw [tendsto_pi_nhds]
  intro i
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.eventually_gt_atTop i] with n hn
  exact (coordinateSpikeL2_apply_ne a (Nat.ne_of_lt hn)).symm

/-- Helper for Exercise 20.8: the coordinate function of a spike has finite support. -/
lemma coordinateSpikeL2_hasFiniteSupport (a : ℕ → ℝ) (n : ℕ) :
    (fun i ↦ coordinateSpikeL2 a n i).HasFiniteSupport := by
  -- Its support is contained in the singleton coordinate `{n}`.
  rw [Function.HasFiniteSupport]
  refine Set.finite_singleton n |>.subset fun i hi ↦ ?_
  simp only [Function.mem_support] at hi
  by_contra hin
  exact hi (coordinateSpikeL2_apply_ne a hin)

/-- Helper for Exercise 20.8: package a coordinate spike as an eventually-zero sequence. -/
@[expose]
def coordinateSpikeEventuallyZero (a : ℕ → ℝ) (n : ℕ) : eventuallyZeroRealSequences :=
  ⟨fun i ↦ coordinateSpikeL2 a n i,
    mem_eventuallyZeroRealSequences.mpr (coordinateSpikeL2_hasFiniteSupport a n)⟩

/-- Helper for Exercise 20.8: forgetting the spike packaging recovers its coordinate
function. -/
lemma coordinateSpikeEventuallyZero_val (a : ℕ → ℝ) (n : ℕ) :
    (coordinateSpikeEventuallyZero a n).1 = fun i ↦ coordinateSpikeL2 a n i := by
  -- The subtype constructor stores exactly this coordinate function.
  rfl

/-- Helper for Exercise 20.8: the eventually-zero inclusion recovers the canonical `ℓ²`
coordinate spike. -/
@[simp]
lemma eventuallyZeroToL2_coordinateSpike (a : ℕ → ℝ) (n : ℕ) :
    eventuallyZeroToL2 (coordinateSpikeEventuallyZero a n) = coordinateSpikeL2 a n := by
  -- Equality follows coordinatewise from the packaging definition.
  apply lp.ext
  rfl

/-- Helper for Exercise 20.8: convergence in an induced topology is convergence after
composition with the inducing map. -/
lemma tendsto_induced_iff {α β γ : Type*} [TopologicalSpace β]
    (f : α → β) (u : γ → α) (l : Filter γ) (x : α) :
    @Filter.Tendsto γ α u l (@nhds α (TopologicalSpace.induced f inferInstance) x) ↔
      Filter.Tendsto (f ∘ u) l (nhds (f x)) := by
  -- Rewrite the induced neighborhood filter and use the comap characterization.
  rw [nhds_induced, Filter.tendsto_comap_iff]

end
