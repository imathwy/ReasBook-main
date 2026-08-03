module

public import Topology_Munkres_2000.Book.Example_39_1.IntegerIntervals
public import Topology_Munkres_2000.Book.Example_39_1.ReciprocalIntervals
public import Topology_Munkres_2000.Book.Definition_6_0_1.LocallyFinite
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Order.AtTopBotIxx

public section

open Filter Set Topology

/-- Helper for Example 39.1: The integer-indexed family of length-two open intervals is locally
finite. -/
lemma locallyFinite_integerShiftedInterval :
    _root_.LocallyFinite integerShiftedInterval := by
  -- The two endpoint functions diverge in the directions required for open intervals.
  have hleft : Tendsto (fun n : ℤ ↦ (n : ℝ)) atTop atTop :=
    tendsto_intCast_atTop_atTop
  have hrightCast : Tendsto (fun n : ℤ ↦ (n : ℝ)) atBot atBot := by
    exact tendsto_intCast_atBot_iff.mpr tendsto_id
  have hright : Tendsto (fun n : ℤ ↦ (n : ℝ) + 2) atBot atBot :=
    tendsto_atBot_add_const_right atBot 2 hrightCast
  have hintervals : _root_.LocallyFinite (fun n : ℤ ↦ Set.Ioo (n : ℝ) ((n : ℝ) + 2)) :=
    locallyFinite_Ioo_of_tendsto hleft hright
  intro x
  obtain ⟨U, hU, hfinite⟩ := hintervals x
  refine ⟨U, hU, ?_⟩
  have hindices :
      {i : ℤ | (Set.Ioo (i : ℝ) ((i : ℝ) + 2) ∩ U).Nonempty} =
        {i : ℤ | (integerShiftedInterval i ∩ U).Nonempty} := by
    ext i
    constructor
    · rintro ⟨z, hz, hzU⟩
      exact ⟨z, mem_integerShiftedInterval.mpr hz, hzU⟩
    · rintro ⟨z, hz, hzU⟩
      exact ⟨z, mem_integerShiftedInterval.mp hz, hzU⟩
  rw [← hindices]
  exact hfinite

/-- Helper for Example 39.1: Only finitely many positive integers have reciprocal larger than a
fixed positive real number. -/
lemma finite_pnat_reciprocal_gt {a : ℝ} (ha : 0 < a) :
    Set.Finite {n : ℕ+ | a < 1 / (n : ℝ)} := by
  -- Choose a reciprocal threshold and pull back a finite initial segment of `ℕ`.
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt ha
  have hfinite : Set.Finite ((Subtype.val : ℕ+ → ℕ) ⁻¹' Set.Iio (N + 1)) :=
    (Set.finite_Iio (N + 1)).preimage Subtype.val_injective.injOn
  apply hfinite.subset
  intro n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast n.property
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hbound : (n : ℝ) < (N : ℝ) + 1 :=
    lt_of_one_div_lt_one_div hNpos (hN.trans hn)
  exact_mod_cast hbound

/-- Helper for Example 39.1: The reciprocal-initial intervals form a locally finite indexed
family in the subspace `(0, 1)`. -/
lemma locallyFinite_reciprocalInitialInterval_unit :
    _root_.LocallyFinite (fun n : ℕ+ ↦
      (Subtype.val : Set.Ioo (0 : ℝ) 1 → ℝ) ⁻¹' reciprocalInitialInterval n) := by
  -- Near a positive point, only intervals whose reciprocal endpoint exceeds half that point meet.
  intro x
  let U : Set (Set.Ioo (0 : ℝ) 1) :=
    (Subtype.val : Set.Ioo (0 : ℝ) 1 → ℝ) ⁻¹' Set.Ioi ((x : ℝ) / 2)
  have hxhalf : (x : ℝ) / 2 < x := by
    linarith [x.property.1]
  have hU : U ∈ 𝓝 x := by
    exact continuous_subtype_val.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hxhalf)
  refine ⟨U, hU, (finite_pnat_reciprocal_gt (half_pos x.property.1)).subset ?_⟩
  intro n hn
  obtain ⟨y, hyInterval, hyU⟩ := hn
  have hyBounds : 0 < (y : ℝ) ∧ (y : ℝ) < 1 / (n : ℝ) := by
    simpa only [Set.mem_preimage, mem_reciprocalInitialInterval] using hyInterval
  exact hyU.trans hyBounds.2

/-- Helper for Example 39.1: A positive open interval with left endpoint zero determines its right
endpoint. -/
lemma Ioo_zero_right_injective {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : Set.Ioo 0 a = Set.Ioo 0 b) : a = b := by
  -- If the endpoints differed, their midpoint would belong to exactly one interval.
  rcases lt_trichotomy a b with hlt | heq | hgt
  · have hmid : (a + b) / 2 ∈ Set.Ioo 0 b := by
      constructor <;> linarith
    rw [← hab, Set.mem_Ioo] at hmid
    linarith
  · exact heq
  · have hmid : (a + b) / 2 ∈ Set.Ioo 0 a := by
      constructor <;> linarith
    rw [hab, Set.mem_Ioo] at hmid
    linarith

/-- Helper for Example 39.1: Distinct positive integers determine distinct reciprocal-initial
intervals. -/
lemma reciprocalInitialInterval_injective :
    Function.Injective reciprocalInitialInterval := by
  -- Equality of intervals gives equality of their positive reciprocal endpoints.
  intro m n hmn
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast m.property
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast n.property
  have hsets : Set.Ioo 0 (1 / (m : ℝ)) = Set.Ioo 0 (1 / (n : ℝ)) := by
    ext x
    calc
      x ∈ Set.Ioo 0 (1 / (m : ℝ)) ↔ x ∈ reciprocalInitialInterval m :=
        mem_reciprocalInitialInterval.symm
      _ ↔ x ∈ reciprocalInitialInterval n := by rw [hmn]
      _ ↔ x ∈ Set.Ioo 0 (1 / (n : ℝ)) := mem_reciprocalInitialInterval
  have hrecip : 1 / (m : ℝ) = 1 / (n : ℝ) :=
    Ioo_zero_right_injective (one_div_pos.mpr hmpos) (one_div_pos.mpr hnpos) hsets
  have hcast : (m : ℝ) = (n : ℝ) := by
    rw [one_div, one_div] at hrecip
    exact inv_injective hrecip
  exact_mod_cast hcast

/-- Helper for Example 39.1: Distinct positive integers determine distinct reciprocal-adjacent
intervals. -/
lemma reciprocalAdjacentInterval_injective :
    Function.Injective reciprocalAdjacentInterval := by
  -- Ordered distinct indices force every point of one interval to lie beyond the other interval.
  intro m n hmn
  by_contra hne
  rcases lt_or_gt_of_ne hne with hmnIndex | hnmIndex
  · have hmpos : (0 : ℝ) < (m : ℝ) := by
      exact_mod_cast m.property
    have hmnCast : (m : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast hmnIndex
    have hrecipLe : 1 / (n : ℝ) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hmnCast
    have hmid : (1 / ((m : ℝ) + 1) + 1 / (m : ℝ)) / 2 ∈
        reciprocalAdjacentInterval m := by
      rw [mem_reciprocalAdjacentInterval]
      have hstrict := one_div_lt_one_div_of_lt hmpos (by linarith : (m : ℝ) < (m : ℝ) + 1)
      constructor <;> linarith
    have hmidLower := (mem_reciprocalAdjacentInterval.mp hmid).1
    rw [hmn, mem_reciprocalAdjacentInterval] at hmid
    linarith
  · have hnpos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast n.property
    have hnmCast : (n : ℝ) + 1 ≤ (m : ℝ) := by
      exact_mod_cast hnmIndex
    have hrecipLe : 1 / (m : ℝ) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hnmCast
    have hmid : (1 / ((n : ℝ) + 1) + 1 / (n : ℝ)) / 2 ∈
        reciprocalAdjacentInterval n := by
      rw [mem_reciprocalAdjacentInterval]
      have hstrict := one_div_lt_one_div_of_lt hnpos (by linarith : (n : ℝ) < (n : ℝ) + 1)
      constructor <;> linarith
    have hmidLower := (mem_reciprocalAdjacentInterval.mp hmid).1
    rw [← hmn, mem_reciprocalAdjacentInterval] at hmid
    linarith

/-- Helper for Example 39.1: A collection containing an injective sequence of sets with selected
points converging to `x` is not locally finite. -/
lemma not_locallyFinite_of_tendsto_mem {X : Type*} [TopologicalSpace X]
    {𝒜 : Set (Set X)} {f : ℕ → Set X} {y : ℕ → X} {x : X}
    (hf : Function.Injective f) (hy : Tendsto y atTop (𝓝 x))
    (hmem : ∀ n, y n ∈ f n) (hfamily : ∀ n, f n ∈ 𝒜) :
    ¬ 𝒜.LocallyFinite := by
  -- A locally finite neighborhood would meet infinitely many distinct members of the sequence.
  intro hlocal
  rw [Set.locallyFinite_iff] at hlocal
  obtain ⟨U, hU, hfinite⟩ := hlocal x
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hy.eventually hU)
  let g : Set.Ici N → Set X := fun n ↦ f n
  have hg : Function.Injective g := by
    intro m n hmn
    exact Subtype.ext (hf hmn)
  have hinfinite : (Set.range g).Infinite := Set.infinite_range_of_injective hg
  apply hinfinite
  apply hfinite.subset
  intro A hA
  obtain ⟨n, rfl⟩ := hA
  refine ⟨hfamily n, y n, hmem n, ?_⟩
  exact hN n n.property

/-- Example 39.1 (1): The collection of intervals `(n, n + 2)` for `n : ℤ` is
locally finite in `ℝ`. -/
theorem locallyFinite_integerShiftedIntervals :
    integerLengthTwoIntervals.LocallyFinite := by
  -- Transfer the finite set of relevant indices to the corresponding collection members.
  rw [Set.locallyFinite_iff]
  intro x
  obtain ⟨U, hU, hfinite⟩ := locallyFinite_integerShiftedInterval x
  refine ⟨U, hU, (hfinite.image integerShiftedInterval).subset ?_⟩
  intro A hA
  obtain ⟨n, hn⟩ := mem_integerLengthTwoIntervals.mp hA.1
  refine ⟨n, ?_, hn⟩
  change (integerShiftedInterval n ∩ U).Nonempty
  rw [hn]
  exact hA.2

/-- Example 39.1 (2): The collection of intervals `(0, 1 / n)` for `n : ℕ+` is
locally finite in the subspace `Set.Ioo (0 : ℝ) 1`. -/
theorem locallyFinite_reciprocalInitialIntervals_unit :
    reciprocalInitialIntervalsUnit.LocallyFinite := by
  -- Transfer the finite set of relevant indices to the corresponding subspace collection members.
  rw [Set.locallyFinite_iff]
  intro x
  obtain ⟨U, hU, hfinite⟩ := locallyFinite_reciprocalInitialInterval_unit x
  let F : ℕ+ → Set (Set.Ioo (0 : ℝ) 1) := fun n ↦
    (Subtype.val : Set.Ioo (0 : ℝ) 1 → ℝ) ⁻¹' reciprocalInitialInterval n
  refine ⟨U, hU, (hfinite.image F).subset ?_⟩
  intro A hA
  obtain ⟨n, hn⟩ := mem_reciprocalInitialIntervalsUnit.mp hA.1
  refine ⟨n, ?_, hn⟩
  change ((Subtype.val ⁻¹' reciprocalInitialInterval n) ∩ U).Nonempty
  rw [hn]
  exact hA.2

/-- Example 39.1 (3): The collection of intervals `(0, 1 / n)` for `n : ℕ+` is
not locally finite in `ℝ`. -/
theorem not_locallyFinite_reciprocalInitialIntervals_real :
    ¬ reciprocalInitialIntervals.LocallyFinite := by
  -- Reindex positive integers by successors and choose an interior half-reciprocal point.
  let f : ℕ → Set ℝ := fun n ↦ reciprocalInitialInterval n.succPNat
  let y : ℕ → ℝ := fun n ↦ (1 / 2 : ℝ) * (1 / ((n : ℝ) + 1))
  have hf : Function.Injective f :=
    reciprocalInitialInterval_injective.comp Nat.succPNat_injective
  have hy : Tendsto y atTop (𝓝 0) := by
    simpa only [y, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ))).const_mul (1 / 2)
  have hmem : ∀ n, y n ∈ f n := by
    intro n
    rw [mem_reciprocalInitialInterval]
    dsimp only [f, y]
    rw [Nat.succPNat_coe, Nat.cast_succ]
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    constructor
    · positivity
    · linarith
  have hfamily : ∀ n, f n ∈ reciprocalInitialIntervals := by
    intro n
    exact mem_reciprocalInitialIntervals.mpr ⟨n.succPNat, rfl⟩
  exact not_locallyFinite_of_tendsto_mem hf hy hmem hfamily

/-- Example 39.1 (4): The collection of intervals `(1 / (n + 1), 1 / n)` for
`n : ℕ+` is locally finite in the subspace `Set.Ioo (0 : ℝ) 1`. -/
theorem locallyFinite_reciprocalAdjacentIntervals_unit :
    reciprocalAdjacentIntervalsUnit.LocallyFinite := by
  -- Each adjacent interval is contained in the corresponding initial interval.
  have hindexed : _root_.LocallyFinite (fun n : ℕ+ ↦
      (Subtype.val : Set.Ioo (0 : ℝ) 1 → ℝ) ⁻¹' reciprocalAdjacentInterval n) :=
    locallyFinite_reciprocalInitialInterval_unit.subset fun n x hx ↦ by
      rw [Set.mem_preimage] at hx ⊢
      rw [mem_reciprocalAdjacentInterval] at hx
      rw [mem_reciprocalInitialInterval]
      constructor
      · exact (one_div_pos.mpr (by positivity)).trans hx.1
      · exact hx.2
  rw [Set.locallyFinite_iff]
  intro x
  obtain ⟨U, hU, hfinite⟩ := hindexed x
  let F : ℕ+ → Set (Set.Ioo (0 : ℝ) 1) := fun n ↦
    (Subtype.val : Set.Ioo (0 : ℝ) 1 → ℝ) ⁻¹' reciprocalAdjacentInterval n
  refine ⟨U, hU, (hfinite.image F).subset ?_⟩
  intro A hA
  obtain ⟨n, hn⟩ := mem_reciprocalAdjacentIntervalsUnit.mp hA.1
  refine ⟨n, ?_, hn⟩
  change ((Subtype.val ⁻¹' reciprocalAdjacentInterval n) ∩ U).Nonempty
  rw [hn]
  exact hA.2

/-- Example 39.1 (5): The collection of intervals `(1 / (n + 1), 1 / n)` for
`n : ℕ+` is not locally finite in `ℝ`. -/
theorem not_locallyFinite_reciprocalAdjacentIntervals_real :
    ¬ reciprocalAdjacentIntervals.LocallyFinite := by
  -- Reindex by successors and choose the midpoint between consecutive reciprocal endpoints.
  let f : ℕ → Set ℝ := fun n ↦ reciprocalAdjacentInterval n.succPNat
  let y : ℕ → ℝ := fun n ↦
    (1 / 2 : ℝ) * (1 / ((n : ℝ) + 2) + 1 / ((n : ℝ) + 1))
  have hf : Function.Injective f :=
    reciprocalAdjacentInterval_injective.comp Nat.succPNat_injective
  have hsecond : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hfirst : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
      (tendsto_add_atTop_iff_nat 1).mpr hsecond
  have hy : Tendsto y atTop (𝓝 0) := by
    simpa only [y, add_zero, mul_zero] using (hfirst.add hsecond).const_mul (1 / 2)
  have hmem : ∀ n, y n ∈ f n := by
    intro n
    rw [mem_reciprocalAdjacentInterval]
    dsimp only [f, y]
    rw [Nat.succPNat_coe, Nat.cast_succ]
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hstrict := one_div_lt_one_div_of_lt hpos (by linarith :
      (n : ℝ) + 1 < (n : ℝ) + 2)
    have hdenom : (n : ℝ) + 1 + 1 = (n : ℝ) + 2 := by ring
    rw [hdenom]
    constructor <;> linarith
  have hfamily : ∀ n, f n ∈ reciprocalAdjacentIntervals := by
    intro n
    exact mem_reciprocalAdjacentIntervals.mpr ⟨n.succPNat, rfl⟩
  exact not_locallyFinite_of_tendsto_mem hf hy hmem hfamily
