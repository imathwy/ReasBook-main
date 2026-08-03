module

public import Topology_Munkres_2000.Book.Example_26_2

public section

/-- The positive-integer-indexed family corresponding to the intervals `(1 / n, 1]`
inside the subspace `Set.Ioc (0 : ℝ) 1`. -/
def halfOpenUnitCover (n : ℕ+) : Set (Set.Ioc (0 : ℝ) 1) :=
  {x | 1 / (n : ℝ) < (x : ℝ)}

/-- Membership in `halfOpenUnitCover n` is the strict lower-bound condition
`1 / (n : ℝ) < (x : ℝ)`. -/
theorem mem_halfOpenUnitCover (n : ℕ+) (x : Set.Ioc (0 : ℝ) 1) :
    x ∈ halfOpenUnitCover n ↔ 1 / (n : ℝ) < (x : ℝ) := Iff.rfl

/-- Every member of `halfOpenUnitCover` is open in the subspace topology on
`Set.Ioc (0 : ℝ) 1`. -/
theorem isOpen_halfOpenUnitCover (n : ℕ+) : IsOpen (halfOpenUnitCover n) := by
  -- Express the cover member as the strict-order locus of two continuous maps.
  exact isOpen_lt continuous_const continuous_subtype_val

/-- The family `halfOpenUnitCover` covers the half-open unit interval. -/
theorem iUnion_halfOpenUnitCover :
    ⋃ n : ℕ+, halfOpenUnitCover n = Set.univ := by
  -- For each positive point, choose a reciprocal smaller than that point.
  rw [Set.iUnion_eq_univ_iff]
  intro x
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt x.property.1
  refine ⟨Nat.succPNat n, ?_⟩
  simpa [halfOpenUnitCover, Nat.succPNat_coe] using hn

/-- Helper for Example 26.4: a positive point bounded by every reciprocal in a
finite family of cover indices. -/
noncomputable def finiteCoverWitness (s : Finset ℕ+) : ℝ :=
  1 / (1 + ∑ n ∈ s, (n : ℝ))

/-- Helper for Example 26.4: `finiteCoverWitness s` belongs to the half-open unit
interval `(0, 1]`. -/
lemma finiteCoverWitness_mem_Ioc (s : Finset ℕ+) :
    finiteCoverWitness s ∈ Set.Ioc (0 : ℝ) 1 := by
  -- The denominator is positive and at least one because every summand is nonnegative.
  have hsum : 0 ≤ ∑ n ∈ s, (n : ℝ) := by
    exact Finset.sum_nonneg fun n hn ↦ by positivity
  have hdenom : 0 < 1 + ∑ n ∈ s, (n : ℝ) := by
    linarith
  constructor
  · unfold finiteCoverWitness
    exact one_div_pos.mpr hdenom
  · unfold finiteCoverWitness
    refine (one_div_le_one_div_of_le zero_lt_one ?_).trans_eq ?_
    · linarith
    · norm_num

/-- Helper for Example 26.4: `finiteCoverWitness s` is no larger than the
reciprocal attached to any index in `s`. -/
lemma finiteCoverWitness_le_reciprocal (s : Finset ℕ+) {n : ℕ+} (hn : n ∈ s) :
    finiteCoverWitness s ≤ 1 / (n : ℝ) := by
  -- The finite sum dominates each selected index, so its shifted reciprocal is smaller.
  have hn_sum : (n : ℝ) ≤ ∑ m ∈ s, (m : ℝ) := by
    exact Finset.single_le_sum
      (s := s) (f := fun m : ℕ+ ↦ (m : ℝ)) (fun m hm ↦ by positivity) hn
  unfold finiteCoverWitness
  refine one_div_le_one_div_of_le ?_ ?_
  · positivity
  · linarith

/-- No finite subfamily of `halfOpenUnitCover` covers the half-open unit interval. -/
theorem halfOpenUnitCover_noFiniteSubcover (s : Finset ℕ+) :
    ¬ (Set.univ : Set (Set.Ioc (0 : ℝ) 1)) ⊆ ⋃ n ∈ s, halfOpenUnitCover n := by
  -- Test the alleged finite cover on the witness lying below every selected endpoint.
  intro hcover
  let x : Set.Ioc (0 : ℝ) 1 := ⟨finiteCoverWitness s, finiteCoverWitness_mem_Ioc s⟩
  have hx : x ∈ ⋃ n ∈ s, halfOpenUnitCover n := hcover (Set.mem_univ x)
  rcases Set.mem_iUnion.mp hx with ⟨n, hx⟩
  rcases Set.mem_iUnion.mp hx with ⟨hn, hx⟩
  have hle : finiteCoverWitness s ≤ 1 / (n : ℝ) :=
    finiteCoverWitness_le_reciprocal s hn
  have hlt : 1 / (n : ℝ) < finiteCoverWitness s := by
    simpa [x] using (mem_halfOpenUnitCover n x).mp hx
  exact (not_lt_of_ge hle) hlt

/- Example 26.4 (1): The half-open unit interval `(0, 1]` is not compact. -/
#check (by simp : ¬ IsCompact (Set.Ioc (0 : ℝ) 1))

/- Example 26.4 (2): The open unit interval `(0, 1)` is not compact. -/
#check (by simp : ¬ IsCompact (Set.Ioo (0 : ℝ) 1))

/- Example 26.4 (3): The closed unit interval `[0, 1]` is compact. -/
#check (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1))
