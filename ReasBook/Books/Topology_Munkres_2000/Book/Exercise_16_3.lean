module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.Instances.Nat

open Set
open scoped Set.Notation

public section

/-- The set `A` from the exercise: points whose absolute value lies strictly between
`1 / 2` and `1`. -/
def strictAbsBand : Set ℝ :=
  abs ⁻¹' Ioo (1 / 2) 1

/-- The set `B` from the exercise: points whose absolute value is greater than `1 / 2`
and at most `1`. -/
def outerClosedAbsBand : Set ℝ :=
  abs ⁻¹' Ioc (1 / 2) 1

/-- The set `C` from the exercise: points whose absolute value is at least `1 / 2` and
less than `1`. -/
def innerClosedAbsBand : Set ℝ :=
  abs ⁻¹' Ico (1 / 2) 1

/-- The set `D` from the exercise: points whose absolute value lies between `1 / 2` and
`1`, inclusively. -/
def closedAbsBand : Set ℝ :=
  abs ⁻¹' Icc (1 / 2) 1

/-- The set `E` from the exercise: the punctured open unit interval with points whose
reciprocal is a positive integer removed. -/
def reciprocalAvoidingPuncturedInterval : Set ℝ :=
  {x | 0 < |x| ∧ |x| < 1 ∧ ¬ ∃ n : ℕ, 0 < n ∧ (1 / x : ℝ) = n}

/-- Helper for Exercise 16.3: inside `[-1, 1]`, the outer absolute-value bound in
`outerClosedAbsBand` is automatic. -/
lemma negOneOneIcc_preimage_outerClosedAbsBand :
    Icc (-1 : ℝ) 1 ↓∩ outerClosedAbsBand =
      Icc (-1 : ℝ) 1 ↓∩ (abs ⁻¹' Ioi (1 / 2)) := by
  -- Reduce the equality to the automatic estimate `|x| ≤ 1` for points of the subtype.
  ext x
  simp only [outerClosedAbsBand, mem_preimage, mem_Ioc, mem_Ioi]
  constructor
  · exact fun hx ↦ hx.1
  · intro hx
    refine ⟨hx, ?_⟩
    rw [abs_le]
    exact x.property

/-- Helper for Exercise 16.3: a subset of `ℝ` containing its greatest possible point
cannot be open. -/
lemma not_isOpen_of_mem_of_subset_Iic {s : Set ℝ} {b : ℝ} (hb : b ∈ s)
    (hsub : s ⊆ Iic b) : ¬ IsOpen s := by
  -- An open ball at `b` would contain a point strictly larger than `b`.
  intro hs
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hs b hb
  have hnear : b + ε / 2 ∈ Metric.ball b ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    simp only [add_sub_cancel_left, abs_of_pos (half_pos hε)]
    linarith
  have hupper := hsub (hball hnear)
  exact (not_le_of_gt (by linarith : b < b + ε / 2)) hupper

/-- Helper for Exercise 16.3: a point of the interval subspace with an omitted
left-hand interval is not an interior point. -/
lemma not_isOpen_negOneOneIcc_preimage_of_left_gap {s : Set ℝ} {a δ : ℝ}
    (haY : a ∈ Icc (-1 : ℝ) 1) (ha : a ∈ s) (haLower : -1 < a) (hδ : 0 < δ)
    (hgap : Ioo (a - δ) a ⊆ sᶜ) : ¬ IsOpen (Icc (-1 : ℝ) 1 ↓∩ s) := by
  -- Choose a displacement small enough for the open ball, the omitted gap, and the subspace.
  intro hs
  let x : Icc (-1 : ℝ) 1 := ⟨a, haY⟩
  have hx : x ∈ Icc (-1 : ℝ) 1 ↓∩ s := ha
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hs x hx
  let d := min (ε / 2) (min (δ / 2) ((a + 1) / 2))
  have hd : 0 < d := by
    dsimp [d]
    rw [lt_min_iff, lt_min_iff]
    constructor
    · exact half_pos hε
    constructor
    · exact half_pos hδ
    · linarith
  have hdε : d < ε := by
    have hdle : d ≤ ε / 2 := min_le_left _ _
    linarith
  have hdδ : d < δ := by
    have hdle : d ≤ δ / 2 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hda : d < a + 1 := by
    have hdle : d ≤ (a + 1) / 2 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hay : a - d ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · linarith
    · linarith [haY.2]
  let y : Icc (-1 : ℝ) 1 := ⟨a - d, hay⟩
  have hyNear : y ∈ Metric.ball x ε := by
    rw [Metric.mem_ball]
    change dist (a - d) a < ε
    rw [Real.dist_eq]
    have hsub : a - d - a = -d := by ring
    rw [hsub, abs_neg, abs_of_pos hd]
    exact hdε
  have hyGap : (y : ℝ) ∈ Ioo (a - δ) a := by
    change a - d ∈ Ioo (a - δ) a
    constructor
    · linarith
    · linarith
  have hyNot : (y : ℝ) ∉ s := hgap hyGap
  exact hyNot (hball hyNear)

/-- Helper for Exercise 16.3: the positive natural numbers embedded in `ℝ` are the
nonnegative integer lattice points at least `1`. -/
lemma positiveNatReals_eq_range_natCast_inter_Ici :
    {y : ℝ | ∃ n : ℕ, 0 < n ∧ y = n} = Set.range ((↑) : ℕ → ℝ) ∩ Ici 1 := by
  -- The lower bound `1 ≤ n` is exactly positivity for a natural number.
  ext y
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨⟨n, rfl⟩, ?_⟩
    change (1 : ℝ) ≤ n
    exact_mod_cast hn
  · rintro ⟨⟨n, rfl⟩, hn⟩
    refine ⟨n, ?_, rfl⟩
    change (1 : ℝ) ≤ n at hn
    exact_mod_cast hn

/-- Helper for Exercise 16.3: the positive natural numbers form a closed subset of
`ℝ`. -/
lemma isClosed_positiveNatReals : IsClosed {y : ℝ | ∃ n : ℕ, 0 < n ∧ y = n} := by
  -- Use the closed embedding of `ℕ` in `ℝ` and impose the closed lower bound.
  rw [positiveNatReals_eq_range_natCast_inter_Ici]
  exact (Nat.isClosedEmbedding_coe_real).isClosed_range.inter isClosed_Ici

/-- Helper for Exercise 16.3: the reciprocal-avoiding set is the punctured interval
intersected with the inverse image of the complement of the positive natural lattice. -/
lemma reciprocalAvoidingPuncturedInterval_eq :
    reciprocalAvoidingPuncturedInterval =
      Ioo (-1 : ℝ) 1 ∩
        ({0}ᶜ ∩ (fun x : ℝ ↦ x⁻¹) ⁻¹' {y : ℝ | ∃ n : ℕ, 0 < n ∧ y = n}ᶜ) := by
  -- Normalize the absolute-value conditions and rewrite division by `x` as inversion.
  ext x
  simp only [reciprocalAvoidingPuncturedInterval, mem_setOf_eq, mem_inter_iff, mem_Ioo,
    mem_compl_iff, mem_singleton_iff, mem_preimage, abs_pos, abs_lt, one_div]
  tauto

/-- The first classification in Exercise 16.3: `A` is open in the subspace `[-1, 1]`. -/
theorem isOpen_negOneOneIcc_strictAbsBand :
    IsOpen (Icc (-1 : ℝ) 1 ↓∩ strictAbsBand) := by
  -- Pull the open absolute-value band back to the interval subtype.
  exact (continuous_abs.isOpen_preimage _ isOpen_Ioo).preimage_val

/-- The second classification in Exercise 16.3: `A` is open in `ℝ`. -/
theorem isOpen_strictAbsBand : IsOpen strictAbsBand := by
  -- The set is directly the preimage of an open interval under `abs`.
  exact continuous_abs.isOpen_preimage _ isOpen_Ioo

/-- The third classification in Exercise 16.3: `B` is open in the subspace `[-1, 1]`. -/
theorem isOpen_negOneOneIcc_outerClosedAbsBand :
    IsOpen (Icc (-1 : ℝ) 1 ↓∩ outerClosedAbsBand) := by
  -- Replace the redundant closed outer bound by the open lower ray.
  rw [negOneOneIcc_preimage_outerClosedAbsBand]
  exact (continuous_abs.isOpen_preimage _ isOpen_Ioi).preimage_val

/-- The fourth classification in Exercise 16.3: `B` is not open in `ℝ`. -/
theorem not_isOpen_outerClosedAbsBand : ¬ IsOpen outerClosedAbsBand := by
  -- The set contains `1` but has no points greater than `1`.
  refine not_isOpen_of_mem_of_subset_Iic (b := 1) ?_ ?_
  · simp only [outerClosedAbsBand, mem_preimage, mem_Ioc, abs_one]
    norm_num
  · intro x hx
    simp only [outerClosedAbsBand, mem_preimage, mem_Ioc] at hx
    exact (le_abs_self x).trans hx.2

/-- The fifth classification in Exercise 16.3: `C` is not open in the subspace `[-1, 1]`. -/
theorem not_isOpen_negOneOneIcc_innerClosedAbsBand :
    ¬ IsOpen (Icc (-1 : ℝ) 1 ↓∩ innerClosedAbsBand) := by
  -- The included point `1 / 2` is approached from the left by omitted positive points.
  refine not_isOpen_negOneOneIcc_preimage_of_left_gap (a := 1 / 2) (δ := 1 / 2) ?_ ?_ ?_ ?_ ?_
  · norm_num
  · simp only [innerClosedAbsBand, mem_preimage, mem_Ico]
    norm_num
  · norm_num
  · norm_num
  · intro x hx
    simp only [mem_compl_iff, innerClosedAbsBand, mem_preimage, mem_Ico]
    intro hmem
    have hxpos : 0 < x := by
      norm_num at hx ⊢
      exact hx.1
    rw [abs_of_pos hxpos] at hmem
    exact (not_le_of_gt hx.2) hmem.1

/-- The sixth classification in Exercise 16.3: `C` is not open in `ℝ`. -/
theorem not_isOpen_innerClosedAbsBand : ¬ IsOpen innerClosedAbsBand := by
  -- Ambient openness would pull back to openness in the interval subspace.
  intro hs
  exact not_isOpen_negOneOneIcc_innerClosedAbsBand hs.preimage_val

/-- The seventh classification in Exercise 16.3: `D` is not open in the subspace `[-1, 1]`. -/
theorem not_isOpen_negOneOneIcc_closedAbsBand :
    ¬ IsOpen (Icc (-1 : ℝ) 1 ↓∩ closedAbsBand) := by
  -- The same left-hand gap at `1 / 2` obstructs subspace openness.
  refine not_isOpen_negOneOneIcc_preimage_of_left_gap (a := 1 / 2) (δ := 1 / 2) ?_ ?_ ?_ ?_ ?_
  · norm_num
  · simp only [closedAbsBand, mem_preimage, mem_Icc]
    norm_num
  · norm_num
  · norm_num
  · intro x hx
    simp only [mem_compl_iff, closedAbsBand, mem_preimage, mem_Icc]
    intro hmem
    have hxpos : 0 < x := by
      norm_num at hx ⊢
      exact hx.1
    rw [abs_of_pos hxpos] at hmem
    exact (not_le_of_gt hx.2) hmem.1

/-- The eighth classification in Exercise 16.3: `D` is not open in `ℝ`. -/
theorem not_isOpen_closedAbsBand : ¬ IsOpen closedAbsBand := by
  -- Ambient openness would again imply subspace openness.
  intro hs
  exact not_isOpen_negOneOneIcc_closedAbsBand hs.preimage_val

/-- The ninth classification in Exercise 16.3: `E` is open in the subspace `[-1, 1]`. -/
theorem isOpen_negOneOneIcc_reciprocalAvoidingPuncturedInterval :
    IsOpen (Icc (-1 : ℝ) 1 ↓∩ reciprocalAvoidingPuncturedInterval) := by
  -- Build the ambient open set from inversion on the punctured line, then pull it back.
  rw [reciprocalAvoidingPuncturedInterval_eq]
  have hAllowed : IsOpen {y : ℝ | ∃ n : ℕ, 0 < n ∧ y = n}ᶜ :=
    isClosed_positiveNatReals.isOpen_compl
  have hInv : IsOpen
      ({0}ᶜ ∩ (fun x : ℝ ↦ x⁻¹) ⁻¹' {y : ℝ | ∃ n : ℕ, 0 < n ∧ y = n}ᶜ) :=
    continuousOn_inv₀.isOpen_inter_preimage isClosed_singleton.isOpen_compl hAllowed
  exact (isOpen_Ioo.inter hInv).preimage_val

/-- The tenth classification in Exercise 16.3: `E` is open in `ℝ`. -/
theorem isOpen_reciprocalAvoidingPuncturedInterval :
    IsOpen reciprocalAvoidingPuncturedInterval := by
  -- The normalized set is an intersection of two ambient open sets.
  rw [reciprocalAvoidingPuncturedInterval_eq]
  have hAllowed : IsOpen {y : ℝ | ∃ n : ℕ, 0 < n ∧ y = n}ᶜ :=
    isClosed_positiveNatReals.isOpen_compl
  have hInv : IsOpen
      ({0}ᶜ ∩ (fun x : ℝ ↦ x⁻¹) ⁻¹' {y : ℝ | ∃ n : ℕ, 0 < n ∧ y = n}ᶜ) :=
    continuousOn_inv₀.isOpen_inter_preimage isClosed_singleton.isOpen_compl hAllowed
  exact isOpen_Ioo.inter hInv

/-- Exercise 16.3: among the five sets,
exactly `A` and `E` are open in `ℝ`, while `A`, `B`, and `E` are open in the subspace
`[-1, 1]`. -/
theorem exercise16_3_opennessClassification :
    IsOpen (Icc (-1 : ℝ) 1 ↓∩ strictAbsBand) ∧
      IsOpen strictAbsBand ∧
      IsOpen (Icc (-1 : ℝ) 1 ↓∩ outerClosedAbsBand) ∧
      ¬ IsOpen outerClosedAbsBand ∧
      ¬ IsOpen (Icc (-1 : ℝ) 1 ↓∩ innerClosedAbsBand) ∧
      ¬ IsOpen innerClosedAbsBand ∧
      ¬ IsOpen (Icc (-1 : ℝ) 1 ↓∩ closedAbsBand) ∧
      ¬ IsOpen closedAbsBand ∧
      IsOpen (Icc (-1 : ℝ) 1 ↓∩ reciprocalAvoidingPuncturedInterval) ∧
      IsOpen reciprocalAvoidingPuncturedInterval := by
  -- Assemble the ambient and subspace classifications proved above.
  exact ⟨isOpen_negOneOneIcc_strictAbsBand, isOpen_strictAbsBand,
    isOpen_negOneOneIcc_outerClosedAbsBand, not_isOpen_outerClosedAbsBand,
    not_isOpen_negOneOneIcc_innerClosedAbsBand, not_isOpen_innerClosedAbsBand,
    not_isOpen_negOneOneIcc_closedAbsBand, not_isOpen_closedAbsBand,
    isOpen_negOneOneIcc_reciprocalAvoidingPuncturedInterval,
    isOpen_reciprocalAvoidingPuncturedInterval⟩

/-- Compatibility alias for Exercise 16.3: among the five sets, exactly
`A` and `E` are open in `ℝ`, while `A`, `B`, and `E` are open in the subspace `[-1, 1]`. -/
theorem «Exercise 16.3 openness classification theorem family» :
    IsOpen (Icc (-1 : ℝ) 1 ↓∩ strictAbsBand) ∧
      IsOpen strictAbsBand ∧
      IsOpen (Icc (-1 : ℝ) 1 ↓∩ outerClosedAbsBand) ∧
      ¬ IsOpen outerClosedAbsBand ∧
      ¬ IsOpen (Icc (-1 : ℝ) 1 ↓∩ innerClosedAbsBand) ∧
      ¬ IsOpen innerClosedAbsBand ∧
      ¬ IsOpen (Icc (-1 : ℝ) 1 ↓∩ closedAbsBand) ∧
      ¬ IsOpen closedAbsBand ∧
      IsOpen (Icc (-1 : ℝ) 1 ↓∩ reciprocalAvoidingPuncturedInterval) ∧
      IsOpen reciprocalAvoidingPuncturedInterval := by
  -- Expose the established classification under the planner's quoted declaration name.
  exact exercise16_3_opennessClassification

end
