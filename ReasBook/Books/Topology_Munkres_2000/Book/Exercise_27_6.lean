module

public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Instances.CantorSet
public import Mathlib.Topology.Perfect

public section

open scoped BigOperators
open Set

-- Mathlib's `preCantorSet n` and `cantorSet` are the sets `Aₙ` and `C` of the exercise.
#check preCantorSet
#check cantorSet

/-- Part (a) of Exercise 27.6: The Cantor set is totally disconnected. -/
theorem isTotallyDisconnected_cantorSet : IsTotallyDisconnected cantorSet := by
  -- Transport total disconnectedness from binary sequences through the canonical homeomorphism.
  rw [← totallyDisconnectedSpace_subtype_iff]
  exact cantorSetHomeomorphNatToBool.symm.totallyDisconnectedSpace

/-- The Cantor set, regarded as a subspace of `ℝ`, is a totally disconnected space. -/
instance CantorSet.instTotallyDisconnectedSpace : TotallyDisconnectedSpace cantorSet := by
  -- The set-level result is exactly the subtype-space instance criterion.
  exact totallyDisconnectedSpace_subtype_iff.mpr isTotallyDisconnected_cantorSet

-- Exercise 27.6, part (b): The Cantor set is compact.
#check isCompact_cantorSet

namespace CantorInterval

/-- The left endpoint determined by a finite binary word in the stage-`n` Cantor construction. -/
noncomputable def left {n : ℕ} (w : Fin n → Bool) : ℝ :=
  ∑ i, if w i then 2 / 3 ^ (i.val + 1) else 0

/-- The right endpoint determined by a finite binary word in the stage-`n` Cantor construction. -/
noncomputable def right {n : ℕ} (w : Fin n → Bool) : ℝ :=
  left w + 1 / 3 ^ n

/-- The closed component interval determined by a finite binary word. -/
noncomputable def interval {n : ℕ} (w : Fin n → Bool) : Set ℝ :=
  Set.Icc (left w) (right w)

/-- Helper for Exercise 27.6: prepending a binary digit applies the corresponding affine map
to the left endpoint. -/
lemma left_cons {n : ℕ} (b : Bool) (w : Fin n → Bool) :
    left (Fin.cons b w) = if b then (2 + left w) / 3 else left w / 3 := by
  -- Split off the leading digit and factor the remaining ternary weights by `1 / 3`.
  cases b
  · rw [left, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, zero_add, pow_one,
      Bool.false_eq_true, if_false]
    unfold left
    rw [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    cases hwi : w i
    · simp only [Bool.false_eq_true, if_false, zero_mul]
    · simp only [if_pos, Fin.val_succ, pow_succ]
      ring
  · rw [left, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, zero_add, pow_one, if_pos]
    unfold left
    simp only [div_eq_mul_inv, add_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    cases hwi : w i
    · simp only [Bool.false_eq_true, if_false, zero_mul]
    · simp only [if_pos, Fin.val_succ, pow_succ]
      ring

/-- Helper for Exercise 27.6: prepending a binary digit applies the corresponding affine map
to the right endpoint. -/
lemma right_cons {n : ℕ} (b : Bool) (w : Fin n → Bool) :
    right (Fin.cons b w) = if b then (2 + right w) / 3 else right w / 3 := by
  -- Combine the left-endpoint recursion with the successor-stage length identity.
  cases b
  · rw [right, left_cons, right]
    simp only [Bool.false_eq_true, if_false]
    ring
  · rw [right, left_cons, right]
    simp only [if_pos]
    ring

/-- Helper for Exercise 27.6: prepending a digit identifies the new component interval with
the appropriate affine image of the preceding interval. -/
lemma interval_cons {n : ℕ} (b : Bool) (w : Fin n → Bool) :
    interval (Fin.cons b w) =
      if b then (fun x : ℝ ↦ (2 + x) / 3) '' interval w else (fun x : ℝ ↦ x / 3) '' interval w := by
  -- Rewrite both endpoints, then use the standard image formula for a positive affine map.
  cases b
  · ext x
    simp only [interval, left_cons, right_cons, Bool.false_eq_true, if_false, Set.mem_Icc,
      Set.mem_image]
    constructor
    · intro hx
      refine ⟨3 * x, ?_, ?_⟩
      · constructor <;> linarith
      · ring
    · rintro ⟨y, hy, rfl⟩
      constructor <;> linarith
  · ext x
    simp only [interval, left_cons, right_cons, if_pos, Set.mem_Icc,
      Set.mem_image]
    constructor
    · intro hx
      refine ⟨3 * x - 2, ?_, ?_⟩
      · constructor <;> linarith
      · ring
    · rintro ⟨y, hy, rfl⟩
      constructor <;> linarith

/-- Part (c)(1) of Exercise 27.6: The stage-`n` pre-Cantor set is the finite union of its
binary-word-indexed closed component intervals. -/
theorem iUnion_eq (n : ℕ) :
    preCantorSet n = ⋃ w : Fin n → Bool, interval w := by
  -- Induct on stages, reindexing each successor component by its leading binary digit.
  induction n with
  | zero =>
      ext x
      simp [interval, left, right]
  | succ n ih =>
      rw [preCantorSet_succ, ih]
      ext x
      simp only [Set.mem_union, Set.mem_image, Set.mem_iUnion]
      constructor
      · rintro (⟨y, ⟨w, hw⟩, rfl⟩ | ⟨y, ⟨w, hw⟩, rfl⟩)
        · refine ⟨Fin.cons false w, ?_⟩
          rw [interval_cons]
          exact ⟨y, hw, rfl⟩
        · refine ⟨Fin.cons true w, ?_⟩
          rw [interval_cons]
          exact ⟨y, hw, rfl⟩
      · rintro ⟨w, hw⟩
        rw [← Fin.cons_self_tail w, interval_cons] at hw
        cases hbit : w 0
        · left
          simp only [hbit, Bool.false_eq_true, if_false] at hw
          rcases hw with ⟨y, hy, hyx⟩
          exact ⟨y, ⟨Fin.tail w, hy⟩, hyx⟩
        · right
          simp only [hbit, if_pos] at hw
          rcases hw with ⟨y, hy, hyx⟩
          exact ⟨y, ⟨Fin.tail w, hy⟩, hyx⟩

/-- Helper for Exercise 27.6: every finite-stage component interval is contained in
the unit interval. -/
lemma interval_subset_unitInterval {n : ℕ} (w : Fin n → Bool) :
    interval w ⊆ Set.Icc (0 : ℝ) 1 := by
  -- Route correction: use a direct stage-bound bridge instead of repeatedly unpacking images.
  -- Insert the component into its finite-stage union, then use the global stage bound.
  intro x hx
  apply preCantorSet_subset_unitInterval
  rw [iUnion_eq]
  exact Set.mem_iUnion.mpr ⟨w, hx⟩

/-- Helper for Exercise 27.6: the left and right affine branches of any two
finite-stage components are disjoint. -/
lemma disjoint_leftBranch_rightBranch {n : ℕ} (w v : Fin n → Bool) :
    Disjoint ((fun x : ℝ ↦ x / 3) '' interval w)
      ((fun x : ℝ ↦ (2 + x) / 3) '' interval v) := by
  -- Source points lie in `[0,1]`, so equality of their branch images is impossible.
  refine Set.disjoint_image_image ?_
  intro x hx y hy heq
  have hxUnit := interval_subset_unitInterval w hx
  have hyUnit := interval_subset_unitInterval v hy
  simp only [Set.mem_Icc] at hxUnit hyUnit
  linarith

/-- Exercise 27.6, part (c)(2): The closed component intervals at each stage are
pairwise disjoint. -/
theorem pairwiseDisjoint (n : ℕ) :
    Set.univ.PairwiseDisjoint (fun w : Fin n → Bool ↦ interval w) := by
  -- The empty word is unique; successor words are separated by their leading bit.
  induction n with
  | zero =>
      intro w hw v hv hne
      exact (hne (Subsingleton.elim w v)).elim
  | succ n ih =>
      -- Normalize successor components by their leading bits and compare the four branches.
      intro w hw v hv hne
      change Disjoint (interval w) (interval v)
      rw [← Fin.cons_self_tail w, ← Fin.cons_self_tail v, interval_cons, interval_cons]
      cases hw0 : w 0 <;> cases hv0 : v 0
      · simp only [Bool.false_eq_true, if_false]
        have htail : Fin.tail w ≠ Fin.tail v := by
          -- Equal tails and equal leading bits would reconstruct the original words.
          intro htailEq
          apply hne
          rw [← Fin.cons_self_tail w, ← Fin.cons_self_tail v, hw0, hv0, htailEq]
        refine Set.disjoint_image_of_injective ?_
          (ih (show Fin.tail w ∈ Set.univ from Set.mem_univ _)
            (show Fin.tail v ∈ Set.univ from Set.mem_univ _) htail)
        intro x y hxy
        linarith
      · simp only [Bool.false_eq_true, if_false, if_pos]
        exact disjoint_leftBranch_rightBranch (Fin.tail w) (Fin.tail v)
      · simp only [if_pos, Bool.false_eq_true, if_false]
        exact (disjoint_leftBranch_rightBranch (Fin.tail v) (Fin.tail w)).symm
      · simp only [if_pos]
        have htail : Fin.tail w ≠ Fin.tail v := by
          -- Equal tails and equal leading bits would reconstruct the original words.
          intro htailEq
          apply hne
          rw [← Fin.cons_self_tail w, ← Fin.cons_self_tail v, hw0, hv0, htailEq]
        refine Set.disjoint_image_of_injective ?_
          (ih (show Fin.tail w ∈ Set.univ from Set.mem_univ _)
            (show Fin.tail v ∈ Set.univ from Set.mem_univ _) htail)
        intro x y hxy
        linarith

/-- Part (c)(3) of Exercise 27.6: Every stage-`n` component interval has length `1 / 3 ^ n`. -/
theorem length {n : ℕ} (w : Fin n → Bool) :
    right w - left w = 1 / 3 ^ n := by
  -- The right endpoint was defined by adding exactly the stage length.
  rw [right]
  ring

/-- Helper for Exercise 27.6: every point of a finite-stage component is within the
component length of each endpoint. -/
lemma endpoint_dist_le_length {n : ℕ} (w : Fin n → Bool) {x : ℝ} (hx : x ∈ interval w) :
    dist x (left w) ≤ 1 / 3 ^ n ∧ dist x (right w) ≤ 1 / 3 ^ n := by
  -- Convert interval membership into endpoint inequalities and normalize both distances.
  have hxBounds : left w ≤ x ∧ x ≤ right w := hx
  have hlength := length w
  constructor
  · rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxBounds.1)]
    linarith
  · rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxBounds.2)]
    linarith

/-- Part (c)(4) of Exercise 27.6: Every left endpoint of a component interval lies in
the Cantor set. -/
theorem left_mem {n : ℕ} (w : Fin n → Bool) : left w ∈ cantorSet := by
  -- Induct on the word length, following the left or right self-similar branch.
  induction n with
  | zero =>
      simpa [left] using zero_mem_cantorSet
  | succ n ih =>
      rw [← Fin.cons_self_tail w, left_cons, cantorSet_eq_union_halves]
      cases hbit : w 0
      · simp only [Bool.false_eq_true, if_false]
        exact Or.inl ⟨left (Fin.tail w), ih (Fin.tail w), rfl⟩
      · simp only [if_pos]
        exact Or.inr ⟨left (Fin.tail w), ih (Fin.tail w), rfl⟩

/-- Part (c)(5) of Exercise 27.6: Every right endpoint of a component interval lies in
the Cantor set. -/
theorem right_mem {n : ℕ} (w : Fin n → Bool) : right w ∈ cantorSet := by
  -- The base endpoint is `1`; the successor step follows the same affine recursion.
  have one_mem : (1 : ℝ) ∈ cantorSet := by
    have hdigits : (fun _ : ℕ ↦ (2 : Fin 3)) = fun _ ↦ Fin.last 2 := by
      funext i
      apply Fin.ext
      simp
    have hvalue : Real.ofDigits (fun _ ↦ (2 : Fin 3)) = 1 := by
      rw [hdigits]
      exact Real.ofDigits_const_last_eq_one 2
    rw [← hvalue]
    simpa only [Bool.cond_true] using
      (ofDigits_bool_to_fin_three_mem_cantorSet (fun _ ↦ true))
  induction n with
  | zero =>
      simpa [right, left] using one_mem
  | succ n ih =>
      rw [← Fin.cons_self_tail w, right_cons, cantorSet_eq_union_halves]
      cases hbit : w 0
      · simp only [Bool.false_eq_true, if_false]
        exact Or.inl ⟨right (Fin.tail w), ih (Fin.tail w), rfl⟩
      · simp only [if_pos]
        exact Or.inr ⟨right (Fin.tail w), ih (Fin.tail w), rfl⟩

end CantorInterval

/-- Exercise 27.6: Every point of the Cantor set is an accumulation point
of the Cantor set. -/
theorem preperfect_cantorSet : Preperfect cantorSet := by
  -- Put a metric ball inside the neighborhood, then choose an endpoint of a sufficiently
  -- short component interval containing the given Cantor point.
  rw [preperfect_iff_nhds]
  intro x hx U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  -- Choose a stage whose component length is smaller than the neighborhood radius.
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 3 : ℝ) < 1)
  have hlengthLt : 1 / (3 : ℝ) ^ n < ε := by
    simpa only [one_div_pow] using hn
  have hxStage : x ∈ preCantorSet n := Set.mem_iInter.mp hx n
  rw [CantorInterval.iUnion_eq] at hxStage
  obtain ⟨w, hxInterval⟩ := Set.mem_iUnion.mp hxStage
  have hdist := CantorInterval.endpoint_dist_le_length w hxInterval
  by_cases hleft : CantorInterval.left w = x
  · -- If `x` is the left endpoint, the positive-length right endpoint is nearby and distinct.
    have hcomponentPositive : 0 < 1 / (3 : ℝ) ^ n := by positivity
    have hright : CantorInterval.right w ≠ x := by
      intro hrightEq
      have hlength := CantorInterval.length w
      rw [hleft, hrightEq] at hlength
      linarith
    refine ⟨CantorInterval.right w, ?_, hright⟩
    constructor
    · apply hball
      exact Metric.mem_ball'.mpr (lt_of_le_of_lt hdist.2 hlengthLt)
    · exact CantorInterval.right_mem w
  · -- Otherwise the left endpoint itself supplies the required nearby Cantor point.
    refine ⟨CantorInterval.left w, ?_, hleft⟩
    constructor
    · apply hball
      exact Metric.mem_ball'.mpr (lt_of_le_of_lt hdist.1 hlengthLt)
    · exact CantorInterval.left_mem w

/-- Helper for Exercise 27.6: the space of infinite binary sequences is uncountable. -/
lemma uncountable_natToBool : Uncountable (ℕ → Bool) := by
  -- A proposed enumeration misses the sequence obtained by flipping its diagonal.
  rw [uncountable_iff_forall_not_surjective]
  intro f hf
  let diagonal : ℕ → Bool := fun n ↦ !(f n n)
  obtain ⟨n, hn⟩ := hf diagonal
  have h := congrFun hn n
  simp [diagonal] at h

/-- Part (e) of Exercise 27.6: The Cantor set is uncountable. -/
instance CantorSet.instUncountable : Uncountable cantorSet := by
  -- Transfer uncountability along the canonical binary-expansion equivalence.
  letI : Uncountable (ℕ → Bool) := uncountable_natToBool
  exact Uncountable.of_equiv (ℕ → Bool) cantorSetEquivNatToBool.symm
