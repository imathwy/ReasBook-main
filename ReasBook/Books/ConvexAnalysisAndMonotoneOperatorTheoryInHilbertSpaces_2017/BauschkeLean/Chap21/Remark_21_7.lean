import BauschkeLean.Chap01.Text_1_0_47
import BauschkeLean.Chap21.Example_21_6

open Filter SetValuedOperator
open scoped InnerProductSpace Topology SetValuedOperator

universe u

namespace ERealFunction

noncomputable section

local notation "L2pos" => ℓ²(ℕ+, ℝ)
local notation "example21_6_subdifferential" => ∂ example_21_6_l2_counterexample_function

/-- The primal sequence `x_n = e_n / √n` used in Remark 21.7. -/
noncomputable def remark21_7_primalSeq : ℕ+ → L2pos :=
  fun n ↦
    ((1 / Real.sqrt (n : ℝ)) : ℝ) •
      (lp.single 2 n (1 : ℝ) : L2pos)

/-- The dual sequence `u_n = √n e_n` used in Remark 21.7. -/
noncomputable def remark21_7_dualSeq : ℕ+ → L2pos :=
  fun n ↦
    (Real.sqrt (n : ℝ) : ℝ) •
      (lp.single 2 n (1 : ℝ) : L2pos)

/-- The explicit graph point `(x_n, u_n)` from `(21.22)` in `L2pos × L2pos`. -/
noncomputable def remark21_7_graphPair (n : ℕ+) : L2pos × L2pos :=
  (remark21_7_primalSeq n, remark21_7_dualSeq n)

/-- The explicit graph point `(x_n, u_n)` from `(21.22)` viewed in the mixed
strong/weak product `L2pos × WeakSpace ℝ L2pos`. -/
noncomputable def remark21_7_mixedGraphPair (n : ℕ+) : L2pos × WeakSpace ℝ L2pos :=
  (remark21_7_primalSeq n, toWeakSpace ℝ L2pos (remark21_7_dualSeq n))

/-- The explicit pairing `⟪x_n, u_n⟫_ℝ` from `(21.22)`. -/
noncomputable def remark21_7_pairing (n : ℕ+) : ℝ :=
  inner ℝ (remark21_7_primalSeq n) (remark21_7_dualSeq n)

-- Semantic recall: `lean_leansearch` only surfaced ambient weak-topology lemmas, so this item
-- keeps the source-facing explicit `toWeakSpace` formulation already used in Example 21.6.

/-- Helper for Remark 21.7: the standard unit vectors of `ℓ²(ℕ+, ℝ)` are orthonormal. -/
private theorem remark21_7_basis_orthonormal :
    Orthonormal ℝ (fun n : ℕ+ ↦ (lp.single 2 n (1 : ℝ) : L2pos)) := by
  -- Reduce orthonormality to the coordinate formula for `lp.single`.
  rw [orthonormal_iff_ite]
  intro i j
  by_cases hij : i = j
  · subst hij
    simp
  · simp [lp.inner_single_left, hij]

/-- Helper for Remark 21.7: every shifted tail of the standard basis remains orthonormal. -/
private theorem remark21_7_shiftedBasis_orthonormal (N : ℕ) :
    Orthonormal ℝ (fun n : ℕ ↦ (lp.single 2 ⟨n + N + 2, by omega⟩ (1 : ℝ) : L2pos)) := by
  -- Compose the orthonormal basis with the injective shifted-index map.
  refine remark21_7_basis_orthonormal.comp (fun n : ℕ ↦ ⟨n + N + 2, by omega⟩) ?_
  intro m n hmn
  have hvals : m + N + 2 = n + N + 2 := congrArg Subtype.val hmn
  omega

/-- Helper for Remark 21.7: pairing with the `n`th basis vector on the left reads off the `n`th
coordinate. -/
private theorem remark21_7_inner_basis_left (x : L2pos) (n : ℕ+) :
    inner ℝ (lp.single 2 n (1 : ℝ) : L2pos) x = x n := by
  -- Expand the single-support vector and simplify the real inner product.
  calc
    inner ℝ (lp.single 2 n (1 : ℝ) : L2pos) x = ⟪(1 : ℝ), x n⟫_ℝ := by
      rw [lp.inner_single_left]
    _ = x n * 1 := by
      exact RCLike.inner_apply (1 : ℝ) (x n)
    _ = x n := by simp

/-- Helper for Remark 21.7: pairing with the `n`th basis vector on the right reads off the `n`th
coordinate. -/
private theorem remark21_7_inner_basis_right (x : L2pos) (n : ℕ+) :
    inner ℝ x (lp.single 2 n (1 : ℝ) : L2pos) = x n := by
  -- Expand the single-support vector on the right and simplify in `ℝ`.
  calc
    inner ℝ x (lp.single 2 n (1 : ℝ) : L2pos) = ⟪x n, (1 : ℝ)⟫_ℝ := by
      rw [lp.inner_single_right]
    _ = 1 * x n := by
      exact RCLike.inner_apply (x n) (1 : ℝ)
    _ = x n := by simp

/-- Helper for Remark 21.7: the primal sequence is supported on exactly one coordinate. -/
private theorem remark21_7_primalSeq_apply (n m : ℕ+) :
    remark21_7_primalSeq n m =
      if m = n then (1 / Real.sqrt (n : ℝ) : ℝ) else 0 := by
  -- Expand the scalar multiple of the single-support basis vector coordinatewise.
  by_cases hm : m = n
  · subst hm
    simp [remark21_7_primalSeq]
  · simp [remark21_7_primalSeq, hm]

/-- Helper for Remark 21.7: the dual sequence acts by the weighted coordinate
`x ↦ √n x_n`. -/
private theorem remark21_7_inner_dualSeq_right (x : L2pos) (n : ℕ+) :
    inner ℝ x (remark21_7_dualSeq n) = Real.sqrt (n : ℝ) * x n := by
  -- Expand the scalar multiple on the right and read off the chosen coordinate.
  rw [remark21_7_dualSeq, real_inner_smul_right, remark21_7_inner_basis_right]

/-- Helper for Remark 21.7: the explicit pairings are constantly equal to `1`. -/
private theorem remark21_7_pairing_eq_one (n : ℕ+) :
    remark21_7_pairing n = 1 := by
  -- The two weights cancel on the unique active coordinate.
  rw [remark21_7_pairing, remark21_7_inner_dualSeq_right, remark21_7_primalSeq_apply]
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := by positivity
  simp only [↓reduceIte, one_div]
  field_simp [hsqrt_pos.ne']

/-- Helper for Remark 21.7: the primal sequence has norm `1 / √n`. -/
private theorem remark21_7_norm_primalSeq (n : ℕ+) :
    ‖remark21_7_primalSeq n‖ = 1 / Real.sqrt (n : ℝ) := by
  -- Rewrite the sequence as a scaled single-support vector and evaluate its `ℓ²` norm.
  calc
    ‖remark21_7_primalSeq n‖ =
        ‖(1 / Real.sqrt (n : ℝ) : ℝ)‖ * ‖(lp.single 2 n (1 : ℝ) : L2pos)‖ := by
          rw [remark21_7_primalSeq, norm_smul]
    _ = |(1 / Real.sqrt (n : ℝ) : ℝ)| * ‖(lp.single 2 n (1 : ℝ) : L2pos)‖ := by
          rw [Real.norm_eq_abs]
    _ = |(1 / Real.sqrt (n : ℝ) : ℝ)| * ‖(1 : ℝ)‖ := by
          rw [lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
    _ = 1 / Real.sqrt (n : ℝ) := by
          have hnonneg : 0 ≤ (1 / Real.sqrt (n : ℝ) : ℝ) := by positivity
          rw [abs_of_nonneg hnonneg]
          simp

/-- Helper for Remark 21.7: the dual sequence has norm `√n`. -/
private theorem remark21_7_norm_dualSeq (n : ℕ+) :
    ‖remark21_7_dualSeq n‖ = Real.sqrt (n : ℝ) := by
  -- Rewrite the sequence as a scaled unit vector and evaluate its norm.
  calc
    ‖remark21_7_dualSeq n‖ =
        ‖(Real.sqrt (n : ℝ) : ℝ)‖ * ‖(lp.single 2 n (1 : ℝ) : L2pos)‖ := by
          rw [remark21_7_dualSeq, norm_smul]
    _ = |(Real.sqrt (n : ℝ) : ℝ)| * ‖(lp.single 2 n (1 : ℝ) : L2pos)‖ := by
          rw [Real.norm_eq_abs]
    _ = |(Real.sqrt (n : ℝ) : ℝ)| * ‖(1 : ℝ)‖ := by
          rw [lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
    _ = Real.sqrt (n : ℝ) := by
          have hnonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
          simp [hnonneg]

/-- Helper for Remark 21.7: the first affine branch is always bounded above by the full function
value. -/
private theorem remark21_7_firstBranch_le (x : L2pos) :
    (((1 + x (1 : ℕ+) : ℝ) : EReal)) ≤
      (example_21_6_l2_counterexample_function x : EReal) := by
  -- This is the left branch of the defining maximum.
  rw [example_21_6_l2_counterexample_function_apply]
  exact le_max_left _ _

/-- Helper for Remark 21.7: each active tail branch is bounded above by the full function value. -/
private theorem remark21_7_tailBranch_le (x : L2pos) (n : ℕ+) :
    (if 2 ≤ (n : ℕ) then (((Real.sqrt (n : ℝ)) * x n : ℝ) : EReal) else (⊥ : EReal)) ≤
      (example_21_6_l2_counterexample_function x : EReal) := by
  -- This is one branch of the tail supremum inside the defining maximum.
  rw [example_21_6_l2_counterexample_function_apply]
  exact le_trans
    (le_iSup (fun m : ℕ+ ↦
      if 2 ≤ (m : ℕ) then (((Real.sqrt (m : ℝ)) * x m : ℝ) : EReal) else (⊥ : EReal)) n)
    (le_max_right _ _)

/-- Helper for Remark 21.7: the first graph point has function value `2`. -/
private theorem remark21_7_apply_primalSeq_one :
    (example_21_6_l2_counterexample_function (remark21_7_primalSeq 1) : EReal) = 2 := by
  have hcoord_one : remark21_7_primalSeq 1 (1 : ℕ+) = 1 := by
    rw [remark21_7_primalSeq_apply]
    simp
  have hfirst : (((1 + remark21_7_primalSeq 1 (1 : ℕ+) : ℝ) : EReal)) = 2 := by
    rw [hcoord_one]
    norm_num
    rfl
  have htail_zero :
      (⨆ n : ℕ+,
        if 2 ≤ (n : ℕ) then
          (((Real.sqrt (n : ℝ)) * remark21_7_primalSeq 1 n : ℝ) : EReal)
        else (⊥ : EReal)) = 0 := by
    refine le_antisymm ?_ ?_
    · -- Every active tail coordinate vanishes because the primal vector is supported at `1`.
      refine iSup_le fun n ↦ ?_
      by_cases hn : 2 ≤ (n : ℕ)
      · have hne : n ≠ 1 := by
          intro h
          have hvals : (n : ℕ) = 1 := congrArg Subtype.val h
          omega
        have hcoord : remark21_7_primalSeq 1 n = 0 := by
          rw [remark21_7_primalSeq_apply]
          simp [hne]
        have hterm_le :
            ((((Real.sqrt (n : ℝ)) * remark21_7_primalSeq 1 n : ℝ) : EReal) : EReal) ≤ 0 := by
          rw [hcoord]
          simp
        simpa [hn] using hterm_le
      · simp [hn]
    · -- The active tail branch at `n = 2` already yields the lower bound `0`.
      have hcoord : remark21_7_primalSeq 1 (2 : ℕ+) = 0 := by
        rw [remark21_7_primalSeq_apply]
        simp
      have hterm :
          (((Real.sqrt ((2 : ℕ+) : ℝ)) * remark21_7_primalSeq 1 (2 : ℕ+) : ℝ) : EReal) = 0 := by
        rw [hcoord]
        simp
      rw [← hterm]
      simpa [show 2 ≤ (((2 : ℕ+) : ℕ)) by norm_num] using
        (le_iSup
          (fun n : ℕ+ ↦
            if 2 ≤ (n : ℕ) then
              (((Real.sqrt (n : ℝ)) * remark21_7_primalSeq 1 n : ℝ) : EReal)
            else (⊥ : EReal))
          (2 : ℕ+))
  -- Both branches of the defining maximum are now explicit.
  change
    max (((1 + remark21_7_primalSeq 1 (1 : ℕ+) : ℝ) : EReal))
        (⨆ n : ℕ+,
          if 2 ≤ (n : ℕ) then
            (((Real.sqrt (n : ℝ)) * remark21_7_primalSeq 1 n : ℝ) : EReal)
          else (⊥ : EReal)) = 2
  rw [hfirst, htail_zero]
  norm_num

/-- Helper for Remark 21.7: every tail primal graph point has function value `1`. -/
private theorem remark21_7_apply_primalSeq_tail {n : ℕ+} (hn : 2 ≤ (n : ℕ)) :
    (example_21_6_l2_counterexample_function (remark21_7_primalSeq n) : EReal) = 1 := by
  have hfirst : (((1 + remark21_7_primalSeq n (1 : ℕ+) : ℝ) : EReal)) = 1 := by
    have hne : (1 : ℕ+) ≠ n := by
      intro h
      have hvals : (n : ℕ) = 1 := congrArg Subtype.val h.symm
      omega
    rw [remark21_7_primalSeq_apply]
    simp [hne]
  have hactive_real : Real.sqrt (n : ℝ) * remark21_7_primalSeq n n = 1 := by
    have hpair := remark21_7_pairing_eq_one n
    rw [remark21_7_pairing, remark21_7_inner_dualSeq_right] at hpair
    simpa using hpair
  have htail_one :
      (⨆ m : ℕ+,
        if 2 ≤ (m : ℕ) then (((Real.sqrt (m : ℝ)) * remark21_7_primalSeq n m : ℝ) : EReal)
        else (⊥ : EReal)) = 1 := by
    refine le_antisymm ?_ ?_
    · -- The primal vector has a single active tail coordinate, where the branch value is `1`.
      refine iSup_le fun m ↦ ?_
      by_cases hm2 : 2 ≤ (m : ℕ)
      · by_cases hm : m = n
        · subst hm
          simp [hn, hactive_real]
        · have hcoord : remark21_7_primalSeq n m = 0 := by
            rw [remark21_7_primalSeq_apply]
            simp [hm]
          have hterm_le :
              ((((Real.sqrt (m : ℝ)) * remark21_7_primalSeq n m : ℝ) : EReal) : EReal) ≤ 1 := by
            rw [hcoord]
            norm_num
          simpa [hm2] using hterm_le
      · simp [hm2]
    · -- The active tail coordinate attains the value `1`.
      rw [← show
        (if 2 ≤ (n : ℕ) then
          (((Real.sqrt (n : ℝ)) * remark21_7_primalSeq n n : ℝ) : EReal)
        else (⊥ : EReal)) = (1 : EReal) by
          simp [hn, hactive_real]]
      exact le_iSup
        (fun m : ℕ+ ↦
          if 2 ≤ (m : ℕ) then (((Real.sqrt (m : ℝ)) * remark21_7_primalSeq n m : ℝ) : EReal)
          else (⊥ : EReal))
        n
  -- The maximum of the affine branch and the tail supremum is exactly `1`.
  change
    max (((1 + remark21_7_primalSeq n (1 : ℕ+) : ℝ) : EReal))
        (⨆ m : ℕ+,
          if 2 ≤ (m : ℕ) then
            (((Real.sqrt (m : ℝ)) * remark21_7_primalSeq n m : ℝ) : EReal)
          else (⊥ : EReal)) = 1
  rw [hfirst, htail_one]
  simp

/-- Helper for Remark 21.7: the first affine branch gives a supporting minorant at the index
`n = 1`. -/
private theorem remark21_7_dualSeq_minorant_at_primalSeq_one (y : L2pos) :
    ((⟪y - remark21_7_primalSeq 1, remark21_7_dualSeq 1⟫_ℝ : EReal) +
        (example_21_6_l2_counterexample_function (remark21_7_primalSeq 1) : EReal)) ≤
      (example_21_6_l2_counterexample_function y : EReal) := by
  have hpair : inner ℝ (remark21_7_primalSeq 1) (remark21_7_dualSeq 1) = 1 := by
    simpa [remark21_7_pairing] using remark21_7_pairing_eq_one (1 : ℕ+)
  have hinner :
      inner ℝ (y - remark21_7_primalSeq 1) (remark21_7_dualSeq 1) = y (1 : ℕ+) - 1 := by
    -- The first graph point uses the affine branch `1 + y₁`.
    rw [inner_sub_left, remark21_7_inner_dualSeq_right, hpair]
    norm_num
  let a : ℝ := y (1 : ℕ+)
  have hsum :
      ((((a - 1 : ℝ) : EReal)) + 2) = (((1 + a : ℝ) : EReal)) := by
    change ((((a - 1 : ℝ) : EReal)) + (((2 : ℝ) : EReal))) = (((1 + a : ℝ) : EReal))
    rw [← EReal.coe_add]
    congr 1
    ring
  calc
    ((⟪y - remark21_7_primalSeq 1, remark21_7_dualSeq 1⟫_ℝ : EReal) +
          (example_21_6_l2_counterexample_function (remark21_7_primalSeq 1) : EReal)) =
        ((((a - 1 : ℝ) : EReal)) + 2) := by
          rw [hinner, remark21_7_apply_primalSeq_one]
    _ = (((1 + a : ℝ) : EReal)) := hsum
    _ = (((1 + y (1 : ℕ+) : ℝ) : EReal)) := by
          simp [a]
    _ ≤ (example_21_6_l2_counterexample_function y : EReal) := remark21_7_firstBranch_le y

/-- Helper for Remark 21.7: the tail branch gives a supporting minorant at every index `n ≥ 2`.
-/
private theorem remark21_7_dualSeq_minorant_at_primalSeq_tail {n : ℕ+} (hn : 2 ≤ (n : ℕ))
    (y : L2pos) :
    ((⟪y - remark21_7_primalSeq n, remark21_7_dualSeq n⟫_ℝ : EReal) +
        (example_21_6_l2_counterexample_function (remark21_7_primalSeq n) : EReal)) ≤
      (example_21_6_l2_counterexample_function y : EReal) := by
  have hpair : inner ℝ (remark21_7_primalSeq n) (remark21_7_dualSeq n) = 1 := by
    simpa [remark21_7_pairing] using remark21_7_pairing_eq_one n
  have htail :
      ((((Real.sqrt (n : ℝ)) * y n : ℝ) : EReal)) ≤
        (example_21_6_l2_counterexample_function y : EReal) := by
    -- The active tail coordinate is one branch of the defining supremum.
    simpa [hn] using remark21_7_tailBranch_le y n
  have hinner :
      inner ℝ (y - remark21_7_primalSeq n) (remark21_7_dualSeq n) =
        Real.sqrt (n : ℝ) * y n - 1 := by
    -- Expanding the pairing isolates the active coordinate and the touching value `1`.
    rw [inner_sub_left, remark21_7_inner_dualSeq_right, hpair]
  let a : ℝ := Real.sqrt (n : ℝ) * y n
  have hsum :
      ((((a - 1 : ℝ) : EReal)) + 1) = (((a : ℝ) : EReal)) := by
    change ((((a - 1 : ℝ) : EReal)) + (((1 : ℝ) : EReal))) = (((a : ℝ) : EReal))
    rw [← EReal.coe_add]
    congr 1
    ring
  calc
    ((⟪y - remark21_7_primalSeq n, remark21_7_dualSeq n⟫_ℝ : EReal) +
          (example_21_6_l2_counterexample_function (remark21_7_primalSeq n) : EReal)) =
        ((((a - 1 : ℝ) : EReal)) + 1) := by
          rw [hinner, remark21_7_apply_primalSeq_tail hn]
    _ = (((a : ℝ) : EReal)) := hsum
    _ = ((((Real.sqrt (n : ℝ)) * y n : ℝ) : EReal)) := by
          simp [a]
    _ ≤ (example_21_6_l2_counterexample_function y : EReal) := htail

/-- Helper for Remark 21.7: the first graph point belongs to
`gra (∂ example_21_6_l2_counterexample_function)`. -/
private theorem remark21_7_one_mem_graph :
    remark21_7_graphPair 1 ∈ gra example21_6_subdifferential := by
  -- Apply the affine-branch minorant at the first graph point.
  simpa [SetValuedOperator.graph, remark21_7_graphPair] using
    (show remark21_7_dualSeq 1 ∈ example21_6_subdifferential (remark21_7_primalSeq 1) from by
      rw [mem_subdifferential_iff]
      intro y
      exact remark21_7_dualSeq_minorant_at_primalSeq_one y)

/-- Helper for Remark 21.7: every tail graph point belongs to
`gra (∂ example_21_6_l2_counterexample_function)`. -/
private theorem remark21_7_tail_mem_graph {n : ℕ+} (hn : 2 ≤ (n : ℕ)) :
    remark21_7_graphPair n ∈ gra example21_6_subdifferential := by
  -- Apply the active tail-branch minorant at the chosen graph point.
  simpa [SetValuedOperator.graph, remark21_7_graphPair] using
    (show remark21_7_dualSeq n ∈ example21_6_subdifferential (remark21_7_primalSeq n) from by
      rw [mem_subdifferential_iff]
      intro y
      exact remark21_7_dualSeq_minorant_at_primalSeq_tail hn y)

/-- Helper for Remark 21.7: the shifted inverse-square weights normalize to the shifted harmonic
sequence. -/
private theorem remark21_7_shiftedInvSq_eq_inv (N n : ℕ) :
    ((Real.sqrt (n + N + 2 : ℝ))⁻¹)^2 = ((n + N + 2 : ℝ)⁻¹) := by
  -- Rewrite the squared inverse square root as the reciprocal of the shifted index.
  have hnonneg : 0 ≤ (n + N + 2 : ℝ) := by positivity
  rw [inv_pow, Real.sq_sqrt hnonneg]

/-- Helper for Remark 21.7: the shifted inverse-square weights remain non-summable. -/
private theorem remark21_7_shiftedInvSq_notSummable (N : ℕ) :
    ¬ Summable (fun n : ℕ ↦ ((Real.sqrt (n + N + 2 : ℝ))⁻¹)^2) := by
  -- Normalize the shifted inverse squares to the shifted harmonic sequence.
  intro hsummable
  have hshifted : Summable (fun n : ℕ ↦ ((n + N + 2 : ℝ)⁻¹)) := by
    refine hsummable.congr ?_
    intro n
    simpa [Nat.add_assoc] using remark21_7_shiftedInvSq_eq_inv N n
  exact Real.not_summable_natCast_inv <|
    (summable_nat_add_iff (f := fun n : ℕ ↦ ((n : ℝ)⁻¹)) (N + 2)).1 <| by
      simpa [Nat.cast_add, add_assoc] using hshifted

/-- Helper for Remark 21.7: shifting the dual sequence rewrites it into the weighted-tail normal
form used by Example 3.33. -/
private theorem remark21_7_shiftedDual_eq_scaledTailBasis (N n : ℕ) :
    remark21_7_dualSeq ⟨n + N + 2, by omega⟩ =
      (Real.sqrt (n + N + 2 : ℝ) : ℝ) •
        (lp.single 2 ⟨n + N + 2, by omega⟩ (1 : ℝ) : L2pos) := by
  -- This is exactly the defining formula of the dual sequence at the shifted index.
  simp [remark21_7_dualSeq]

/-- Helper for Remark 21.7: every shifted tail of the dual sequence has `0` in its weak closure.
-/
private theorem remark21_7_shiftedDual_zero_mem_closure (N : ℕ) :
    (0 : WeakSpace ℝ L2pos) ∈
      closure
        ((toWeakSpace ℝ L2pos) ''
          Set.range (fun n : ℕ ↦ remark21_7_dualSeq ⟨n + N + 2, by omega⟩)) := by
  let α : ℕ → ℝ := fun n ↦ Real.sqrt (n + N + 2 : ℝ)
  have hα_ge_one : ∀ n : ℕ, 1 ≤ α n := by
    -- Every shifted weight is at least `1` because its index is at least `2`.
    intro n
    dsimp [α]
    have hbase : (1 : ℝ) ≤ n + N + 2 := by
      exact_mod_cast (show 1 ≤ n + N + 2 by omega)
    exact (Real.one_le_sqrt).2 hbase
  have hα_mono : Monotone α := by
    -- The square root preserves the monotonicity of the shifted indices.
    intro m n hmn
    dsimp [α]
    refine Real.sqrt_le_sqrt ?_
    exact_mod_cast Nat.add_le_add_right hmn (N + 2)
  have hα_tendsto : Tendsto α atTop atTop := by
    -- The shifted weights still diverge to `+∞`.
    convert
      (Real.tendsto_sqrt_atTop.comp <|
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat (N + 2)))) using 1
    ext n
    simp [α, Nat.cast_add, add_assoc]
  have hzero_mem :
      (0 : WeakSpace ℝ L2pos) ∈
        closure
          ((toWeakSpace ℝ L2pos) ''
            Set.range
              (fun n : ℕ ↦
                α n • (lp.single 2 ⟨n + N + 2, by omega⟩ (1 : ℝ) : L2pos))) := by
    -- Consume Example 3.33 directly on the shifted weighted orthonormal tail.
    exact
      (scaled_orthonormal_range_weaklySeqClosed_and_not_weaklyClosed
        (fun n : ℕ ↦ (lp.single 2 ⟨n + N + 2, by omega⟩ (1 : ℝ) : L2pos))
        (remark21_7_shiftedBasis_orthonormal N) α hα_ge_one hα_mono hα_tendsto
        (remark21_7_shiftedInvSq_notSummable N)).2.2.2.1
  -- Rewrite the weighted orthonormal tail back to the concrete dual sequence.
  simpa [α, remark21_7_shiftedDual_eq_scaledTailBasis] using hzero_mem

/-- Helper for Remark 21.7: the mixed strong/weak graph family has `(0,0)` as a cluster point. -/
private theorem remark21_7_zeroMixed_mapClusterPt :
    MapClusterPt ((0 : L2pos), (0 : WeakSpace ℝ L2pos)) atTop remark21_7_mixedGraphPair := by
  rw [mapClusterPt_iff_frequently]
  intro s hs
  rw [Filter.frequently_atTop]
  intro b
  rcases mem_nhds_prod_iff.mp hs with ⟨V, hV, W, hW, hVW⟩
  rcases Metric.mem_nhds_iff.mp hV with ⟨r, hr_pos, hrV⟩
  have hnorm_tendsto :
      Tendsto (fun n : ℕ ↦ 1 / Real.sqrt (n + 2 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    -- The primal norms are reciprocal square roots along the tail.
    convert
      (tendsto_inv_atTop_zero.comp <|
        Real.tendsto_sqrt_atTop.comp <|
          (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))) using 1
    ext n
    simp [one_div, Nat.cast_add]
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.1 hnorm_tendsto r hr_pos
  let N : ℕ := max K (b : ℕ)
  have hprimal_mem : ∀ n : ℕ, remark21_7_primalSeq ⟨n + N + 2, by omega⟩ ∈ V := by
    intro n
    have hlarge : K ≤ n + N := by
      dsimp [N]
      omega
    have hsmall_scalar : dist (1 / Real.sqrt (n + N + 2 : ℝ)) 0 < r := by
      simpa [Nat.cast_add, add_assoc] using hK (n + N) hlarge
    have hsmall_scalar' : (Real.sqrt (n + N + 2 : ℝ))⁻¹ < r := by
      have habs_lt : |(Real.sqrt (n + N + 2 : ℝ))⁻¹| < r := by
        simpa [one_div, Real.dist_eq] using hsmall_scalar
      have hnonneg_inv : 0 ≤ (Real.sqrt (n + N + 2 : ℝ))⁻¹ := by positivity
      simpa [abs_of_nonneg hnonneg_inv] using habs_lt
    have hsmall_norm : ‖remark21_7_primalSeq ⟨n + N + 2, by omega⟩‖ < r := by
      simpa [remark21_7_norm_primalSeq, one_div] using hsmall_scalar'
    exact hrV <| by
      change remark21_7_primalSeq ⟨n + N + 2, by omega⟩ ∈ Metric.ball (0 : L2pos) r
      simpa [Metric.mem_ball, dist_eq_norm] using hsmall_norm
  rcases (mem_closure_iff_nhds.mp (remark21_7_shiftedDual_zero_mem_closure N)) W hW with
    ⟨w, hw⟩
  rcases hw with ⟨hwW, hwRange⟩
  rcases hwRange with ⟨z, hzRange, rfl⟩
  rcases hzRange with ⟨n, rfl⟩
  refine ⟨⟨n + N + 2, by omega⟩, ?_, ?_⟩
  · -- The shifted tail index lies beyond the prescribed starting point `b`.
    change (b : ℕ) ≤ n + N + 2
    dsimp [N]
    omega
  · -- Assemble the witness from the strong primal neighborhood and the weak dual neighborhood.
    exact hVW ⟨hprimal_mem n, hwW⟩

/-- First claim of Remark 21.7: each explicit pair `(e_n / √n, √n e_n)` belongs to
`gra (∂ example_21_6_l2_counterexample_function)`. -/
theorem remark21_7_counterexample_mem_graph (n : ℕ+) :
    remark21_7_graphPair n ∈ gra example21_6_subdifferential := by
  -- Split the positive index into the affine case `n = 1` and the tail case `n ≥ 2`.
  by_cases hn : n = 1
  · subst hn
    exact remark21_7_one_mem_graph
  · have htail : 2 ≤ (n : ℕ) := by
      have hval_ne : (n : ℕ) ≠ 1 := by
        intro hval
        apply hn
        exact Subtype.ext hval
      have hpos : 0 < (n : ℕ) := n.property
      omega
    exact remark21_7_tail_mem_graph htail

/-- A textbook subnet of the explicit graph pairs from `(21.22)` whose mixed strong/weak graph net
converges to `(0, 0)`. The monotone cofinal reindexing data are the canonical subnet owner, while
the graph-membership, unboundedness, and pairing conclusions are exported as companion theorems. -/
structure Remark21_7CounterexampleSubnet {B : Type u} [Nonempty B] [Preorder B]
    [IsDirectedOrder B] (φ : B → ℕ+) : Prop where
  monotone : Monotone φ
  tendsto_atTop : Tendsto φ atTop atTop
  mixed_tendsto_zero :
    Tendsto (fun b : B ↦ remark21_7_mixedGraphPair (φ b)) atTop
      (𝓝 ((0 : L2pos), (0 : WeakSpace ℝ L2pos)))

namespace Remark21_7CounterexampleSubnet

/-- Every reindexed graph pair in a Remark 21.7 counterexample subnet still lies in
`gra (∂ example_21_6_l2_counterexample_function)`. -/
theorem mem_graph {B : Type u} (φ : B → ℕ+) (b : B) :
    remark21_7_graphPair (φ b) ∈ gra example21_6_subdifferential :=
  remark21_7_counterexample_mem_graph (φ b)

end Remark21_7CounterexampleSubnet

/-- Remark 21.7 (2): there exists a monotone cofinal reindexing of the explicit graph points from
`(21.22)` whose mixed strong/weak graph net converges to `(0, 0)`. By the companion theorems for
`Remark21_7CounterexampleSubnet`, every such subnet remains in
`gra (∂ example_21_6_l2_counterexample_function)`, is unbounded, and has pairings tending to `1`.
-/
theorem remark21_7_counterexample_tendsto_zero :
    ∃ (B : Type u) (_ : Nonempty B) (_ : Preorder B) (_ : IsDirectedOrder B) (φ : B → ℕ+),
      Remark21_7CounterexampleSubnet φ := by
  -- Extract a monotone cofinal subnet from the mixed cluster-point statement.
  rcases mapClusterPt_atTop_iff_exists_subnet_tendsto.mp remark21_7_zeroMixed_mapClusterPt with
    ⟨B, hBne, hBpre, hBdir, φ, hmono, hφ, hconv⟩
  let B' : Type u := ULift.{u} B
  let φ' : B' → ℕ+ := fun b ↦ φ b.down
  let _ : IsDirectedOrder B' := by
    refine ⟨?_⟩
    intro p q
    rcases (show ∃ r : B, p.down ≤ r ∧ q.down ≤ r from hBdir.1 p.down q.down) with
      ⟨r, hpr, hqr⟩
    exact ⟨ULift.up r, hpr, hqr⟩
  have hdown_tendsto : Tendsto (fun b : B' ↦ b.down) atTop atTop := by
    -- The universe lift preserves the directed order and has a cofinal projection back to `B`.
    refine Monotone.tendsto_atTop_atTop (fun _ _ hab ↦ hab) ?_
    intro b
    exact ⟨ULift.up b, le_rfl⟩
  have hmono' : Monotone φ' := by
    intro b₁ b₂ hb
    exact hmono hb
  have hφ' : Tendsto φ' atTop atTop := hφ.comp hdown_tendsto
  have hconv' :
      Tendsto (fun b : B' ↦ remark21_7_mixedGraphPair (φ' b)) atTop
        (𝓝 ((0 : L2pos), (0 : WeakSpace ℝ L2pos))) := by
    simpa [φ', Function.comp] using hconv.comp hdown_tendsto
  refine ⟨B', inferInstance, inferInstance, inferInstance, φ', ?_⟩
  exact ⟨hmono', hφ', hconv'⟩

/-- Helper for Remark 21.7: every cofinal reindexing of the dual family `√n e_n` remains
unbounded. -/
private theorem remark21_7_dualSeq_unbounded_reindex {B : Type u} [Nonempty B] [Preorder B]
    [IsDirectedOrder B] (φ : B → ℕ+) (hφ : Tendsto φ atTop atTop) :
    ¬ Bornology.IsBounded (Set.range fun b : B ↦ remark21_7_dualSeq (φ b)) := by
  intro hbounded
  rcases isBounded_iff_forall_norm_le.mp hbounded with ⟨C₀, hC₀⟩
  let C : ℝ := max C₀ 0
  have hC : ∀ b : B, ‖remark21_7_dualSeq (φ b)‖ ≤ C := by
    -- A uniform bound on the range gives a uniform bound on every reindexed dual vector.
    intro b
    exact le_trans (hC₀ _ (Set.mem_range_self b)) (le_max_left _ _)
  obtain ⟨M, hM⟩ := exists_nat_gt (C ^ 2)
  let n : ℕ+ := ⟨M + 1, by omega⟩
  obtain ⟨b, hb⟩ := (tendsto_atTop_atTop.1 hφ) n
  have hn_le : n ≤ φ b := hb b le_rfl
  have hsqrt_le : Real.sqrt ((φ b : ℕ+) : ℝ) ≤ C := by
    simpa [remark21_7_norm_dualSeq] using hC b
  have hsq_le : ((φ b : ℕ+) : ℝ) ≤ C ^ 2 := by
    -- Squaring the norm bound transfers the estimate from `√(φ b)` back to `φ b`.
    have hsqrt_nonneg : 0 ≤ Real.sqrt (((φ b : ℕ+) : ℝ)) := Real.sqrt_nonneg _
    have hsq : (Real.sqrt (((φ b : ℕ+) : ℝ))) ^ 2 = (((φ b : ℕ+) : ℝ)) := by
      rw [Real.sq_sqrt]
      positivity
    nlinarith
  have hn_large : C ^ 2 < (((φ b : ℕ+) : ℝ)) := by
    -- Cofinality lets us choose an index past the arbitrary threshold `C^2`.
    have hcast : (n : ℝ) ≤ (((φ b : ℕ+) : ℝ)) := by
      exact_mod_cast hn_le
    exact lt_of_lt_of_le (lt_of_lt_of_le hM <| by
      norm_num [n]) hcast
  exact not_le_of_gt hn_large hsq_le

/-- Unboundedness claim from Remark 21.7: the explicit family from `(21.22)` is unbounded in
`L2pos × L2pos`. -/
theorem remark21_7_counterexample_unbounded :
    ¬ Bornology.IsBounded (Set.range remark21_7_graphPair) := by
  intro hbounded
  have hsnd :
      Prod.snd '' Set.range remark21_7_graphPair = Set.range remark21_7_dualSeq := by
    ext u
    constructor
    · rintro ⟨p, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨remark21_7_graphPair n, ⟨n, rfl⟩, rfl⟩
  have hu_bounded : Bornology.IsBounded (Set.range remark21_7_dualSeq) := by
    -- Boundedness of the graph family bounds its second coordinate.
    rw [← hsnd]
    exact hbounded.image_snd
  exact (remark21_7_dualSeq_unbounded_reindex (fun n : ℕ+ ↦ n) tendsto_id) hu_bounded

/-- Limit-point exclusion from Remark 21.7: the limit pair `(0, 0)` does not belong to
`gra (∂ example_21_6_l2_counterexample_function)`. -/
theorem remark21_7_zero_not_mem_graph :
    ((0 : L2pos), (0 : L2pos)) ∉ gra example21_6_subdifferential := by
  have hnot_argmin : (0 : L2pos) ∉ Argmin example_21_6_l2_counterexample_function := by
    -- The explicit argmin description from Example 21.6 excludes the origin.
    rw [example_21_6_argmin_eq]
    intro hzero
    have hfalse : ¬ ((0 : ℝ) ≤ -1) := by norm_num
    exact hfalse hzero.1
  have hnot_zero : (0 : L2pos) ∉ (∂ example_21_6_l2_counterexample_function).zeros := by
    -- Fermat's rule transfers the argmin exclusion to the zero set of the subdifferential.
    simpa [argmin_eq_zeros_subdifferential] using hnot_argmin
  simpa [SetValuedOperator.graph, SetValuedOperator.mem_zeros_iff] using hnot_zero

/-- Pairing claim from Remark 21.7: the explicit pairings from `(21.22)` converge to `1`, so any
reindexing of these pairs still has pairings tending to `1` rather than to `⟪0, 0⟫_ℝ = 0`. -/
theorem remark21_7_counterexample_inner_tendsto_one :
    Tendsto remark21_7_pairing atTop (𝓝 (1 : ℝ)) := by
  -- The explicit pairings are constantly equal to `1`.
  refine tendsto_const_nhds.congr' ?_
  exact Filter.Eventually.of_forall fun n ↦ (remark21_7_pairing_eq_one n).symm

namespace Remark21_7CounterexampleSubnet

/-- A Remark 21.7 counterexample subnet preserves the `⟪x_n, u_n⟫_ℝ → 1` pathology. -/
theorem pairing_tendsto_one {B : Type u} [Nonempty B] [Preorder B] [IsDirectedOrder B]
    {φ : B → ℕ+} (hφ : Remark21_7CounterexampleSubnet φ) :
    Tendsto (fun b : B ↦ remark21_7_pairing (φ b)) atTop (𝓝 (1 : ℝ)) := by
  simpa [Function.comp] using
    remark21_7_counterexample_inner_tendsto_one.comp hφ.tendsto_atTop

/-- A Remark 21.7 counterexample subnet remains unbounded in `L2pos × L2pos`. -/
theorem unbounded {B : Type u} [Nonempty B] [Preorder B] [IsDirectedOrder B] {φ : B → ℕ+}
    (hφ : Remark21_7CounterexampleSubnet φ) :
    ¬ Bornology.IsBounded (Set.range fun b : B ↦ remark21_7_graphPair (φ b)) := by
  intro hbounded
  have hsnd :
      Prod.snd '' Set.range (fun b : B ↦ remark21_7_graphPair (φ b)) =
        Set.range (fun b : B ↦ remark21_7_dualSeq (φ b)) := by
    ext u
    constructor
    · rintro ⟨p, ⟨b, rfl⟩, rfl⟩
      exact ⟨b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨remark21_7_graphPair (φ b), ⟨b, rfl⟩, rfl⟩
  have hu_bounded : Bornology.IsBounded (Set.range fun b : B ↦ remark21_7_dualSeq (φ b)) := by
    -- Boundedness of the reindexed graph family bounds its second coordinate.
    rw [← hsnd]
    exact hbounded.image_snd
  exact (remark21_7_dualSeq_unbounded_reindex φ hφ.tendsto_atTop) hu_bounded

end Remark21_7CounterexampleSubnet

end

end ERealFunction
