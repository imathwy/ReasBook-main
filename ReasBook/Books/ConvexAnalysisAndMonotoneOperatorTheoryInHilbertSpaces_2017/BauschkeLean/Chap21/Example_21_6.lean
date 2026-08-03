import BauschkeLean.Chap02.Fact_2_35
import BauschkeLean.Chap03.Example_3_33
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_3
import BauschkeLean.Chap09.Proposition_9_5
import BauschkeLean.Chap16.Theorem_16_3
import BauschkeLean.Chap21.Theorem_21_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Topology SetValuedOperator
open SetValuedOperator
open Filter

namespace ERealFunction

noncomputable section

local notation "L2pos" => ℓ²(ℕ+, ℝ)

/-- Helper for Example 21.6: the standard unit vector `e_n` of `ℓ²(ℕ+, ℝ)`. -/
private def example21_6_basisVector (n : ℕ+) : L2pos :=
  lp.single 2 n (1 : ℝ)

/-- Helper for Example 21.6: the raw `EReal` owner of the function from `(21.16)`. -/
private noncomputable def example21_6_rawEReal (x : L2pos) : EReal :=
  max (((1 + x (1 : ℕ+) : ℝ) : EReal))
    (⨆ n : ℕ+,
      if 2 ≤ (n : ℕ) then (((Real.sqrt (n : ℝ)) * x n : ℝ) : EReal) else (⊥ : EReal))

/-- The `]-∞,+∞]`-valued function on `ℓ²(ℕ+, ℝ)` used in Example 21.6, defined by
`x ↦ max {1 + x₁, sup_{n ≥ 2} (√n) xₙ}`, written through the canonical coordinate functionals of
the standard basis of `ℓ²(ℕ+, ℝ)`. -/
noncomputable def example_21_6_l2_counterexample_function : L2pos → Set.Ioi (⊥ : EReal) :=
  fun x ↦
    ⟨example21_6_rawEReal x, by
      have hfirst : (⊥ : EReal) < (((1 + x (1 : ℕ+) : ℝ) : EReal)) := EReal.bot_lt_coe _
      rw [example21_6_rawEReal]
      exact lt_of_lt_of_le hfirst (le_max_left _ _)⟩

/-- Evaluating the Example 21.6 function recovers the explicit coordinatewise formula. -/
@[simp] theorem example_21_6_l2_counterexample_function_apply (x : L2pos) :
    (example_21_6_l2_counterexample_function x : EReal) = example21_6_rawEReal x :=
  rfl

/-- Helper for Example 21.6: the shifted index `n + 2` viewed in `ℕ+`. -/
private theorem example21_6_tailIndex_pos (n : ℕ) : 0 < n + 2 := by
  simp

/-- Helper for Example 21.6: the `ℕ`-indexed positive coordinate `n + 2`. -/
private def example21_6_tailIndex (n : ℕ) : ℕ+ :=
  ⟨n + 2, example21_6_tailIndex_pos n⟩

/-- Helper for Example 21.6: the primal graph witness `e_{n+2} / √(n+2)`. -/
private noncomputable def example21_6_primalPoint (n : ℕ) : L2pos :=
  ((1 / Real.sqrt (n + 2 : ℝ)) : ℝ) • example21_6_basisVector (example21_6_tailIndex n)

/-- Helper for Example 21.6: the dual graph witness `√(n+2) e_{n+2}`. -/
private noncomputable def example21_6_dualPoint (n : ℕ) : L2pos :=
  (Real.sqrt (n + 2 : ℝ) : ℝ) • example21_6_basisVector (example21_6_tailIndex n)

/-- Helper for Example 21.6: the shifted indices all lie in the tail `n ≥ 2`. -/
private theorem example21_6_tailIndex_two_le (n : ℕ) :
    2 ≤ ((example21_6_tailIndex n : ℕ)) := by
  change 2 ≤ n + 2
  omega

/-- Helper for Example 21.6: no shifted tail index equals `1`. -/
private theorem example21_6_tailIndex_ne_one (n : ℕ) :
    example21_6_tailIndex n ≠ 1 := by
  intro h
  have hval : ((example21_6_tailIndex n : ℕ)) = 1 := congrArg Subtype.val h
  have htwo : 2 ≤ ((example21_6_tailIndex n : ℕ)) := example21_6_tailIndex_two_le n
  omega

/-- Helper for Example 21.6: the standard basis of `ℓ²(ℕ+, ℝ)` is orthonormal. -/
private theorem example21_6_basisVector_orthonormal :
    Orthonormal ℝ example21_6_basisVector := by
  -- Reduce orthonormality to the coordinate formula for `lp.single`.
  rw [orthonormal_iff_ite]
  intro i j
  by_cases hij : i = j
  · subst hij
    simp [example21_6_basisVector]
  · simp [example21_6_basisVector, lp.inner_single_left, hij]

/-- Helper for Example 21.6: every shifted tail of the standard basis stays orthonormal. -/
private theorem example21_6_tailBasis_orthonormal (N : ℕ) :
    Orthonormal ℝ (fun n : ℕ ↦ example21_6_basisVector ⟨n + N + 2, by omega⟩) := by
  -- Compose the standard orthonormal basis with the injective shifted-index map.
  refine example21_6_basisVector_orthonormal.comp (fun n : ℕ ↦ ⟨n + N + 2, by omega⟩) ?_
  intro m n hmn
  have hvals : m + N + 2 = n + N + 2 := congrArg Subtype.val hmn
  omega

/-- Helper for Example 21.6: reading the `n`th coordinate against the standard basis recovers
that coordinate. -/
private theorem example21_6_inner_basisVector_left (x : L2pos) (n : ℕ+) :
    inner ℝ (example21_6_basisVector n) x = x n := by
  -- Expand the single-support basis vector and simplify the real scalar inner product.
  calc
    inner ℝ (example21_6_basisVector n) x = ⟪(1 : ℝ), x n⟫_ℝ := by
      rw [example21_6_basisVector, lp.inner_single_left]
    _ = x n * 1 := by
      exact RCLike.inner_apply (1 : ℝ) (x n)
    _ = x n := by simp

/-- Helper for Example 21.6: reading the `n`th coordinate against the standard basis recovers
that coordinate. -/
private theorem example21_6_inner_basisVector_right (x : L2pos) (n : ℕ+) :
    inner ℝ x (example21_6_basisVector n) = x n := by
  -- Expand the single-support basis vector on the right and simplify in `ℝ`.
  calc
    inner ℝ x (example21_6_basisVector n) = ⟪x n, (1 : ℝ)⟫_ℝ := by
      rw [example21_6_basisVector, lp.inner_single_right]
    _ = 1 * x n := by
      exact RCLike.inner_apply (x n) (1 : ℝ)
    _ = x n := by simp

/-- Helper for Example 21.6: the dual witness acts by the weighted coordinate
`x ↦ √(n+2) x_(n+2)`. -/
private theorem example21_6_inner_dualPoint_right (x : L2pos) (n : ℕ) :
    inner ℝ x (example21_6_dualPoint n) =
      (Real.sqrt (n + 2 : ℝ)) * x (example21_6_tailIndex n) := by
  -- Expand the scalar multiple on the right and then read the chosen coordinate.
  rw [example21_6_dualPoint, real_inner_smul_right, example21_6_inner_basisVector_right]

/-- Helper for Example 21.6: the primal witness is supported at a single tail coordinate. -/
private theorem example21_6_primalPoint_apply (n : ℕ) (m : ℕ+) :
    example21_6_primalPoint n m =
      if m = example21_6_tailIndex n then (1 / Real.sqrt (n + 2 : ℝ) : ℝ) else 0 := by
  -- Expand the scalar multiple of the single-support basis vector coordinatewise.
  by_cases hm : m = example21_6_tailIndex n
  · subst hm
    simp [example21_6_primalPoint, example21_6_basisVector]
  · simp [example21_6_primalPoint, example21_6_basisVector, hm]

/-- Helper for Example 21.6: the primal and dual witnesses pair to `1`. -/
private theorem example21_6_inner_primalPoint_dualPoint (n : ℕ) :
    inner ℝ (example21_6_primalPoint n) (example21_6_dualPoint n) = 1 := by
  -- The two witnesses meet on exactly one coordinate, where the weights cancel.
  rw [example21_6_inner_dualPoint_right, example21_6_primalPoint_apply]
  have hsqrt_pos : 0 < Real.sqrt (n + 2 : ℝ) := by positivity
  simp only [↓reduceIte, one_div]
  field_simp [hsqrt_pos.ne']

/-- Helper for Example 21.6: the primal witness has norm `1 / √(n+2)`. -/
private theorem example21_6_norm_primalPoint (n : ℕ) :
    ‖example21_6_primalPoint n‖ = 1 / Real.sqrt (n + 2 : ℝ) := by
  -- Rewrite the primal witness as a scaled single-support vector and evaluate its `ℓ²` norm.
  calc
    ‖example21_6_primalPoint n‖ =
        ‖(1 / Real.sqrt (n + 2 : ℝ) : ℝ)‖ *
          ‖example21_6_basisVector (example21_6_tailIndex n)‖ := by
          rw [example21_6_primalPoint, norm_smul]
    _ = |(1 / Real.sqrt (n + 2 : ℝ) : ℝ)| *
          ‖example21_6_basisVector (example21_6_tailIndex n)‖ := by
          rw [Real.norm_eq_abs]
    _ = |(1 / Real.sqrt (n + 2 : ℝ) : ℝ)| * ‖(1 : ℝ)‖ := by
          rw [example21_6_basisVector, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
    _ = 1 / Real.sqrt (n + 2 : ℝ) := by
          have hnonneg : 0 ≤ (1 / Real.sqrt (n + 2 : ℝ) : ℝ) := by
            positivity
          simp

/-- Helper for Example 21.6: the scalar affine branch `t ↦ t - c`, viewed in `EReal`, belongs
to `Γ(ℝ)`. -/
private theorem example21_6_realShift_mem_gamma (c : ℝ) :
    (fun t : ℝ ↦ ((t - c : ℝ) : EReal)) ∈ Γ(ℝ) := by
  -- Affine scalar maps are convex and continuous, hence belong to `Γ(ℝ)`.
  rw [mem_gamma_iff]
  refine ⟨?_, ?_⟩
  · intro x y a ha0 ha1
    have hreal : a * x + (1 - a) * y - c = a * (x - c) + (1 - a) * (y - c) := by
      ring
    have hcoeff : (1 - (a : EReal)) = (((1 - a : ℝ) : EReal)) := by
      norm_num
    change (((a * x + (1 - a) * y - c : ℝ) : EReal)) ≤
      (a : EReal) * (((x - c : ℝ) : EReal)) +
        (1 - a : EReal) * (((y - c : ℝ) : EReal))
    rw [hcoeff, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    exact congrArg (fun t : ℝ ↦ ((t : ℝ) : EReal)) hreal |>.le
  · simpa [Function.comp] using
      (continuous_coe_real_ereal.comp (continuous_id.sub continuous_const)).lowerSemicontinuous

/-- Helper for Example 21.6: the constant `⊥` branch is a member of `Γ(ℓ²(ℕ+, ℝ))`. -/
private theorem example21_6_bot_mem_gamma :
    (fun _ : L2pos ↦ (⊥ : EReal)) ∈ Γ(L2pos) := by
  -- The constant bottom function is convex and lower semicontinuous.
  rw [mem_gamma_iff]
  refine ⟨?_, ?_⟩
  · intro x y a ha0 ha1
    simp
  · simpa using (lowerSemicontinuous_const : LowerSemicontinuous (fun _ : L2pos ↦ (⊥ : EReal)))

/-- Helper for Example 21.6: the affine first-coordinate branch belongs to `Γ(ℓ²(ℕ+, ℝ))`. -/
private theorem example21_6_firstBranch_mem_gamma :
    (fun x : L2pos ↦ (((1 + x (1 : ℕ+) : ℝ) : EReal))) ∈ Γ(L2pos) := by
  -- Precompose the scalar affine map with the first-coordinate inner-product functional.
  have hcomp :
      (fun t : ℝ ↦ ((t - (-1) : ℝ) : EReal)) ∘
          innerSL ℝ (example21_6_basisVector 1) ∈ Γ(L2pos) :=
    mem_gamma_comp_continuousLinearMap
      (fun t : ℝ ↦ ((t - (-1) : ℝ) : EReal))
      (innerSL ℝ (example21_6_basisVector 1))
      (example21_6_realShift_mem_gamma (-1))
  simpa [Function.comp, sub_eq_add_neg, example21_6_inner_basisVector_left,
    add_comm, add_left_comm, add_assoc] using hcomp

/-- Helper for Example 21.6: each tail coordinate branch belongs to `Γ(ℓ²(ℕ+, ℝ))`. -/
private theorem example21_6_tailBranch_mem_gamma (n : ℕ+) :
    (fun x : L2pos ↦
      if 2 ≤ (n : ℕ) then (((Real.sqrt (n : ℝ)) * x n : ℝ) : EReal) else (⊥ : EReal)) ∈
        Γ(L2pos) := by
  by_cases hn : 2 ≤ (n : ℕ)
  · -- On the active branch, precompose the zero-offset affine map with the weighted coordinate.
    have hcomp :
        (fun t : ℝ ↦ ((t - 0 : ℝ) : EReal)) ∘
            innerSL ℝ ((Real.sqrt (n : ℝ)) • example21_6_basisVector n) ∈ Γ(L2pos) :=
      mem_gamma_comp_continuousLinearMap
        (fun t : ℝ ↦ ((t - 0 : ℝ) : EReal))
        (innerSL ℝ ((Real.sqrt (n : ℝ)) • example21_6_basisVector n))
        (example21_6_realShift_mem_gamma 0)
    simpa [hn, Function.comp, sub_eq_add_neg, example21_6_inner_basisVector_left,
      real_inner_smul_left] using hcomp
  · -- On the inactive branch, the function is constantly `⊥`.
    simpa [hn] using example21_6_bot_mem_gamma

/-- Helper for Example 21.6: the raw `EReal` owner belongs to `Γ(ℓ²(ℕ+, ℝ))` and is proper. -/
private theorem example21_6_rawEReal_mem_gamma_and_proper :
    example21_6_rawEReal ∈ Γ(L2pos) ∧ IsProper example21_6_rawEReal := by
  let tailBranch : L2pos → EReal := fun x ↦
    ⨆ n : ℕ+,
      if 2 ≤ (n : ℕ) then (((Real.sqrt (n : ℝ)) * x n : ℝ) : EReal) else (⊥ : EReal)
  let splitBranch : Bool → L2pos → EReal := fun b x ↦
    cond b (((1 + x (1 : ℕ+) : ℝ) : EReal)) (tailBranch x)
  have htail_gamma : tailBranch ∈ Γ(L2pos) := by
    -- Proposition 9.3 packages the tail supremum from the coordinatewise tail branches.
    exact iSup_mem_gamma
      (fun n : ℕ+ ↦
        fun x : L2pos ↦
          if 2 ≤ (n : ℕ) then (((Real.sqrt (n : ℝ)) * x n : ℝ) : EReal) else (⊥ : EReal))
      example21_6_tailBranch_mem_gamma
  have hsplit_gamma : ∀ b : Bool, splitBranch b ∈ Γ(L2pos) := by
    -- Each Boolean branch is either the affine first-coordinate term or the tail supremum.
    intro b
    cases b
    · simpa [splitBranch, tailBranch] using htail_gamma
    · simpa [splitBranch, tailBranch] using example21_6_firstBranch_mem_gamma
  have hgamma_split : (fun x : L2pos ↦ ⨆ b : Bool, splitBranch b x) ∈ Γ(L2pos) := by
    -- A two-branch supremum stays in `Γ(L2pos)` by another use of Proposition 9.3.
    exact iSup_mem_gamma splitBranch hsplit_gamma
  have hraw_eq : example21_6_rawEReal = fun x : L2pos ↦ ⨆ b : Bool, splitBranch b x := by
    -- The outer `max` is the Boolean supremum of the first branch and the tail branch.
    funext x
    rw [iSup_bool_eq]
    simp [example21_6_rawEReal, splitBranch, tailBranch, max_def]
  have hgamma : example21_6_rawEReal ∈ Γ(L2pos) := by
    -- Rewriting through the Boolean-supremum normal form exposes the `Γ` proof.
    simpa [hraw_eq] using hgamma_split
  have hproper : IsProper example21_6_rawEReal := by
    refine ⟨?_, ?_⟩
    · -- The affine first branch is always finite, so the outer maximum never reaches `⊥`.
      intro x
      have hfirst : (⊥ : EReal) < (((1 + x (1 : ℕ+) : ℝ) : EReal)) := EReal.bot_lt_coe _
      rw [example21_6_rawEReal]
      exact ne_of_gt (lt_of_lt_of_le hfirst (le_max_left _ _))
    · -- The origin belongs to the domain once we compute the raw value there explicitly.
      refine ⟨0, ?_⟩
      rw [mem_dom_iff_ne_top]
      have htail_le_zero :
          (⨆ n : ℕ+,
            if 2 ≤ (n : ℕ) then (((Real.sqrt (n : ℝ)) * (0 : L2pos) n : ℝ) : EReal)
            else (⊥ : EReal)) ≤ 0 := by
        refine iSup_le fun n ↦ ?_
        by_cases hn : 2 ≤ (n : ℕ)
        · have hcoord : (0 : L2pos) n = 0 := by rfl
          have hterm_le : (((Real.sqrt (n : ℝ)) * (0 : L2pos) n : ℝ) : EReal) ≤ 0 := by
            rw [hcoord]
            simp
          simpa [hn] using hterm_le
        · simp [hn]
      have hraw_le_one : example21_6_rawEReal (0 : L2pos) ≤ 1 := by
        have hcoord : (0 : L2pos) (1 : ℕ+) = 0 := by rfl
        rw [example21_6_rawEReal]
        refine max_le ?_ (le_trans htail_le_zero (by norm_num))
        have hfirst_le : (((1 + (0 : L2pos) (1 : ℕ+) : ℝ) : EReal) ≤ 1) := by
          rw [hcoord]
          norm_num
        exact hfirst_le
      have htop : (1 : EReal) < ⊤ := EReal.coe_lt_top 1
      exact ne_of_lt (lt_of_le_of_lt hraw_le_one htop)
  exact ⟨hgamma, hproper⟩

/-- Helper for Example 21.6: the raw owner takes the value `1` at the origin. -/
private theorem example21_6_rawEReal_zero :
    example21_6_rawEReal (0 : L2pos) = 1 := by
  have htail_zero :
      (⨆ n : ℕ+,
        if 2 ≤ (n : ℕ) then (((Real.sqrt (n : ℝ)) * (0 : L2pos) n : ℝ) : EReal)
        else (⊥ : EReal)) = 0 := by
    refine le_antisymm ?_ ?_
    · -- Every tail branch at the origin is at most `0`.
      refine iSup_le fun n ↦ ?_
      by_cases hn : 2 ≤ (n : ℕ)
      · have hcoord : (0 : L2pos) n = 0 := by rfl
        have hterm_le : (((Real.sqrt (n : ℝ)) * (0 : L2pos) n : ℝ) : EReal) ≤ 0 := by
          rw [hcoord]
          simp
        simpa [hn] using hterm_le
      · simp [hn]
    · -- The active branch at `n = 2` already attains `0`.
      have hcoord : (0 : L2pos) (2 : ℕ+) = 0 := by rfl
      have hterm :
          (((Real.sqrt ((2 : ℕ+) : ℝ)) * (0 : L2pos) (2 : ℕ+) : ℝ) : EReal) = 0 := by
        rw [hcoord]
        simp
      rw [← hterm]
      simpa [show 2 ≤ (((2 : ℕ+) : ℕ)) by norm_num] using
        (le_iSup
          (fun n : ℕ+ ↦
            if 2 ≤ (n : ℕ) then (((Real.sqrt (n : ℝ)) * (0 : L2pos) n : ℝ) : EReal)
            else (⊥ : EReal))
          (2 : ℕ+))
  -- With the tail supremum normalized to `0`, the first branch gives the value `1`.
  have hcoord : (0 : L2pos) (1 : ℕ+) = 0 := by rfl
  have hfirst : (((1 + (0 : L2pos) (1 : ℕ+) : ℝ) : EReal)) = 1 := by
    rw [hcoord]
    norm_num
  rw [example21_6_rawEReal, htail_zero, hfirst]
  simp

/-- Helper for Example 21.6: the function value at the origin is `1`. -/
private theorem example21_6_apply_zero :
    (example_21_6_l2_counterexample_function (0 : L2pos) : EReal) = 1 := by
  -- Identify the packaged owner with the raw `EReal` formula at the origin.
  simpa [example_21_6_l2_counterexample_function_apply, example21_6_rawEReal] using
    example21_6_rawEReal_zero

/-- Helper for Example 21.6: the function value at `-e₁` is `0`. -/
private theorem example21_6_apply_neg_basis_one :
    (example_21_6_l2_counterexample_function (-example21_6_basisVector 1) : EReal) = 0 := by
  have htail_zero :
      (⨆ n : ℕ+,
        if 2 ≤ (n : ℕ) then
          (((Real.sqrt (n : ℝ)) * (-example21_6_basisVector 1 : L2pos) n : ℝ) : EReal)
        else (⊥ : EReal)) = 0 := by
    refine le_antisymm ?_ ?_
    · -- Every active tail coordinate vanishes because `-e₁` is supported only at `1`.
      refine iSup_le fun n ↦ ?_
      by_cases hn : 2 ≤ (n : ℕ)
      · have hne : n ≠ 1 := by
          have hnat : (n : ℕ) ≠ 1 := by
            omega
          intro h
          exact hnat (congrArg Subtype.val h)
        have hcoordBasis : (example21_6_basisVector 1 : L2pos) n = 0 := by
          simp [example21_6_basisVector, hne]
        have hcoord : (-example21_6_basisVector 1 : L2pos) n = 0 := by
          change -((example21_6_basisVector 1 : L2pos) n) = 0
          rw [hcoordBasis]
          norm_num
        have hterm_le :
            ((((Real.sqrt (n : ℝ)) * (-example21_6_basisVector 1 : L2pos) n : ℝ) : EReal) : EReal) ≤
              0 := by
          rw [hcoord]
          simp
        simpa [hn] using hterm_le
      · simp [hn]
    · -- The active tail branch at `n = 2` already gives the lower bound `0`.
      have hcoordBasis : (example21_6_basisVector 1 : L2pos) (2 : ℕ+) = 0 := by
        simp [example21_6_basisVector]
      have hcoord : (-example21_6_basisVector 1 : L2pos) (2 : ℕ+) = 0 := by
        change -((example21_6_basisVector 1 : L2pos) (2 : ℕ+)) = 0
        rw [hcoordBasis]
        norm_num
      have hterm :
          (((Real.sqrt ((2 : ℕ+) : ℝ)) * (-example21_6_basisVector 1 : L2pos) (2 : ℕ+) : ℝ) :
            EReal) = 0 := by
        rw [hcoord]
        simp
      rw [← hterm]
      simpa [show 2 ≤ (((2 : ℕ+) : ℕ)) by norm_num] using
        (le_iSup
          (fun n : ℕ+ ↦
            if 2 ≤ (n : ℕ) then
              (((Real.sqrt (n : ℝ)) * (-example21_6_basisVector 1 : L2pos) n : ℝ) : EReal)
            else (⊥ : EReal))
          (2 : ℕ+))
  have hcoordOne : (-example21_6_basisVector 1 : L2pos) (1 : ℕ+) = -1 := by
    change -((example21_6_basisVector 1 : L2pos) (1 : ℕ+)) = -1
    simp [example21_6_basisVector]
  have hfirst : (((1 + (-example21_6_basisVector 1 : L2pos) (1 : ℕ+) : ℝ) : EReal)) = 0 := by
    rw [hcoordOne]
    norm_num
  -- Both branches of the defining maximum evaluate to `0`.
  rw [example_21_6_l2_counterexample_function_apply, example21_6_rawEReal, hfirst, htail_zero]
  simp

/-- Helper for Example 21.6: the primal graph witness has function value `1`. -/
private theorem example21_6_apply_primalPoint (n : ℕ) :
    (example_21_6_l2_counterexample_function (example21_6_primalPoint n) : EReal) = 1 := by
  have hfirst : (((1 + example21_6_primalPoint n (1 : ℕ+) : ℝ) : EReal)) = 1 := by
    have hne : (1 : ℕ+) ≠ example21_6_tailIndex n := by
      intro h
      exact example21_6_tailIndex_ne_one n h.symm
    rw [example21_6_primalPoint_apply]
    simp [hne]
  have hactive_real :
      (Real.sqrt (((example21_6_tailIndex n : ℕ) : ℝ))) *
        example21_6_primalPoint n (example21_6_tailIndex n) = 1 := by
    have hpair := example21_6_inner_primalPoint_dualPoint n
    rw [example21_6_inner_dualPoint_right] at hpair
    simpa [example21_6_tailIndex] using hpair
  have htail_one :
      (⨆ m : ℕ+,
        if 2 ≤ (m : ℕ) then (((Real.sqrt (m : ℝ)) * example21_6_primalPoint n m : ℝ) : EReal)
        else (⊥ : EReal)) = 1 := by
    refine le_antisymm ?_ ?_
    · -- The primal witness has a single active tail coordinate, where the branch value is `1`.
      refine iSup_le fun m ↦ ?_
      by_cases hm2 : 2 ≤ (m : ℕ)
      · by_cases hm : m = example21_6_tailIndex n
        · subst hm
          simp [example21_6_tailIndex_two_le n, hactive_real]
        · have hcoord : example21_6_primalPoint n m = 0 := by
            rw [example21_6_primalPoint_apply]
            simp [hm]
          have hterm_le :
              ((((Real.sqrt (m : ℝ)) * example21_6_primalPoint n m : ℝ) : EReal) : EReal) ≤ 1 := by
            rw [hcoord]
            norm_num
          simpa [hm2] using hterm_le
      · simp [hm2]
    · -- The active tail coordinate attains the value `1`.
      rw [← show
        (if 2 ≤ ((example21_6_tailIndex n : ℕ)) then
          (((Real.sqrt (((example21_6_tailIndex n : ℕ) : ℝ))) *
              example21_6_primalPoint n (example21_6_tailIndex n) : ℝ) : EReal)
        else (⊥ : EReal)) = (1 : EReal) by
          simp [example21_6_tailIndex_two_le n, hactive_real]]
      exact le_iSup
        (fun m : ℕ+ ↦
          if 2 ≤ (m : ℕ) then (((Real.sqrt (m : ℝ)) * example21_6_primalPoint n m : ℝ) : EReal)
          else (⊥ : EReal))
        (example21_6_tailIndex n)
  -- Both branches of the defining maximum evaluate to `1`.
  rw [example_21_6_l2_counterexample_function_apply, example21_6_rawEReal, hfirst, htail_one]
  simp

/-- Helper for Example 21.6: the first affine branch is always bounded above by the full
function value. -/
private theorem example21_6_firstBranch_le (x : L2pos) :
    (((1 + x (1 : ℕ+) : ℝ) : EReal)) ≤
      (example_21_6_l2_counterexample_function x : EReal) := by
  -- This is the left branch of the defining maximum.
  rw [example_21_6_l2_counterexample_function_apply]
  exact le_max_left _ _

/-- Helper for Example 21.6: every active tail branch is bounded above by the full function
value. -/
private theorem example21_6_tailBranch_le (x : L2pos) (n : ℕ+) :
    (if 2 ≤ (n : ℕ) then (((Real.sqrt (n : ℝ)) * x n : ℝ) : EReal) else (⊥ : EReal)) ≤
      (example_21_6_l2_counterexample_function x : EReal) := by
  -- This is one of the branches contributing to the tail supremum inside the defining maximum.
  rw [example_21_6_l2_counterexample_function_apply]
  exact le_trans (le_iSup (fun m : ℕ+ ↦
    if 2 ≤ (m : ℕ) then (((Real.sqrt (m : ℝ)) * x m : ℝ) : EReal) else (⊥ : EReal)) n)
    (le_max_right _ _)

/-- Helper for Example 21.6: the weighted inverse squares associated with any shifted tail remain
non-summable. -/
private theorem example21_6_shiftedInvSq_eq_inv (N n : ℕ) :
    ((Real.sqrt (n + N + 2 : ℝ))⁻¹)^2 = ((n + N + 2 : ℝ)⁻¹) := by
  -- Rewrite the squared inverse square root as the inverse of the underlying shifted index.
  have hnonneg : 0 ≤ (n + N + 2 : ℝ) := by
    positivity
  rw [inv_pow, Real.sq_sqrt hnonneg]

/-- Helper for Example 21.6: the weighted inverse squares associated with any shifted tail remain
non-summable. -/
private theorem example21_6_shiftedInvSq_notSummable (N : ℕ) :
    ¬ Summable (fun n : ℕ => ((Real.sqrt (n + N + 2 : ℝ))⁻¹)^2) := by
  -- Normalize the shifted inverse-square sequence to the shifted harmonic sequence.
  intro hsummable
  have hshifted :
      Summable (fun n : ℕ ↦ ((n + N + 2 : ℝ)⁻¹)) := by
    refine hsummable.congr ?_
    intro n
    simpa [Nat.add_assoc] using example21_6_shiftedInvSq_eq_inv N n
  exact Real.not_summable_natCast_inv <|
    (summable_nat_add_iff (f := fun n : ℕ ↦ ((n : ℝ)⁻¹)) (N + 2)).1 <| by
      simpa [Nat.cast_add, add_assoc] using hshifted

/-- Helper for Example 21.6: shifting the dual witness rewrites it into the exact weighted-tail
normal form used by Example 3.33. -/
private theorem example21_6_shiftedDualPoint_eq_scaledTailBasis (N n : ℕ) :
    example21_6_dualPoint (n + N) =
      (Real.sqrt (n + N + 2 : ℝ) : ℝ) •
        example21_6_basisVector ⟨n + N + 2, by omega⟩ := by
  -- This normalizes the local witness family to the weighted orthonormal sequence of Example 3.33.
  simp [example21_6_dualPoint, example21_6_tailIndex, Nat.add_assoc]

/-- Helper for Example 21.6: every shifted weighted tail still has `0` in its weak closure. -/
private theorem example21_6_shiftedDual_zero_mem_closure (N : ℕ) :
    (0 : WeakSpace ℝ L2pos) ∈
      closure
        ((toWeakSpace ℝ L2pos) ''
          Set.range (fun n : ℕ ↦ example21_6_dualPoint (n + N))) := by
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
                α n • example21_6_basisVector ⟨n + N + 2, by omega⟩)) := by
    -- Route correction: consume Example 3.33 directly on the shifted weighted basis.
    exact
      (scaled_orthonormal_range_weaklySeqClosed_and_not_weaklyClosed
        (fun n : ℕ ↦ example21_6_basisVector ⟨n + N + 2, by omega⟩)
        (example21_6_tailBasis_orthonormal N) α hα_ge_one hα_mono hα_tendsto
        (example21_6_shiftedInvSq_notSummable N)).2.2.2.1
  -- Rewrite the weighted orthonormal range back to the concrete dual witnesses.
  simpa [α, example21_6_shiftedDualPoint_eq_scaledTailBasis] using hzero_mem

/-- Helper for Example 21.6: the dual witness defines the affine minorant touching `f` at the
matching primal witness. -/
private theorem example21_6_dualPoint_minorant_at_primalPoint (n : ℕ) (y : L2pos) :
    ((⟪y - example21_6_primalPoint n, example21_6_dualPoint n⟫_ℝ : EReal) +
        (example_21_6_l2_counterexample_function (example21_6_primalPoint n) : EReal)) ≤
      (example_21_6_l2_counterexample_function y : EReal) := by
  have htail :
      ((((Real.sqrt (((example21_6_tailIndex n : ℕ) : ℝ))) *
            y (example21_6_tailIndex n) : ℝ) : EReal)) ≤
        (example_21_6_l2_counterexample_function y : EReal) := by
    -- The active tail branch is one of the branches in the defining supremum.
    simpa [example21_6_tailIndex_two_le n] using
      example21_6_tailBranch_le y (example21_6_tailIndex n)
  have hinner :
      inner ℝ (y - example21_6_primalPoint n) (example21_6_dualPoint n) =
        Real.sqrt (n + 2 : ℝ) * y (example21_6_tailIndex n) - 1 := by
    -- Expanding the pairing isolates the active tail coordinate and the touching value `1`.
    rw [inner_sub_left, example21_6_inner_dualPoint_right,
      example21_6_inner_primalPoint_dualPoint]
  let a : ℝ := Real.sqrt (n + 2 : ℝ) * y (example21_6_tailIndex n)
  have hsum :
      ((((a - 1 : ℝ) : EReal)) + 1) = (((a : ℝ) : EReal)) := by
    change ((((a - 1 : ℝ) : EReal)) + (((1 : ℝ) : EReal))) = (((a : ℝ) : EReal))
    rw [← EReal.coe_add]
    congr 1
    ring
  calc
    ((⟪y - example21_6_primalPoint n, example21_6_dualPoint n⟫_ℝ : EReal) +
          (example_21_6_l2_counterexample_function (example21_6_primalPoint n) : EReal)) =
        ((((a - 1 : ℝ) : EReal)) + 1) := by
          rw [hinner, example21_6_apply_primalPoint]
    _ = (((a : ℝ) : EReal)) := hsum
    _ = ((((Real.sqrt (((example21_6_tailIndex n : ℕ) : ℝ))) *
            y (example21_6_tailIndex n) : ℝ) : EReal)) := by
          simp [a, example21_6_tailIndex]
    _ ≤ (example_21_6_l2_counterexample_function y : EReal) := htail

/-- Helper for Example 21.6: the dual witness at the primal witness is a subgradient. -/
private theorem example21_6_counterexamplePair_mem_graph (n : ℕ) :
    example21_6_dualPoint n ∈
      (∂ example_21_6_l2_counterexample_function) (example21_6_primalPoint n) := by
  -- The affine minorant from the dual witness is exactly the active tail branch.
  rw [mem_subdifferential_iff]
  intro y
  exact example21_6_dualPoint_minorant_at_primalPoint n y

/-- Helper for Example 21.6: the mixed graph image accumulates at `(0,0)` when the primal
variable is strong and the dual variable is weak. -/
private theorem example21_6_zeroMixed_mem_closure_graphImage :
    ((0 : L2pos), (0 : WeakSpace ℝ L2pos)) ∈
      closure
        ((Prod.map id (toWeakSpace ℝ L2pos)) ''
          gra (∂ example_21_6_l2_counterexample_function)) := by
  -- Route correction: replace the earlier subnet route by direct product-neighborhood assembly.
  rw [mem_closure_iff_nhds]
  intro s hs
  rcases mem_nhds_prod_iff.mp hs with ⟨V, hV, W, hW, hVW⟩
  rcases Metric.mem_nhds_iff.mp hV with ⟨r, hr_pos, hrV⟩
  have hnorm_tendsto :
      Tendsto (fun n : ℕ ↦ 1 / Real.sqrt (n + 2 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    -- The norms of the primal witnesses are reciprocal square roots of a shifted index.
    convert
      (tendsto_inv_atTop_zero.comp <|
        Real.tendsto_sqrt_atTop.comp <|
          (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))) using 1
    ext n
    simp [one_div, Nat.cast_add]
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hnorm_tendsto r hr_pos
  have hprimal_mem : ∀ n : ℕ, example21_6_primalPoint (n + N) ∈ V := by
    intro n
    have hsmall_scalar : dist (1 / Real.sqrt (n + N + 2 : ℝ)) 0 < r := by
      simpa [Nat.cast_add, add_assoc] using hN (n + N) (by omega)
    have hsmall_scalar' : (Real.sqrt (n + N + 2 : ℝ))⁻¹ < r := by
      have habs_lt : |(Real.sqrt (n + N + 2 : ℝ))⁻¹| < r := by
        simpa [one_div, Real.dist_eq] using hsmall_scalar
      have hnonneg_inv : 0 ≤ (Real.sqrt (n + N + 2 : ℝ))⁻¹ := by
        positivity
      simpa [abs_of_nonneg hnonneg_inv] using habs_lt
    have hsmall_norm : ‖example21_6_primalPoint (n + N)‖ < r := by
      simpa [example21_6_norm_primalPoint, one_div] using hsmall_scalar'
    exact hrV <| by
      show example21_6_primalPoint (n + N) ∈ Metric.ball (0 : L2pos) r
      simpa [Metric.mem_ball, dist_eq_norm] using hsmall_norm
  rcases (mem_closure_iff_nhds.mp (example21_6_shiftedDual_zero_mem_closure N)) W hW with
    ⟨w, hw⟩
  rcases hw with ⟨hwW, hwRange⟩
  rcases hwRange with ⟨z, hzRange, rfl⟩
  rcases hzRange with ⟨n, rfl⟩
  have hgraph :
      (example21_6_primalPoint (n + N), example21_6_dualPoint (n + N)) ∈
        gra (∂ example_21_6_l2_counterexample_function) := by
    -- The concrete witness pair lies in the graph by the subgradient computation above.
    simpa [SetValuedOperator.graph] using example21_6_counterexamplePair_mem_graph (n + N)
  refine ⟨(example21_6_primalPoint (n + N),
      toWeakSpace ℝ L2pos (example21_6_dualPoint (n + N))), ?_⟩
  constructor
  · -- The chosen witness hits the prescribed product neighborhood.
    exact hVW ⟨hprimal_mem n, hwW⟩
  · exact ⟨(example21_6_primalPoint (n + N), example21_6_dualPoint (n + N)), hgraph, rfl⟩

/-- Helper for Example 21.6: the origin does not belong to the graph of the subdifferential. -/
private theorem example21_6_zero_not_mem_graph :
    ((0 : L2pos), (0 : L2pos)) ∉ gra (∂ example_21_6_l2_counterexample_function) := by
  have hnot_argmin : (0 : L2pos) ∉ Argmin example_21_6_l2_counterexample_function := by
    intro hzero
    rw [mem_argmin_iff, isMinOn_univ_iff] at hzero
    have hcompare := hzero (-example21_6_basisVector 1)
    have hzero_val :
        (Function.asEReal example_21_6_l2_counterexample_function (0 : L2pos) : EReal) = 1 := by
      simpa using example21_6_apply_zero
    have hneg_val :
        (Function.asEReal example_21_6_l2_counterexample_function (-example21_6_basisVector 1) :
          EReal) = 0 := by
      simpa using example21_6_apply_neg_basis_one
    rw [hzero_val, hneg_val] at hcompare
    have hfalse : ¬ ((1 : EReal) ≤ 0) := by norm_num
    exact hfalse hcompare
  have hnot_zero : (0 : L2pos) ∉ (∂ example_21_6_l2_counterexample_function).zeros := by
    -- Fermat's rule turns the strict gap `f(-e₁) < f(0)` into nonmembership in the zero set.
    simpa [argmin_eq_zeros_subdifferential] using hnot_argmin
  simpa [SetValuedOperator.graph, SetValuedOperator.mem_zeros_iff] using hnot_zero

/-- Helper for Example 21.6: the tail supremum is always nonnegative. -/
private theorem example21_6_tailSup_nonneg (x : L2pos) :
    (0 : EReal) ≤
      (⨆ n : ℕ+,
        if 2 ≤ (n : ℕ) then (((Real.sqrt (n : ℝ)) * x n : ℝ) : EReal) else (⊥ : EReal)) := by
  let s : EReal :=
    ⨆ n : ℕ+,
      if 2 ≤ (n : ℕ) then (((Real.sqrt (n : ℝ)) * x n : ℝ) : EReal) else (⊥ : EReal)
  by_contra hs_nonneg
  have hs_lt_zero : s < 0 := lt_of_not_ge hs_nonneg
  have hbranch_two :
      ((((Real.sqrt ((2 : ℕ+) : ℝ)) * x (2 : ℕ+) : ℝ) : EReal)) ≤ s := by
    -- The second coordinate is an active branch of the tail supremum.
    simpa [s, show 2 ≤ (((2 : ℕ+) : ℕ)) by norm_num] using
      (le_iSup
        (fun n : ℕ+ ↦
          if 2 ≤ (n : ℕ) then (((Real.sqrt (n : ℝ)) * x n : ℝ) : EReal) else (⊥ : EReal))
        (2 : ℕ+))
  have hs_ne_bot : s ≠ ⊥ := by
    -- The tail supremum dominates a genuine real branch, so it cannot be `⊥`.
    exact ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe _) hbranch_two)
  have hs_ne_top : s ≠ ⊤ := by
    intro hs_top
    simp [hs_top] at hs_lt_zero
  have hs_toReal_eq : (((s.toReal : ℝ) : EReal)) = s := EReal.coe_toReal hs_ne_top hs_ne_bot
  have hs_real_lt_zero : s.toReal < 0 := by
    have : (((s.toReal : ℝ) : EReal)) < (0 : EReal) := by
      simpa [hs_toReal_eq] using hs_lt_zero
    exact_mod_cast this
  let ε : ℝ := -s.toReal / 2
  have hε_pos : 0 < ε := by
    dsimp [ε]
    linarith
  have hs_lt_negε : s < ((-ε : ℝ) : EReal) := by
    have hs_real_lt : s.toReal < -ε := by
      dsimp [ε]
      linarith
    have : (((s.toReal : ℝ) : EReal)) < (((-ε : ℝ) : EReal)) := by
      exact_mod_cast hs_real_lt
    simpa [hs_toReal_eq]
      using this
  let ψ : WeakSpace ℝ L2pos → ℝ := fun w ↦ inner ℝ ((toWeakSpace ℝ L2pos).symm w) x
  let W : Set (WeakSpace ℝ L2pos) := {w | |ψ w| < ε}
  have hW : W ∈ 𝓝 (0 : WeakSpace ℝ L2pos) := by
    -- Use the weakly continuous coordinate functional and an absolute-value ball around `0`.
    have hψ0 : ψ (0 : WeakSpace ℝ L2pos) = 0 := by
      simp [ψ]
    have hball : Metric.ball (ψ (0 : WeakSpace ℝ L2pos)) ε ∈ 𝓝 (ψ (0 : WeakSpace ℝ L2pos)) := by
      simpa [hψ0] using Metric.ball_mem_nhds (ψ (0 : WeakSpace ℝ L2pos)) hε_pos
    have hpre :
        ψ ⁻¹' Metric.ball (ψ (0 : WeakSpace ℝ L2pos)) ε ∈ 𝓝 (0 : WeakSpace ℝ L2pos) := by
      exact (weakSpace_continuous_inner_right x).continuousAt.preimage_mem_nhds hball
    simpa [W, ψ, hψ0, Metric.ball, Real.dist_eq] using hpre
  rcases (mem_closure_iff_nhds.mp (example21_6_shiftedDual_zero_mem_closure 0)) W hW with
    ⟨w, hw⟩
  rcases hw with ⟨hwW, hwRange⟩
  rcases hwRange with ⟨z, hzRange, rfl⟩
  rcases hzRange with ⟨n, rfl⟩
  have hbranch_le :
      ((((Real.sqrt (((example21_6_tailIndex n : ℕ) : ℝ))) *
            x (example21_6_tailIndex n) : ℝ) : EReal)) ≤ s := by
    -- Each concrete dual witness corresponds to one active branch of the tail supremum.
    simpa [s, example21_6_tailIndex_two_le n] using
      (le_iSup
        (fun m : ℕ+ ↦
          if 2 ≤ (m : ℕ) then (((Real.sqrt (m : ℝ)) * x m : ℝ) : EReal) else (⊥ : EReal))
        (example21_6_tailIndex n))
  have hbranch_real_lt :
      Real.sqrt (((example21_6_tailIndex n : ℕ) : ℝ)) * x (example21_6_tailIndex n) < -ε := by
    have hbranch_lt :
        ((((Real.sqrt (((example21_6_tailIndex n : ℕ) : ℝ))) *
              x (example21_6_tailIndex n) : ℝ) : EReal)) < (((-ε : ℝ) : EReal)) :=
      lt_of_le_of_lt hbranch_le hs_lt_negε
    exact_mod_cast hbranch_lt
  have hvalue_lt :
      ψ (toWeakSpace ℝ L2pos (example21_6_dualPoint n)) < -ε := by
    -- Evaluating the weak coordinate at the concrete dual witness recovers the active branch.
    simpa [ψ, real_inner_comm, example21_6_inner_dualPoint_right, example21_6_tailIndex] using
      hbranch_real_lt
  have hnot_mem : toWeakSpace ℝ L2pos (example21_6_dualPoint n) ∉ W := by
    intro hmem
    have habs_lt : |ψ (toWeakSpace ℝ L2pos (example21_6_dualPoint n))| < ε := hmem
    have habs_ge : ε ≤ |ψ (toWeakSpace ℝ L2pos (example21_6_dualPoint n))| := by
      have hneg : ψ (toWeakSpace ℝ L2pos (example21_6_dualPoint n)) < 0 :=
        lt_trans hvalue_lt (by linarith)
      rw [abs_of_neg hneg]
      linarith
    exact not_lt_of_ge habs_ge habs_lt
  exact hnot_mem hwW

/-- Helper for Example 21.6: `f(x)` is nonnegative and vanishes exactly on the coordinatewise
half-space from `(21.17)`. -/
private theorem example21_6_nonneg_and_eq_zero_iff (x : L2pos) :
    (0 : EReal) ≤ (example_21_6_l2_counterexample_function x : EReal) ∧
      ((example_21_6_l2_counterexample_function x : EReal) = 0 ↔
        x (1 : ℕ+) ≤ (-1 : ℝ) ∧ ∀ n : ℕ+, 2 ≤ (n : ℕ) → x n ≤ 0) := by
  let tailSup : EReal :=
    ⨆ n : ℕ+,
      if 2 ≤ (n : ℕ) then (((Real.sqrt (n : ℝ)) * x n : ℝ) : EReal) else (⊥ : EReal)
  have htail_nonneg : (0 : EReal) ≤ tailSup := by
    simpa [tailSup] using example21_6_tailSup_nonneg x
  have hnonneg : (0 : EReal) ≤ (example_21_6_l2_counterexample_function x : EReal) := by
    -- The active tail supremum is a nonnegative lower bound for the whole maximum.
    rw [example_21_6_l2_counterexample_function_apply, example21_6_rawEReal]
    exact le_trans htail_nonneg (le_max_right _ _)
  refine ⟨hnonneg, ?_⟩
  constructor
  · intro hx_zero
    have hfirst_le_zero :
        (((1 + x (1 : ℕ+) : ℝ) : EReal)) ≤ 0 := by
      calc
        (((1 + x (1 : ℕ+) : ℝ) : EReal)) ≤
            (example_21_6_l2_counterexample_function x : EReal) := example21_6_firstBranch_le x
        _ = 0 := hx_zero
    have htail_le_zero : tailSup ≤ 0 := by
      calc
        tailSup ≤ (example_21_6_l2_counterexample_function x : EReal) := by
          dsimp [tailSup]
          rw [example21_6_rawEReal]
          exact le_max_right _ _
        _ = 0 := hx_zero
    have htail_eq_zero : tailSup = 0 := le_antisymm htail_le_zero htail_nonneg
    refine ⟨?_, ?_⟩
    · -- The first branch vanishes only when the first coordinate is at most `-1`.
      have hfirst_real : 1 + x (1 : ℕ+) ≤ 0 := by
        exact EReal.coe_le_coe_iff.mp hfirst_le_zero
      linarith
    · intro n hn
      have hbranch_le_zero :
          ((((Real.sqrt (n : ℝ)) * x n : ℝ) : EReal)) ≤ 0 := by
        have hbranch_le_tail :
            (if 2 ≤ (n : ℕ) then (((Real.sqrt (n : ℝ)) * x n : ℝ) : EReal) else (⊥ : EReal)) ≤
              tailSup := by
          exact le_iSup
            (fun m : ℕ+ ↦
              if 2 ≤ (m : ℕ) then (((Real.sqrt (m : ℝ)) * x m : ℝ) : EReal) else (⊥ : EReal))
            n
        simp [hn] at hbranch_le_tail
        exact hbranch_le_tail.trans htail_eq_zero.le
      have hbranch_real : Real.sqrt (n : ℝ) * x n ≤ 0 := by
        exact_mod_cast hbranch_le_zero
      have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := by
        positivity
      nlinarith
  · intro hxcond
    rcases hxcond with ⟨hx₁, htail_coords⟩
    have hfirst_le_zero :
        (((1 + x (1 : ℕ+) : ℝ) : EReal)) ≤ 0 := by
      have hfirst_real : 1 + x (1 : ℕ+) ≤ 0 := by
        linarith
      exact EReal.coe_le_coe_iff.mpr hfirst_real
    have htail_le_zero : tailSup ≤ 0 := by
      refine iSup_le fun n ↦ ?_
      by_cases hn : 2 ≤ (n : ℕ)
      · have hbranch_real : Real.sqrt (n : ℝ) * x n ≤ 0 := by
          have hsqrt_nonneg : 0 ≤ Real.sqrt (n : ℝ) := by positivity
          nlinarith [htail_coords n hn]
        exact (by simpa [tailSup, hn] using (show ((((Real.sqrt (n : ℝ)) * x n : ℝ) : EReal)) ≤ 0 by
          exact_mod_cast hbranch_real))
      · simp [hn]
    have htail_eq_zero : tailSup = 0 := le_antisymm htail_le_zero htail_nonneg
    -- Once both branches are nonpositive and the tail branch is already nonnegative,
    -- the maximum is `0`.
    change
      max (((1 + x (1 : ℕ+) : ℝ) : EReal))
          (⨆ n : ℕ+,
            if 2 ≤ (n : ℕ) then (((Real.sqrt (n : ℝ)) * x n : ℝ) : EReal) else (⊥ : EReal)) = 0
    have htail_eq_zero' :
        (⨆ n : ℕ+,
          if 2 ≤ (n : ℕ) then (((Real.sqrt (n : ℝ)) * x n : ℝ) : EReal) else (⊥ : EReal)) = 0 := by
      simpa [tailSup] using htail_eq_zero
    rw [htail_eq_zero', max_eq_right hfirst_le_zero]

-- Semantic recall: `lean_leansearch` only surfaced the ambient weak-space closure API, and the
-- local Chapter 20 precedent encodes strong-weak graph closedness through `Prod.map id
-- (toWeakSpace ℝ H)`.

/-- Clause (1) of Example 21.6: the function from `(21.16)` belongs to `Γ₀(ℓ²(ℕ+, ℝ))`. -/
theorem example_21_6_l2_counterexample_function_mem_gamma_zero :
    example_21_6_l2_counterexample_function ∈ Γ₀(L2pos) := by
  rcases example21_6_rawEReal_mem_gamma_and_proper with ⟨hgamma, hproper⟩
  -- Package the raw owner through the canonical `properIoi` wrapper.
  simpa [example_21_6_l2_counterexample_function, properIoi] using
    properIoi_mem_gammaZero_of_mem_gamma hproper hgamma

/-- Clause (2) of Example 21.6: the subdifferential of the function from `(21.16)` is maximally
monotone. -/
theorem example_21_6_subdifferential_is_maximally_monotone :
    Maximal IsMonotone (∂ example_21_6_l2_counterexample_function) := by
  simpa using
    subdifferential_isMaximallyMonotone_of_mem_gammaZero
      example_21_6_l2_counterexample_function_mem_gamma_zero

/-- Example 21.6 (3): the graph of the subdifferential is not closed in the mixed topology with
strong convergence in the primal variable and weak convergence in the dual variable, encoded as the
image of the graph in `ℓ²(ℕ+, ℝ) × WeakSpace ℝ (ℓ²(ℕ+, ℝ))`. -/
theorem example_21_6_subdifferential_graph_not_closed_strong_weak :
    ¬ IsClosed
        ((Prod.map id (toWeakSpace ℝ L2pos)) '' gra (∂ example_21_6_l2_counterexample_function)) :=
  by
  intro hclosed
  have hzero_mem :
      ((0 : L2pos), (0 : WeakSpace ℝ L2pos)) ∈
        ((Prod.map id (toWeakSpace ℝ L2pos)) '' gra (∂ example_21_6_l2_counterexample_function)) :=
    by
      rw [← hclosed.closure_eq]
      exact example21_6_zeroMixed_mem_closure_graphImage
  rcases hzero_mem with ⟨⟨x, u⟩, hpGraph, hpEq⟩
  have hx : x = (0 : L2pos) := by
    exact congrArg Prod.fst hpEq
  have hu : u = (0 : L2pos) := by
    apply (toWeakSpace ℝ L2pos).injective
    exact congrArg Prod.snd hpEq
  have hp_zero : ((0 : L2pos), (0 : L2pos)) ∈ gra (∂ example_21_6_l2_counterexample_function) := by
    simpa [hx, hu] using hpGraph
  exact example21_6_zero_not_mem_graph hp_zero

/-- Clause (4) of Example 21.6: the minimizers of the function from `(21.16)` are exactly the
sequences
whose first coordinate is at most `-1` and whose remaining coordinates are all nonpositive. -/
theorem example_21_6_argmin_eq :
    Argmin example_21_6_l2_counterexample_function =
      {x : L2pos | x (1 : ℕ+) ≤ (-1 : ℝ) ∧ ∀ n : ℕ+, 2 ≤ (n : ℕ) → x n ≤ 0} := by
  ext x
  constructor
  · intro hx
    rw [mem_argmin_iff, isMinOn_univ_iff] at hx
    have hle_zero : (example_21_6_l2_counterexample_function x : EReal) ≤ 0 := by
      calc
        (example_21_6_l2_counterexample_function x : EReal) ≤
            (example_21_6_l2_counterexample_function (-example21_6_basisVector 1) : EReal) :=
          hx (-example21_6_basisVector 1)
        _ = 0 := example21_6_apply_neg_basis_one
    have hnonneg := (example21_6_nonneg_and_eq_zero_iff x).1
    have hx_zero : (example_21_6_l2_counterexample_function x : EReal) = 0 :=
      le_antisymm hle_zero hnonneg
    exact ((example21_6_nonneg_and_eq_zero_iff x).2).1 hx_zero
  · intro hx
    rw [mem_argmin_iff, isMinOn_univ_iff]
    intro y
    have hy_nonneg := (example21_6_nonneg_and_eq_zero_iff y).1
    have hx_zero : (example_21_6_l2_counterexample_function x : EReal) = 0 :=
      ((example21_6_nonneg_and_eq_zero_iff x).2).2 hx
    calc
      (example_21_6_l2_counterexample_function x : EReal) = 0 := hx_zero
      _ ≤ (example_21_6_l2_counterexample_function y : EReal) := hy_nonneg

end

end ERealFunction
