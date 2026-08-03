import Mathlib
import BauschkeLean.Chap01.Definition_1_8
import BauschkeLean.Chap09.Example_9_43
import BauschkeLean.Chap11.Definition_11_3

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open Set

namespace ERealFunction

local notation "q" => (fun y : ℝ × ℝ ↦ (normPowerPerspectiveAtOrigin 2 y : EReal))

/-- Helper for Example 11 23: the quadratic specialization satisfies the required hypothesis
`1 < 2`. -/
private theorem one_lt_two_real : (1 : ℝ) < 2 := by
  norm_num

/-- Helper for Example 11 23: specializing `normPowerPerspectiveAtOrigin` to `p = 2` gives the
explicit quadratic-perspective branch formula. -/
@[simp] private theorem quadraticPerspective_apply (z : ℝ × ℝ) :
    q z =
      if 0 < z.1 then
        ((‖z.2‖ ^ (2 : ℝ) / z.1 : ℝ) : EReal)
    else if z = ((0 : ℝ), (0 : ℝ)) then
      0
    else
      ⊤ := by
  change (normPowerPerspectiveAtOrigin 2 z : EReal) =
    if 0 < z.1 then
      ((‖z.2‖ ^ (2 : ℝ) / z.1 : ℝ) : EReal)
    else if z = ((0 : ℝ), (0 : ℝ)) then
      0
    else
      ⊤
  convert normPowerPerspectiveAtOrigin_apply (H := ℝ) 2 one_lt_two_real z using 1
  simp [show ((2 : ℝ) - 1) = 1 by norm_num, Real.rpow_one]

/-- Helper for Example 11 23: the quadratic perspective is bounded below by `0`. -/
private theorem quadraticPerspective_nonneg (z : ℝ × ℝ) :
    (0 : EReal) ≤ q z := by
  -- Split according to the explicit branch formula.
  by_cases hz1 : 0 < z.1
  · rw [quadraticPerspective_apply, if_pos hz1]
    exact EReal.coe_nonneg.mpr <|
      div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hz1.le
  · rw [quadraticPerspective_apply, if_neg hz1]
    by_cases hz : z = ((0 : ℝ), (0 : ℝ))
    · simp [hz]
    · simp [hz]

/-- Helper for Example 11 23: the quadratic perspective vanishes exactly on the nonnegative
horizontal axis. -/
private theorem quadraticPerspective_eq_zero_iff (z : ℝ × ℝ) :
    q z = 0 ↔ z ∈ Set.Ici (0 : ℝ) ×ˢ ({0} : Set ℝ) := by
  by_cases hz1 : 0 < z.1
  · -- On the positive branch, vanishing forces the numerator `‖z.2‖^2` to vanish.
    rw [quadraticPerspective_apply, if_pos hz1]
    constructor
    · intro hz
      have hdiv : ‖z.2‖ ^ (2 : ℝ) / z.1 = 0 := by
        simpa using hz
      have hpow_zero : ‖z.2‖ ^ (2 : ℝ) = 0 := by
        rcases (div_eq_zero_iff).1 hdiv with hpow_zero | hz1_zero
        · exact hpow_zero
        · exact False.elim ((ne_of_gt hz1) hz1_zero)
      have hnorm_zero : ‖z.2‖ = 0 := by
        by_contra hnorm_zero
        have hnorm_pos : 0 < ‖z.2‖ := by
          exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnorm_zero)
        have hpow_pos : 0 < ‖z.2‖ ^ (2 : ℝ) :=
          Real.rpow_pos_of_pos hnorm_pos 2
        exact hpow_pos.ne' hpow_zero
      refine ⟨hz1.le, ?_⟩
      simpa [Set.mem_singleton_iff, norm_eq_zero] using hnorm_zero
    · rintro ⟨hz1_nonneg, hz2_mem⟩
      have hz2 : z.2 = 0 := by simpa using hz2_mem
      -- Once the second coordinate is zero, the positive branch evaluates to `0`.
      simp [hz2]
  · constructor
    · intro hqz
      rw [quadraticPerspective_apply, if_neg hz1] at hqz
      by_cases hz_origin : z = ((0 : ℝ), (0 : ℝ))
      · subst hz_origin
        simp
      · have htop : (⊤ : EReal) = 0 := by
          simp [hz_origin] at hqz
        exact False.elim (EReal.top_ne_zero htop)
    · rintro ⟨hz1_nonneg, hz2_mem⟩
      have hz2 : z.2 = 0 := by simpa using hz2_mem
      have hz1_zero : z.1 = 0 := by
        exact le_antisymm (le_of_not_gt hz1) hz1_nonneg
      have hz : z = ((0 : ℝ), (0 : ℝ)) := by
        ext <;> simp [hz1_zero, hz2]
      -- Outside the positive branch, the only zero-value point is the origin.
      subst z
      simp

/-- Helper for Example 11 23: the global infimum of the quadratic perspective is attained at the
origin and equals `0`. -/
private theorem quadraticPerspective_sInf_eq_zero_aux :
    sInf (Set.range q) = 0 := by
  have hzero_lb : ∀ y ∈ Set.range q, (0 : EReal) ≤ y := by
    rintro y ⟨z, rfl⟩
    exact quadraticPerspective_nonneg z
  have horigin : q ((0 : ℝ), (0 : ℝ)) = 0 := by
    simp
  have hsInf_le : sInf (Set.range q) ≤ 0 := by
    exact (isGLB_sInf (Set.range q)).1 ⟨((0 : ℝ), (0 : ℝ)), horigin⟩
  have hzero_le : (0 : EReal) ≤ sInf (Set.range q) := by
    exact (isGLB_sInf (Set.range q)).2 hzero_lb
  exact le_antisymm hsInf_le hzero_le

/-- Helper for Example 11 23: for a positive base, cancelling the extra quadratic factor in the
sequence evaluation leaves the reciprocal power. -/
private theorem sq_div_rpow_add_two_eq_inv_rpow {a p : ℝ} (ha : 0 < a) :
    a ^ (2 : ℝ) / a ^ (p + 2) = 1 / a ^ p := by
  have hpow_ne : a ^ p ≠ 0 := (Real.rpow_pos_of_pos ha p).ne'
  have htwo_ne : a ^ (2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos ha 2).ne'
  calc
    a ^ (2 : ℝ) / a ^ (p + 2) = a ^ (2 : ℝ) / (a ^ p * a ^ (2 : ℝ)) := by
      rw [Real.rpow_add ha]
    _ = 1 / a ^ p := by
      field_simp [hpow_ne, htwo_ne]

/-- Helper for Example 11 23: above the horizontal axis, the product-max distance to the
nonnegative horizontal axis is exactly the absolute vertical displacement. -/
private theorem infDist_nonnegative_horizontal_axis_eq_abs_snd {a b : ℝ} (ha : 0 ≤ a) :
    Metric.infDist (a, b) (Set.Ici (0 : ℝ) ×ˢ ({0} : Set ℝ)) = |b| := by
  have hmem : (a, (0 : ℝ)) ∈ Set.Ici (0 : ℝ) ×ˢ ({0} : Set ℝ) := by
    exact ⟨ha, by simp⟩
  refine le_antisymm ?_ ?_
  · -- The point `(a, 0)` realizes the vertical displacement upper bound.
    simpa [Prod.dist_eq, Real.dist_eq] using
      (Metric.infDist_le_dist_of_mem (x := (a, b)) hmem)
  · -- Every point on the horizontal axis stays at least `|b|` away in the max metric.
    rw [Metric.le_infDist
      (x := (a, b)) (s := Set.Ici (0 : ℝ) ×ˢ ({0} : Set ℝ)) ⟨(a, 0), hmem⟩]
    intro y hy
    have hy2 : y.2 = 0 := by simpa using hy.2
    simp [Prod.dist_eq, Real.dist_eq, hy2]

/- Example 11.23: the closed quadratic perspective is exactly the specialization `p = 2` of the
canonical `Γ₀` theorem `normPowerPerspectiveAtOrigin_mem_gammaZero` from Example 9.43. -/
#check (normPowerPerspectiveAtOrigin_mem_gammaZero 2 one_lt_two_real :
    normPowerPerspectiveAtOrigin 2 ∈ Γ₀(ℝ × ℝ))

-- Proof sketch: show that the global minimizers are exactly the points where the quadratic
-- perspective takes its minimal value `0`, namely the nonnegative horizontal axis.
/-- The minimizers of the quadratic perspective are exactly `ℝ₊ × {0}`. -/
theorem quadraticPerspectiveArgmin_eq :
    Argmin q =
      Set.Ici (0 : ℝ) ×ˢ ({0} : Set ℝ) := by
  ext z
  -- `Argmin` is the zero set because the infimum of the range is `0`.
  rw [mem_argmin_iff_eq_sInf, quadraticPerspective_sInf_eq_zero_aux,
    quadraticPerspective_eq_zero_iff]

-- Proof sketch: evaluate the explicit branch formula at the origin to see that the infimum is
-- attained there and equals `0`.
/-- The infimum of the quadratic perspective is `0`. -/
theorem quadraticPerspective_sInf_eq_zero :
    sInf (Set.range q) = 0 := by
  -- The auxiliary `sInf` computation is exactly the main statement here.
  exact quadraticPerspective_sInf_eq_zero_aux

/-- The sequence used in Example 11.23. -/
noncomputable def example11_23Sequence (p : ℝ) : ℕ → ℝ × ℝ :=
  fun n ↦ (((n + 1 : ℝ) ^ (p + 2)), (n + 1 : ℝ))

-- Proof sketch: unfold `example11_23Sequence`, substitute the sequence coordinates into the
-- explicit formula for `normPowerPerspectiveAtOrigin` at `p = 2`, and simplify
-- `(n + 1)^2 / (n + 1)^(p + 2) = 1 / (n + 1)^p`.
/-- Along the Example 11.23 sequence, the quadratic perspective has the exact value
`1 / (n + 1)^p`. -/
theorem quadraticPerspective_value_example11_23Sequence
    (p : ℝ) (n : ℕ) :
    q (example11_23Sequence p n) =
      ((1 / ((n + 1 : ℝ) ^ p) : ℝ) : EReal) := by
  have hbase_pos : 0 < (n + 1 : ℝ) := by
    positivity
  have hfst_pos : 0 < (n + 1 : ℝ) ^ (p + 2) := by
    exact Real.rpow_pos_of_pos hbase_pos _
  -- Along the textbook sequence, the first coordinate is positive, so only the finite branch
  -- of the quadratic perspective contributes.
  rw [example11_23Sequence, quadraticPerspective_apply, if_pos hfst_pos]
  simpa [Real.norm_of_nonneg hbase_pos.le] using
    congrArg (fun t : ℝ ↦ (t : EReal))
      (sq_div_rpow_add_two_eq_inv_rpow (a := (n + 1 : ℝ)) (p := p) hbase_pos)

-- Proof sketch: combine the previous value formula with `quadraticPerspective_sInf_eq_zero` and
-- the convergence of `n ↦ 1 / (n + 1)^p` to `0` for `p ≥ 1`.
/-- For every `p ≥ 1`, the textbook sequence is a minimizing sequence of the quadratic
perspective. -/
theorem example11_23Sequence_isMinimizing
    (p : ℝ) (hp : 1 ≤ p) :
    IsMinimizingSequence q (example11_23Sequence p) := by
  rw [isMinimizingSequence_iff_lt_top]
  refine ⟨?_, ?_⟩
  · intro n
    change q (example11_23Sequence p n) < ⊤
    rw [quadraticPerspective_value_example11_23Sequence]
    exact EReal.coe_lt_top _
  · have hp_pos : 0 < p := by
      linarith
    have hshift : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop := by
      exact tendsto_atTop_add_const_right Filter.atTop 1 tendsto_natCast_atTop_atTop
    have hpow :
        Tendsto (fun n : ℕ ↦ ((n + 1 : ℝ) ^ p)) atTop atTop := by
      exact (tendsto_rpow_atTop hp_pos).comp hshift
    have hinv :
        Tendsto (fun n : ℕ ↦ (1 / ((n + 1 : ℝ) ^ p) : ℝ)) atTop (nhds (0 : ℝ)) := by
      simpa [one_div] using hpow.inv_tendsto_atTop
    have hcoe :
        Tendsto
          (fun n : ℕ ↦ (((1 / ((n + 1 : ℝ) ^ p) : ℝ) : EReal)))
          atTop (nhds (0 : EReal)) :=
      EReal.tendsto_coe.2 hinv
    have hvalues :
        q ∘ example11_23Sequence p =
          fun n : ℕ ↦ (((1 / ((n + 1 : ℝ) ^ p) : ℝ) : EReal)) := by
      funext n
      exact quadraticPerspective_value_example11_23Sequence p n
    -- The explicit value formula turns the minimizing-sequence limit into the reciprocal-power
    -- limit toward the infimum `0`.
    rw [hvalues, quadraticPerspective_sInf_eq_zero]
    exact hcoe

-- Proof sketch: use the description `Argmin f = ℝ₊ × {0}` and observe that the
-- point `((n + 1)^(p + 2), 0)` lies in that set and realizes the distance from
-- `((n + 1)^(p + 2), n + 1)` to the horizontal axis.
/-- The distance from the Example 11.23 sequence to the minimizer set is exactly `n + 1`. -/
theorem example11_23Sequence_infDist_argmin
    (p : ℝ) (n : ℕ) :
    Metric.infDist (example11_23Sequence p n)
      (Argmin q) = n + 1 := by
  have hfst_nonneg : 0 ≤ (example11_23Sequence p n).1 := by
    dsimp [example11_23Sequence]
    exact (Real.rpow_nonneg (by positivity : 0 ≤ (n + 1 : ℝ)) _)
  -- Replacing `Argmin q` by the horizontal axis reduces the set distance to the vertical gap.
  rw [quadraticPerspectiveArgmin_eq]
  simpa [example11_23Sequence, abs_of_nonneg (by positivity : 0 ≤ (n + 1 : ℝ))] using
    infDist_nonnegative_horizontal_axis_eq_abs_snd
      (a := (example11_23Sequence p n).1) (b := (example11_23Sequence p n).2) hfst_nonneg

-- Proof sketch: compare the norm distance to any minimizer with the exact set distance from the
-- previous theorem, then use that `n + 1 → +∞`.
/-- The Example 11.23 sequence diverges away from every minimizer of the quadratic perspective. -/
theorem tendsto_norm_sub_of_mem_quadraticPerspectiveArgmin
    (p : ℝ) {x : ℝ × ℝ}
    (hx : x ∈ Argmin q) :
    Tendsto (fun n ↦ ‖example11_23Sequence p n - x‖) atTop atTop := by
  have hlower :
      ∀ n : ℕ, (n + 1 : ℝ) ≤ ‖example11_23Sequence p n - x‖ := by
    intro n
    have hdist :
        Metric.infDist (example11_23Sequence p n) (Argmin q) ≤
          dist (example11_23Sequence p n) x :=
      Metric.infDist_le_dist_of_mem (x := example11_23Sequence p n) hx
    rw [example11_23Sequence_infDist_argmin] at hdist
    simpa [dist_eq_norm] using hdist
  -- The exact distance lower bound grows like `n + 1`, so the norm difference also tends to
  -- `+∞`.
  have hshift : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop := by
    exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact Filter.tendsto_atTop_mono hlower hshift

-- Proof sketch: combine the minimizing-sequence result with the divergence statement for every
-- minimizer.
/-- Example 11 23: for every `p ≥ 1`, the textbook sequence minimizes the quadratic perspective,
while its distance to each minimizer diverges to `+∞`. -/
theorem example11_23_minimizingSequence_and_tendsto_norm_sub
    (p : ℝ) (hp : 1 ≤ p) :
    IsMinimizingSequence q (example11_23Sequence p) ∧
      ∀ {x : ℝ × ℝ}, x ∈ Argmin q →
        Tendsto (fun n ↦ ‖example11_23Sequence p n - x‖) atTop atTop := by
  refine ⟨example11_23Sequence_isMinimizing p hp, ?_⟩
  intro x hx
  exact tendsto_norm_sub_of_mem_quadraticPerspectiveArgmin p hx

end ERealFunction
