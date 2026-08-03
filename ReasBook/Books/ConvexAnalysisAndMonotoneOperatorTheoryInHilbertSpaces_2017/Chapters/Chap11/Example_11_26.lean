import Mathlib
import BauschkeLean.Chap01.Definition_1_8
import BauschkeLean.Chap11.Definition_11_3

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open Set
open scoped InnerProductSpace Topology

universe u

namespace ERealFunction

variable {H : Type u}

section

variable [AddCommGroup H] [Module ℝ H]

/-- Helper for Example 11 26: each term of the alternating sequence is one of the two endpoints
`x` or `-x`. -/
lemma alternating_sequence_eq_self_or_neg (x : H) (n : ℕ) :
    ((-1 : ℝ) ^ n) • x = x ∨ ((-1 : ℝ) ^ n) • x = -x := by
  -- Reduce the scalar `(-1)^n` to the two possible values `1` and `-1`.
  rcases neg_one_pow_eq_or ℝ n with hpow | hpow
  · left
    simp [hpow]
  · right
    simp [hpow]

/-- Helper for Example 11 26: the symmetric-segment indicator has infimum `0` on its range. -/
lemma sInf_range_symmetricSegmentIndicator_eq_zero (x : H) :
    sInf (Set.range (ι[segment ℝ (-x) x]).asEReal) = (0 : EReal) := by
  -- The right endpoint belongs to the segment, so the value `0` is attained.
  have hzero_mem : (0 : EReal) ∈ Set.range (ι[segment ℝ (-x) x]).asEReal := by
    refine ⟨x, ?_⟩
    simp [Function.asEReal_apply, indicator_apply, right_mem_segment]
  have hsInf_le_zero : sInf (Set.range (ι[segment ℝ (-x) x]).asEReal) ≤ (0 : EReal) :=
    (isGLB_sInf (Set.range (ι[segment ℝ (-x) x]).asEReal)).1 hzero_mem
  have hzero_le_sInf : (0 : EReal) ≤ sInf (Set.range (ι[segment ℝ (-x) x]).asEReal) := by
    -- Every indicator value is either `0` or `⊤`, so `0` is a lower bound.
    refine (isGLB_sInf (Set.range (ι[segment ℝ (-x) x]).asEReal)).2 ?_
    intro z hz
    rcases hz with ⟨y, rfl⟩
    by_cases hy : y ∈ segment ℝ (-x) x
    · simp [Function.asEReal_apply, indicator_apply, hy]
    · simp [Function.asEReal_apply, indicator_apply, hy]
  exact le_antisymm hsInf_le_zero hzero_le_sInf

/-- Helper for Example 11 26: the even subsequence of the alternating sequence is constantly
`x`. -/
lemma alternating_sequence_even (x : H) (n : ℕ) :
    ((-1 : ℝ) ^ (2 * n)) • x = x := by
  -- Even powers of `-1` are `1`, so the scalar action collapses to the identity.
  have hpow : (-1 : ℝ) ^ (2 * n) = 1 := by
    exact Even.neg_one_pow (show Even (2 * n) from even_two.mul_right n)
  simp [hpow]

/-- Helper for Example 11 26: the odd subsequence of the alternating sequence is constantly
`-x`. -/
lemma alternating_sequence_odd (x : H) (n : ℕ) :
    ((-1 : ℝ) ^ (2 * n + 1)) • x = -x := by
  -- Split the odd exponent into an even part and one extra factor `-1`.
  calc
    ((-1 : ℝ) ^ (2 * n + 1)) • x
        = (((-1 : ℝ) ^ (2 * n)) * ((-1 : ℝ) ^ 1)) • x := by
            rw [pow_add]
    _ = ((-1 : ℝ) ^ (2 * n)) • (((-1 : ℝ) ^ 1) • x) := by
          rw [mul_smul]
    _ = -x := by
          simp [pow_one]

-- Proof sketch: each term of `n ↦ ((-1 : ℝ) ^ n) • x` is one of the endpoints `x` or `-x`,
-- hence lies in `segment ℝ (-x) x`; therefore the indicator of that segment vanishes along the
-- whole sequence, so the function values converge to the infimum `0`.
/-- Example 11 26 (1): the alternating sequence `xₙ = (-1)^n x` is a minimizing sequence for the
indicator of the symmetric segment `[-x,x]`. -/
theorem alternatingSequence_isMinimizing_symmetricSegmentIndicator (x : H) :
    IsMinimizingSequence (ι[segment ℝ (-x) x]).asEReal
      (fun n : ℕ ↦ ((-1 : ℝ) ^ n) • x) := by
  rw [isMinimizingSequence_iff_lt_top]
  constructor
  · intro n
    -- Each sequence term lands at an endpoint of the segment, so the indicator value is `0`.
    rcases alternating_sequence_eq_self_or_neg x n with hterm | hterm
    · rw [hterm]
      simp [Function.asEReal_apply, indicator_apply, right_mem_segment]
    · rw [hterm]
      simp [Function.asEReal_apply, indicator_apply, left_mem_segment]
  · -- The indicator values are constantly `0`, so they converge to the range infimum `0`.
    have hvalue :
        ∀ n : ℕ, (ι[segment ℝ (-x) x]).asEReal (((-1 : ℝ) ^ n) • x) = (0 : EReal) := by
      intro n
      rcases alternating_sequence_eq_self_or_neg x n with hterm | hterm
      · rw [hterm]
        simp [Function.asEReal_apply, indicator_apply, right_mem_segment]
      · rw [hterm]
        simp [Function.asEReal_apply, indicator_apply, left_mem_segment]
    have hconst :
        (fun n : ℕ ↦ (ι[segment ℝ (-x) x]).asEReal (((-1 : ℝ) ^ n) • x)) =
          fun _ : ℕ ↦ (0 : EReal) := by
      funext n
      exact hvalue n
    have htendsto_zero :
        Tendsto ((ι[segment ℝ (-x) x]).asEReal ∘ fun n : ℕ ↦ ((-1 : ℝ) ^ n) • x) atTop
          (𝓝 (0 : EReal)) := by
      refine Tendsto.congr' ?_ (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : EReal)) atTop (𝓝 0))
      exact Filter.Eventually.of_forall fun n => by
        simpa [Function.comp] using (hvalue n).symm
    simpa [sInf_range_symmetricSegmentIndicator_eq_zero] using htendsto_zero

end

section

variable [NormedAddCommGroup H] [NormedSpace ℝ H]

-- Proof sketch: the range of `n ↦ ((-1 : ℝ) ^ n) • x` is contained in the two-point set
-- `{x, -x}`, and every finite set is bounded in a normed additive group.
/-- Example 11 26 (2): the alternating sequence `xₙ = (-1)^n x` has bounded range. -/
theorem alternatingSequence_isBounded (x : H) :
    Bornology.IsBounded (Set.range fun n : ℕ ↦ ((-1 : ℝ) ^ n) • x) := by
  have hsubset :
      Set.range (fun n : ℕ ↦ ((-1 : ℝ) ^ n) • x) ⊆ ({x} ∪ ({-x} : Set H)) := by
    intro y hy
    rcases hy with ⟨n, rfl⟩
    -- Each term is either `x` or `-x`, so the range is contained in the two-point set.
    rcases alternating_sequence_eq_self_or_neg x n with hterm | hterm
    · left
      simp [hterm]
    · right
      simp [hterm]
  have hpair_finite : (({x} : Set H) ∪ ({-x} : Set H)).Finite := by
    simp
  have hpair_bounded : Bornology.IsBounded (({x} : Set H) ∪ ({-x} : Set H)) :=
    hpair_finite.isBounded
  exact hpair_bounded.subset hsubset

end

section

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: if the alternating sequence converged weakly to some `y`, then its even
-- subsequence, which is constantly `x`, and its odd subsequence, which is constantly `-x`, would
-- both converge weakly to `y`; uniqueness of weak limits would force `x = -x`, hence `x = 0`,
-- contradicting the hypothesis.
/-- Example 11 26 (3): for `x ≠ 0`, the alternating sequence `xₙ = (-1)^n x` is not weakly
convergent. -/
theorem alternatingSequence_not_tendsto_weakly (x : H) (hx : x ≠ 0) :
    ¬ ∃ y : H,
      Tendsto (fun n ↦ toWeakSpace ℝ H (((-1 : ℝ) ^ n) • x)) atTop
        (𝓝 (toWeakSpace ℝ H y)) := by
  intro hconv
  rcases hconv with ⟨y, hy⟩
  have hEvenMono : StrictMono (fun n : ℕ ↦ 2 * n) := by
    intro m n hmn
    simpa [two_mul] using Nat.mul_lt_mul_of_pos_left hmn (by decide : 0 < 2)
  have hOddMono : StrictMono (fun n : ℕ ↦ 2 * n + 1) := by
    intro m n hmn
    exact Nat.add_lt_add_right (hEvenMono hmn) 1
  have hEvenTendsto : Tendsto (fun n : ℕ ↦ 2 * n) atTop atTop :=
    hEvenMono.tendsto_atTop
  have hOddTendsto : Tendsto (fun n : ℕ ↦ 2 * n + 1) atTop atTop :=
    hOddMono.tendsto_atTop
  have heven_comp :
      Tendsto ((fun n ↦ toWeakSpace ℝ H (((-1 : ℝ) ^ n) • x)) ∘ fun n : ℕ ↦ 2 * n) atTop
        (𝓝 (toWeakSpace ℝ H y)) := by
    simpa using hy.comp hEvenTendsto
  have hodd_comp :
      Tendsto ((fun n ↦ toWeakSpace ℝ H (((-1 : ℝ) ^ n) • x)) ∘ fun n : ℕ ↦ 2 * n + 1) atTop
        (𝓝 (toWeakSpace ℝ H y)) := by
    simpa using hy.comp hOddTendsto
  have heven_eq :
      ((fun n ↦ toWeakSpace ℝ H (((-1 : ℝ) ^ n) • x)) ∘ fun n : ℕ ↦ 2 * n) =
        fun _ : ℕ ↦ toWeakSpace ℝ H x := by
    funext n
    simp [Function.comp]
  have hodd_eq :
      ((fun n ↦ toWeakSpace ℝ H (((-1 : ℝ) ^ n) • x)) ∘ fun n : ℕ ↦ 2 * n + 1) =
        fun _ : ℕ ↦ toWeakSpace ℝ H (-x) := by
    funext n
    simp [Function.comp, alternating_sequence_odd]
  have heven_lim :
      Tendsto (fun _ : ℕ ↦ toWeakSpace ℝ H x) atTop (𝓝 (toWeakSpace ℝ H y)) := by
    -- Composing with the even subsequence rewrites the sequence to the constant value `x`.
    rw [← heven_eq]
    exact heven_comp
  have hodd_lim :
      Tendsto (fun _ : ℕ ↦ toWeakSpace ℝ H (-x)) atTop (𝓝 (toWeakSpace ℝ H y)) := by
    -- Composing with the odd subsequence rewrites the sequence to the constant value `-x`.
    rw [← hodd_eq]
    exact hodd_comp
  have hx_lim :
      Tendsto (fun _ : ℕ ↦ toWeakSpace ℝ H x) atTop (𝓝 (toWeakSpace ℝ H x)) :=
    tendsto_const_nhds
  have hnegx_lim :
      Tendsto (fun _ : ℕ ↦ toWeakSpace ℝ H (-x)) atTop (𝓝 (toWeakSpace ℝ H (-x))) :=
    tendsto_const_nhds
  have hxy : toWeakSpace ℝ H x = toWeakSpace ℝ H y :=
    tendsto_nhds_unique hx_lim heven_lim
  have hnegxy : toWeakSpace ℝ H (-x) = toWeakSpace ℝ H y :=
    tendsto_nhds_unique hnegx_lim hodd_lim
  have hx_negx : toWeakSpace ℝ H x = toWeakSpace ℝ H (-x) := by
    calc
      toWeakSpace ℝ H x = toWeakSpace ℝ H y := hxy
      _ = toWeakSpace ℝ H (-x) := hnegxy.symm
  have hself_neg : x = -x := (toWeakSpace ℝ H).injective hx_negx
  have hsum_zero : x + x = 0 := by
    -- Substitute the second copy of `x` by `-x` and then cancel.
    calc
      x + x = x + -x := congrArg (fun z : H ↦ x + z) hself_neg
      _ = 0 := by simp
  have htwo_zero : (2 : ℝ) • x = 0 := by
    -- The identity `x = -x` forces the doubled vector to vanish.
    simpa [two_smul] using hsum_zero
  have hx_zero : x = 0 := by
    rcases smul_eq_zero.mp htwo_zero with htwo | hx0
    · norm_num at htwo
    · exact hx0
  exact hx hx_zero

end

end ERealFunction
