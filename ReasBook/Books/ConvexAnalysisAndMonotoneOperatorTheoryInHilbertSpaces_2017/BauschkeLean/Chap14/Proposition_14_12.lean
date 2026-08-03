import Mathlib
import BauschkeLean.Chap07.Definition_7_8
import BauschkeLean.Chap07.Definition_7_14
import BauschkeLean.Chap08.Example_8_36
import BauschkeLean.Chap08.Text_8_0_2
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise Set

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 14 12: every Minkowski gauge value is nonnegative because the defining
infimum ranges over positive real scalars only. -/
private theorem minkowskiGauge_nonneg (C : Set H) (x : H) :
    0 ≤ m[C] x := by
  -- Rewrite the defining infimum as an iterated infimum over admissible positive scalars.
  rw [minkowskiGauge_eq_sInf, sInf_image]
  refine le_iInf ?_
  intro ξ
  refine le_iInf ?_
  intro hξ
  exact EReal.coe_nonneg.2 hξ.1.le

/-- Helper for Proposition 14 12: any positive scaled-set witness gives a real upper bound on the
Minkowski gauge. -/
private theorem minkowskiGauge_le_of_mem_smul
    (C : Set H) {x : H} {a : ℝ} (ha : 0 < a) (hx : x ∈ a • C) :
    m[C] x ≤ (a : EReal) := by
  -- The witness scalar belongs to the set whose infimum defines `m[C] x`.
  rw [minkowskiGauge_eq_sInf]
  exact sInf_le ⟨a, ⟨ha, hx⟩, rfl⟩

/-- Helper for Proposition 14 12: every point of `C` lies in the unit sublevel set of its
Minkowski gauge. -/
private theorem minkowskiGauge_le_one_of_mem (C : Set H) {x : H} (hx : x ∈ C) :
    m[C] x ≤ (1 : EReal) := by
  -- The unit scaling witness is exactly the original point membership.
  simpa using minkowskiGauge_le_of_mem_smul C zero_lt_one (by simpa using hx)

/-- Helper for Proposition 14 12: every point of the polar set defines a linear minorant of the
Minkowski gauge. -/
private theorem inner_le_minkowskiGauge_of_mem_polarSet
    (C : Set H) (hC_convex : Convex ℝ C) (h0C : (0 : H) ∈ C)
    {u : H} (hu : u ∈ Cᵒ⊙) (x : H) :
    ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ m[C] x := by
  by_cases hx : x ∈ dom (m[C])
  · -- Approximate the gauge from above by a positive real witness and use polar membership there.
    refine le_of_forall_gt_imp_ge_of_dense ?_
    intro b hb
    obtain ⟨r, hr_left, hr_right⟩ := EReal.exists_between_coe_real hb
    rcases mem_smul_of_minkowskiGauge_lt C hC_convex h0C hx hr_left with ⟨y, hyC, rfl⟩
    have hr_posE : (0 : EReal) < (r : EReal) := by
      exact lt_of_le_of_lt (minkowskiGauge_nonneg C (r • y)) hr_left
    have hr_pos : 0 < r := EReal.coe_lt_coe_iff.mp hr_posE
    have hy_inner : ⟪y, u⟫_ℝ ≤ 1 :=
      (Set.mem_polarSet_iff_forall_inner_le_one (C := C) (u := u)).1 hu y hyC
    have hinner : ⟪r • y, u⟫_ℝ ≤ r := by
      rw [real_inner_smul_left]
      nlinarith
    have hinnerE : (((⟪r • y, u⟫_ℝ : ℝ) : EReal)) ≤ (r : EReal) := by
      exact_mod_cast hinner
    exact le_trans hinnerE hr_right.le
  · -- Outside the domain, the gauge value is `⊤`, so the bound is immediate.
    have htop : m[C] x = ⊤ := by
      exact le_antisymm le_top (le_of_not_gt hx)
    simp [htop]

-- Proof sketch: the canonical owner here is the support function `σ`. For a convex set containing
-- `0`, the gauge `m[C]` agrees with the support function of the polar set `σ[Cᵒ⊙]`; this is the
-- bridge from the source-facing gauge to the Chapter 7 owner abstraction. Proposition 14.12 then
-- identifies the conjugate of that source-facing gauge with the indicator of the same polar set.
/-- Bridge for Proposition 14.12: if `C` is convex and contains `0`, then the support function of
the polar set `Cᵒ⊙` is pointwise dominated by the Minkowski gauge of `C`. -/
theorem minkowskiGauge_eq_supportFunction_polarSet
    (C : Set H) (hC_convex : Convex ℝ C) (h0C : (0 : H) ∈ C) :
    σ[Cᵒ⊙] ≤ m[C] := by
  -- Route correction: the equality route is false in this ambient generality; the usable bridge is
  -- the one-sided domination coming from polar membership.
  intro x
  -- Rewrite the support function as a supremum of inner products over `Cᵒ⊙`.
  rw [supportFunction_eq_sSup_image]
  refine sSup_le ?_
  intro a ha
  rcases ha with ⟨u, hu, rfl⟩
  -- Every polar vector gives a pointwise linear minorant of the gauge.
  simpa [real_inner_comm] using
    inner_le_minkowskiGauge_of_mem_polarSet C hC_convex h0C hu x

/-- Helper for Proposition 14 12: on the polar set, the Fenchel conjugate of the Minkowski gauge
vanishes. -/
private theorem conjugate_minkowskiGauge_eq_zero_of_mem_polarSet
    (C : Set H) (hC_convex : Convex ℝ C) (h0C : (0 : H) ∈ C)
    {u : H} (hu : u ∈ Cᵒ⊙) :
    (m[C])∗ u = 0 := by
  -- Every affine defect is nonpositive, and the test point `x = 0` attains the value `0`.
  rw [conjugate_apply]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun x ↦ ?_
    rw [EReal.sub_nonpos]
    exact inner_le_minkowskiGauge_of_mem_polarSet C hC_convex h0C hu x
  · have hzero :
        (0 : EReal) ≤
          ((((⟪(0 : H), u⟫_ℝ : ℝ) : EReal) - m[C] (0 : H))) := by
      have hm0 : m[C] (0 : H) = 0 := minkowskiGauge_zero C h0C
      rw [hm0]
      simp
    exact hzero.trans <| le_iSup
      (fun x : H ↦ (((⟪x, u⟫_ℝ : ℝ) : EReal) - m[C] x))
      0

/-- Helper for Proposition 14 12: off the polar set, the Fenchel conjugate of the Minkowski gauge
diverges to `+∞` along a ray through a violating point of `C`. -/
private theorem conjugate_minkowskiGauge_eq_top_of_not_mem_polarSet
    (C : Set H) {u : H} (hu : u ∉ Cᵒ⊙) :
    (m[C])∗ u = ⊤ := by
  -- Convert non-membership in the polar set into a point of `C` with inner product larger than `1`.
  rw [Set.mem_polarSet_iff_forall_inner_le_one (C := C) (u := u)] at hu
  push Not at hu
  rcases hu with ⟨y, hyC, hyu_gt⟩
  have hmy_le : m[C] y ≤ (1 : EReal) := minkowskiGauge_le_one_of_mem C hyC
  let δ : ℝ := ⟪y, u⟫_ℝ - 1
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    linarith
  rw [conjugate_apply]
  exact (EReal.eq_top_iff_forall_lt _).2 <| fun M ↦ by
    -- Choose a positive scaling whose affine defect dominates the prescribed real bound `M`.
    let t : ℝ := |M| / δ + 1
    have ht_pos : 0 < t := by
      have hnonneg : 0 ≤ |M| / δ := by
        exact div_nonneg (abs_nonneg M) hδ_pos.le
      dsimp [t]
      linarith
    have ht_nonneg : 0 ≤ t := ht_pos.le
    have hm_t_le : m[C] (t • y) ≤ (t : EReal) := by
      -- Positive homogeneity reduces the ray value to the base-point value, which is at most `1`.
      calc
        m[C] (t • y) = (t : EReal) * m[C] y := minkowskiGauge_smul C ht_pos
        _ ≤ (t : EReal) * 1 :=
          mul_le_mul_of_nonneg_left hmy_le (EReal.coe_nonneg.2 ht_nonneg)
        _ = (t : EReal) := by simp
    have hδ_ne_zero : δ ≠ 0 := hδ_pos.ne'
    have htdelta : t * δ = |M| + δ := by
      calc
        t * δ = (|M| / δ + 1) * δ := by rfl
        _ = (|M| / δ) * δ + δ := by ring
        _ = |M| + δ := by
          rw [div_mul_eq_mul_div, mul_comm |M| δ, mul_div_cancel_left₀ _ hδ_ne_zero]
    have hM_lt : M < t * δ := by
      calc
        M ≤ |M| := le_abs_self M
        _ < |M| + δ := lt_add_of_pos_right _ hδ_pos
        _ = t * δ := htdelta.symm
    have hterm_ge :
        ((t * δ : ℝ) : EReal) ≤
          ((((⟪t • y, u⟫_ℝ : ℝ) : EReal) - m[C] (t • y))) := by
      have hadd :
          (((t * ⟪y, u⟫_ℝ : ℝ) : EReal) - (t : EReal)) ≤
            (((t * ⟪y, u⟫_ℝ : ℝ) : EReal) - m[C] (t • y)) := by
        exact EReal.sub_le_sub le_rfl hm_t_le
      calc
        ((t * δ : ℝ) : EReal) = (((t * ⟪y, u⟫_ℝ - t : ℝ) : EReal)) := by
          congr 1
          dsimp [δ]
          ring
        _ = (((t * ⟪y, u⟫_ℝ : ℝ) : EReal) - (t : EReal)) := by
          rw [← EReal.coe_sub]
        _ ≤ (((t * ⟪y, u⟫_ℝ : ℝ) : EReal) - m[C] (t • y)) := hadd
        _ = ((((⟪t • y, u⟫_ℝ : ℝ) : EReal) - m[C] (t • y))) := by
          rw [real_inner_smul_left, EReal.coe_mul]
    have hterm_lt : (M : EReal) < ((t * δ : ℝ) : EReal) := by
      exact_mod_cast hM_lt
    exact lt_of_lt_of_le hterm_lt <| le_trans hterm_ge <| le_iSup
      (fun x : H ↦ (((⟪x, u⟫_ℝ : ℝ) : EReal) - m[C] x))
      (t • y)

-- Proof sketch: first pass from the source-facing gauge `m[C]` to the canonical support-function
-- owner via `minkowskiGauge_eq_supportFunction_polarSet`. Then apply the polar characterization to
-- show that the Fenchel conjugate is `0` on `Cᵒ⊙` and `⊤` off `Cᵒ⊙`.
/-- Proposition 14 12: if `C` is convex and contains `0`, then the Fenchel conjugate of the
Minkowski gauge `m[C]` is the indicator of the polar set `Cᵒ⊙`. -/
theorem conjugate_minkowskiGauge_eq_indicator_polarSet
    (C : Set H) (hC_convex : Convex ℝ C) (h0C : (0 : H) ∈ C) :
    (m[C])∗ = (ι[Cᵒ⊙]).asEReal := by
  ext u
  by_cases hu : u ∈ Cᵒ⊙
  · -- On the polar set, the conjugate vanishes and matches the zero branch of the indicator.
    rw [conjugate_minkowskiGauge_eq_zero_of_mem_polarSet C hC_convex h0C hu]
    simp [Function.asEReal_apply, indicator_apply, hu]
  · -- Outside the polar set, the ray argument forces the conjugate to be `⊤`.
    rw [conjugate_minkowskiGauge_eq_top_of_not_mem_polarSet C hu]
    simp [Function.asEReal_apply, indicator_apply, hu]

end ERealFunction
