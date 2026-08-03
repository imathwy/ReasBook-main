import Mathlib
import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap08.Example_8_36
import BauschkeLean.Chap08.Text_8_0_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

open scoped Pointwise

section GaugeHelpers

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

/-- Helper for Corollary 14 13: any positive scaled-set witness gives a real upper bound on the
source-facing Minkowski gauge. -/
theorem minkowskiGauge_le_of_mem_smul
    (C : Set H) {x : H} {a : ℝ} (ha : 0 < a) (hx : x ∈ a • C) :
    m[C] x ≤ (a : EReal) := by
  -- The witness scalar `a` belongs to the set whose infimum defines the gauge.
  rw [minkowskiGauge_eq_sInf]
  exact sInf_le ⟨a, ⟨ha, hx⟩, rfl⟩

/-- Helper for Corollary 14 13: absorbency turns a strict real upper bound on `m[C] x` into a
concrete positive scaling witness below that bound. -/
theorem exists_mem_smul_of_minkowskiGauge_lt
    (C : Set H) (hC_absorbent : Absorbent ℝ C) {x : H} {r : ℝ}
    (hr : m[C] x < (r : EReal)) :
    ∃ a : ℝ, 0 < a ∧ a < r ∧ x ∈ a • C := by
  -- Rewrite to the defining infimum and extract an element below `r`.
  rw [minkowskiGauge_eq_sInf] at hr
  have hnonempty : (Real.toEReal '' {a : ℝ | 0 < a ∧ x ∈ a • C}).Nonempty := by
    rcases hC_absorbent.gauge_set_nonempty (x := x) with ⟨a, ha⟩
    refine ⟨(a : EReal), ?_⟩
    exact ⟨a, ha, rfl⟩
  rcases exists_lt_of_csInf_lt hnonempty hr with ⟨s, hs, hs_lt⟩
  rcases hs with ⟨a, ha, rfl⟩
  refine ⟨a, ha.1, ?_, ha.2⟩
  exact EReal.coe_lt_coe_iff.mp hs_lt

/-- Helper for Corollary 14 13: any strict real upper bound for `m[C] x` is also a strict upper
bound for mathlib's real-valued gauge when `C` is absorbent. -/
theorem gauge_lt_of_minkowskiGauge_lt
    (C : Set H) (hC_absorbent : Absorbent ℝ C) {x : H} {r : ℝ}
    (hr : m[C] x < (r : EReal)) :
    gauge C x < r := by
  -- A witness below `r` for `m[C] x` is also a witness for `gauge C x`.
  rcases exists_mem_smul_of_minkowskiGauge_lt C hC_absorbent hr with ⟨a, ha_pos, ha_lt, hx⟩
  exact (gauge_le_of_mem ha_pos.le hx).trans_lt ha_lt

/-- Helper for Corollary 14 13: any strict real upper bound for mathlib's gauge is also a strict
upper bound for the source-facing Minkowski gauge. -/
theorem minkowskiGauge_lt_of_gauge_lt
    (C : Set H) (hC_absorbent : Absorbent ℝ C) {x : H} {r : ℝ}
    (hr : gauge C x < r) :
    m[C] x < (r : EReal) := by
  -- Use the same scaled-set witness that certifies the strict bound for `gauge C x`.
  rcases exists_lt_of_gauge_lt hC_absorbent hr with ⟨a, ha_pos, ha_lt, hx⟩
  exact lt_of_le_of_lt (minkowskiGauge_le_of_mem_smul C ha_pos hx)
    (EReal.coe_lt_coe_iff.mpr ha_lt)

end GaugeHelpers

section ClosedLevelSet

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Helper for Corollary 14 13: every point of `C` lies in the level set `{x | m[C] x ≤ 1}`. -/
theorem minkowskiGauge_le_one_of_mem (C : Set H) {x : H} (hx : x ∈ C) :
    m[C] x ≤ (1 : EReal) := by
  -- The unit scaling witness is exactly the original point membership `x ∈ C`.
  simpa using minkowskiGauge_le_of_mem_smul C zero_lt_one (by simpa using hx)

/-- Helper for Corollary 14 13: a strict separating functional forces the Minkowski gauge above
`1`. -/
theorem one_lt_minkowskiGauge_of_strict_upper_bound
    (C : Set H) (hC_convex : Convex ℝ C) (h0C : (0 : H) ∈ C)
    {x : H} (f : StrongDual ℝ H) {u : ℝ}
    (huC : ∀ y ∈ C, f y < u) (hux : u < f x) :
    (1 : EReal) < m[C] x := by
  let a : ℝ := f x / u
  -- First normalize the separating inequality so the relevant scaling factor exceeds `1`.
  have hu_pos : 0 < u := by
    simpa using huC 0 h0C
  have ha_gt_one : 1 < a := by
    dsimp [a]
    rwa [one_lt_div hu_pos]
  have ha_pos : 0 < a := lt_trans zero_lt_one ha_gt_one
  -- Assuming `m[C] x ≤ 1` would force `x ∈ a • C`, contradicting strict separation.
  by_contra hnot
  have hm_le : m[C] x ≤ (1 : EReal) := le_of_not_gt hnot
  have hx_dom : x ∈ dom (m[C]) := by
    apply (mem_dom_iff _ _).2
    exact lt_of_le_of_lt hm_le (EReal.coe_lt_top 1)
  have hm_lt_a : m[C] x < (a : EReal) := by
    exact lt_of_le_of_lt hm_le (EReal.coe_lt_coe_iff.mpr ha_gt_one)
  have hx_mem : x ∈ a • C := mem_smul_of_minkowskiGauge_lt C hC_convex h0C hx_dom hm_lt_a
  rcases hx_mem with ⟨y, hyC, hyx⟩
  have hfy_lt : f y < u := huC y hyC
  have hfx_eq : f x = a * f y := by
    rw [← hyx, map_smul]
    rfl
  have hau : a * u = f x := by
    dsimp [a]
    field_simp [hu_pos.ne']
  have hcontr : f x < f x := by
    calc
      f x = a * f y := hfx_eq
      _ < a * u := by
        exact mul_lt_mul_of_pos_left hfy_lt ha_pos
      _ = f x := hau
  exact lt_irrefl _ hcontr

-- Proof sketch: the inclusion `C ⊆ lowerLevelSet (m[C]) 1` comes from the defining infimum of the
-- gauge. For the reverse inclusion, separate a point `x ∉ C` from the closed convex set `C` by a
-- continuous linear functional and use the resulting strict supporting inequality to force
-- `m[C] x > 1`.
/-- Corollary 14 13 (1): clause (i). If `C` is closed, convex, and contains `0`, then `C` is
exactly the lower level set `{x | m[C] x ≤ 1}` of its Minkowski gauge. -/
theorem lowerLevelSet_minkowskiGauge_one_eq_of_isClosed_of_convex_of_zero_mem
    (C : Set H) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (h0C : (0 : H) ∈ C) :
    lowerLevelSet (m[C]) 1 = C := by
  -- Prove the two inclusions separately: one from the unit witness, one from closed-set separation.
  ext x
  constructor
  · intro hx
    rw [mem_lowerLevelSet_iff] at hx
    by_contra hxC
    rcases geometric_hahn_banach_closed_point hC_convex hC_closed hxC with ⟨f, u, huC, hux⟩
    have hm_gt : (1 : EReal) < m[C] x :=
      one_lt_minkowskiGauge_of_strict_upper_bound C hC_convex h0C f huC hux
    exact (not_lt_of_ge hx) hm_gt
  · intro hx
    rw [mem_lowerLevelSet_iff]
    exact minkowskiGauge_le_one_of_mem C hx

end ClosedLevelSet

section GaugeBridgeAbsorbent

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

/-- Helper for Corollary 14 13: for absorbent sets, the source-facing Minkowski gauge agrees with
mathlib's canonical real-valued gauge viewed in `EReal`. -/
theorem minkowskiGauge_eq_coe_gauge_of_absorbent
    (C : Set H) (hC_absorbent : Absorbent ℝ C) :
    m[C] = fun x ↦ (gauge C x : EReal) := by
  -- Compare the two gauges through the same strict real upper bounds.
  funext x
  apply le_antisymm
  · refine le_of_forall_gt_imp_ge_of_dense ?_
    intro b hb
    obtain ⟨r, hr_left, hr_right⟩ := EReal.exists_between_coe_real hb
    have hm_lt : m[C] x < (r : EReal) := by
      exact minkowskiGauge_lt_of_gauge_lt C hC_absorbent (EReal.coe_lt_coe_iff.mp hr_left)
    exact le_trans hm_lt.le hr_right.le
  · refine le_of_forall_gt_imp_ge_of_dense ?_
    intro b hb
    obtain ⟨r, hr_left, hr_right⟩ := EReal.exists_between_coe_real hb
    have hg_lt : gauge C x < r := gauge_lt_of_minkowskiGauge_lt C hC_absorbent hr_left
    exact le_trans (EReal.coe_lt_coe_iff.mpr hg_lt).le hr_right.le

end GaugeBridgeAbsorbent

section GaugeBridge

variable {H : Type u} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H]
  [ContinuousSMul ℝ H]

-- Proof sketch: when `0 ∈ interior C`, the set of positive scalars used to define `m[C] x` is
-- nonempty for every `x`, so the source-facing `EReal`-valued gauge is exactly mathlib's canonical
-- real-valued `gauge C`, viewed in `EReal`.
/-- Bridge for Corollary 14 13 (2): if `0 ∈ interior C`, then the source-facing Minkowski gauge
`m[C]` agrees pointwise with mathlib's canonical owner `gauge C`, viewed in `EReal`. -/
theorem minkowskiGauge_eq_coe_gauge_of_zero_mem_interior
    (C : Set H) (h0C : (0 : H) ∈ interior C) :
    m[C] = fun x ↦ (gauge C x : EReal) := by
  -- Interior membership gives absorbency, so the absorbent bridge applies directly.
  exact minkowskiGauge_eq_coe_gauge_of_absorbent C
    (absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp h0C))

-- Proof sketch: rewrite the source-facing gauge `m[C]` to the canonical owner `gauge C` through
-- `minkowskiGauge_eq_coe_gauge_of_zero_mem_interior`, then apply mathlib's
-- `gauge_lt_one_eq_interior`.
/-- Corollary 14 13 (2): clause (ii). If `C` is convex and `0` lies in its interior, then the
strict lower level set `{x | m[C] x < 1}` of the Minkowski gauge is exactly `interior C`. -/
theorem strictLowerLevelSet_minkowskiGauge_one_eq_interior_of_convex_of_zero_mem_interior
    [IsTopologicalAddGroup H]
    (C : Set H) (hC_convex : Convex ℝ C) (h0C : (0 : H) ∈ interior C) :
    strictLowerLevelSet (m[C]) 1 = interior C := by
  calc
    strictLowerLevelSet (m[C]) 1 = {x | gauge C x < 1} := by
      ext x
      rw [mem_strictLowerLevelSet_iff, minkowskiGauge_eq_coe_gauge_of_zero_mem_interior C h0C,
        EReal.coe_lt_coe_iff]
      change gauge C x < 1 ↔ gauge C x < 1
      rfl
    _ = interior C :=
      gauge_lt_one_eq_interior hC_convex (mem_interior_iff_mem_nhds.mp h0C)

end GaugeBridge

end ERealFunction
