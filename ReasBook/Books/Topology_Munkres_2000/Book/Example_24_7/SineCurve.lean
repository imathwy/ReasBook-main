module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Connected.PathConnected

public section

open Filter Set Topology

namespace TopologistsSineCurve

/-- The oscillating graph used to define the topologist's sine curve. -/
@[expose]
def curve : Set (ℝ × ℝ) :=
  (fun x : ℝ ↦ (x, Real.sin (1 / x))) '' Ioc 0 1

/-- The limiting vertical interval of the topologist's sine curve. -/
def vertical : Set (ℝ × ℝ) :=
  ({0} : Set ℝ) ×ˢ Icc (-1) 1

/-- Helper for Example 38.3: membership in the limiting vertical interval is coordinatewise. -/
theorem mem_vertical_iff (z : ℝ × ℝ) :
    z ∈ vertical ↔ z.1 = 0 ∧ z.2 ∈ Icc (-1 : ℝ) 1 := by
  -- Unfold the product set and identify membership in the singleton first coordinate.
  simp only [vertical, mem_prod, mem_singleton_iff]

/-- The closure of the oscillating graph in the plane. -/
abbrev carrier : Set (ℝ × ℝ) :=
  closure curve

/-- The topologist's sine curve as a topological subspace of the plane. -/
abbrev Space := carrier

/-- The oscillating-graph part of the topologist's sine curve. -/
def curvePart : Set Space :=
  Subtype.val ⁻¹' curve

/-- The vertical-interval part of the topologist's sine curve. -/
def verticalPart : Set Space :=
  Subtype.val ⁻¹' vertical

/-- Helper for Example 24.7: a closure point with nonzero first coordinate lies on the graph. -/
private lemma mem_curve_of_mem_closure_fst_ne_zero {p : ℝ × ℝ}
    (hp : p ∈ closure curve) (hp_ne : p.1 ≠ 0) : p ∈ curve := by
  rw [mem_closure_iff_seq_limit] at hp
  obtain ⟨v, hv_curve, hv_lim⟩ := hp
  have hx_lim : Filter.Tendsto (fun n ↦ (v n).1) Filter.atTop (𝓝 p.1) :=
    continuousAt_fst.tendsto.comp hv_lim
  have hy_lim : Filter.Tendsto (fun n ↦ (v n).2) Filter.atTop (𝓝 p.2) :=
    continuousAt_snd.tendsto.comp hv_lim
  have hpos : 0 ≤ p.1 := by
    apply ge_of_tendsto hx_lim
    filter_upwards with n
    rcases hv_curve n with ⟨x, hx, hv⟩
    rw [← hv]
    exact hx.1.le
  have hle : p.1 ≤ 1 := by
    apply le_of_tendsto hx_lim
    filter_upwards with n
    rcases hv_curve n with ⟨x, hx, hv⟩
    rw [← hv]
    exact hx.2
  have hsin_lim :
      Filter.Tendsto (fun n ↦ Real.sin (1 / (v n).1)) Filter.atTop
        (𝓝 (Real.sin (1 / p.1))) := by
    have hcont : ContinuousAt (fun x : ℝ ↦ Real.sin (1 / x)) p.1 := by
      fun_prop
    exact hcont.tendsto.comp hx_lim
  have hy_eq : p.2 = Real.sin (1 / p.1) := by
    apply tendsto_nhds_unique hy_lim
    convert hsin_lim using 1
    funext n
    rcases hv_curve n with ⟨x, hx, hv⟩
    rw [← hv]
  exact ⟨p.1, ⟨lt_of_le_of_ne hpos (Ne.symm hp_ne), hle⟩, Prod.ext rfl hy_eq.symm⟩

/-- Helper for Example 24.7: every point of the limiting vertical interval is a graph limit. -/
private lemma vertical_subset_closure_curve : vertical ⊆ closure curve := by
  rintro ⟨x, y⟩ hp
  rcases hp with ⟨hx, hy⟩
  simp only [mem_singleton_iff] at hx
  subst x
  rw [mem_closure_iff_seq_limit]
  let phase : ℕ → ℝ := fun n ↦ Real.arcsin y + (n + 1) * (2 * Real.pi)
  let v : ℕ → ℝ × ℝ := fun n ↦ (1 / phase n, y)
  have hphase_pos (n : ℕ) : 0 < phase n := by
    have harcsin : -(Real.pi / 2) ≤ Real.arcsin y := Real.neg_pi_div_two_le_arcsin _
    have hn : (1 : ℝ) ≤ n + 1 := by norm_num
    dsimp [phase]
    nlinarith [Real.pi_pos]
  refine ⟨v, ?_, ?_⟩
  · intro n
    refine ⟨1 / phase n, ?_, ?_⟩
    · constructor
      · exact one_div_pos.mpr (hphase_pos n)
      · apply (div_le_iff₀ (hphase_pos n)).2
        dsimp [phase]
        have harcsin : -(Real.pi / 2) ≤ Real.arcsin y := Real.neg_pi_div_two_le_arcsin _
        have hn : (1 : ℝ) ≤ n + 1 := by norm_num
        have hpi : (2 : ℝ) ≤ Real.pi := by
          linarith [Real.one_le_pi_div_two]
        nlinarith
    · apply Prod.ext
      · rfl
      · dsimp [v]
        simp only [one_div, inv_inv]
        dsimp [phase]
        convert Real.sin_add_nat_mul_two_pi (Real.arcsin y) (n + 1) using 1
        · norm_num
        exact (Real.sin_arcsin hy.1 hy.2).symm
  · have hphase : Filter.Tendsto phase Filter.atTop Filter.atTop := by
      dsimp [phase]
      apply tendsto_atTop_add_const_left
      have hnat : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) + 1)
          Filter.atTop Filter.atTop :=
        tendsto_atTop_add_const_right Filter.atTop 1 tendsto_natCast_atTop_atTop
      exact hnat.atTop_mul_const
        (show (0 : ℝ) < 2 * Real.pi by positivity)
    have hx : Filter.Tendsto (fun n ↦ 1 / phase n) Filter.atTop (𝓝 0) :=
      (tendsto_inv_atTop_zero.comp hphase).congr fun n ↦ by
        simp only [Function.comp_apply, one_div]
    exact hx.prodMk_nhds tendsto_const_nhds

/-- The closure of the oscillating graph is its union with the limiting vertical interval. -/
theorem carrier_eq_curve_union_vertical : carrier = curve ∪ vertical := by
  apply Set.Subset.antisymm
  · intro p hp
    by_cases hp_zero : p.1 = 0
    · right
      rw [vertical, mem_prod, mem_singleton_iff]
      refine ⟨hp_zero, ?_⟩
      rw [mem_closure_iff_seq_limit] at hp
      obtain ⟨v, hv_curve, hv_lim⟩ := hp
      have hy_lim : Filter.Tendsto (fun n ↦ (v n).2) Filter.atTop (𝓝 p.2) :=
        continuousAt_snd.tendsto.comp hv_lim
      constructor
      · apply ge_of_tendsto hy_lim
        filter_upwards with n
        rcases hv_curve n with ⟨x, hx, hv⟩
        rw [← hv]
        exact Real.neg_one_le_sin _
      · apply le_of_tendsto hy_lim
        filter_upwards with n
        rcases hv_curve n with ⟨x, hx, hv⟩
        rw [← hv]
        exact Real.sin_le_one _
    · left
      exact mem_curve_of_mem_closure_fst_ne_zero hp hp_zero
  · exact union_subset subset_closure vertical_subset_closure_curve

/-- Membership in `curvePart` is ambient membership in the oscillating graph. -/
theorem mem_curvePart_iff (p : Space) : p ∈ curvePart ↔ p.1 ∈ curve := Iff.rfl

/-- Membership in `verticalPart` is ambient membership in the limiting vertical interval. -/
theorem mem_verticalPart_iff (p : Space) : p ∈ verticalPart ↔ p.1 ∈ vertical := Iff.rfl

end TopologistsSineCurve
